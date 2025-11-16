{-# LANGUAGE PatternGuards #-}
module TCMisc(
        splitF, satisfyFV, satisfy,
        reducePred, reducePredsAggressive, expPrimTCons, expTConPred,
        findAssump, mkQualType, closeFD, niceTypes,
        unifyFnFrom, unifyFnTo, unifyFnFromTo,
        mkSchemeNoBVs, rmPatLit, rmQualLit, expandSynN, expandFullType,
        unify, unifyNoEq,
        mkVPred, mkVPredNoNewPos, mkVPredFromPred, toPredWithPositions, toPred,
        defaultClasses,
        checkForAmbiguousPreds,
        propagateFunDeps, isReduciblePred
              ) where

import Data.Maybe
import Data.List
import Control.Monad(foldM, when)
import qualified Data.Map as M
import qualified Data.Set as S
import System.IO.Unsafe(unsafePerformIO)

import ListMap(lookupWithDefault)
import Util
import PFPrint
import Position
import CType
import FStringCompat(mkFString)
import Id
import Error(internalError, EMsg, ErrMsg(..))
import Flags(Flags, useProvisoSAT)
import Type
import Subst
import Assump
import Scheme
import Unify
import Pred
import SATPred
import TIMonad
import PreIds
import StdPrel(isPreClass)
import CSyntax(CDefl(..), CExpr(..), CPat(..), CQual(..),
               CLiteral(..), cTApply, cVApply, anyTExpr)
import Literal
import IntLit
import SymTab
import MakeSymTab(convCQType)
import PreStrings(sAcute)
import IOUtil(progArgs)
import Debug.Trace

-------

doRTrace :: Bool
doRTrace = elem "-trace-type" progArgs
rtrace :: String -> a -> a
rtrace s x = if doRTrace then traces s x else x

doTraceSatisfy :: Bool
doTraceSatisfy = elem "-trace-tc-satisfy" progArgs

satTrace :: String -> a -> a
satTrace s x = if doTraceSatisfy then traces s x else x

satTraceM :: Monad m => String -> m ()
satTraceM s = when (doTraceSatisfy) $ traceM s

doTraceReducePred :: Bool
doTraceReducePred = elem "-trace-tc-reducepred" progArgs
rpTrace :: String -> a -> a
rpTrace s x = if doTraceReducePred then traces s x else x

doVarTrace :: Bool
doVarTrace = elem "-trace-tcvar" progArgs

-------

type DVS = Maybe [TyVar]

splitF :: [TyVar] -> [VPred] -> ([VPred], [VPred])
splitF fs ps = partition (all (`elem` fs) . tv) ps

-------

-- The following "satisfy" functions take a list of predicates
-- ("es" of type [EPred]) which can be assumed to exist (that is, they
-- are the provided context in an explicitly-typed let-binding, and
-- the converted function will take in dictionaries for these
-- predicates).  And they take a list of predicates which were
-- inferred, and need to be solved.  And they return a list of any
-- unsolved predicates, and new definitions for dictionaries of any
-- predicates which were solved.  (The dictionaries are defined in
-- terms of existing dictionaries, such as the "es".)

satisfy :: [EPred] -> [VPred] -> TI ([VPred], [CDefl])
satisfy es ps = satisfyX Nothing es ps

-- This version also takes a list of the variables from the
-- environment, which have been filtered for dependencies.  These
-- TyVars are used only in "genInsts" (in "reducePred") for numeric
-- classes in the StdPrel.  For example (Add x y (TVar v)) only turns
-- into (Add x y (TAdd x y)) if the "v" being replaced isn't in the
-- list of TyVars.
satisfyFV :: [TyVar] -> [EPred] -> [VPred] -> TI ([VPred], [CDefl])
satisfyFV vs es ps =
        satTrace ("satisfyFV " ++ ppReadable ps) $
        satisfyX (Just vs) es ps

satisfyX :: DVS -> [EPred] -> [VPred] -> TI ([VPred], [CDefl])
satisfyX _   es [] = return ([], [])
satisfyX dvs es ps = do
        -- satTraceM ("satisfy enter: " ++ ppString (dvs, ps))
-- it is not clear if applying the substitution here wins or not
        s0 <- getSubst
        (rs, bs, s) <- satisfy' dvs (apSub s0 es) (apSub s0 ps)
--      (rs, bs, s) <- satisfy' dvs es ps
        -- satTraceM ("satisfy exit: " ++ ppString (rs,bs,s) ++ "\n")
        extSubst "satisfyX" s
        return $ (rs, apSub s (map mkDefl bs))

-- break up preds into those affected by a substitution and those not
-- in order to loop more efficiently in satisfy'
split_rs :: Subst -> [VPred] -> ([VPred], [VPred])
split_rs s' rs  = partition affected_pred rs
          -- should only be a few since classes are small
          -- and the substitution comes from a single reducePred
          -- or joinCtx (at the end)
    where changed_tv = getSubstDomain s'
          affected_var v = v `elem` changed_tv
          affected_pred r = any affected_var (tv r)

satisfy' :: DVS -> [EPred] -> [VPred] -> TI ([VPred], [Bind], Subst)
satisfy' dvs es ps = do
       (ps0, s0, bs0) <- joinNeededCtxs ps
       -- satTraceM ("satisfy (join)' = " ++ ppString (ps0, bs0, s0))
       (vp, binds, s) <- sMany dvs es [] bs0 s0 ps0
       -- satTraceM ("satisfy (result)' = " ++ ppString (vp,binds,s))
       return (vp, binds, s)
  where
        -- sMany
        -- Arguments:
        --   dvs - dependent vars, when attempting "last resort" satisfying
        --   es - given preds, which can be assumed for satisfying other preds
        --   rs - preds which we tried to satisfy but couldn't
        --   bs - bindings resulting from satisfying
        --   s  - substitution resulting from satisfying
        --   ps - the predicates to try satisfying
        -- Try satisfying each pred in "ps" in turn.  If "sat" cannot reduce
        -- it entirely (that is, "sat" returns the preds that it reduced to),
        -- then we ignore the result of "sat" and put the predicate aside
        -- (in "rs").  If "sat" can reduce the pred entirely, then we add the
        -- pred to the list of known preds ("es") and we add the bindings
        -- and substitution to the current result.  If the subst gives us
        -- new information about any of the unsatisfied preds ("rs") then
        -- we attempt to solve those again (put them back in "ps") in case
        -- progress can be made with the new information.
        --
        -- XXX Why do we ignore the result when a pred doesn't sat all the way?
        -- Is it for better error messages?  That is, so that we report the
        -- original pred?
        -- XXX Can we at least keep any of the substitution?
        --
        -- Note that we do allow partial results from numeric typeclasses
        -- (but only when not attempting "last resort" satisfying, though
        -- is that condition even necessary?).
        --
        sMany :: DVS -> [EPred] -> [VPred] -> [Bind] -> Subst -> [VPred] ->
                 TI ([VPred], [Bind], Subst)
        sMany dvs es rs bs s [] =
            {- satTrace ("sMany: rs=" ++ ppReadable rs) $ -} do
            (rs', s', bs') <- joinNeededCtxs rs
            let (changed_rs, unchanged_rs) = split_rs s' rs'
            if null changed_rs then do
                checkJoinCtxs "satisfy" rs s' rs'
                return (rs', bs' ++ bs, s' @@ s)
             else
                sMany (dvsSub s' dvs) (apSub s' es) unchanged_rs (bs' ++ bs) (s' @@ s) (apSub s' changed_rs)
        sMany dvs es rs bs s (p:ps) = do
            x <- sat dvs es p
            -- satTrace ("sMany: sat=" ++ ppReadable (p, x)) $ return ()
            case x of
                -- if the predicate failed to reduce away completely,
                -- put it aside and ignore its result,
                -- except when it's a numeric typeclass and we're not doing
                -- "last resort" satisfying
                ((_:_), _, _) | not (vpIsPreClass p) || isJust dvs ->
                    sMany dvs es (p:rs) bs s ps
                (new_ps, bs', s') ->
                    if isNullSubst s' then
                        sMany dvs es (new_ps ++ rs) (bs'++bs) s ps
                    else do
                        let (changed_rs, unchanged_rs) = split_rs s' rs
                        sMany (dvsSub s' dvs) (apSub s' es) (new_ps ++ unchanged_rs) (bs' ++ bs) (s' @@ s) (apSub s' (changed_rs ++ ps))

expTConPred :: VPred -> TI [VPred]
expTConPred (VPred e (PredWithPositions (IsIn c ts) pos)) = do
        vsts <- mapM expPrimTCons ts
        let (vss, ts') = unzip vsts
        return (VPred e (PredWithPositions (IsIn c ts') pos): concat vss)

primTConMap :: [(Id, Id -> Type -> TI ([VPred], Type))]
primTConMap = [(idSizeOf, expSizeOfT),
               (idId, expIdOfT)]

-- default action for TCons
-- no need to recurse because there is no additional structure
defaultTConAp :: Type -> Id -> Type -> TI ([VPred], Type)
defaultTConAp tcon _ t = do
  (ps, t') <- expPrimTCons t
  return (ps, TAp tcon t')

-- expand all primitive type-constructors (SizeOf, Id, ...)
expPrimTCons :: Type -> TI ([VPred], Type)
expPrimTCons (TAp tcon@(TCon (TyCon idcon _ _)) t) = do
  -- traceM ("idcon: " ++ ppReadable idcon)
  let f = lookupWithDefault primTConMap (defaultTConAp tcon) idcon
  f idcon t

expPrimTCons (TAp f a) = do
        (vfs, f') <- expPrimTCons f
        (vas, a') <- expPrimTCons a
        return (vfs++vas, TAp f' a')
expPrimTCons t = return ([], t)

expSizeOfT :: Id -> Type -> TI ([VPred], Type)
expSizeOfT sz t = do
        v <- newTVar "expSizeOfT" KNum sz
        bits <- bitCls
        vp <- mkVPredFromPred [getPosition sz] (IsIn bits [t, v])
        return ([vp], v)

-- eliminate the identity type constructior
expIdOfT :: Id -> Type -> TI ([VPred], Type)
expIdOfT _ t = do -- traceM ("expIdOf: " ++ ppReadable t)
                  return ([], t)

-- This is faster than the old joinCtxs in the pathological case
-- where no contexts are found because we discover that with
-- an O (n log n) sort, instead of an O(n^2) scan
-- We sort by the class, the fundep pattern used and the compressed tyvars
-- More complex, so possibly less efficient than scanning
-- when a suitable match is found early in the list
-- Hopefully a good trade-off
-- XXX For efficiency, we should "join in parallel",
-- i.e. attempt to merge possible substitutions
-- so that we can handle more than one duplicate pred at once
joinCtxs :: [TyVar] -> [VPred] -> Maybe ([VPred], Subst, Bind)
joinCtxs bound_tyvars vps = listToMaybe (mapMaybe matchBlobs joined_blob_list)
  where blob_list = [((c, n, boolCompress (map not bs) ts), vp) |
                     vp@(VPred _ (PredWithPositions (IsIn c ts) _)) <- vps,
                     (n, bs) <- zip [0..] (funDeps c)]
        joined_blob_list = joinByFst blob_list
        matchPreds n (VPred i pp@(PredWithPositions (IsIn c ts) pos))
                     (VPred i' pp'@(PredWithPositions (IsIn _ ts') pos')) = do
          let bs = funDeps c !! n
          -- we could try to capture and use numeric equalities here
          -- but that would require being on the TI monad,
          -- which doesn't seem worth it
          (s, []) <- mgu bound_tyvars (boolCompress bs ts) (boolCompress bs ts')
          let p'' = VPred i' (PredWithPositions (IsIn c ts') (pos' ++ pos))
              rs  = p'':[ vp | vp@(VPred j _) <- vps, j /= i && j /= i']
              pr = removePredPositions pp
          return (rs, s, (i, predToType (apSub s pr), CVar i'))
        -- uniquePairs because we need to try every possible pair of matching VPreds
        matchBlobs ((_,n,_), vps) = listToMaybe $ mapMaybe (uncurry (matchPreds n)) $ uniquePairs vps

-- This function is successful if the list of VPred is empty, indicating
-- that the pred was fully satisfied.  In which case, the bindings and subst
-- can be used freely.
-- If the list of VPred is non-empty, that means that we were able to reduce
-- the given VPred to the list of preds, and the bindings indicate how we got
-- there.  The subst may still be useful b/c it includes what we learned from
-- functional dependencies whether or not the VPred is satisfied "all the way"
--
-- sat corresponds to section 7.2 "Entailment" in the paper
-- Typing Haskell in Haskell
sat :: DVS -> [EPred] -> VPred -> TI ([VPred], [Bind], Subst)
{-
sat dvs ps (VPred w pr@(IsIn bts [t1, TAp szof t2]))
    | name bts == idBits && szof == tSizeOf = do
    traces ("SizeOf " ++ ppReadable pr) $ return ()
    tunify t1 t1 t2        -- XXX t1
    v <- newTVar KNum szof
    sat dvs ps (VPred w (IsIn bts [t1, v]))
-}
sat dvs ps p =
    satTrace ("sat: trying " ++ ppReadable p ++ " in " ++ ppReadable ps) $ do
    whole_stack <- getSatStack
    bound_tyvars <- getBoundTVs
    let lookfor_result :: Maybe ([Bind], (Subst, [(Type,Type)]))
        -- I'm a little worried that matching against the whole_stack
        -- will have lexical scoping issues where p will match against
        -- something very "old", that it should not be able to "see"
        -- due to shadowing or something.  We are probably OK because
        -- the TIMonad is reset for each top-level definition.
        lookfor_result = lookfor bound_tyvars p whole_stack
    case lookfor_result of
      Just (bs, (s, [])) ->
         -- tie the recursive knot!
         -- traces ("recursive knot: " ++ (ppString p) ++ " = " ++ (ppString lookfor_result))$
         case p of
           (VPred vp (PredWithPositions (IsIn cl tys) poss))
            | (name cl) == (CTypeclass idBits)
               -> err (makeERecursiveBitsErrorMessage poss tys cl)
                  {-
                  internalError (
                                   "cl: " ++ (ppString cl) ++
                                   "\n\ntys: " ++ (ppString tys) ++
                                   "\n\npos: " ++ (ppString pos) ++
                                   "\n\nlf: " ++ (ppString lookfor_result) ++
                                   "\n\nvp: " ++ (ppString vp) ++
                                   "\n\nvp tys: " ++ (pfpString tys) ++
                                    ""
                                  )
                                  -}
           -- if we satisfy numeric provisos recursively, we haven't proven it
           (VPred vp (PredWithPositions (IsIn cl _) poss)) | isPreClass cl ->
                   return ([p], [], nullSubst)
           _ -> satTrace ("sat recursive: " ++ ppReadable (p, bs, s)) $
                return ([], bs, s)
      _ -> do
       let this_point :: TSSatElement
           this_point = (mkTSSatElement dvs ps p)
       incrementSatStack this_point
       return_val <- case lookfor bound_tyvars p (concatMap bySuperE ps) of
         Just (bs, (s, [])) -> do
             satTrace ("sat in super: " ++ ppReadable (p, concatMap bySuperE ps)) $ return ()
             return ([], bs, s)
         -- we might introduce a numeric equality here, so try instance reduction first
         m_equals -> do
          -- if instance reduction fails, fall back to introducing an equality
          let fail msg =
                case m_equals of
                  Just (bs, (s, num_eqs)) -> do
                    satTrace ("sat in super (num eq): " ++ ppReadable (p, concatMap bySuperE ps, num_eqs)) $ return ()
                    eq_ps <- mapM (eqToVPred (getVPredPositions p)) num_eqs
                    satMany (dvsSub s dvs) (apSub s ps) [] bs s eq_ps
                  Nothing -> satTrace msg $ return ([p], [], nullSubst)
          ai <- getAllowIncoherent
          x  <- reducePred ps dvs p
          case x of
            Nothing -> fail "sat unreduced"
            Just (qs, b, us, Nothing) ->
                satTrace ("sat calls satMany ") $ do
                satMany (dvsSub us dvs) (apSub us ps) [] [b] us qs -- qs should have us applied already
            Just (qs, b, us, Just (h@(IsIn c _))) | fromMaybe ai (allowIncoherent c) ->
              satTrace ("sat calls satMany (incoherent) ") $ do
              result <- satMany (dvsSub us dvs) (apSub us ps) [] [b] us qs
              case result of
                (ps@(_:_), bs, s_final) -> return $ (ps, bs, s_final)
                ([], bs, s_final) -> do
                  let (vp_pred, inst_pred) = niceTypes (apSub s_final (toPred p, h))
                  let pos = getPosition $ getVPredPositions p
                  when (allowIncoherent c /= Just True) $
                    twarn (pos, WIncoherentMatch (pfpString vp_pred) (pfpString inst_pred))
                  return $ ([], bs, s_final)
            bad_match -> fail ("sat incoherent disallowed: " ++ ppReadable bad_match)
       decrementSatStack
       return return_val

makeERecursiveBitsErrorMessage :: [Position] -> [Type] -> Class -> EMsg
-- a somewhat hacky function which tries to come up with the best
-- error message possible
makeERecursiveBitsErrorMessage poss tys cl =
    let remove_tyvars :: Type -> Bool
        -- often TVars are compiler generated and not useful.
        remove_tyvars (TVar _) = False
        remove_tyvars _ = True
    in
    ((case poss of
            [] -> noPosition
            -- first position seems as good as any
            pos1:_ -> pos1 ),
         (ERecursiveBits
          (pfpString (name cl))
          (case (filter remove_tyvars tys) of
             [] -> pfpString tys
             [singleton] -> pfpString singleton
             list -> pfpString list)
         ))

-- make sure we've joined contexts "all the way"
checkJoinCtxs :: String -> [VPred] -> Subst -> [VPred] -> TI ()
checkJoinCtxs tag rs s rs' = do
  bound_tyvars <- getBoundTVs
  when (isJust (joinCtxs bound_tyvars rs')) $
    internalError ("incomplete join (" ++ tag ++ "): " ++ ppReadable (rs, rs', s))

joinNeededCtxs :: [VPred] -> TI ([VPred], Subst, [Bind])
joinNeededCtxs = joinNeededCtxs' nullSubst []

joinNeededCtxs' :: Subst -> [Bind] -> [VPred] -> TI ([VPred], Subst, [Bind])
joinNeededCtxs' s bs ps = do
  bvs <- getBoundTVs
  case (joinCtxs bvs ps) of
    Nothing ->
        return (ps, s, bs)
    Just (ps', s', b) ->
        let (changed_rs, unchanged_rs) = split_rs s' ps'
            rs' = (apSub s' changed_rs) ++ unchanged_rs
        in joinNeededCtxs' (s' @@ s) (b:bs) rs'

-- as we commit to substitutions, we extend the monad with them
-- we preserve them this far so we can efficiently decide which
-- preds to retry satisfying
--
-- Return values are similar to "sat" since they recursively call each other.
satMany :: DVS -> [EPred] -> [VPred] -> [Bind] -> Subst -> [VPred] ->
           TI ([VPred], [Bind], Subst)
-- rs_accum is an accumulating parameter of "needed" VPreds
-- if satisfying fails these are returned (for error messages and ctxReduce)
satMany dvs es [] bs s [] = return $ ([], bs, s)
satMany dvs es rs_accum bs s [] = do
  (final_rs, s', bs') <- joinNeededCtxs rs_accum
  return $ (final_rs, bs' ++ bs, s' @@ s)
satMany dvs es rs_accum bs s (p:ps) = do
    x <- sat dvs es p
    rtrace ("satMany: sat="++ ppReadable (p,x)) $ return ()
    case x of
        (needed@(_:_), bs', s') ->
            -- If we are unable to satisfy "p", we add the "needed"
            -- preds to the "rs_accum" argument, potentially heading toward
            -- the "return Nothing" case above.
            -- We also accum the bindings to get from "p" to "needed".
            -- we keep growing the substitution because anything we
            -- have learned we can commit to
            --
            -- We apply the substitution to the "needed" preds because we
            -- encounted an example where they were unsubstituted and that
            -- prevented satisfying -- is this apSub just covering for an
            -- issue elsewhere (that should not have returned unsubst'd preds)?
            --
            rtrace ("satMany Right: " ++ ppReadable needed) $
            satMany dvs es ((apSub s' needed) ++ rs_accum) (bs'++bs) (s' @@ s) ps
        ([], bs', s') ->
            -- If p is satisfied, we "drop" it, but add its binding and
            -- substitution.
            if isNullSubst s' then
                -- Straight-up drop it
                rtrace ("satMany Left True") $
                satMany dvs es rs_accum (bs'++bs) s ps
            else do
              let (changed_rs, unchanged_rs) = split_rs s' rs_accum
              if null changed_rs then
                 -- no impact on accumulated predicates
                 rtrace ("satMany Left False True") $
                 satMany dvs es rs_accum (bs'++bs) (s' @@ s) (apSub s' ps)
               else
                -- Drop it, but try from the beginning again to see if any of
                -- the accumulated rs's can now be
                -- satisfied in the New State Of The World.  This might lead to
                -- horrible running time in the worst case.
                rtrace ("satMany Left False False") $ do
                let rs' = (apSub s' changed_rs) ++ unchanged_rs
                (rs'', s1, bs1) <- joinNeededCtxs rs'
                let s2 = s1 @@ s'
                satMany (dvsSub s2 dvs) (apSub s2 es) [] (bs1 ++ bs'++ bs)
                        (s2 @@ s) (rs'' ++ apSub s2 ps)

-- try to reduce the supplied VPreds as far as possible
-- returning the underlying preds required
reducePredsAggressive :: DVS -> [EPred] -> [VPred] -> TI ([VPred], [CDefl], Subst)
reducePredsAggressive dvs es vps0 = do
  -- traceM ("reducePredsAggressive (enter): " ++ ppReadable vps0)
  (vps1, s1, bs1) <- joinNeededCtxs vps0
  checkJoinCtxs "reducePredsAggressive 1" vps0 s1 vps1
  reducePredsAggressive' dvs es bs1 s1 vps1

reducePredsAggressive' :: DVS -> [EPred] -> [Bind] -> Subst -> [VPred] ->
                          TI ([VPred], [CDefl], Subst)
reducePredsAggressive' dvs es bs1 s1 vps1 = do
  (vps2, bs2, s2) <- maskAllowIncoherent $ satMany dvs es [] [] s1 vps1
  checkJoinCtxs "reducePredsAggressive 2" vps1 s2 vps2
  let allPredTyCons = concat [ concatMap allTyCons ts | IsIn _ ts <- map toPred vps2 ]
  let badCon (TyCon _ _ (TItype _ _)) = True
      badCon (TyCon i _ _) = isJust (lookup i primTConMap)
      badCon _ = False
  if (any badCon allPredTyCons) then do
    -- loop to keep synonyms and SizeOf out of instance heads
    vps2' <- concatMapM (expTConPred . expandSynVPred) vps2
    reducePredsAggressive' dvs es (bs1 ++ bs2) s2 vps2'
   else do
    -- satMany is inside a loop, so it doesn't consistently apply
    -- its accumulated substitution to the reduced predicates.
    -- Apply the substitution here to clean that up before returning
    -- to the external caller.
    return (apSub s2 vps2, map mkDefl (bs1 ++ bs2), s2)

-- note that the subst we return is safe to commit to as long as the
-- instance match isn't incoherent (or if we are ok committing to an
-- incoherent match)
reducePred :: [EPred] -> DVS -> VPred ->
              TI (Maybe ([VPred], Bind, Subst, Maybe Pred))
reducePred eps dvs (VPred w pp@(PredWithPositions pr@(IsIn c ts) pos)) = do
    pushSatStackContext
    bound_tyvars <- getBoundTVs
    ts' <- mapM normT ts
    let pr' = IsIn c ts'
        pp' = PredWithPositions pr' pos
        v' = VPred w pp'
        f :: Bool -> [Inst] -> TI (Maybe ([VPred], Bind, Subst, Maybe Pred))
        f incoherent [] = return Nothing
        f incoherent (i:is) = do
                (m_tv, i'@(Inst _ _ (_ :=> h) _)) <- newInst i (getVPredPositions v')
                x <- byInst v' i'
                case x of
                   Nothing -> do
                     let chk = predUnify bound_tyvars pr' h
                     f (chk || incoherent) is
                   Just (qs, b, (inst_subst, fd_subst)) -> do
                     -- when ((not $ null qs) && (not $ isNullSubst inst_subst)) $
                     --     traceM("qs, inst_subst, fd_subst: " ++ ppReadable (qs, inst_subst, fd_subst))
                     -- does the inst_subst affect anything *outside* of the instance?
                     let bad_inst_subst = fromMaybe inst_subst $
                                          fmap (flip trimSubst $ inst_subst) m_tv
                     when (not (isNullSubst bad_inst_subst)) $
                       internalError("reducePred - bad inst subst: " ++
                                     ppReadable (v', i', m_tv, inst_subst, fd_subst, incoherent))
                     let Inst _ _ (_ :=> h) _ = i
                     let minst = toMaybe incoherent h
                     return $ Just (qs,b,fd_subst,minst)

    let is' = genInsts c bound_tyvars dvs pr'
    r <- f False is'
    rpTrace ("reducePred " ++ ppReadable (dvs, pr', is', r)) $ return ()
    popSatStackContext
    flags <- getFlags
    if (useProvisoSAT flags) && (isNothing r) && (isPreClass c)
      then do --traceM("attempting to solve numeric proviso")
              let ps = [ p | (EPred _ p) <- eps ]
              let res = unsafePerformIO $ do
                          s <- initSATPredState flags
                          (r, _) <- solvePred s ps pr'
                          return r
              case res of
                Nothing -> do
                    --traceM("   failed.")
                    return Nothing
                Just _ -> do
                    -- XXX for now, no new info is learned, just sat
                    --traceM("   success.")
                    let r = anyTExpr (predToType pr')
                    let b = (w, predToType pr', r)
                    return $ Just ([], b, nullSubst, Nothing)
      else return r

predUnify :: [TyVar] -> Pred -> Pred -> Bool
predUnify bound_tyvars (IsIn c1 ts1) (IsIn c2 ts2)
    | c1 == c2 = isJust (mgu bound_tyvars ts1 ts2)
    | otherwise = False

dvsSub :: Subst -> DVS -> DVS
dvsSub s dvs = dvs
{-
dvsSub _ Nothing = Nothing
dvsSub s dvs =
    if isNullSubst s then
        dvs
    else
        traces ("dvsSub " ++ ppReadable (dvs, s)) dvs
-}

byInst :: VPred -> Inst -> TI (Maybe ([VPred], Bind, (Subst, Subst)))
byInst (VPred i p) (Inst e _ (ps :=> h) _) = do
    -- no longer necessary because reducePred now provides a fresh instance
    -- Inst e _ (ps :=> h) <- newInst ii (getPredPositions p)
    bound_tyvars <- getBoundTVs
    let m = matchTop bound_tyvars matchList
                     h (removePredPositions p)
    -- rtrace ("byInst " ++ ppReadable (p, ps :=> h, m)) $ return ()
    case m of
     Nothing -> return Nothing
     Just (inst_subst, (fd_subst, num_eqs)) -> do
        let s = fd_subst @@ inst_subst
        vs <- mapM (const newDict) ps
        -- if the instance is recursive (has a proviso for itself and expects
        -- a dictionary argument for that), then don't use a new dictionary
        -- for that argument, just pass the instance to itself
        let vs' = zipWith (\ x y -> if (y == p) then i else x) vs (apSub s ps)
        eq_ps <- mapM eqToPred num_eqs
        let eq_pwps = map (mkPredWithPositions []) eq_ps
        eq_vs <- mapM (const newDict) eq_pwps
        -- if p introduces a new predicate, carry on the position info
        let mkvpred x y = VPred x (addPredPositions y (getPredPositions p))
            -- if the instance is recursive one of these will be unused?
            ps' = zipWith mkvpred (vs ++ eq_vs) (map (apSub s) (ps ++ eq_pwps))
            t = predToType (apSub s h)
            e' = apSub s e
        ps'' <- concatMapM (expTConPred . expandSynVPred) ps'
        -- rtrace ("byInst: " ++ ppReadable (ps', e', t)) $ return ()
        return (Just (ps'', (i, t, CApply e' (map CVar vs')), (inst_subst, fd_subst)))

-- Create a new instance by replacing the type variables in the instance
-- with fresh variables.
-- Give the variables a position based on where the predicate was
-- introduced (the list of positions is the positions where the predicate
-- was introduced). XXX unfortunately we can only pass one pos to the var
-- Also the lowest TVar, for use in trimming
newInst :: Inst -> [Position] -> TI (Maybe TyVar, Inst)
newInst ii@(Inst _ vs _ _) poss = do
    let getpos v = getMostUsefulPosition poss (getPosition v)
    when doVarTrace $ traceM ("newInst " ++ ppReadable ii)
    ts <- mapM (\ v -> newTVar "newInst" (kind v) (getpos v)) vs
    let v = case ts of
                (TVar x:xs) -> Just x
                _ -> Nothing
    return (v, apSub (mkSubst (zip vs ts)) ii)

lookfor :: [TyVar] -> VPred -> [EPred] -> Maybe ([Bind], (Subst, [(Type, Type)]))
lookfor bound_tyvars _ [] = Nothing
lookfor bound_tyvars v@(VPred i pp) eps@(EPred e pr':ps) =
    let pr = removePredPositions pp
        meq x y = if x == y then Just nullSubst else Nothing
    in  -- traces ("lookfor " ++ ppReadable (pr, pr', matchTop bound_tyvars meq pr pr', ps)) $
        case matchTop bound_tyvars meq pr pr' of
        Just (inst_subst, fd_subst_and_eqs) | isNullSubst inst_subst ->
            Just ([(i, predToType pr, e)], fd_subst_and_eqs)
        Just (inst_subst, fd_subst) ->
            internalError ("lookfor bad: " ++
                           ppReadable (bound_tyvars, v, eps, inst_subst, fd_subst))
        Nothing -> lookfor bound_tyvars v ps

commute :: [Type] -> [Type]
commute ts@[t1,t2] = [t2, t1]
commute ts@[t1,t2,t3] = [t2, t1, t3]
commute _ = internalError("commutative class not taking two or three arguments")

bySuperE :: EPred -> [EPred]
bySuperE ep@(EPred e p@(IsIn c ts)) = ep : eps ++ comm
  where s       = mkSubst (zip (csig c) ts)
        esupers = map (\ (CTypeclass i, p) ->
                        let p' = apSub s p
                        in  EPred (CApply (cTApply (CSelectT (typeclassId $ name c) i) ts) [e]) p') (super c)
        eps     = concatMap bySuperE esupers
        comm    = if (isComm c) then {- (traces ("expr: " ++ ppReadable e) $-}
                     [(EPred e (IsIn c (commute ts)))]
                  else []

-- Given:
-- * bound variables
-- * a function for determining when two predicates "match"
--   (by matching their lists of type parameters)
--   which returns the substitution which makes them match
-- * two predicates
-- Returns:
-- * two substitutions:
--     the first is applied to the instance (to specialize it)
--     the second is anything we've learned from fundeps (added to the monad)
--     the second substitution is paired with any numeric equalities we discover
--      we need
--
-- This function is used by byInst to test if a predicate matches an instance,
-- where the "match" function is list unification.  By changing the match
-- function, this could be used in other ways.
--
matchTop :: [TyVar] ->
            ([Type] -> [Type] -> Maybe Subst) ->
            Pred -> Pred -> Maybe (Subst, (Subst, [(Type, Type)]))
matchTop bound_tyvars mtch (IsIn c1 ts1) (IsIn c2 ts2) =
    -- rtrace ("matchTop: " ++ ppReadable (IsIn c1 ts1, IsIn c2 ts2, c1==c2)) $
    if c1 /= c2 then
        -- different classes obviously don't match
        Nothing
    else
        -- rtrace ("matchTop 0: " ++ ppReadable (name c1, funDeps c1, ts1, ts2)) $
        let mfd bs =
                -- first check that the nonfundep types match
                let nbs = map not bs
                    v1 = (boolCompress nbs ts1)
                    v2 = (boolCompress nbs ts2)
                    mv = mtch v1 v2
                in
                case mv of
                Nothing ->
                    -- rtrace ("matchTop 1a: " ++ ppReadable (v1, v2, mv)) $
                    Nothing
                Just ms ->
                    -- if the nonfundep types match, then apply the found
                    -- substitution and see if the fundep types match
                    -- rtrace ("matchTop 1b: " ++ ppReadable ms) $
                    case mgu bound_tyvars (apSub ms (boolCompress bs ts1))
                                          (apSub ms (boolCompress bs ts2)) of
                    Nothing -> Nothing
                    Just us ->  Just (ms, us)
        in
            -- find the first fundep list which matches
            -- XXX the fundep lists are not used jointly?
            pickJust (map mfd (funDeps c1))

pickJust :: [Maybe a] -> Maybe a
pickJust mxs = foldr pickL Nothing mxs
  where pickL m@(Just _) _ = m
        pickL _          m = m


-------

findAssump :: Id -> [Assump] -> TI Assump
findAssump i as =
    case [ sc | (i':>:sc) <- as, i==i' ] of
    [] -> do
        s <- getSymTab
        case findVar s i of
         Nothing -> errorAtId EUnboundVar i
         Just (VarInfo _ a d _) -> do
            case d of
                Nothing -> return ()
                Just str -> twarn (getPosition i,
                                   WDeprecated "definition" (pfpString i) str)
            return (updAssumpPos i a)
    sc : _ -> return (i :>: sc)

-------


mkSchemeNoBVs :: CQType -> TI Scheme
mkSchemeNoBVs cqt = do
    sy <- getSymTab
    bvs <- getBoundTVs
    case convCQType sy cqt of
     Left emsg -> err emsg
     Right qt -> return (quantify (tv qt \\ bvs) qt)

mkQualType :: CQType -> TI (Qual Type)
mkQualType cqt = do
    s <- getSymTab
    case convCQType s cqt of
     Left emsg -> err emsg
     Right qt -> return qt

-------

rmPatLit :: CPat -> TI (CPat, [CQual])
--rmPatLit p = return (p, [])
rmPatLit (CPCon i ps) = do
    pqs <- mapM rmPatLit ps
    let (ps', qss) = unzip pqs
    return (CPCon i ps', concat qss)
rmPatLit (CPstruct mb i ips) = do
    let f (i, p) = do (p, qs) <- rmPatLit p; return ((i, p), qs)
    ipqs <- mapM f ips
    let (ips', qss) = unzip ipqs
    return (CPstruct mb i ips', concat qss)
rmPatLit p@(CPVar _) = return (p, [])
rmPatLit (CPAs i p) = do
    (p', qs) <- rmPatLit p
    return (CPAs i p', qs)
rmPatLit p@(CPAny {}) = return (p, [])
rmPatLit (CPLit (CLiteral p l)) = do
    v <- newVar p "rmPatLit"
    return (CPVar v, [CQFilter (cVApply idEqual [CVar v, CLit (CLiteral p l)])])
rmPatLit (CPMixedLit pos base ps) = do
    -- only binary, hex and octal are legal
    let bitwidth = log2 base
    v <- newVar pos "rmPatLit"
    let mkLit len val = CLit (CLiteral pos (LInt (IntLit { ilWidth = Just len,
                                                           ilBase = base,
                                                           ilValue = val })))
        mkUnsizedLit val = CLit (CLiteral pos (LInt (ilDec val)))
    let foldfunc (len, Nothing)  (idx, quals) = (idx + (len * bitwidth), quals)
        foldfunc (len, Just val) (idx, quals) =
            let bitsize = len * bitwidth
                lo = mkUnsizedLit idx
                hi = mkUnsizedLit (idx + bitsize - 1)
                extract_expr = CSub2 (CVar v) hi lo
                val_expr = mkLit bitsize val
                q = CQFilter (cVApply idEqual [extract_expr, val_expr])
            in  (idx + bitsize, q:quals)
        (_, quals) = foldr foldfunc (0,[]) ps
    return (CPVar v, quals)
rmPatLit (CPCon1 ti i p) = do
    (p', qs) <- rmPatLit p
    return (CPCon1 ti i p', qs)
rmPatLit (CPConTs ti i ts ps) = do
    pqs <- mapM rmPatLit ps
    let (ps', qss) = unzip pqs
    return (CPConTs ti i ts ps', concat qss)
rmPatLit _ = internalError "TCMisc.rmPatLit"

rmQualLit :: CQual -> TI [CQual]
rmQualLit q@(CQFilter _) = return [q]
rmQualLit (CQGen i p e) = do
    (p', qs) <- rmPatLit p
    return (CQGen i p' e : qs)

-------

-- only for expanding synonyms when you are NOT on a type-checking monad
-- will substitute in fresh variables for all type variables in the input type
-- to avoid variable capture
expandSynN :: Flags -> SymTab -> Type -> Type
expandSynN flags s t =
   -- should only need to match instances for coherent typeclasses
   -- XXX user code corner-case?
   case fst $ runTI flags False s $
                do addBoundTVs (tv t) -- to prevent generated variable capture
                   normT t
   of  Left msg -> internalError ("expandSynN " ++ ppReadable msg)
       Right t  -> t

normT :: Type -> TI Type
normT t = do
    let t' = expandSyn t
    (ps, t'') <- expPrimTCons t'
    -- traceM ("normT: " ++ ppReadable (t,t',(ps,t'')))
    if null ps then
        return t''
     else do
        (ps', _) <- satisfy [] ps
        --unless (null ps') (internalError ("expandSynN " ++ ppReadable (t, ps')))
        if not (null ps') then
            return t'                -- XXX could expand some
         else do
            s <- getSubst
            let t''' = expandSyn (apSub s t'')
            --traces ("normT " ++ ppReadable (ps', t''', s)) $ return ()
            return t'''

-- expands synonyms and applies the substitution
-- to get a "fully desugared" type based on all
-- available information
expandFullType :: Type -> TI (Type)
expandFullType t = do
                      sy <- getSymTab
                      s <- getSubst
                      tunexp  <- normT t
                      let t' = expandSyn (apSub s tunexp)
                      return (t')

----
-- a::x is only used for error reporting
unify :: (PPrint a, PVPrint a, HasPosition a)
      => a -> Type -> Type -> TI ([VPred])
unify x t1 t2 = do
    let pos = getPosition x
    -- traceM("unify 1: " ++ ppReadable(t1, t2))
    s <- getSubst
    bound_vars <- getBoundTVs
    let t1' = apSub s t1
        t2' = apSub s t2
    -- traceM("unify 2: " ++ ppReadable(t1', t2'))
    case mgu bound_vars t1' t2' of
     Just (u,[])  -> do extSubst "unify" u; return []
     otherwise -> do
        t1'' <- normT t1'
        t2'' <- normT t2'
        -- traceM ("unify 3:\n" ++ ppReadable (t1'', t2''))
        case mgu bound_vars t1'' t2'' of
          Just (u,eqs)  ->
              do extSubst "unify" u
                 mapM (eqToVPred [pos]) eqs
          Nothing -> let (t1'', t2'') = niceTypes (t1', t2')
                     in reportUnifyError bound_vars x t1'' t2''

eqToPred :: (Type, Type) -> TI Pred
eqToPred (t1, t2) = do
  clsNumEq <- numEqCls
  return $ IsIn clsNumEq [t1, t2]

eqToVPred :: [Position] -> (Type, Type) -> TI VPred
eqToVPred poss num_eq = do
  p <- eqToPred num_eq
  mkVPredFromPred poss p

unifyNoEq :: (PPrint a, PVPrint a, HasPosition a)
          => [Char] -> a -> Type -> Type -> TI ()
unifyNoEq loc x t1 t2 = do
  ps <- unify x t1 t2
  when (not $ null ps) $
    internalError ("unexpected unification equalities (" ++ loc ++ "): " ++
                   ppReadable(t1, t2, ps))
  return ()

-----

reportUnifyError :: (PPrint a, PVPrint a, HasPosition a)
                 => [TyVar] -> a -> Type -> Type -> TI b
reportUnifyError bound_vars x orig_t1 orig_t2 =
    let
        def_err = defaultUnifyError x orig_t1 orig_t2

        -- readable versions for err msgs
        x'  = pfpReadable x
        orig_t1' = pfpReadable orig_t1
        orig_t2' = pfpReadable orig_t2

        -- return value mismatch
        err_res r1 r2 =
            err (getPosition x,
                 EFuncMismatchResult x' orig_t1' orig_t2'
                                     (pfpReadable r1) (pfpReadable r2))

        -- mismatch in the number of args
        err_wrong_arg_num n1 n2 =
            err (getPosition x,
                 EFuncMismatchNumArgs x' orig_t1' orig_t2' n1 n2 Nothing)

        -- mismatch in num of args, but we know where the first
        -- type mismatch occurred, so maybe the arg is missing there?
        err_wrong_arg_num_maybe_n n1 n2 startnum =
            err (getPosition x,
                 EFuncMismatchNumArgs x' orig_t1' orig_t2' n1 n2 (Just startnum))

        -- mismatch in the type of argument n
        err_arg_n num a1 a2 =
            err (getPosition x,
                 EFuncMismatchArgN x' orig_t1' orig_t2'
                                   num (pfpReadable a1) (pfpReadable a2))

        -- not expecting args
        err_no_args_expected =
            err (getPosition x,
                 EFuncMismatchNoArgsExpected x' orig_t1' orig_t2')

        -- expecting args, but given none
        err_args_expected n =
            err (getPosition x,
                 EFuncMismatchArgsExpected x' orig_t1' orig_t2' n)

        -- This allows more unification that would actually be allowed
        -- because it does not take into account substitutions from previous
        -- unifications.  Therefore a->a->a would match Bool->Int->Int.
        -- This is ok, because it will be reported with the default error.
        canUnify t1 t2 =
            case (mgu bound_vars t1 t2) of
                Nothing -> do -- call normT because unify does
                              t1' <- normT t1
                              t2' <- normT t2
                              case (mgu bound_vars t1' t2') of
                                  Nothing -> return False
                                  Just _  -> return True
                Just _  -> return True

        -- find the number of arguments expected by a type
        findNumArgs :: Type -> Integer
        findNumArgs t = genericLength $ fst $ getArrows t

        -- Try to find the specific mismatch, else report the default
        -- mismatch error on the entire original type.
        -- The 'n' is the number of args which matched so far.
        findMismatch n (TAp (TAp (TCon arr1) a1) r1) (TAp (TAp (TCon arr2) a2) r2)
                      | isTConArrow arr1 && isTConArrow arr2 = do
            b <- canUnify a1 a2
            if (b)
              then findMismatch (n+1) r1 r2
              else let num_args1 = n + 1 + findNumArgs r1
                       num_args2 = n + 1 + findNumArgs r2
                   in  if (num_args1 == num_args2)
                       then err_arg_n (n+1) a1 a2
                       else err_wrong_arg_num_maybe_n num_args1 num_args2 (n+1)
        findMismatch n (TAp (TAp (TCon arr1) a1) r1) t1 | isTConArrow arr1 =
            if (n == 0)
            then err_args_expected (1 + findNumArgs r1)
            else -- see if the return value matches?
                 err_wrong_arg_num (n + 1 + findNumArgs r1) n
        findMismatch n t1 (TAp (TAp (TCon arr2) a2) r2) | isTConArrow arr2 =
            if (n == 0)
            then err_no_args_expected
            else err_wrong_arg_num n (n + 1 + findNumArgs r2)
        findMismatch n t1 t2 =
            if (n == 0)
            then def_err
            else do b <- canUnify t1 t2
                    if (b)
                      then def_err -- couldn't find the mismatch
                      else err_res t1 t2
    in
        findMismatch 0 orig_t1 orig_t2

defaultUnifyError :: (HasPosition a, PPrint a, PVPrint a)
                  => a -> Type -> Type -> TI d
defaultUnifyError x t1 t2 =
    err (getPosition x,
         EUnify (pfpReadable x) (pfpReadable t1) (pfpReadable t2))

-----

-- unify e td (a `fn` rt)
unifyFnFrom :: (HasPosition a, HasPosition b, PPrint b, PVPrint b)
            => a -> b -> Type -> Type -> TI (Type, [VPred])
unifyFnFrom x e (TAp (TAp arr a) r) rt | arr == tArrow = do
    ps <- unify e r rt
    return (a, ps)
unifyFnFrom x e t rt = do
{-
  s <- getSubst
  case apSub s t of
   (TAp (TAp arr a) r) | arr == tArrow -> do
    unify e r rt
    return a
   _ -> do
-}
    v <- newTVar "unifyFnFrom" KStar x
    ps <- unify e t (v `fn` rt)
    return (v, ps)

-- unify e td (at `fn` r)
unifyFnTo :: (HasPosition a, HasPosition b, PPrint b, PVPrint b)
          => a -> b -> Type -> Type -> TI (Type, [VPred])
unifyFnTo x e (TAp (TAp arr a) r) at | arr == tArrow = do
    ps <- unify e a at
    return (r, ps)
unifyFnTo x e t at = do
{-
  s <- getSubst
  case apSub s t of
   (TAp (TAp arr a) r) | arr == tArrow -> do
    unify e a at
    return r
   _ -> do
-}
    v <- newTVar "unifyFnTo" KStar x
    ps <- unify e t (at `fn` v)
    return (v, ps)

-- because we merely break apart the type if it has function structure
-- and create new type variables only if it doesn't
-- we never do anything that might generate numeric equalities
-- unify e td (a `fn` r)
unifyFnFromTo :: (HasPosition a, HasPosition b, PPrint b, PVPrint b)
              => a -> b -> Type -> TI (Type, Type)
unifyFnFromTo x e (TAp (TAp arr a) r) | arr == tArrow = do
    return (a, r)
unifyFnFromTo x e t = do
{-
  s <- getSubst
  case apSub s t of
   (TAp (TAp arr a) r) | arr == tArrow -> do
    return (a, r)
   _ -> do
-}
    v <- newTVar "unifyFnFromTo" KStar x
    r <- newTVar "unifyFnFromTo" KStar x
    unifyNoEq "unifyFnFromTo" e t (v `fn` r)
    return (v, r)

-----

-- clean up synonyms and TCons when VPreds are made
-- they should not be re-introduced later (by predicate reduction)o
mkVPred :: Position -> PredWithPositions -> TI [VPred]
mkVPred pos p = do
    v <- newDict
    expTConPred (expandSynVPred $ VPred v (addPredPositions p [pos]))

mkVPredNoNewPos :: PredWithPositions -> TI [VPred]
mkVPredNoNewPos p = do
    v <- newDict
    expTConPred (expandSynVPred $ VPred v p)

-- entry point when we don't need synonyms reduced
-- mainly deriving and other places where we check reducibility
mkVPredFromPred :: [Position] -> Pred -> TI VPred
mkVPredFromPred poss p = do
  v <- newDict
  return (VPred v $ mkPredWithPositions poss p)

toPredWithPositions :: VPred -> PredWithPositions
toPredWithPositions (VPred _ p) = p

toPred :: VPred -> Pred
toPred p = removePredPositions (toPredWithPositions p)

vpIsPreClass :: VPred -> Bool
vpIsPreClass (VPred _ (PredWithPositions (IsIn cl _) _)) = isPreClass cl


-- Close a set of variables with respect to predicates and their functional
-- dependencies.
-- In otherwords: Extend a set of variables to includes all the variables
-- which depend on them, as indicated in a list of predicates.
closeFD :: [VPred] -> [TyVar] -> [TyVar]
closeFD ps vs =
    let ps' = map toPred ps
    in  closeFD_pred ps' vs

closeFD_pred :: [Pred] -> [TyVar] -> [TyVar]
closeFD_pred ps vs =
    let
        -- extend given one dependency
        step1 ts bs vars_in_set =
            let dependee_exprs  = (boolCompress (map not bs) ts)
                dependee_vars   = tv dependee_exprs
                dependent_exprs = (boolCompress bs ts)
                dependent_vars  = tv dependent_exprs
            in
                -- This intentionally includes situations where the dependee
                -- set is null
                if all (`elem` vars_in_set) dependee_vars
                then vars_in_set `union` dependent_vars
                else vars_in_set

        -- extend for all dependencies for a given predicate
        step p vars_in_set =
            let (IsIn c ts) = p
            in  foldr (step1 ts) vars_in_set (funDeps c)

        vs' = foldr step vs ps
    in
        -- recurse until no new vars are found
        if (length vs == length vs')
        then vs
        else closeFD_pred ps vs'

-------

-- Note that "t" can be a tuple of types, or list of types, or a predicate,
-- because class Types just means that "t" *contains* types.
niceTypes :: (Types t) => t -> t
niceTypes given_type =
        let
            -- Variables in the given "t"
            type_vars :: [TyVar]
            type_vars = tv given_type

            type_var_names = map (getIdString . getTyVarId) type_vars

            -- Make an inexaustible list of nice names
            from_a_to_z prefix = [prefix ++ [letter] | letter <- ['a'..'z']]
            inexhaustible_var_names =
                (map (:[]) ['a'..'z'] ++
                 concatMap from_a_to_z inexhaustible_var_names)

            -- Make the names end with an identifiable suffix
            new_inexhaustible_var_names =
                -- and rule out any existing names
                filter (`notElem` type_var_names) $
                map (\ s -> s ++ sAcute) inexhaustible_var_names

            -- Function to substitute in the new names
            subst_vars :: [TyVar] -> [String] -> [(TyVar, Type)]
            subst_vars (orig_var:rest_orig_vars)
                       new_names@(new_name:rest_new_names)
                | isNewTVar orig_var =
                    let new_id  =
                            -- preserve the "isNewTVar" property
                            setBadId $
                            mkId (getPosition orig_var) (mkFString new_name)
                        new_var = cTVarKind new_id (kind orig_var)
                    in  (orig_var, new_var) :
                        subst_vars rest_orig_vars rest_new_names
                | otherwise =
                    subst_vars rest_orig_vars new_names
            subst_vars [] _ = []
            subst_vars _ [] =
                internalError ("TCMisc.niceTypes: " ++
                               "inexhaustible name supply exhausted")

            -- Create a substitution pairing the existing vars with the new
            var_subst_pairs = subst_vars type_vars new_inexhaustible_var_names
            substitution = mkSubst var_subst_pairs
        in
            apSub substitution given_type

-------

-- The following code is for defaulting types when an explicit type
-- declaration is reached but for which type inference has inferred
-- more contexts than appear in the explicit type.  Any contexts which
-- have variables that appear in the base type result in "context too
-- weak" errors.  For multi-parameter type classes, if some variables
-- are not in the base type, we may want to default them, which could
-- cause the context to be resolved.

-- In the following code we define the classes that are defaultable
-- and how to compute potential default assignments from an
-- unsatisfied predicate. Defaulting can fill in, at most, one
-- "hole" (i.e. potentially ambiguous type variable) in a predicate.
-- Some classes (e.g. Literal) have multiple defaults worth trying
-- while others (e.g. BitExtend) need to compute the default from
-- the other arguments of the predicate.

-- Ideally, Pred.Class would have a field "getDefaults" that would replace
-- getStarDefaults / getNumDefaults, but we'd need syntax for specifying
-- the defaults for of a class (steal / extend the Haskell' proposal?)

-- If more than one class proposes defaults for a particular
-- ambiguous type variable, we currently intersect the proposed defaults
-- (which handles the PrimIndex/Literal/RealLiteral possible overlap with
-- no wasted work). In some cases (particularly if we made defaults more
-- general) it might be better to union the proposed defaults.

-- Classes with *-kind types which can be defaulted
getStarDefaults :: S.Set TyVar -> VPred -> [(TyVar, [Type])]
getStarDefaults fvs (VPred i (PredWithPositions (IsIn (Class {name=(CTypeclass cid)}) ts) _)) =
    case ts of
      [TVar v, _] | cid == idPrimIndex,
                     not (S.member v fvs) -> [(v, [tInteger, tNat noPosition])]
      [TVar v]    | cid == idLiteral,
                     not (S.member v fvs) -> [(v, [tInteger, tNat noPosition, tReal])]
      [TVar v]    | cid == idRealLiteral,
                     not (S.member v fvs) -> [(v, [tReal])]
      [TVar v, n] | cid == idSizedLiteral,
                     not (S.member v fvs) -> [(v, [TAp tBit n, TAp tUInt n, TAp tInt n])]
      [TVar v]    | cid == idStringLiteral,
                     not (S.member v fvs) -> [(v, [tString, tChar])]
      _ -> []

-- Classes with #-kind types which can be defaulted
getNumDefaults :: S.Set TyVar -> VPred -> [(TyVar, [Type])]
getNumDefaults fvs (VPred i (PredWithPositions (IsIn (Class {name=(CTypeclass cid)}) ts) _)) =
    case ts of
      [TVar v, t, _] | cid == idBitExtend,
                        not (S.member v fvs),
                        all (flip S.member $ fvs) (tv t) -> [(v, [t])]
      [t, TVar v, _] | cid == idBitExtend,
                        not (S.member v fvs),
                        all (flip S.member $ fvs) (tv t) -> [(v, [t])]
      [TVar v, t, _] | cid == idAdd,
                        not (S.member v fvs),
                        all (flip S.member $ fvs) (tv t) -> [(v, [cTNum 0 noPosition])]
      [t, TVar v, _] | cid == idAdd,
                        not (S.member v fvs),
                        all (flip S.member $ fvs) (tv t) -> [(v, [cTNum 0 noPosition])]
      _ -> []

getForceDefaults :: S.Set TyVar -> VPred -> [(TyVar, Type)]
getForceDefaults fvs (VPred i (PredWithPositions (IsIn (Class {name=(CTypeclass cid)}) ts) _)) =
    case ts of
      [TVar v]    | cid == idStringLiteral,
                     not (S.member v fvs) -> [(v, tString)]
      _ -> []

-- Takes
--   fixedVars = list of variables from the base type unioned with a
--       list of variables from the context (bound variables, assumptions)
--   givenPreds = explicit predicates provided by the user
--   unsatisfiedPreds = unsatisfied predicates on the base type
--
-- Then, the function identifies ambiguous variables in the predicates
-- and tries to default them.
--
-- It returns:
--   any unsatisfied predicates,
--   any bindings resulting from satisfying predicates, and
--   any remaining ambiguous type variables (which were not defaultable or
--       defaulting didn't succeed).
--
defaultClasses :: [TyVar] -> [EPred] -> [VPred] ->
                  TI ([VPred], [CDefl], [TyVar])
defaultClasses fixedVars givenPreds unsatisfiedPreds =
   let
       -- all variables which are not ambiguous
       fixedVars_closed = closeFD unsatisfiedPreds fixedVars

       fixedVarsSet :: S.Set TyVar
       fixedVarsSet = S.fromList fixedVars_closed

       -- whether a substitution substitutes for a fixed variable
       -- (we use "fixedVars_closed" because we do not want to limit the
       -- fixed variables at all; we'd rather report an ambiguity error)
       subsFixedVar s = any (`S.member` fixedVarsSet) (getSubstDomain s)

       -- identify the ambiguous variables
       -- (we leave it to "handleAmbiguousContext" to filter out any ambig
       -- vars that are determined by other ambig vars)
       ambVarsSet :: S.Set TyVar
       ambVarsSet = S.fromList (concatMap tv unsatisfiedPreds) `S.difference` fixedVarsSet

       isAmbiguousVar v = S.member v ambVarsSet

       preds_with_vars :: [(VPred, [TyVar])]
       preds_with_vars = [(p, filter isAmbiguousVar (tv p)) | p <- unsatisfiedPreds ]

       -- produce a list of
       -- pairs of ambiguous vars and the preds they appear in
       vars_with_preds :: [(TyVar, [VPred])]
       vars_with_preds = M.toList . (M.fromListWith (++)) $
                             [(v,[p]) | (p, vs) <- preds_with_vars, v <- vs]

       preds_to_default = map fst preds_with_vars

       num_defaults  :: [(TyVar, [Type])]
       num_defaults  = concatMap (getNumDefaults  fixedVarsSet) preds_to_default

       star_defaults :: [(TyVar, [Type])]
       star_defaults = concatMap (getStarDefaults fixedVarsSet) preds_to_default

       defaultsMap :: M.Map TyVar [Type]
       defaultsMap = M.fromListWith (intersect) $ num_defaults ++ star_defaults

       -- Given a type variable, a list of predicates in which it
       -- appears, and a type to default to, substitute the default
       -- for the variable in the predicates and determine if "sat"
       -- succeeds for all predicates.  If so, return that substitution.
       -- If a substitution was found by a prior call, just pass its
       -- value through.
       tryDefault :: TyVar -> [VPred] -> (Maybe Subst) -> Type ->
                     TI (Maybe Subst)

       tryDefault i ps Nothing t =
           do
              let s = mkSubst [(i,t)]
                  ps' = apSub s ps

              answer <- satMany (Just fixedVars) givenPreds [] [] s ps'
              return $ case answer of
              -- we reject this default if it does not work for some pred
              -- or if it results in a substitution of a bound variable
                ([], _, s') | not $ subsFixedVar s' -> Just s'
                _ -> Nothing
       tryDefault i ps s@(Just _) t = return s

       tryDefaults :: Subst -> (TyVar, [VPred]) -> TI Subst
       tryDefaults subst (i,ps) =
           do
              let typesToTry = M.findWithDefault [] i defaultsMap
              r <- foldM (tryDefault i ps) Nothing typesToTry
              return $ case r of
                         Nothing -> subst
                         -- only merge agreements so we are (mostly)
                         -- order-independent
                         Just s -> mergeAgreements s subst

       -- take a new subst and the remaining unsatisfied preds, and simplify
       makeResult amb_set s ps = do
         -- see how many total preds are satisfied now
         -- this is different because we're trying to satisfy preds
         -- whether or not they contain ambiguous vars
         (remaining_ps, new_bindings)
             <- satisfyFV fixedVars givenPreds (apSub s ps)

         -- find the remaining ambiguous variables
         -- (this used to intersect the tyvars of the remaining preds with
         -- the original set of ambig vars, but that doesn't work after
         -- forcing, only after defaulting, so we do the real calculation)
         let new_fixedVarsSet = S.fromList (closeFD remaining_ps fixedVars)
             remaining_amb_set = S.fromList (concatMap tv remaining_ps)
                                     `S.difference` new_fixedVarsSet

         return (remaining_ps, new_bindings, remaining_amb_set)

   in
       if (S.null ambVarsSet) then
           -- no defaulting to do
           return (unsatisfiedPreds, [], [])
       else do
            let s0 = nullSubst
            s1 <- foldM tryDefaults s0 vars_with_preds

            let defaulted_vars = getSubstDomain s1
            -- extend the substitution
            extSubst "defaultClasses" s1

            -- numeric defaulting is now an unknown-size error
            let mkNumError v
                    | v `elem` defaulted_vars = [(getPosition v, EUnknownSize)]
                    | otherwise = []
                msgs = nub $ concatMap (mkNumError . fst) num_defaults
            when (not $ null msgs) $ errs "defaultClasses unknown size" msgs

            -- simplify, given what we know
            (remaining_preds, new_bindings, remaining_amb_set)
                <- makeResult ambVarsSet s1 unsatisfiedPreds

            -- see if we need to force any preds
            let typesToForce = concatMap (getForceDefaults fixedVarsSet)
                                   remaining_preds
            if (null typesToForce)
              then return (remaining_preds,
                           new_bindings,
                           S.toList remaining_amb_set)
              else do
                -- otherwise, force these variables and simplify again
                (res_ps, res_bs, res_aset)
                    <-  makeResult remaining_amb_set
                                   (mkSubst typesToForce)
                                   remaining_preds
                -- XXX issue a warning that the types have been forced?
                return (res_ps, res_bs, S.toList res_aset)

-------

-- Given the fixed variables from the context (that is, any vars in
-- the assumptions and any bound vars) and a qualified type, determine
-- if any of the preds in the qualified type are unsatisfiabl because
-- they contain variables not fixed by the caller.

checkForAmbiguousPreds :: Id -> [TyVar] -> Qual Type -> TI ()
checkForAmbiguousPreds i fvs1 qt = do
  -- in order to catch ambiguous variables arising from uses of TLog etc,
  -- expand such TCons into additional predicates
  (qs :=> t) <- expandNumericTCons qt

  let
        -- the explicit predicates
        ps = map removePredPositions qs

        -- fixed vars from the base type
        fvs2 = tv t
        -- all fixed vars
        fvs = fvs1 `union` fvs2
        -- close the fixed vars over fundeps
        cfvs = closeFD_pred ps fvs

        -- ambiguous variables in the predicates
        amb_vars = tv ps \\ cfvs

        hasAmbigVar p = any (`elem` amb_vars) (tv p)

        -- ambiguous predicates
        amb_preds = filter hasAmbigVar ps

        -- pprint
        pfp :: (PPrint a, PVPrint a) => a -> Doc
        pfp = pfPrint PDReadable 0

        -- rename generated typevars with "a__", "b__", etc
        -- (names are only generated by TCon expansion)
        (amb_preds', amb_vars', t') =
            niceTypes (amb_preds, map TVar amb_vars, t)

  if (null amb_vars)
        then return ()
        else err (getPosition i,
                  EAmbiguousExplCtx (map pfp amb_vars')
                                    (map pfp amb_preds')
                                    (pfp t'))

expandNumericTCons :: Qual Type -> TI (Qual Type)
expandNumericTCons (orig_qs :=> orig_t) =
  let
      mkResult cls_id ts v = do
        symt <- getSymTab
        let cls = mustFindClass symt (CTypeclass cls_id)
            p = PredWithPositions (IsIn cls ts) []
        return ([p], v)

      expQual :: PredWithPositions -> TI ([PredWithPositions], PredWithPositions)
      expQual (PredWithPositions (IsIn c ts) poss) = do
        (qs, ts') <- mapM exp ts >>= return . apFst concat . unzip
        return (qs, PredWithPositions (IsIn c ts') poss)

      -- all TCon could be expanded as NumEq#(var,TC) but we go ahead and
      -- expand to the associate typeclass (is this better for err msgs?)
      exp :: Type -> TI ([PredWithPositions], Type)
      exp (TAp tc t)
          | tc == tLog = do v <- newTVar "expandNumericTCons" KNum tc
                            mkResult idLog [t, v] v
          | tc == tExp = do v <- newTVar "expandNumericTCons" KNum tc
                            -- There's no class for this, so use NumEq
                            mkResult idNumEq [v, TAp tc t] v
          | tc == tSizeOf = do v <- newTVar "expandNumericTCons" KNum tc
                               mkResult idBits [t, v] v
      exp (TAp (TAp tc t1) t2)
          | tc == tAdd = do v <- newTVar "expandNumericTCons" KNum tc
                            mkResult idAdd [t1, t2, v] v
          | tc == tSub = do v <- newTVar "expandNumericTCons" KNum tc
                            mkResult idAdd [t1, v, t2] v
          | tc == tMul = do v <- newTVar "expandNumericTCons" KNum tc
                            mkResult idMul [t1, t2, v] v
          | tc == tDiv = do v <- newTVar "expandNumericTCons" KNum tc
                            mkResult idDiv [t1, t2, v] v
          | tc == tMax = do v <- newTVar "expandNumericTCons" KNum tc
                            mkResult idMax [t1, t2, v] v
          | tc == tMin = do v <- newTVar "expandNumericTCons" KNum tc
                            mkResult idMin [t1, t2, v] v
      exp (TAp t1 t2) = do (ps1, t1') <- exp t1
                           (ps2, t2') <- exp t2
                           return (ps1 ++ ps2, TAp t1' t2')
      exp t = return ([], t)
  in
      do
        (new_qs1, orig_qs') <- mapM expQual orig_qs >>=
                                   return . apFst concat . unzip
        (new_qs2, orig_t') <- exp orig_t
        return ((new_qs1 ++ new_qs2 ++ orig_qs') :=> orig_t')


-------

-- Propagation of functional dependencies was more complex
-- before we required fundeps to be full. Now that we have,
-- propagateFunDeps just uses satisfy (for full fundeps,
-- propagation and matching are the same thing).

-- propagateFunDeps returns the supplied predicates updated with
-- any information learned by matching instances. It does not
-- drop any matched predicates because it doesn't bind dictionaries.
-- propagateFunDeps also returns the (possibly smaller) list of
-- unsatisfied predicates for use in fail-fast context reduction
-- (see updateContexts)
propagateFunDeps :: [VPred] -> TI ([VPred], [VPred])
propagateFunDeps ps0 =
  do
    s <- getSubst
    eps <- getExplPreds

    let ps = apSub s ps0
    satTraceM("propagateFunDeps satisfy: " ++ ppReadable ps)

    -- SAT solving of numeric provisos isn't needed for propagating fundeps,
    -- so turn it off, since it appears to be expensive here
    flags <- getFlags
    setFlags (flags { useProvisoSAT = False })

    (ps_unsat, _) <- satisfy eps ps

    -- restore the flags
    setFlags flags

    s' <- getSubst
    return (apSub s' ps, ps_unsat)

-------

-- like "reducePred", but we want to differentiate between those which
-- don't reduce now (not enough type info yet) and those which could
-- never reduce (which we'll want to report an error about now, not later)
--
isReduciblePred :: VPred -> TI Bool
isReduciblePred (VPred i pp@(PredWithPositions p@(IsIn c ts) pos)) |
    -- XXX for now, we don't consider Add, Max, Min, Log, Mul, Div, NumEq
    -- XXX (the "genInsts" of these classes doesn't handle "maybe reducible")
    (isPreClass c) = return True
isReduciblePred (VPred i pp@(PredWithPositions p@(IsIn c ts) pos)) = do
    ts' <- mapM normT ts
    let p' = IsIn c ts'
        pp' = PredWithPositions p' pos
        v' = VPred i pp'
        f [] = getExplPreds >>= g
        f (i:is) = do isReducible <- byInstIsReducible v' i
                      -- if we discover that it could match or definitely
                      -- does not match, then stop; otherwise, try the
                      -- remaining instances
                      case (isReducible) of
                          Fails   -> return False
                          Matches -> return True
                          _       -> f is
        g [] = return False
        g (ep:eps) = do isReducible <- byExplPredIsReducible v' ep
                        case (isReducible) of
                            Fails   -> return False
                            Matches -> return True
                            _       -> g eps
    bvs <- getBoundTVs
    let is' = genInsts c bvs Nothing p'
    r <- f is'
    return r


data MatchResult = NoConclusion
                 | Fails
                 | Matches
                 deriving (Eq)


byInstIsReducible :: VPred -> Inst -> TI MatchResult
byInstIsReducible (VPred i p) ii = do
    (mv, Inst e _ (ps :=> h) _) <- newInst ii (getPredPositions p)
    bound_tyvars <- getBoundTVs
    return $
        matchTopIsReducible bound_tyvars h (removePredPositions p)


-- This is like "matchTop" except that we need to try matching first
-- and if it fails, then we try unifying.  Also, when we try matching,
-- we need to differentiate between failure to match the non-fundep types
-- (which means we still have a chance of matching somewhere else) and
-- matching the non-fundep types but failing to match the dependent types
-- (which is an immediate error, because the fundeps should be unique).
-- Returns:
--  * Nothing if the predicate can be proven unsatisfiable (because the
--    fundeps don't match the unique instance)
--  * Just False if the predicate does not match any existing instances
--  * Just True if the predicate has a chance of matching an existing instance
matchTopIsReducible :: [TyVar] -> Pred -> Pred -> MatchResult
matchTopIsReducible bound_tyvars p1@(IsIn c1 ts1) p2@(IsIn c2 ts2) =
  if c1 /= c2 then
      NoConclusion
  else
      let
          try_match :: [Bool] -> MatchResult
          try_match bs =
              let nbs = map not bs
                  v1 = (boolCompress nbs ts1)
                  v2 = (boolCompress nbs ts2)
                  -- whether the non-fundeps match
                  mv = matchList v1 v2
                  -- whether the non-fundeps unify
                  uv = mgu bound_tyvars v1 v2
                  -- check if the fundeps unify, given a subst for non-fundeps
                  check_fds s =
                      case (mgu bound_tyvars
                                (apSub s (boolCompress bs ts1))
                                (apSub s (boolCompress bs ts2))) of
                        Nothing -> False
                        Just _  -> True
              in
                  case (mv) of
                    Nothing ->
                        -- doesn't match, so try unify
                        case (uv) of
                           Nothing -> NoConclusion
                           Just (s,num_eqs)  ->
                               if (check_fds s && null num_eqs)
                               then Matches
                               else NoConclusion
                    Just s  ->
                        -- it matches, so we have a conclusive answer
                        if (check_fds s)
                        then Matches
                        else -- we'd like to return Fails, but to support
                             -- overlapping instances which disagree on the
                             -- fundeps, we have to accept that there could
                             -- be an overlapping instance where it matches
                             --Fails
                             NoConclusion
      in
          pickFirst (map try_match (funDeps c1))


pickFirst :: [MatchResult] -> MatchResult
pickFirst mbs =
    if (any (== Matches) mbs)
    then Matches
    else if (any (== Fails) mbs)
         then Fails
         else NoConclusion


byExplPredIsReducible :: VPred -> EPred -> TI MatchResult
byExplPredIsReducible (VPred _ p) (EPred _ ep) = do
    bound_tyvars <- getBoundTVs
    return $
        matchExplPred bound_tyvars (removePredPositions p) ep


matchExplPred :: [TyVar] -> Pred -> Pred -> MatchResult
matchExplPred bound_tyvars p1@(IsIn c1 ts1) p2@(IsIn c2 ts2) =
  if c1 /= c2 then
      NoConclusion
  else
      case (matchList ts1 ts2) of
          Nothing -> NoConclusion
          Just s  -> Matches

-------
