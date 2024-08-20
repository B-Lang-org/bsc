module ContextErrors (
                      handleContextReduction,
                      handleWeakContext,
                      handleAmbiguousContext,
                      updateContexts
                      ) where

import Data.List
import qualified Data.Set as S
import Control.Monad(when)

import Position
import Error(internalError, EMsg, ErrMsg(..))
import PFPrint

import Pred

import Subst(Types(..))
import TIMonad
import TCMisc
import Unify

import FStringCompat (FString, mkFString, getFString)
import Id(mkId)
import PreIds
import CSyntax
import Util(separate, concatMapM, quote, headOrErr, toMaybe, boolCompress)
import CType(typeclassId, isTNum, getTNum)

--import Debug.Trace


-- ========================================================================
-- Context Reduction
--

--
-- Given a position where the context reduction failed and
-- a list of the contexts which failed to reduce, this function
-- returns the list of error messages which should be reported
--
handleContextReduction :: Position -> [VPred] -> TI a
handleContextReduction pos vps =
    do
       -- We used to remove duplicates:
       --   let vps' = nubVPred vps
       -- Now this is covered under the following filter, which removes
       -- predicates that are implied by predicates already in the list.
       -- That way, we only report the predicates which need to be resolved
       -- (the others would be satisfied given the reported predicates).
       vps_noimpl <- removeImpliedPreds [] [] vps

       -- For each proviso, figure out whether it can be reduced, just
       -- not all the way (the inability to reduce a required proviso is
       -- the real stumbling point)
       vps_noimpl_reduced <- findReducedPreds [] vps_noimpl

       -- It is now safe to rename type variables to use nicer names
       -- (a__, b__, c__, etc)
       -- It was not safe to do so before, because some might have been
       -- bound variables and thus were named in the TI monad state
       -- which "findReducedPreds" used to simplify the preds.
       let vps_reduced_nicenames = niceTypes vps_noimpl_reduced

       -- we use to do messing around with PrimSelectable because it could
       -- introduce messed-up literal, etc. contexts
       -- now that indexing is rationalized, we expect that all the
       -- non-implied predicates are legitimate problems
       -- e.g. x[c] where x is not selectable and c is a clock
       -- x is an issue because you can't select from it and c
       -- is an issue because it is not a valid index for selection

       -- But now we do the same "messing around" for IsModule:
       -- Filter the IsModule predicates on "<-"
       let is_mod_arrow_vps =
               filter (isIsModuleArrow . fst) vps_reduced_nicenames

       -- if there are any, report only them, else report all the preds
       let err_vps = if (null is_mod_arrow_vps)
                     then vps_reduced_nicenames
                     else is_mod_arrow_vps

       emsgs <- mapM (handleContextReduction' pos) err_vps

       errs "handleContextReduction" emsgs

-- --------------------

-- This helper function takes one predicate at a time
handleContextReduction' :: Position -> (VPred, [VPred]) -> TI EMsg
handleContextReduction' pos
    p@((VPred vpi (PredWithPositions (IsIn c@(Class { name=(CTypeclass cid) }) ts) _)), _)
    | cid == idBitwise =
        case ts of
            [t] -> return $ handleCtxRedBitwise pos p t
            _ -> internalError("handleContextReduction': " ++
                               "Bitwise instance contains wrong number of types")
    | cid == idBitReduce =
        case ts of
            [vec, sz] -> return $ handleCtxRedBitReduce pos p vec sz
            _ -> internalError("handleContextReduction': " ++
                               "Bitwise instance contains wrong number of types")
    | cid == idBits =
        case ts of
            [t,szt] -> case szt of
                         (TCon (TyNum sz _)) ->
                              handleCtxRedWrongBitSize pos p c t sz
                         _ -> return $ defaultContextReductionErr pos p
            _ -> internalError("handleContextReduction': " ++
                               "Bits instance contains wrong number of types")
    | cid == idBitExtend =
        case ts of
            [szt1, szt2, t3] -> handleCtxRedBitExtend pos p c szt1 szt2 t3
            _ -> internalError("handleContextReduction': " ++
                               "BitExtend instance contains wrong number of types")
    | cid == idPrimSelectable =
        case ts of
            [arr, val] -> handleCtxRedPrimSelectable pos p c arr val
            _ -> internalError
                   ("handleContextReduction': " ++
                    "PrimSelectable instance contains wrong number of types")
    | cid == idPrimUpdateable =
        case ts of
            [arr, val] -> handleCtxRedPrimUpdateable pos p c arr val
            _ -> internalError
                   ("handleContextReduction': " ++
                    "PrimUpdateable instance contains wrong number of types")
    | cid == idPrimWriteable =
        case ts of
            [arr, val] -> handleCtxRedPrimWriteable pos p c arr val
            _ -> internalError
                   ("handleContextReduction': " ++
                    "PrimWriteable instance contains wrong number of types")
    | cid == idPrimIndex =
        case ts of
          [ix, sz] -> handleCtxRedPrimIndex pos p c ix sz
          _ -> internalError("handleContextReduction': " ++
                             "PrimIndex instance contains wrong number of types")
    | cid == idIsModule =
        case ts of
          [mt, ct] -> return $ handleCtxRedIsModule pos p mt ct
          _ -> internalError
                   ("handleContextReduction': " ++
                    "IsModule instance contains wrong number of types")
    | cid == idNumEq =
        case ts of
          [t1, t2] -> return $ handleNotNumEq pos (getVPredPositions (fst p)) t1 t2
          _ -> internalError ("handleContextReduction': " ++
                              "NumEq instance contains wrong number of types")
    | cid == idPrimParam =
        case ts of
            [t, tsz] -> return $ handleCtxRedPrimParam pos p t
            _ -> internalError("handleContextReduction': " ++
                               "PrimParam instance contains wrong number of types")
    | cid == idPrimPort =
        case ts of
            [t, tsz] -> return $ handleCtxRedPrimPort pos p t
            _ -> internalError("handleContextReduction': " ++
                               "PrimPort instance contains wrong number of types")
    | cid == idSizedLiteral =
        case ts of
          [t, szt] -> case szt of
                        (TCon (TyNum sz _)) ->
                             handleCtxRedWrongBitSize pos p c t sz
                        _ -> return $ defaultContextReductionErr pos p
          _ -> internalError("handleContextReduction': " ++
                             "SizedLiteral instance contains wrong number of types")
    | cid == idWrapField =
        case ts of
          [TCon (TyStr name _), t, _] -> return $ handleCtxRedWrapField pos p name t
          _ -> internalError("handleContextReduction': " ++
                             "WrapField instance contains wrong number of types")

--  | cid == idLiteral =
--  | cid == idRealLiteral =
--  | cid == idStringLiteral =

handleContextReduction' pos p =
    return (defaultContextReductionErr pos p)

-- --------------------

defaultContextReductionErr :: Position -> (VPred, [VPred]) -> EMsg
defaultContextReductionErr pos (p, reduced_ps) =
    let
        mkVarPos v = (pfpString v, getPosition v)
        -- now that we fail fast, "pos" could be in "poss", remove it
        poss = filterPositions pos $ getVPredPositions p
        pred = toPred p
        varposs = map mkVarPos (tv pred)
    in
        if null reduced_ps
        then (pos, EContextReduction (pfpString pred) poss varposs)
        else (pos, EContextReductionReduces
                      (pfpString pred) (map (predToDescr . toPred) reduced_ps)
                      poss varposs)

-- --------------------

-- If the unreduced context is Bits for a known size, try to satisfy
-- the context with a fresh variable replaced for the known size.  If
-- the context reduces, and the variable is bound to a specific size,
-- then report an error about the mismatched size.

handleCtxRedWrongBitSize :: Position -> (VPred, [VPred]) -> Class -> Type -> Integer -> TI EMsg
handleCtxRedWrongBitSize pos (vp@(VPred vpi _), reduced_ps) c t sz = do
    let default_err = defaultContextReductionErr pos (vp, reduced_ps)
    szv <- newTVar "handleCtxRedWrongBitSize" KNum vpi
    let p' = IsIn c [t,szv]
        vp' = VPred vpi (PredWithPositions p' [])
    -- Use "satisfy", instead of "reducePred", because the size might
    -- result from arithmetic on the sizes of subtypes, via new predicates
    -- (so we need to continue until all preds are satisfied)
    (rs,_) <- satisfy [] [vp']
    s <- getSubst
    let szv' = apSub s szv
    return $
        if (null rs) && (isTNum szv')
        then wrongBitSizeErr pos vp t (getTNum szv') sz
        else default_err

wrongBitSizeErr :: Position -> VPred -> Type -> Integer -> Integer -> EMsg
wrongBitSizeErr pos p t tsz sz2 =
    let
        poss = filterPositions pos $ getVPredPositions p
    in
        (pos, ECtxRedWrongBitSize (pfpString t) tsz sz2 poss)


-- --------------------

-- If bitwise operations are used on a Bool value, give a special warning.
-- If any other concrete type the subject of bitwise operators, but there
-- is no instance for it, then report a special error.  If the type is a
-- variable (presumably an ambiguous variable), report the default error.

handleCtxRedBitwise :: Position -> (VPred, [VPred]) -> Type -> EMsg
handleCtxRedBitwise pos (vp, reduced_ps) t =
    let poss = filterPositions pos $ getVPredPositions vp
        bwbool_err = (pos, ECtxRedBitwiseBool poss)
        bw_err = (pos, ECtxRedBitwise (pfpString t) poss)
        default_err = defaultContextReductionErr pos (vp, reduced_ps)
    in
        case t of
            TCon (TyCon i _ _) | i == idBool -> bwbool_err
            _ -> case (tv t) of
                     [] -> bw_err
                     _  -> -- let's assume that a proviso would work here
                           default_err

-- --------------------

handleCtxRedBitReduce :: Position -> (VPred, [VPred]) -> Type -> Type -> EMsg
handleCtxRedBitReduce pos (vp, reduced_ps) vec_type vec_size =
    let poss = filterPositions pos $ getVPredPositions vp
        br_err = (pos, ECtxRedBitReduce (pfpString vec_type) poss)
        default_err = defaultContextReductionErr pos (vp, reduced_ps)
    in
        case (tv vec_type) of
            [] -> br_err
            _  -> -- let's assume that a proviso would work here
                  default_err


-- --------------------

-- Check to see if replacing the size types with variables matches any
-- instance.  If not, then the value type does not have
-- extend/truncate defined for it.  (This is a rare case, but what
-- the heck, let's check for it.)  If this passes, then check to see
-- if the two numeric sizes are known.  If so, and if sz1 > sz2, then
-- the problem is bad sizes.

handleCtxRedBitExtend :: Position -> (VPred, [VPred]) -> Class ->
                         Type -> Type -> Type -> TI EMsg
handleCtxRedBitExtend pos (vp@(VPred vpi _), reduced_ps) c szt1 szt2 t3 = do
    let poss = filterPositions pos $ getVPredPositions vp
        badsize_err sz1 sz2 =
          (pos, ECtxRedBitExtendBadSizes sz1 sz2 poss)
        badtype_err =
          (pos, ECtxRedBitExtendBadType (pfpString t3) poss)
        default_err = defaultContextReductionErr pos (vp, reduced_ps)

    szt1' <- newTVar "handleCtxRedBitExtend1" KNum vpi
    szt2' <- newTVar "handleCtxRedBitExtend2" KNum vpi
    let p' = IsIn c [szt1',szt2',t3]
        vp' = VPred vpi (PredWithPositions p' [])
    x <- reducePred [] Nothing vp'
    case x of
      (Just ([vp2], b, us, _)) | (vpClassIs (CTypeclass idAdd) vp2) ->
        case (szt1, szt2) of
          (TCon (TyNum sz1 _), TCon (TyNum sz2 _)) ->
               return (badsize_err sz1 sz2)
          _ -> return default_err
      _ -> return badtype_err


-- --------------------

type PredError = Position -> VPred -> Type -> EMsg
type ElemError = Position -> VPred -> Type -> Type -> Type -> EMsg

notSelectableErr :: PredError
notSelectableErr pos p t =
    let
        poss = filterPositions pos $ getVPredPositions p
    in
        (pos, ECtxRedNotSelectable (pfpString t) poss)

wrongSelectionResultErr :: ElemError
wrongSelectionResultErr pos p arr expected_val found_val =
    let
        poss = filterPositions pos $ getVPredPositions p
    in
        (pos, ECtxRedWrongSelectionResult (pfpString arr)
                  (pfpString expected_val) (pfpString found_val) poss)

notUpdateableErr :: PredError
notUpdateableErr pos p t =
    let
        poss = filterPositions pos $ getVPredPositions p
    in
        (pos, ECtxRedNotUpdateable (pfpString t) poss)

wrongUpdateArgErr :: ElemError
wrongUpdateArgErr pos p arr expected_val found_val =
    let
        poss = filterPositions pos $ getVPredPositions p
    in
        (pos, ECtxRedWrongUpdateArg (pfpString arr)
                  (pfpString expected_val) (pfpString found_val) poss)

notWriteableErr :: PredError
notWriteableErr pos p t =
    let
        poss = filterPositions pos $ getVPredPositions p
    in
        (pos, ECtxRedNotWriteable (pfpString t) poss)

wrongWriteArgErr :: ElemError
wrongWriteArgErr pos p arr expected_val found_val =
    let
        poss = filterPositions pos $ getVPredPositions p
    in
        (pos, ECtxRedWrongWriteArg (pfpString arr)
                  (pfpString expected_val) (pfpString found_val) poss)

-- handle context reduction errors for the [] contexts
-- PrimSelectable, PrimUpdateable, PrimWriteable
handleBracketCtxRed :: PredError -> ElemError ->
                       Position -> (VPred, [VPred]) -> Class ->
                       Type -> Type -> TI (EMsg)
handleBracketCtxRed pred_error elem_error pos (vp@(VPred vpi _), _) c arr val = do
    -- create new val variable
    val_var <- newTVar "handleBracketCtxRed" KStar vpi
    let p' = IsIn c [arr, val_var]
        vp' = VPred vpi (PredWithPositions p' [])
    x <- reducePred [] Nothing vp'
    case x of
      -- there is an instance of the bracket class for type "arr"
      Just (ps, _, us, _) -> do
        -- there may be context with informative fundeps, so propagate them
        _ <- propagateFunDeps ps
        s <- getSubst
        let real_val = apSub us (apSub s val_var)
        return (elem_error pos vp arr real_val val)
      -- there is no instance of the class for type "arr"
      x -> return (pred_error pos vp arr)
handleCtxRedPrimSelectable :: Position -> (VPred, [VPred]) -> Class -> Type -> Type
                           -> TI EMsg
handleCtxRedPrimSelectable = handleBracketCtxRed notSelectableErr wrongSelectionResultErr
handleCtxRedPrimUpdateable :: Position -> (VPred, [VPred]) -> Class -> Type -> Type
                           -> TI EMsg
handleCtxRedPrimUpdateable = handleBracketCtxRed notUpdateableErr wrongUpdateArgErr
handleCtxRedPrimWriteable  :: Position -> (VPred, [VPred]) -> Class -> Type -> Type
                           -> TI EMsg
handleCtxRedPrimWriteable  = handleBracketCtxRed notWriteableErr  wrongWriteArgErr

handleCtxRedPrimIndex :: Position -> (VPred, [VPred]) -> Class ->
                         Type -> Type -> TI (EMsg)
handleCtxRedPrimIndex pos (vp@(VPred vpi _), reduced_ps) c ix sz = do
  -- create new size variable
   sz_var <- newTVar "handleCtxRedPrimIndex" KNum vpi
   let p' = IsIn c [ix, sz_var]
       vp' = VPred vpi (PredWithPositions p' [])
   x <- reducePred [] Nothing vp'
   case x of
     -- there is an instance of PrimIndex for type "i"
     Just (_, _, us, _) ->
       let real_sz = (apSub us sz_var)
       in return (wrongIndexSizeErr pos (vp, reduced_ps) ix real_sz sz )
     x -> return (notIndexTypeErr pos vp ix)

notIndexTypeErr :: Position -> VPred -> Type -> EMsg
notIndexTypeErr pos p t =
    let
        poss = filterPositions pos $ getVPredPositions p
    in
        (pos, ECtxRedBadSelectionIndex (pfpString t) poss)

-- currently just generates a standard context reduction error
-- but this could be improved if the issue actually turns up in
-- user code
wrongIndexSizeErr :: Position -> (VPred, [VPred]) -> Type -> Type -> Type -> EMsg
wrongIndexSizeErr pos p ix real_sz sz = defaultContextReductionErr pos p

-- --------------------

isIsModuleArrow :: VPred -> Bool
isIsModuleArrow
    (VPred vpi (PredWithPositions (IsIn (Class { name=(CTypeclass cid) }) [mt, ct]) _))
      | (cid == idIsModule) && (isArrow mt)
                  = True
isIsModuleArrow _ = False

isArrow :: Type -> Bool
isArrow t = case (leftCon t) of
                Just i | (i == idArrow noPosition) -> True
                _                                  -> False

isActionValue :: Type -> Bool
isActionValue (TCon (TyCon i _ _)) | (i == idActionValue) = True
isActionValue _ = False

handleCtxRedIsModule :: Position -> (VPred, [VPred]) -> Type -> Type -> EMsg
handleCtxRedIsModule pos (vp, _) mt ct =
    let poss = filterPositions pos $ getVPredPositions vp
    in  if (isArrow mt)
        then (pos, EModInstWrongArgs poss)
        else if (isActionValue mt)
        then (pos, ECtxRedIsModuleActionValue poss)
        else (pos, ECtxRedIsModule (pfpString mt) poss)


-- --------------------

handleNotNumEq :: Position -> [Position] -> Type -> Type -> EMsg
handleNotNumEq pos poss t1 t2 = (pos, ENotNumEq t1_str t2_str poss')
  where poss' = filterPositions pos poss
        t1_str = pfpString t1
        t2_str = pfpString t2


-- --------------------

handleCtxRedPrimParam :: Position -> (VPred, [VPred]) -> Type -> EMsg
handleCtxRedPrimParam pos (vp, reduced_ps) userty =
    let poss = filterPositions pos $ getVPredPositions vp
        hasVar = toMaybe (not (null (tv userty)))
                         (map (pfpString . toPred) reduced_ps)
    in
        (pos, ECtxErrPrimParam (pfpString userty) poss hasVar)

handleCtxRedPrimPort :: Position -> (VPred, [VPred]) -> Type -> EMsg
handleCtxRedPrimPort pos (vp, reduced_ps) userty =
    let poss = filterPositions pos $ getVPredPositions vp
        hasVar = toMaybe (not (null (tv userty)))
                         (map (pfpString . toPred) reduced_ps)
    in
        (pos, ECtxErrPrimPort (pfpString userty) poss hasVar)

-- --------------------

handleCtxRedWrapField:: Position -> (VPred, [VPred]) -> FString -> Type -> EMsg
handleCtxRedWrapField pos (vp, reduced_ps) name userty =
    (pos, EBadIfcType (getFString name)
     "This method uses types that are not in the Bits or SplitPorts typeclass.")


-- ========================================================================
-- Weak Context
--

-- When adding new errors, remember to use "niceTypes" to convert
-- mangled type variable names into letters.

handleWeakContext :: Position -> Type -> [PredWithPositions] ->
                     [Pred] -> [PredWithPositions] -> TI a
handleWeakContext pos t qs ds rs = do
    -- traceM ("handleWeakContext qs: " ++ ppReadable qs)
    -- traceM ("handleWeakContext ds: " ++ ppReadable ds)
    -- traceM ("handleWeakContext rs: " ++ ppReadable rs)

    -- Only report the predicates which are necessary, not those
    -- which could be left off because other predicates imply them.
    rs_noimpl <- removeImpliedPredWPs qs ds rs

    -- traceM("handleWeakContext rs_noimpl: " ++ ppReadable rs_noimpl)

    -- For each proviso, figure out whether it can be reduced, just
    -- not all the way (the inability to reduce a required proviso is
    -- the real stumbling point)
    rs_noimpl_reduced <- findReducedPredWPs ds rs_noimpl

    xs <- mapM (handleWeakContext' pos t qs) rs_noimpl_reduced
    -- separate out the handled from the non-handled
    let (ctx_errs, rs') = separate xs

    -- traceM("handleWeakContext rs': " ++ ppReadable rs')

    -- report the remaining errors in one emsg
    let def_errs = [defaultWeakContextErr pos t qs rs' | not (null rs')]
    -- report the specific errors first
    errs "handleWeakContext" (ctx_errs ++ def_errs)


handleWeakContext' :: Position -> Type -> [PredWithPositions] ->
                      (PredWithPositions, [Pred]) ->
                      TI (Either EMsg (PredWithPositions, [Pred]))
handleWeakContext' pos t qs
    pwp@((PredWithPositions (IsIn (Class {name=(CTypeclass cid)}) ts) _), _)
    | cid == idBitExtend = handleWeakCtxBitExtend pos t qs pwp
    | cid == idPrimSelectable = handleWeakCtxPrimSelectable pos t qs pwp
    | cid == idPrimUpdateable = handleWeakCtxPrimUpdateable pos t qs pwp
    | cid == idPrimWriteable  = handleWeakCtxPrimWriteable  pos t qs pwp
    | cid == idPrimParam = handleWeakCtxPrimParam pos t qs pwp
    | cid == idPrimPort = handleWeakCtxPrimPort pos t qs pwp
    | cid == idNumEq =
        case ts of
          [t1, t2] ->
              return $ Left (handleNotNumEq pos (getPredPositions (fst pwp)) t1 t2)
          _ -> internalError ("handleWeakContext' NumEq: " ++ ppReadable (t,qs,pwp))
--  | cid == idPrimIndex = handleWeakCtxPrimIndex pos t qs pwp
--  | cid == ...
handleWeakContext' pos _ _ p = return (Right p)


defaultWeakContextErr :: Position -> Type -> [PredWithPositions] ->
                         [(PredWithPositions, [Pred])] -> EMsg
defaultWeakContextErr pos t qs rs =
    let
        -- rename generated typevars with "a__", "b__", etc
        -- (should only be new tvars in the required preds)
        -- but skip any that are already in the user-given type
        (rs', qs', t') = niceTypes (rs, qs, t)

        -- find the tvars so that we can report a position for any
        -- generated tvars
        tvars = nub $ sort $ concat [tv (removePredPositions pred)
                                        | (pred, _) <- rs']
        -- only report the location of generated tvars
        -- (niceTypes preserves the "isNewTVar" property)
        gen_tvars = filter isNewTVar tvars
        -- pair the renamed gen_tvars with their positions
        -- (only those which have a position)
        gen_tvars_with_positions =
            [(ppString t, tpos)
                | t <- gen_tvars,
                  let tpos = getPosition t,
                  tpos /= noPosition ]

        -- format the predicates for the error message
        mkinfo (p, ps) = (pfpString (removePredPositions p),
                          getPredPositions p,
                          map predToDescr ps)
        rps = map mkinfo rs'
    in
        (pos, EWeakContext (pfpString t') (map pfpString qs') rps
                  gen_tvars_with_positions)

-- --------------------

-- A BitExtend context could fail to resolve because the Add superclass
-- requirement might be failing.  If this is the only reason, report the
-- Add class instead.
handleWeakCtxBitExtend :: Position -> Type -> [PredWithPositions] ->
                          (PredWithPositions, [Pred]) ->
                          TI (Either EMsg (PredWithPositions, [Pred]))
handleWeakCtxBitExtend pos t qs pps@(pwp, _) = do
    let vpi = mkId noPosition (mkFString "_handleWeakCtxBitExtend")
        vp  = VPred vpi pwp
    x <- reducePred [] Nothing vp
    case x of
      Just ([vp2], b, us, _) ->
        -- separated out the matching of vp2 for readability
        case vp2 of
          (VPred _ (PredWithPositions p2@(IsIn (Class {name=(CTypeclass cid)}) ts) poss))
            | cid == idAdd -> do
                -- we don't use the reduced preds that came with pwp,
                -- because the tyvars in it won't match the ones in vp2
                reduced_vp2 <- findReducedPreds [] [vp2]
                let reduced_ps = map toPred $ snd $
                                 headOrErr "handleWeakCtxBitExtend" reduced_vp2
                -- now put it together
                let (qs', t', p2', reduced_ps') =
                        niceTypes (qs, t, p2, reduced_ps)
                return (Left (pos, EWeakCtxBitExtendNeedsAddCtx
                                       (pfpString t') (map pfpString qs')
                                       (pfpString p2')
                                       (map predToDescr reduced_ps')
                                       poss))
          k -> return (Right pps)
      _ -> return (Right pps)

-- --------------------

-- (1) A PrimSelectable could fail as weak instead of failed-to-reduce because
--     there is a variable in the type.  For instance, Vector#(n,Bool) being
--     selected and expecting an Integer would fail, but because of "n", it
--     is not reported as ctx-reduction but as too-weak.
--
-- Other situations we could identify:
--  * the array type is a variable (or the left-most constructor is a var),
--    in which case we could explain that for []-syntax to be used on a
--    parameterized type the proviso PrimSelectable is needed.
--    for now, the too-weak error should be sufficient?
--
handleWeakCtxPrimSelectable :: Position -> Type -> [PredWithPositions] ->
                               (PredWithPositions, [Pred]) ->
                               TI (Either EMsg (PredWithPositions, [Pred]))
handleWeakCtxPrimSelectable pos t qs pps@(pwp, _) = do
    let vpi = mkId noPosition (mkFString "_handleWeakCtxPrimSelectable")
        vp  = VPred vpi pwp
    case (removePredPositions pwp) of
      (IsIn c [arr, val]) -> do
        mesg <- isSelectionResultErr pos vp c arr val
        case mesg of
          Nothing -> return (Right pps)
          Just emsg -> return (Left emsg)
      p -> internalError ("handleWeakCtxPrimSelectable: Unexpected p: " ++ ppReadable p)

isSelectionResultErr :: Position -> VPred -> Class ->
                        Type -> Type -> TI (Maybe EMsg)
isSelectionResultErr pos vp@(VPred vpi _) c arr val = do
    -- create new val variable
    val_var <- newTVar "isSelectionResultErr (element)" KStar vpi
    let p' = IsIn c [arr, val_var]
        vp' = VPred vpi (PredWithPositions p' [])
    x <- reducePred [] Nothing vp'
    bound_tyvars <- getBoundTVs
    case x of
      -- there is an instance of PrimSelectable for type "arr"
      Just (_, _, us, _) ->
        let real_val = (apSub us val_var)
        in  -- compare the return result
            case (mgu bound_tyvars val real_val) of
              Nothing ->
                  let (arr', real_val', val') = niceTypes (arr, real_val, val)
                  in  return $ Just $
                      wrongSelectionResultErr pos vp arr' real_val' val'
              Just s ->  return Nothing
      x -> return Nothing

handleWeakCtxPrimUpdateable :: Position -> Type -> [PredWithPositions] ->
                               (PredWithPositions, [Pred]) ->
                               TI (Either EMsg (PredWithPositions, [Pred]))
handleWeakCtxPrimUpdateable pos t qs pps@(pwp, _) = do
    let vpi = mkId noPosition (mkFString "_handleWeakCtxPrimUpdateable")
        vp  = VPred vpi pwp
    case (removePredPositions pwp) of
      (IsIn c [arr, val]) -> do
        mesg <- isUpdateArgErr pos vp c arr val
        case mesg of
          Nothing -> return (Right pps)
          Just emsg -> return (Left emsg)
      p -> internalError ("handleWeakCtxPrimUpdateable: Unexpected p: " ++ ppReadable p)

isUpdateArgErr :: Position -> VPred -> Class ->
                        Type -> Type -> TI (Maybe EMsg)
isUpdateArgErr pos vp@(VPred vpi _) c arr val = do
    -- create new val variable
    val_var <- newTVar "isUpdateArgErr (element)" KStar vpi
    let p' = IsIn c [arr, val_var]
        vp' = VPred vpi (PredWithPositions p' [])
    x <- reducePred [] Nothing vp'
    bound_tyvars <- getBoundTVs
    case x of
      -- there is an instance of PrimUpdateable for type "arr"
      Just (_, _, us, _) ->
        let real_val = (apSub us val_var)
        in  -- compare the return result
            case (mgu bound_tyvars val real_val) of
              Nothing ->
                  let (arr', real_val', val') = niceTypes (arr, real_val, val)
                  in  return $ Just $
                      wrongUpdateArgErr pos vp arr' real_val' val'
              Just s ->  return Nothing
      x -> return Nothing

handleWeakCtxPrimWriteable :: Position -> Type -> [PredWithPositions] ->
                               (PredWithPositions, [Pred]) ->
                               TI (Either EMsg (PredWithPositions, [Pred]))
handleWeakCtxPrimWriteable pos t qs pps@(pwp, _) = do
    let vpi = mkId noPosition (mkFString "_handleWeakCtxUpdateable")
        vp  = VPred vpi pwp
    case (removePredPositions pwp) of
      (IsIn c [arr, val]) -> do
        mesg <- isWriteArgErr pos vp c arr val
        case mesg of
          Nothing -> return (Right pps)
          Just emsg -> return (Left emsg)
      p -> internalError ("handleWeakCtxPrimWriteable: Unexpected p: " ++ ppReadable p)

isWriteArgErr :: Position -> VPred -> Class ->
                        Type -> Type -> TI (Maybe EMsg)
isWriteArgErr pos vp@(VPred vpi _) c arr val = do
    -- create new val variable
    val_var <- newTVar "isWriteArgErr (element)" KStar vpi
    let p' = IsIn c [arr, val_var]
        vp' = VPred vpi (PredWithPositions p' [])
    x <- reducePred [] Nothing vp'
    bound_tyvars <- getBoundTVs
    case x of
      -- there is an instance of PrimSelectable for type "arr"
      Just (_, _, us, _) ->
        let real_val = (apSub us val_var)
        in  -- compare the return result
            case (mgu bound_tyvars val real_val) of
              Nothing ->
                  let (arr', real_val', val') = niceTypes (arr, real_val, val)
                  in  return $ Just $
                      wrongWriteArgErr pos vp arr' real_val' val'
              Just s ->  return Nothing
      x -> return Nothing

-- --------------------

handleWeakCtxPrimParam :: Position -> Type -> [PredWithPositions] ->
                          (PredWithPositions, [Pred]) ->
                          TI (Either EMsg (PredWithPositions, [Pred]))
handleWeakCtxPrimParam pos _ _ (pwp, _) =
   case pwp of
     (PredWithPositions (IsIn (Class { }) [userty, _]) poss0) -> do
         let poss = filterPositions pos poss0
             ty_str = pfpString userty
         let vpi = mkId noPosition (mkFString "_handleWeakCtxPrimParam")
             vp  = VPred vpi pwp
         x <- reducePred [] Nothing vp
         case x of
           Just (vps, _, _, _) -> do
               let ps = niceTypes (map toPred vps)
                   hasVar = Just $ map pfpString ps
               return $ Left (pos, ECtxErrPrimParam ty_str poss hasVar)
           _ -> internalError ("handleWeakCtxPrimParam: reduced")
     _ -> internalError ("handleWeakCtxPrimParam: wrong number of types")

handleWeakCtxPrimPort :: Position -> Type -> [PredWithPositions] ->
                         (PredWithPositions, [Pred]) ->
                         TI (Either EMsg (PredWithPositions, [Pred]))
handleWeakCtxPrimPort pos _ _ (pwp, _) =
   case pwp of
     (PredWithPositions (IsIn (Class { }) [userty, _]) poss0) -> do
         let poss = filterPositions pos poss0
             ty_str = pfpString userty
         let vpi = mkId noPosition (mkFString "_handleWeakCtxPrimPort")
             vp  = VPred vpi pwp
         x <- reducePred [] Nothing vp
         case x of
           Just (vps, _, _, _) -> do
               let ps = niceTypes (map toPred vps)
                   hasVar = Just $ map pfpString ps
               return $ Left (pos, ECtxErrPrimPort ty_str poss hasVar)
           _ -> internalError ("handleWeakCtxPrimPort: reduced")
     _ -> internalError ("handleWeakCtxPrimPort: wrong number of types")


-- ========================================================================
-- Contexts with Ambiguous Type Variables
--

handleAmbiguousContext :: Position -> [TyVar] -> [VPred] -> TI a
handleAmbiguousContext pos amb_vars vps =
    do
       -- Remove duplicates and implied predicates
       vps' <- removeImpliedPreds [] [] vps

       -- produce a list of pairs of ambiguous vars
       -- and the preds they appear in
       let findPreds ps v = (v, filter (elem v . tv) ps)
       let pairs :: [(TyVar, [VPred])]
           pairs = map (findPreds vps') amb_vars

       -- use a heuristic to remove ambiguous variables that would be
       -- determined if other ambiguous variables were resolved first
       let pairs_minusFD = removeFD pairs

       let emsg = ambiguousVarsErr pos pairs_minusFD

       -- Report ambiguous vars on all the contexts.
       err emsg

removeFD :: [(TyVar, [VPred])] -> [(TyVar, [VPred])]
removeFD pairs0 =
    let vset0 = S.fromList (map fst pairs0)

        foldFn (v, ps) (vset, pairs) =
            if isDetermined v ps vset
            then (S.delete v vset, pairs)
            else (vset, ((v, ps) : pairs))

        isDetermined v ps vset =
            let -- try one dependency
                tryOneDep ts bs =
                    let dependee_exprs  = (boolCompress (map not bs) ts)
                        dependee_vars   = tv dependee_exprs
                        dependent_exprs = (boolCompress bs ts)
                        dependent_vars  = tv dependent_exprs
                    in
                        (v `elem` dependent_vars) &&
                        -- XXX should we rule out when dependee set is null?
                        all (`S.member` vset) dependee_vars

                -- try all dependencies for a pred
                anyDep vp =
                    let (IsIn c ts) = toPred vp
                    in  any (tryOneDep ts) (funDeps c)
            in
                -- if the type is determined in all preds (by any one fundep)
                all (anyDep) ps
    in
        snd $ foldr foldFn (vset0, []) pairs0

-- --------------------

ambiguousVarsErr :: Position -> [(TyVar, [VPred])] -> EMsg
ambiguousVarsErr pos pairs =
    let
        niceTypesPairs xs =
            let -- TyVar is not in Types, so have to add TVar constructor
                upgradeTyVar (v, ps) = (TVar v, ps)
                -- and then strip it off
                downgradeTyVar (t, ps) =
                    case t of
                        TVar v -> (v, ps)
                        _ -> internalError ("downgradeTyVar: not TVar")
            in  map downgradeTyVar (niceTypes (map upgradeTyVar xs))

        mkVarInfo (v, ps) =
            let pwps = map toPredWithPositions ps
                v_str = pfpString v
                v_pos = getPosition v
                use_explanations = map mkAmbVarExplanation pwps
            in  (v_str, v_pos, use_explanations)

        nice_pairs = niceTypesPairs pairs
    in
        (pos, EAmbiguous (map mkVarInfo nice_pairs))

mkAmbVarExplanation :: PredWithPositions -> Doc
mkAmbVarExplanation (PredWithPositions p@(IsIn c _) poss) =
    let cid = typeclassId $ name c
        use_poss_doc = nest 2 (vcat (map (text . prPosition) (nub poss)))
        use_doc
            | cid == idBitwise =
               s2par ("Bitwise operators" ++
                      " in or at the following locations:")
            | cid == idBitReduce =
               s2par ("Bit reduction operator" ++
                      " in or at the following locations:")
            | cid == idBits =
               s2par ("Bits#() proviso introduced" ++
                      " (for bit vector packing/unpacking)" ++
                      " in or at the following locations:")
            | cid == idBitExtend =
               s2par ("Bit vector extend or truncate" ++
                      " in or at the following locations:")
            | cid == idPrimSelectable =
               s2par ("Selection with []" ++
                      " in or at the following locations:")
            | cid == idPrimIndex =
               -- this shouldn't happen?
               -- unless we change "<<" and "[x:y]" to take index types?
               s2par ("Indexing into a vector" ++
                      " in or at the following locations:")
            | cid == idEq =
               s2par ("Equality or inequality operator" ++
                      " in or at the following locations:")
            | cid == idLiteral =
               s2par ("Numeric constant" ++
                      " in or at the following locations:")
            | cid == idSizedLiteral =
               s2par ("Sized numeric constant" ++
                      " in or at the following locations:")
            | cid == idRealLiteral =
               s2par ("Real numeric constant" ++
                      " in or at the following locations:")
            | cid == idStringLiteral =
               s2par ("String constant" ++
                      " in or at the following locations:")
            | cid == idArith =
               s2par ("Arithmetic operator" ++
                      " in or at the following locations:")
            | cid == idOrd =
               s2par ("Comparison operator" ++
                      " in or at the following locations:")
            | cid == idBounded =
               s2par ("Use of minBound or maxBound" ++
                      " in or at the following locations:")
            | cid == idPrimParam =
               s2par ("Assignment to an imported module parameter" ++
                      " in or at the following locations:")
            | cid == idPrimPort =
               s2par ("Assignment to an imported module port" ++
                      " in or at the following locations:")
            | otherwise =
               -- just display the predicate
               s2par ("The proviso " ++ pfpString p ++ " introduced" ++
                      " in or at the following locations:")
    in
        use_doc $$ use_poss_doc


-- ========================================================================
-- Utilities

-- removed positions that are the same as the reported position
-- and which are otherwise unhelpful
filterPositions :: Position -> [Position] -> [Position]
filterPositions pos poss = filter (/= noPosition) $ filter (/= pos) poss

-- --------------------

-- Given a list of predicates, this returns a subset of the predicates
-- which would be sufficient to satisfy the entire set.

removeImpliedPreds :: [VPred] -> [Pred] -> [VPred] -> TI [VPred]
removeImpliedPreds qs ds [] = return []
removeImpliedPreds qs ds vps = do
    eps <- mapM (mkEPred . toPred) vps
    eds <- mapM mkEPred ds
    eqs <- mapM (mkEPred . toPred) qs
    (vps',_) <- removeImpliedPreds' ([],eds ++ eqs) (vps,eps)
    return vps'

removeImpliedPreds' ::
    ([VPred],[EPred]) -> ([VPred],[EPred]) -> TI ([VPred],[EPred])
removeImpliedPreds' keeps ([], []) = return keeps
removeImpliedPreds' (keep_vps, keep_eps) ((vp:vps), (ep:eps)) = do
    bvs <- getBoundTVs
    let all_bvs = (tv (keep_eps ++ eps)) ++ bvs
        closed_bvs = closeFD (vp:vps) all_bvs
    (vp', _) <- satisfyFV closed_bvs (keep_eps ++ eps) [vp]
    case (vp') of
       [] -> removeImpliedPreds' (keep_vps, keep_eps) (vps, eps)
       _ -> removeImpliedPreds' (vp:keep_vps, ep:keep_eps) (vps, eps)
removeImpliedPreds' _ _ =
    internalError "ContextErrors.removeImpliedPreds'"


-- Context Too Weak errors only have PredWithPositions
removeImpliedPredWPs :: [PredWithPositions] -> [Pred] -> [PredWithPositions] ->
                        TI [PredWithPositions]
removeImpliedPredWPs qpwps ds pwps = do
    vps <- concatMapM mkVPredNoNewPos pwps
    qps <- concatMapM mkVPredNoNewPos qpwps
    vps' <- removeImpliedPreds qps ds vps
    return (map toPredWithPositions vps')

-- --------------------

-- In some cases, we want to reduce a pred to its unsatisfiable requirements.
-- For instance, if Bits#(Vector#(8,Integer),sz) is not satisfied, we want
-- to discover that it is because Bits#(Integer),sz2) could not be satisfied.

findReducedPreds :: [Pred] -> [VPred] -> TI [(VPred, [VPred])]
findReducedPreds ds vps = do
  eps <- getTopExplPreds
  eds <- mapM mkEPred ds
  bvs <- getBoundTVs
  let reduceOne vp = do
          let dvs = (tv vp) ++ bvs
          (reduce_res, _, _) <- reducePredsAggressive (Just dvs) (eds ++ eps) [vp]
          case (reduce_res) of
            -- shouldn't reduce away entirely
            [] -> internalError ("findReducedPreds: reduces: " ++
                                 ppReadable vp)
            -- didn't reduce at all
            [vp'] | toPred vp' == toPred vp
               -> return (vp, [])
            -- reduced to other preds
            ps -> return (vp, ps)
  mapM reduceOne vps


-- Context Too Weak errors only have PredWithPositions
findReducedPredWPs :: [Pred] -> [PredWithPositions] -> TI [(PredWithPositions, [Pred])]
findReducedPredWPs ds pwps = do
    vps <- concatMapM mkVPredNoNewPos pwps
    vps' <- findReducedPreds ds vps
    let fn (p,ps) = (toPredWithPositions p, map toPred ps)
    return (map fn vps')

-- --------------------

pwpClassIs :: CTypeclass -> PredWithPositions -> Bool
pwpClassIs cid1 (PredWithPositions (IsIn c@(Class { name=cid2 }) _) _)
    | cid1 == cid2 = True
pwpClassIs _ _ = False

vpClassIs :: CTypeclass -> VPred -> Bool
vpClassIs cid (VPred _ pwp) = pwpClassIs cid pwp


{-
pwpGetTypes :: PredWithPositions -> [Type]
pwpGetTypes (PredWithPositions (IsIn _ ts) _) = ts

vpGetTypes :: VPred -> [Type]
vpGetTypes (VPred _ pwp) = pwpGetTypes pwp
-}


-- ========================================================================

-- During typecheck, in places where new contexts are deduced, we should
-- call this function to propagate fundeps in the substitution and to
-- error early on any non-reducible predicates.
-- It returns the predicates with the substitution applied -- in case this
-- saves effort later of not having to re-apply the substitution so much.
updateContexts :: Position -> [VPred] -> TI [VPred]
updateContexts pos ps =
  do
    -- this will get the subst and apply it to ps
    (ps', ps_unsat) <- propagateFunDeps ps
    -- this doesn't need to subst because the preds already have that done
    _ <- earlyContextReduction pos ps_unsat
    return ps'


-- function to error early if any contexts are not resolvable
-- (This function assumes that the substitution has already been applied
-- to the predicates.)
earlyContextReduction :: Position -> [VPred] -> TI ()
earlyContextReduction pos ps =
  do
    let try_pred p = do isReducible <- isReduciblePred p
                        return (p, isReducible)
    rs <- mapM try_pred ps
    let err_preds = map fst (filter (not . snd) rs)
    when (not (null err_preds)) $
        handleContextReduction pos err_preds

-- ========================================================================

-- Display a proviso as a string, except for primitive classes which are
-- expressed in natural language
predToDescr :: Pred -> String
predToDescr p@(IsIn (Class { name = CTypeclass cid }) ts)
   -- primitive classes which users don't know about
   | cid == idNumEq =
       case ts of
          [t1, t2] -> "type " ++ quote (pfpString t1) ++ " and type " ++
                      quote (pfpString t2) ++ " are equal"
          _ -> internalError ("predToDescr: " ++
                              "NumEq instance contains wrong number of types")
   | cid == idPrimSelectable =
       case ts of
          [arr, val] -> "Selection with [] from a value of type " ++
                        quote (pfpString arr) ++
                        " results in a value of type " ++
                        quote (pfpString val)
          _ -> internalError
                   ("predToDescr: " ++
                    "PrimSelectable instance contains wrong number of types")
   | cid == idPrimUpdateable =
       case ts of
          [arr, val] -> "A value of type " ++ quote (pfpString arr) ++
                        " can be updated at compile-time with [] and = " ++
                        "with an argument of type " ++
                        quote (pfpString val)
          _ -> internalError
                   ("predToDescr: " ++
                    "PrimUpdateable instance contains wrong number of types")
   | cid == idPrimWriteable =
       case ts of
          [arr, val] -> "A value of type " ++ quote (pfpString arr) ++
                        " can be updated at run-time with [] and <= " ++
                        " with an argument of type " ++
                        quote (pfpString val)
          _ -> internalError
                   ("predToDescr: " ++
                    "PrimWriteable instance contains wrong number of types")
   | cid == idPrimIndex =
       case ts of
          [ix, sz] -> "Selection with [] is possible with an index value " ++
                      "of type " ++ quote (pfpString ix)
          _ -> internalError
                   ("predToDescr: " ++
                    "PrimIndex instance contains wrong number of types")

   -- The rest are documented, so it's OK to reveal to the user
   | otherwise = pfpString p
{-
   | cid == idIsModule =

   | cid == idBitExtend =
   | cid == idBitwise =
   | cid == idBitReduce =

   | cid == idSizedLiteral =
   | cid == idLiteral =
   | cid == idRealLiteral =
   | cid == idStringLiteral =
-}

-- ========================================================================
