{-# LANGUAGE PatternGuards #-}
module TCheck(tiExpr, tiExpl) where

import Data.List
import Control.Monad(when, unless)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified GraphWrapper as GW
import Data.Ix(range)

import ListMap(lookupWithDefaultBy)
import SCC(scc)
import Util(findDup, concatMapM,
            headOrErr, initOrErr, lastOrErr, fromJustOrErr)
import Util(fst3)
import IntLit
import IntegerUtil(mask)
import Classic(isBSV)
import Flags(Flags)
import PFPrint
import Id
import FStringCompat
import PreStrings(fsEmpty)
import PreIds
import Position(Position(..), noPosition)
import Error(internalError, ErrMsg(..))
import ContextErrors
import Type
import Subst
import Pred hiding (name)
import qualified Pred(name)
import Scheme
import Assump
import TIMonad
import TCPat
import TCMisc
import CtxRed
import CSyntax
import CSyntaxUtil
import CFreeVars(getFVDl, getFVE, fvSetToFreeVars)
import CType(noTyVarNo, getTyVarId, getArrows, isTConArrow, leftTyCon,
             isTypeBit, isTypeString, isTypeUnit, isTypePrimAction, isTVar, isUpdateable,
             isTypeActionValue, isTypeActionValue_, getActionValueArg,
             splitTAp, tyConArgs, cTVarKind)
import VModInfo(VSchedInfo, VFieldInfo(..), VArgInfo(..), VPort)
import SchedInfo(SchedInfo(..), MethodConflictInfo(..))
import SymTab
import Pragma(PProp(..))
import CSubst
import ForeignFunctions(toAVId)
import CFreeVars(getFQTyVarsT)
-------

import Util(traces)
import Debug.Trace(traceM)
import IOUtil(progArgs)

doRTrace :: Bool
doRTrace = elem "-trace-type" progArgs
doRTrace2 :: Bool
doRTrace2 = length (filter (== "-trace-type") progArgs) > 1
doETrace :: Bool
doETrace = elem "-trace-type-expl" progArgs
rtrace :: String -> a -> a
rtrace s x = if doRTrace then traces s x else x
etrace :: String -> a -> a
etrace s x = if doETrace then traces s x else x

doTraceSatisfy :: Bool
doTraceSatisfy= elem "-trace-tc-satisfy" progArgs
-- satTrace s x = if doTraceSatisfy then traces s x else x
satTraceM :: String -> TI ()
satTraceM s = when (doTraceSatisfy) $ traceM s

warnMethArgMismatch :: Bool
warnMethArgMismatch = elem "-warn-meth-arg-mismatch" progArgs

-------

-- used to force-bit Integer types
bit32 :: Type
bit32 = TAp tBit t32

{- Unused:
int32 :: Type
int32 = TAp tInt t32
-}


data ImplReadTag = NoRead | ImplRead (Maybe Id)

-- tiExpr: type-infer an expression
--   first argument (as):    type environment (a.k.a., assumptions)
--   second argument (td):   expected type of exp
--   third argument (exp):   expression to typecheck
-- returns: TI (preds, exp') where
--   preds: context requirements
--   exp':  exp, possibly rewritten
tiExpr :: CheckT CExpr

tiExpr as td exp@(CLam ei e) = do
      --posCheck "A" i
      v <- newTVar "tiExpr CLam" KStar ei
      (rt, eq_ps) <- unifyFnTo ei exp td v
      s <- getSubst
      let v'  = apSub s v
      let rt' = apSub s rt
      -- trimSubst?
      (ps, e') <- case ei of
                    Right i -> tiExpr ((i :>: toScheme v') : as) rt' e
                    Left _  -> tiExpr as rt e -- don't bind
      def_id <- newVar (getPosition ei) "tiExprCLam"
      let ipat = either CPAny CPVar ei
          def_ty = (CQType [] (v' `fn` rt'))
          def = CDefT def_id [] def_ty [CClause [ipat] [] e']
      -- trace ("CLam " ++ ppReadable (ei, def_id)) $ return ()
      return (eq_ps ++ ps, Cletrec [CLValueSign def []] (CVar def_id))

{- XXX not quite right
tiExpr as td exp@(CLamT i qt e) = do
    sc <- mkSchemeNoBVs qt
    (qs :=> ty, ts) <- freshInst i sc
    qs'             <- mapM (mkVPred (getPosition exp)) qs

    trace (ppReadable(qs, ty, ts)) $ return ()

    v <- unifyFnTo i exp td ty
    (ps, e') <- tiExpr ((i :>: toScheme ty) : as) v e
    il <- newVar (getPosition i) "tiExprCLamT"
    return (qs' ++ ps, Cletrec [CLValueSign (CDefT il [] (CQType [] td) [CClause [CPVar i] [] e']) []] (CVar il))
-}

tiExpr as td exp@(CLamT ei (CQType [] ty) e) = do
    (v, eq_ps) <- unifyFnTo ei exp td ty
    (ps, e') <- case ei of
                  Right i -> tiExpr ((i :>: toScheme ty) : as) v e
                  Left _  -> tiExpr as v e -- don't bind
    --posCheck "B" i
    def_id <- newVar (getPosition ei) "tiExprCLamT"
    let ipat = either CPAny CPVar ei
        def = CDefT def_id [] (CQType [] td) [CClause [ipat] [] e']
    -- trace ("CLamT " ++ ppReadable (ei, def_id)) $ return ()
    return (eq_ps ++ ps, Cletrec [CLValueSign def []] (CVar def_id))

tiExpr as td exp@(CLamT ei (CQType _ ty) e) = do
    x <- (err (getPosition ei, (internalError "TCheck.tiExpr: CLamT with context")))
    return x

-- Monomorphic let binding used by deriving code
-- XXX Is this necessary?  Instead of "ei" should this just match "Right i"?
tiExpr type_env expected_type (CApply (CLam ei b) [e]) = do
    --trace ("mono let") $ return ()
    type_var <- newTVar "tiExpr CLam" KStar ei
    (ps, e') <- tiExpr type_env type_var e
    (qs, b') <- case ei of
                  Right i -> tiExpr ((i :>: toScheme type_var) : type_env) expected_type b
                  Left _ -> tiExpr type_env expected_type b -- don't bind
    let res_e = case ei of
                  Right i -> let def = CDefT i [] (CQType [] type_var) [CClause [] [] e']
                             in  Cletrec [CLValueSign def []] b'
                  Left _ -> b'
    return (ps ++ qs, res_e)

tiExpr type_env expected_type expr@(Cletseq defs body) = do
    -- desugar pattern matching in let defs
    defs_without_patterns <- mapM expCLMatch defs >>= return . concat
    (provisos_from_defs, type_env_from_defs, rewritten_defs)
        <- tiSeq tiLetseqDef type_env defs_without_patterns
    (provisos_from_body, rewritten_body)
        <- tiExpr (type_env_from_defs ++ type_env) expected_type body
    return (provisos_from_defs ++ provisos_from_body,
            Cletseq rewritten_defs rewritten_body)

tiExpr as td expr@(Cletrec ds e) = do
    (ps, as', ds') <- tiDefls as ds
    (qs, e')       <- tiExpr (as' ++ as) td e
    return (ps ++ qs, Cletrec ds' e')

tiExpr as td (CSelect e i) = tiSelect (ImplRead Nothing) as td e i id
tiExpr as td (CSelectTT ti e i) = tiSelect NoRead as td e i (const t)
  where t = TCon (TyCon ti (Just KStar) TIabstract)

tiExpr as td exp@(CCon c es) = do
    (c' :>: sc, ti) <- findCons td c
    (ps :=> t, ts) <- freshInstT "C" c sc td
    s <- getSubst
    let finalTD = apSub s td
        numTDExpected = genericLength $ fst $ getArrows $ finalTD
        numConExpected =
          case fst $ getArrows t of
            [argTy] | isTypeUnit argTy -> 0
                    | Just (TyCon _ _ (TIstruct (SDataCon _ False) fs)) <- leftTyCon argTy -> genericLength fs
            _ -> 1
        numGiven = genericLength es
        numRemaining = numConExpected - numGiven
    -- traceM ("CCon: " ++ ppReadable c ++ " " ++ show t ++ " " ++ show numExpected ++ " " ++ show numGiven)
    if numGiven > numConExpected
      -- XXX Errors about consturctor argument mismatches should contain the type of
      -- the constructor, but this is overly hard to actually compute.
      then err (getPosition exp, EConMismatchNumArgs (show c') numConExpected numGiven)
      else if not (isTVar finalTD) && numGiven < numConExpected && numRemaining /= numTDExpected
      then err (getPosition exp, EPartialConMismatchNumArgs (show c') (pfpReadable finalTD) numConExpected numGiven numTDExpected)
      else do extraArgs <- sequence $
                   map ((newVar $ getPosition c) . ("a" ++) . show) $
                   range (0, numRemaining - 1)
              let res =
                    case es ++ map CVar extraArgs of
                      []  -> let unit = setIdPosition (getPosition c) idPrimUnit
                             in CApply (CCon0 Nothing c) [CStruct (Just True) unit []]
                      [e] -> CApply (CCon0 Nothing c) [e]
                      es  ->
                        let ies = zipWith (\ i e -> (setIdPosition (getPosition e) i, e)) tupleIds es
                        in  CApply (CCon0 Nothing c) [CStruct (Just True) (mkTCId ti c) ies]
              tiExpr as td $ foldr CLam res $ map Right extraArgs

tiExpr as td (CCon1 ti c e) = tiExpr as td (CApply (CCon0 (Just ti) c) [e])

tiExpr as td exp@(CCon0 mti c) = do
    --trace ("CCon0: " ++ ppReadable c) $ return ()
    -- XXX not so nice, but must get result type to findCons
    tdc <- case mti of
           Nothing -> do
                        (_, tdc) <- unifyFnFromTo c exp td
                        return tdc
           Just ti -> return (TCon (TyCon ti Nothing TIabstract))
    --
    (c' :>: sc, ti) <- findCons tdc c
    (ps :=> t, ts) <- freshInstT "C" c sc td
    eq_ps <- unify exp t td
    ps'            <- concatMapM (mkVPred (getPosition exp)) ps
    return (eq_ps ++ ps', iAPs (CConT ti c' []) ts ps')

tiExpr as td exp@(CStruct mb c ies) = do
    --trace ("CStruct " ++ ppReadable exp) $ return ()
    disamb <- disambiguateStruct mb td c (map fst ies)
    case disamb of
      Left tc -> handleStruct tc
      Right ti  -> handleCons ti
 where
   handleCons ti = tiExpr as td (CApply (CCon0 Nothing c) [CStruct (Just True) ti ies])
   handleStruct tyc@(TyCon c' (Just k) (TIstruct ss qfs)) = do
            -- find any defaults
            defaults <- concatMapM (findFieldDefault td c c') qfs
            let mkTS t KStar = return t
                mkTS t (Kfun ka k) = do v <- newTVar "tiExpr CStruct" ka c; mkTS (TAp t v) k
                mkTS _ _ = internalError "TCheck.tiExpr mkTS"
                -- Given a field name from the type, find its definition
                -- in the CStruct (if a def isn't found, return don't-care).
                -- (Compare unqualified because "f" is unqualified and "i"
                -- might be qualified -- GenWrap creates qualified names.)
                mkIE f =
                  let -- lookup from a map, in case the number of fields is large
                      -- (this preserves the qualified name, since that's what the
                      -- previous code did; is it necessary?)
                      ies_map = M.fromList [ (unQualId i, (i,e)) | (i,e) <- ies ]
                      dflts_map = M.fromList defaults  -- defaults are unqualified
                      pos = getPosition c
                      und = anyExprAt pos
                  in
                    case (M.lookup f ies_map) of
                      Just (i,e) -> (i,e)
                      Nothing ->
                        case (M.lookup f dflts_map) of
                          Just e -> (f,e)
                          Nothing -> (setIdPosition pos f, und)
            -- Check for errors, such as duplicate fields or invalid fields
            -- (see similar code in tiExpr of CStructUpd and tiPat of CPstruct)
            --
            -- We will want to perform "is \\ qfs" to find fields
            -- mentioned by the user which are not in the type.
            -- Since "is" can be qualified (by GenWrap, at least),
            -- we need to define what equality means and use "deleteFirstsBy"
            -- instead of "\\".
            let eq_func type_id user_id =
                    let (uqual, ubase) = getIdFStrings user_id
                        (tqual, tbase) = getIdFStrings type_id
                    in  (ubase == tbase) &&
                        (uqual == fsEmpty || uqual == tqual)
                del_func = deleteFirstsBy eq_func
            let is = map fst ies
                dfs = map unQualId is
                fs = map unQualId qfs
            case findDup dfs of
             i : _ -> err (getPosition i, EDupField (pfpString i))
             [] -> case (is `del_func` qfs) of
                   i : _ -> -- report the qualified type name (c')
                            err (getPosition i, ENotField (pfpString c') (pfpString i))
                   [] -> do
                    -- identify the missing fields
                    -- (except those with default values)
                    let missing_fs = fs \\ (dfs ++ map fst defaults)
                    -- warn about any missing defs which are not defaulted
                    let mkWarn i = twarn (getPosition c,
                                          WMissingField (pfpString i))
                    mapM_ mkWarn (filter (not . isRdyId) missing_fs)
                    st <- mkTS (TCon tyc) k
                    eq_ps <- unify exp st td
                    -- we already know that "i" is a member of "fs",
                    -- so call tiField1 directly
                    --psies <- mapM (tiField c fs as st) (map mkIE fs)
                    psies <- mapM (tiField1 as st) (map mkIE fs)
                    let (pss, ies') = unzip psies
                    --trace (show (fs, map fst ies)) $ return ()
                    return (concat (eq_ps:pss), CStructT st ies')
   handleStruct _ = internalError ("tiExpr: struct disambig didn't return expected TyCon")

tiExpr as td exp@(CStructUpd e []) = tiExpr as td e
tiExpr as td exp@(CStructUpd e ies@((i,_):_)) = do
    (ps, e') <- tiExpr as td e
    -- XXX should use all fields to disambiguate
    (_, ti, _) <- findFields td i
    sy <- getSymTab
    case findType sy ti of
     Just (TypeInfo _ _ _ (TIstruct sst qfs) _) | isUpdateable sst -> do
        --posCheck "C" e
        x <- newVar (getPosition e) "tiExprCStructUpd"
        let v = CVar x
            -- Desugar the struct-update into a struct-creation, where
            -- any field not mentioned by the user is populated with
            -- the value of that field in the original struct.
            -- For fields mentioned by the user, use that Id (for its position).
            -- For other fields, use the qualified field name, in case the
            -- unqualified name isn't in scope.
            new = CStruct (Just True) ti (map mk qfs)
            mk qf = case find (qualEq qf . fst) ies of
                      Just (i, e) -> (i, e)
                      Nothing -> (qf, CSelectTT ti v qf)
        -- Check for errors, such as duplicate fields or invalid fields
        -- (see similar code in tiExpr of CStruct and tiPat of CPstruct)
        -- A field name that appears both qualified and unqualified counts as a
        -- duplicate.  Fields with the right base name but wrong qualifier
        -- should be reported as invalid.
        let updids = map fst ies
        -- We could use something like "findDupBy qualEq updids" but that wouldn't
        -- handle the case of "GoodQual.f" and "BadQual.f", which we want to report
        -- early, particularly until we fix the disambiguation of the type to
        -- consult more of the fields than just the first
        case findDup (map unQualId updids) of
            i : _ -> err (getPosition i, EDupField (pfpString i))
            [] -> case deleteFirstsBy qualEq updids qfs of
                   i : _ -> err (getPosition i, ENotField (pfpString ti) (pfpString i))
                   [] -> do
                            (qs, new') <- tiExpr ((x :>: toScheme td) : as) td new
                            return (ps ++ qs, cLet [(x, td, e')] new')
     _ -> -- findFields would fail if the type was not a struct
          -- so this should only be reachable if the subtype is not SStruct
          err (getPosition e, ENotStructUpd (pfpString e))

-- case statement must have at least one arm
tiExpr as td exp@(Ccase pos _ []) = err (pos, EEmptyCase)
tiExpr as td exp@(Ccase pos e arms) =
  do
    -- traceM("original case: " ++ ppReadable exp)
    e_type <- newTVar "tiExpr.CCase scrutinee" KStar e
    (ps, e') <- tiExpr as e_type e
    let clause_type = e_type `fn` td
    let clauses = [CClause [cca_pattern arm] (cca_filters arm)
                   (cca_consequent arm) | arm <- arms]
    (ps', clauses') <- tiClauses as clause_type clauses
    s <- getSubst
    -- traceM("substitution: " ++ ppReadable s)
    -- bvs <- getBoundTVs
    -- traceM("bound tyvars" ++ ppReadable bvs)
    -- convert constraints to concrete predicates & remove duplicates
    let cpreds = nub (map (predToCPred . toPred) (apSub s (ps ++ ps')))
    let cqt_clause_type = (CQType cpreds (apSub s clause_type))
    -- addBoundTVs (tv cqt_clause_type)
    let ic = id_case pos
    -- desugar into *type-checked* CLValueSign of a function applied to the scrutinee
    -- NOTE: none of the variables in the cqt are to be generalized over (hence the [] in CDefT)
    let ccase = (Cletrec [CLValueSign (CDefT ic [] cqt_clause_type clauses') []]
                      (cApply 3 (CVar ic) [e']))
    -- traceM("desugared case: " ++ ppReadable ccase)
    -- (ps ++ ps', exp') <- tiExpr as td ccase
    -- popBoundTVs
    let ret_ps = ps ++ ps'
    ret_ps' <- updateContexts pos ret_ps  -- because tiApply does this
    return (ret_ps', ccase)

tiExpr as td (CAny pos uk) = do
    return ([], CAnyT pos uk td)

tiExpr as td exp@(CVar i) =
    -- it is ok to add register read to the variable
    tiVar (ImplRead Nothing) as td exp

tiExpr as td (CApply (CVar f) [exp]) | f `qualEq` idAsIfc =
    case (exp) of
        var@(CVar i) -> tiVar NoRead as td var
        sub@(CSub pos e1 e2) -> tiSub NoRead as td pos e1 e2
        sel@(CSelect e i) -> tiSelect NoRead as td e i id
        _ -> tiExpr as td exp

tiExpr as td exp@(CApply f@(CVar gn) es@[(CVar i)]) | gn `qualEq` idPrimGetName = do
  unifyNoEq "primGetName" exp tName td
  -- need to make sure to qualify the primitive identifier for IConv
  return ([], (CApply (CVar idPrimGetName) es))

tiExpr as td exp@(CApply f@(CVar vo) [e@(CHasType _ t)]) | vo == idValueOf = do
    let vs = nub (tv t)
    bvs <- getBoundTVs
    case vs \\ bvs of
        [] -> tiApply as td exp f e
        v : _ -> err (getPosition exp, EValueOf (pfpString v))

tiExpr as td exp@(CApply f@(CVar vo) [e@(CHasType _ t)]) | vo == idStringOf = do
    let vs = nub (tv t)
    bvs <- getBoundTVs
    case vs \\ bvs of
        [] -> tiApply as td exp f e
        v : _ -> err (getPosition exp, EStringOf (pfpString v))

tiExpr as td (CApply e []) = tiExpr as td e
tiExpr as td exp@(CApply f [e]) = tiApply as td exp f e
tiExpr as td (CApply e es) = tiExpr as td (foldl ap e es)
  where ap f a = CApply f [a]

-- lookup system-task handler in taskCheckMap and run
tiExpr as td exp@(CTaskApply f@(CVar task) es) =
  let undeftask as td f es = err (getPosition task, EUndefinedTask (pfpString task))
      checker = lookupWithDefaultBy qualEq taskCheckMap undeftask task
  in checker as td f es

-- already type-checked - just ensure expected type is PrimAction
-- and qualify the task identifier
-- unify is not needed since these are wrapped with a fromAction or fromPrimAction
tiExpr as td exp@(CTaskApplyT (CVar task) t es) =
  do
    -- pick out the matching qualified task identifier
    let task' = headOrErr ("TCheck.tiExpr: unmatched task: " ++
                           pfpString task)
                (filter (qualEq task) taskIds)
    let task'' = setIdPosition (getPosition task) task'
    --unify exp tPrimAction td
    --unify exp tAction td
    return([],(CTaskApplyT (CVar task'') t es))

-- apply "fromString" to string literals when the syntax is BSV
-- (Classic has a syntax for distinguishing Char from String)
-- XXX we could do this in the BSV parse, except that CPLit doesn't have
-- XXX a place to put the expression; so we put it here (after CPLit has
-- XXX been converted to CLit in a pattern clause)
tiExpr as td (CLit l@(CLiteral pos (LString _))) =
  let lt = CLitT tString l
  in  if (isBSV())
      then tiExpr as td (cVApply (idFromString pos) [lt])
      else tiExpr as td lt
tiExpr as td (CLit l@(CLiteral pos (LChar _))) = tiExpr as td (CLitT tChar l)

-- insert fromInteger for unsized integer literals
tiExpr as td exp@(CLit l@(CLiteral pos
                          (LInt iv@(IntLit { ilWidth = Nothing })))) = do
    --traceM("tiExpr: CLiteral: fromInteger")
    tiExpr as td (cVApply (idFromInteger pos) [CLitT tInteger l])

-- insert fromSizedInteger for sized integer literals
tiExpr as td exp@(CLit l@(CLiteral pos
                          (LInt iv@(IntLit { ilWidth = Just nBits,
                                             ilValue = val })))) = do
    --traceM("tiExpr: CLiteral: fromSizedInteger")
    let ty = tBitN nBits pos
        qty = CQType [] ty
    -- detect if the value is out of range
    let sizeErr = let lit = pfpString (iv { ilWidth = Nothing })
                  in  err (pos, EInvalidSizedLiteral lit nBits)
    if (nBits < 0)
       then internalError("TCheck.tiExpr: negative sized literal: " ++
                          ppReadable iv)
       else if (nBits == 0)
            then when (val /= 0) sizeErr
            else when ((val >= 2^nBits) || (val < -(2^(nBits-1)))) sizeErr
    -- convert the possibly negative integer to a bit vector
    let l' = CLiteral pos (LInt (iv { ilValue = mask nBits val }))
    tiExpr as td (cVApply (idFromSizedInteger pos)
                  [(CHasType (CLitT ty l') qty)])

-- insert fromReal for real literals
tiExpr as td exp@(CLit l@(CLiteral pos (LReal iv))) = do
    --traceM("tiExpr: CLiteral: fromReal")
    tiExpr as td (cVApply (idFromReal pos) [CLitT tReal l])

tiExpr as td (CLit l@(CLiteral pos LPosition)) = tiExpr as td (CLitT tPosition l)

tiExpr as td e@(CLitT t _) = do
    eq_ps <- unify e t td
    return (eq_ps, e)

tiExpr as td e@(CAnyT _ _ t) = do
    eq_ps <- unify e t td
    return (eq_ps, e)

tiExpr as td (CBinOp e1 comma e2) | comma == idComma =
    let pos = getIdPosition comma
    in  tiExpr as td (CStruct (Just True) (setIdPosition pos idPrimPair)
                [(setIdPosition pos (unQualId idPrimFst), e1), (setIdPosition pos (unQualId idPrimSnd), e2)])

tiExpr as td (CBinOp e1 op e2) = tiExpr as td (cVApply op [e1, e2])

-- XXX This handles the "hacky encoding of dict" by convInst
tiExpr as td (CHasType (CAny {}) qt@(CQType [_] nt)) | nt == noType = do
    qual_type <- mkQualType qt
    case qual_type of
      [PredWithPositions p poss] :=> _ -> do
          -- poss is probably a list of only one position
          VPred i pwp <- mkVPredFromPred poss p
          let pwp' = addPredPositions pwp poss
          return ([VPred i pwp'], CVar i)
      _ -> internalError ("tiExpr: unexpected mkQualType result")

{- fast special case
tiExpr as td (CHasType (CLit pos l@(LInt _)) (TAp b n)) | b == tBit =
-}

tiExpr as td exp@(CHasType e ct) = do
    --posCheck "D" e
    x <- newVar (getPosition e) "tiExprCHasType"
--    trace ("CHasType " ++ ppReadable (x, e, ct)) $ return ()
    (ps, e') <- tiExpr as td (Cletrec [CLValueSign (CDef x ct [CClause [] [] e]) []] (CVar x))
    return (ps, optTrivLet e')

tiExpr as td (Cif pos e e1 e2) = tiExpr as td (cVApply (id_if pos) [e, e1, e2])

--tiExpr as td exp@(CSub e1 e2) = tiExpr as td (cVApply (id_asub (getPosition e2)) [e1, e2])

tiExpr as td exp@(CSub2 e1 e2 e3) = do
        eq_ps <- case guessBitSize e2 e3 of
                   NoGuess -> return []
                   Guess t -> unify exp t td
                   BadSize sz pos -> err (pos, EBadExtractSize sz)
                   BadIndex idx pos -> err (pos, EBadExtractIndex idx)
        let extractPos = getPosition e2
        (ps, e') <- tiExpr as td (cVApply (idExtract extractPos) [posLiteral extractPos, e1, e2, e3])
        return (eq_ps ++ ps, e')

tiExpr as td exp@(CSubUpdate pos e_vec (e_hi, e_lo) e_rhs) = do
  e_rhs' <- case guessBitSize e_hi e_lo of
              NoGuess -> return e_rhs
              Guess t -> return $ CHasType e_rhs (CQType [] t)
              BadSize sz pos -> err (pos, EBadExtractSize sz)
              BadIndex idx pos -> err (pos, EBadExtractIndex idx)
  let e' = CApply (CVar (idPrimUpdateRangeFn pos)) [posLiteral pos, e_vec, e_hi, e_lo, e_rhs']
  tiExpr as td e'

tiExpr as td exp@(CSub pos e1 e2) = tiSub (ImplRead Nothing) as td pos e1 e2

tiExpr as td exp@(Cinterface pos Nothing ds) = internalError "TCheck.tiExpr: Cinterface Nothing"

-- Converts an interface expr to a struct expr and typechecks that.
-- An interface is a list of definitions, but a struct is a list of exprs,
-- so each def "i = e" is converted to "let {i = e} in i".  Thus, if the
-- def has no explicit type, even though the struct field has a type,
-- the "i" in the expr for the struct field is not nailed down (only its
-- use becomes nailed down).  Thus, ambiguities in "e" are not resolved.
--
-- (The choice of "let {i=e} in i" allows two things: implicit conditions
--  on the method to be preserved, and a user-specified explicit type to
--  be preserved.  If no explicit type was given by the user, you might
--  consider converting the CDefl to just an expr, but there is currently
--  no CSyntax "when" expr to retain the CQual part of the CDefl.)
--
-- Possible solutions:
-- * Typecheck interfaces directly
-- * Do enough checking of the interface type to put explicit types on
--   the field defs
--
-- Chosen solution:
-- * Do nothing here.  Instead, inside typechecking of CStruct fields,
--   in tiField1, we notice that the expr's are then converted again
--   to a def, to call tiExpl'.  There's no point into converting an ifc
--   def to an expr just to converted in forward into a def again.
--   So ... in tiField, look for "let {i=e} in i" and just extract
--   the "e" (to convert backwards, rather than convert forward).
--   The one downside, is that auto adding of _read to variables, won't
--   apply once we remove the "in i" part.
--
tiExpr as td exp@(Cinterface pos (Just ti) ds) = do
    let
        mkFieldPair d = let i = getLName d
                        in  (i, Cletseq [d] (CVar i))
        ifc = CStruct (Just True) ti (map mkFieldPair ds)
    -- check that the user's argument names match those in the type
    -- declaration, and warn if not (if the warning is turned on)
    checkMethodArgNames ti ds
    -- return type-check of the result
    tiExpr as td ifc

tiExpr as td exp@(Cmodule modulePos ms) = do
    s <- getSubst
    v <- newTVar "tiExpr Cmodule" (KStar `Kfun` KStar) exp
    -- let pos = getPosition exp
    case expandSyn (apSub s td) of
      TAp tc t ->  do ms' <- fixup
                      stmts <- mapM toStmt ms'
                      tiExpr as td (Cdo True stmts)
        where isMifc (CMinterface _) = True
              isMifc (CMTupleInterface _ _) = True
              isMifc _ = False
              forceIsMod e = cVApply (idForceIsModuleAt (getPosition e)) [e]
              toStmt (CMStmt (CSExpr n e)) = return (CSExpr n (forceIsMod e))
              toStmt (CMStmt s) = return (s)
              toStmt (CMrules e) = return (CSExpr Nothing (cVApply (idAddRules (getPosition e)) [e]))
              toStmt (CMinterface e@(Cinterface pos Nothing ies)) =
                case leftCon t of
                  Nothing -> err (getPosition exp, ENoTypeSign (pfpString exp))
                  Just ti -> return (CSExpr Nothing (cVApply
                                              (idReturn pos)
                                              [Cinterface pos (Just (setIdPosition pos ti)) ies]))
              toStmt (CMinterface e) = return (CSExpr Nothing (cVApply (idReturn (getPosition e)) [e]))
              toStmt (CMTupleInterface pos es) = return (CSExpr Nothing (cVApply (idReturn pos) [mkTuple pos es]))
              isMExpr (CMStmt (CSExpr _ _)) = True
              isMExpr _ = False
              fixup = case partition isMifc ms of
                        ([], _:_) | isMExpr (last ms) -> return (ms)
                        ([], _)                       -> return (ms ++ [CMinterface (Cinterface modulePos Nothing [])])
                        (m@[ifc], ms')                -> return (ms' ++ m)
                        _                             -> err(getPosition exp, EMultipleInterfaces)
      t -> err (getPosition exp, ENoTypeSign (pfpString exp))

tiExpr as td exp@(CmoduleVerilog name ui clks rsts args fields sch ps) = do
    (nps, name') <- tiExpr as tString name
    v <- newTVar "tiExpr CmoduleVerilog" KStar exp
    eq_ps <- unify exp (TAp tModule v) td
    s <- getSubst
    sy <- getSymTab

    -- some common definitions for error messages
    let getString (CLit (CLiteral _ (LString x))) = x
        getString x = internalError ("Cmoduleverilog not lit: " ++ show x)
    let name_str = getString name
        name_pos_str = ppReadable (getPosition name)

    -- param or port argument typecheck
    -- params allow strings, ports do not (see ACheck)
    let tiVerilogParam e = do
          v <- newTVar "tiExpr CmoduleVerilog 2 param" KStar e
          let e' = cVApply (idPrimToParam (getPosition e)) [e]
          res <- tiExpr as v e'
          t'  <- expandFullType v
          return (res, t')
    let tiVerilogPort e = do
          v <- newTVar "tiExpr CmoduleVerilog 2 port" KStar e
          let e' = cVApply (idPrimToPort (getPosition e)) [e]
          res <- tiExpr as v e'
          t'  <- expandFullType v
          return (res, t')

    let tiInoutArg e = do
           v <- newTVar "tiExpr CmoduleVerilog 3" KStar e
           res <- tiExpr as v e
           t'  <- expandFullType v
           if isInout_ t'
              then return (res, t')
              else internalError("TCheck: tiInoutArg: " ++ show t')

    -- type-check primitive module argument
    let tiArg (a, e) = do
            ((ps, e'), t) <- case a of
                          (Param _)    -> tiVerilogParam e
                          (Port _ _ _) -> tiVerilogPort e
                          (ClockArg _) -> tiExpr as tClock e >>= (\res -> return (res, tClock))
                          (ResetArg _) -> tiExpr as tReset e >>= (\res -> return (res, tReset))
                          (InoutArg {}) -> tiInoutArg e
            return (ps, t, (a, e'))

        -- This checks the types and number of Verilog ports,
        -- and updates Classic VFI to BSV format
        chkVeriIfc :: [Id] -> VFieldInfo -> TI (VFieldInfo)
        chkVeriIfc self_sbs vfi = do
                let f = vf_name vfi
                    f_str = pfpString f

                (_ :>: sc, _, _) <- findFields v f
                -- traceM(ppReadable sc)
                (_ :=> ft, _)    <- freshInst "D" f sc
                (t, eq_ps) <- unifyFnTo f exp ft v
                when (not . null $ eq_ps) $
                  internalError("TCheck.chkVeriIfc: " ++ ppReadable (exp,v,f,ft,t))
                s <- getSubst
                let mtype = expandSyn (apSub s t)
                let (argTypes, resType) = getArrows mtype

                -- This function checks that the number of port names
                -- matches the number of arguments in the type.
                let chkArgs :: [VPort] -> [Type] -> TI ()
                    chkArgs ports types =
                        if (length ports > length types)
                        then -- The extra port names could be used in the error
                             err (getPosition f,
                                  EForeignModTooManyPorts f_str)
                        else if (length ports < length types)
                        then err (getPosition f,
                                  EForeignModTooFewPorts f_str)
                        else mapM_ chkArgType types

                -- This function checks that the argument types are bitable
                    chkArgType t =
                        if isBit t then
                            return ()
                        else
                            err (getPosition f,
                                 EForeignModBadArgType
                                     (pfpString t) name_str name_pos_str)

                -- Check that the return type is either bitable,
                -- an Action, or an ActionValue, and that the port info
                -- matches the types.
                let
                    -- XXX These errors should give more info
                    chkResType :: [VPort] -> Maybe VPort -> Maybe VPort -> Type ->
                                  TI ([VPort], Maybe VPort, Maybe VPort)
                    chkResType ps me@(Just _) mo@Nothing t =
                        if (isActionWithoutValue t) then return (ps, me, mo)
                        else if (isActionWithValue t)
                        then errMissingValue "ActionValue" t
                        else if (isBit t)
                        then errUnexpectedEnable "value" t
                        else errBadResType t
                    chkResType ps me@Nothing mo@(Just _) t =
                        if (isBit t) then return (ps, me, mo)
                        else if (isActionWithValue t)
                        then errMissingEnable "ActionValue" t
                        else if (isActionWithoutValue t)
                        then errUnexpectedValue "Action" t
                        else errBadResType t
                    chkResType ps me@(Just _) mo@(Just _) t =
                        if (isActionWithValue t) then return (ps, me, mo)
                        else if (isActionWithoutValue t)
                        then errUnexpectedValue "Action" t
                        else if (isBit t)
                        then errUnexpectedEnable "value" t
                        else errBadResType t
                    chkResType ps Nothing Nothing t = do
                        -- must have more than 0 ports
                        when (null ps) $
                          err (getPosition f,
                               EForeignModTooFewPorts (pfpString f))
                        -- update the Classic fieldinfo to BSV format
                        let inputs = initOrErr "chkResType" ps
                        let final_port = lastOrErr "chkResType" ps
                        -- XXX kill PrimAction once imports in Prelude are converted over
                        if (isActionWithoutValue t) || (isPrimAction t)
                         then return (inputs, Just final_port, Nothing)
                         else if (isBit t)
                               then return (inputs, Nothing, Just final_port)
                               else errBadResType t

                    errBadResType t =
                        err (getPosition f,
                             EForeignModBadResType
                                 (pfpString t) name_str name_pos_str)
                    errMissingValue desc t =
                        err (getPosition f,
                             EForeignModMissingValuePort desc name_str f_str)
                    errMissingEnable desc t =
                        err (getPosition f,
                             EForeignModMissingEnablePort desc name_str f_str)
                    errUnexpectedValue desc t =
                        err (getPosition f,
                             EForeignModUnexpectedValuePort
                                 desc name_str f_str)
                    errUnexpectedEnable desc t =
                        err (getPosition f,
                             EForeignModUnexpectedEnablePort
                                 desc name_str f_str)

                    errActionSelfSB f =
                        err (getPosition f, EActionSelfSB [f_str])

                    errNotClockType t =
                        err (getPosition f, EForeignModNotClockType
                                              f_str (pfpString t)
                                              name_str name_pos_str)
                    errNotResetType t =
                        err (getPosition f, EForeignModNotResetType
                                              f_str (pfpString t)
                                              name_str name_pos_str)
                    errClockHasArgs =
                        err (getPosition f, EForeignModClockHasArgs
                                              f_str name_str name_pos_str)
                    errResetHasArgs =
                        err (getPosition f, EForeignModResetHasArgs
                                              f_str name_str name_pos_str)
                    errNotInoutType t =
                        err (getPosition f, EForeignModNotInoutType
                                              f_str (pfpString t)
                                              name_str name_pos_str)
                    errInoutHasArgs =
                        err (getPosition f, EForeignModInoutHasArgs
                                              f_str name_str name_pos_str)

                case vfi of
                    Clock {} -> if (not (isClock resType))
                                then errNotClockType resType
                                else if (null argTypes)
                                then return vfi
                                else errClockHasArgs
                    Reset {} -> if (not (isReset resType))
                                then errNotResetType resType
                                else if (null argTypes)
                                then return vfi
                                else errResetHasArgs
                    Inout {} -> if (not (isInout_ resType))
                                then errNotInoutType resType
                                else if (null argTypes)
                                then return vfi
                                else errInoutHasArgs
                    Method { vf_inputs = inputs, vf_enable = me, vf_output = mo } ->
                            do -- updates inputs, me and mo when processing Classic format
                               (inputs', me', mo') <- chkResType inputs me mo resType
                               -- check if any actions are SB with themselves
                               when (((isActionWithValue resType) ||
                                      (isActionWithoutValue resType) ||
                                      (isPrimAction resType)) &&
                                      (f `elem` self_sbs))
                                    (errActionSelfSB f)
                               chkArgs inputs' argTypes
                               return (vfi { vf_inputs = inputs', vf_enable = me', vf_output = mo' })
    -- paramResults <- mapM tiParam es
    qsses <- mapM tiArg args
--  let   (pses, tys) = unzip paramResults
--        (pss, es') = unzip pses
    let (qss, ts, ses') = unzip3 qsses
    let methnames  = [n | (Method { vf_name = n }) <- fields]
    let clocknames = [c | (Clock c) <- fields]
    let resetnames = [r | (Reset r) <- fields]
    let inoutnames = [n | (Inout { vf_name = n }) <- fields]
    let self_sb_methods =
             let mci = methodConflictInfo sch
             in  [ m | (m,m') <- sSB mci, m == m' ]
    chkSchedInfo methnames sch
    let fieldnames = methnames ++ clocknames ++ resetnames ++ inoutnames
--    traceM("Field names: " ++ ppReadable(fieldnames))
    -- monadic evaluations for ty below
--    tyM1 <- mapM (\ e -> newTVar "tiExpr CmoduleVerilog 4" KStar e) es
--    tyM2 <- mapM (\ t -> newTVar "tiExpr CmoduleVerilog 5" KStar t) ts
    case leftCon (expandSyn (apSub s v)) of
     Just ti | (Just fs0) <- getIfcFields ti sy ->
         let fs = {- trace ("fields:" ++ ppReadable fs0) $ -} map unQualId fs0
             ty = foldr fn td ts
         in
                -- check for extra fields first
                case fieldnames \\ fs of
                  i:_ -> err (getIdPosition i, EForeignModNotField
                                                   (pfpString ti) (pfpString i))
                  [] -> -- now check for missing fields
                      case fs \\ fieldnames of
                        i:_ -> err (getIdPosition i,
                                    EForeignModMissingField (pfpString i)
                                        name_str name_pos_str)
                        _ -> do fields' <- mapM (chkVeriIfc self_sb_methods) fields
                                let e' = CmoduleVerilogT ty name' ui clks rsts
                                                         ses' fields' sch ps
                                return (eq_ps ++ nps {- ++ concat pss -} ++ concat qss, e')
     _ -> err (getPosition exp, ENotAnInterface)

tiExpr as td exp@(CForeignFuncC link_id wrap_cqt) = do
    -- the "wrap_type" should be identical to "td"
    s <- getSubst
    let src_type = expandSyn (apSub s td)
        (argTypes, resType) = getArrows src_type
        -- for positions for new CSyntax constructs
        pos = getPosition link_id
    let bits = CTypeclass idBits

    -- functions for analyzing the argument and result type
    let isPrimArg t = (isTypeBit t) || (isTypeString t)
        isPrimRes t = (isTypeBit t) ||
                      (isTypePrimAction t) || (isTypeActionValue_ t)

    -- given a type, find its bit-size
    let findBitSize t = do
            szv <- newTVar "findBitSize" KNum t
            let ctx = CPred bits [t, szv]
            return ([ctx], szv)

    -- determine the prim types and csyntax wrappers
    let -- return the primitive type, any contexts, and the csyntax
        -- for converting the wrapper argument to the primitive
        mkArg (t,i) | isPrimArg t = return ([], t, CVar i)
        mkArg (t,i) = do (ctxs, prim_sz) <- findBitSize t
                         let prim_t = TAp tBit prim_sz
                             cexpr = cVApply idPack [CVar i]
                         return (ctxs, prim_t, cexpr)

        -- determine the result wrapper based on the return type.
        -- returns (ctxs, prim type, csyntax expr func)
        mkRes =
                -- return type cannot be a string
                if (isTypeString resType)
                then err (getPosition pos, EForeignFuncStringRes)
                -- primitive types don't need conversion
                else if (isPrimRes resType)
                then return ([], resType, \e -> e)
                -- convert ActionValue types
                else if (isTypeActionValue resType)
                then do let cexpr = \e -> cVApply idFromActionValue_ [e]
                            av_arg = getActionValueArg resType
                        when (isTypeString av_arg) $
                            err (getPosition pos, EForeignFuncStringRes)
                        (ctxs, prim_sz) <- findBitSize av_arg
                        let prim_t = TAp tActionValue_ prim_sz
                        return (ctxs, prim_t, cexpr)
                -- anything else must be bitifiable
                else do let cexpr = \e -> cVApply idUnpack [e]
                        (ctxs, prim_sz) <- findBitSize resType
                        let prim_t = TAp tBit prim_sz
                        return (ctxs, prim_t, cexpr)

    -- get the pieces of the CSyntax
    pattern_var_ids <-
        mapM (\t -> newVar (getPosition t) "tiExprCForeignFuncC") argTypes
    let pat_args = map CPVar pattern_var_ids

    -- construct info for the arguments
    arg_triples <- mapM mkArg (zip argTypes pattern_var_ids)
    let (arg_ctxss, arg_prim_tys, arg_cexprs) = unzip3 arg_triples
    let arg_ctxs = concat arg_ctxss

    -- construct info for the result
    (res_ctxs, res_prim_ty, res_cexpr_func) <- mkRes

    let prim_basetype = foldr fn res_prim_ty arg_prim_tys
        --ctxs = res_ctxs ++ arg_ctxs
        --prim_type = CQType ctxs prim_basetype

    -- ----------
    -- for better error message reporting, check the "ctxs" here

    -- get the available epreds
    epreds <- getExplPreds

    -- function to extract the type which is not bitifiable
    let extractType vp =
            case (toPred vp) of
                (IsIn c [t,_]) | (Pred.name c == bits) -> t
                p -> internalError ("tiExpr CForeignFuncC: extractType: " ++
                                    ppReadable p)
    -- for polymorphic types, suggest that the user add a proviso
    let hasTyVar t = not (null (tv t))

    -- function to check predicates
    let checkCtxs ctxs errmsg = do
            (vqs :=> _) <- mkQualType (CQType ctxs prim_basetype)
            vpreds <- concatMapM (mkVPred (getPosition exp)) vqs
            -- see whether they can be satisfied
            (unsat_vpreds, _) <- satisfy epreds vpreds
            -- report any unsatisfied preds as errors
            let mkPair vp = let t = extractType vp
                            in  (pfpString t, hasTyVar t)
            when (not (null unsat_vpreds)) $
                err (pos, errmsg (map mkPair unsat_vpreds))

    checkCtxs arg_ctxs EForeignFuncBadArgType
    -- there should not be more than one result ctx
    let resErr [(t,b)] = EForeignFuncBadResType t b
        resErr _ = internalError ("tiExpr CForeignFuncC: res ctx")
    checkCtxs res_ctxs resErr

    -- ----------

    -- put the CSyntax together
    il <- newVar pos "tiExprCForeignFuncC"
    let -- the foreign is given the basetype, without the contexts
        prim_expr = CForeignFuncCT link_id prim_basetype
        wrapper_expr = res_cexpr_func (CApply prim_expr arg_cexprs)
        clause = CClause pat_args [] wrapper_expr
        defl_cqt = CQType [] src_type
        defl = CLValueSign (CDef il defl_cqt [clause]) []
        new_expr = Cletseq [defl] (CVar il)
    --traceM("new_expr = " ++ ppReadable new_expr)
    -- rather than duplicate the dictionary work that tiExpl does,
    -- just call tiExpr on the new_expr here
    tiExpr as td new_expr

-- This is needed because we call tiExpr on the new_expr in type checking
-- for CForeignFuncC, which contains CForeignFuncCT.
tiExpr as td exp@(CForeignFuncCT link_id prim_ty) = do
    eq_ps <- unify exp prim_ty td
    return (eq_ps, exp)

tiExpr as td e@(Cdo False ss) = do
    v <- newTVar "tiExpr Cdo False" (KStar `Kfun` KStar) e
    tiStmts v Nothing as td ss

tiExpr as td e@(Cdo True ss) = do
    v <- newTVar "tiExpr Cdo True" (KStar `Kfun` KStar) e
    ss' <- recStmts ss
    tiStmts v Nothing as td ss'

tiExpr as td e@(Caction pos ss) = tiRecoveringFromError
                                  (tiAction as td pos ss)
                                  (return ([],e))

tiExpr as td e@(Crules ps rs) = do
    unifyNoEq "Crules" e tRules td
    psrs <- mapM (tiRule as) rs
    let (pss, rs') = unzip psrs
    return (concat pss, Crules ps rs')

tiExpr as td e@(Cattributes pps) = do
    unifyNoEq "Cattributes" e tAttributes td
    return ([], e)

tiExpr as td e0@(Cwrite write_pos lhs rhs) = do
    unifyNoEq "Cwrite" e0 tAction td
    -- traceM ("Cwrite top before: " ++ ppReadable e0)
    new_e <- rebuild lhs
               -- pre_ifc_cont
               ifc_error
               (\t -> (CApply (CSelect lhs (write_id t)) [rhs]))
               id
    -- traceM ("Cwrite top after: " ++ ppReadable new_e)
    tiExpr as td new_e

  where write_id t = let wid = id_write write_pos
                     -- if we have a TyCon, get its qualifier,
                     -- otherwise leave id unqualified
                     -- supports <= magic on interfaces whose fields
                     -- might not be visible (see 1213)
                     in case (leftCon t) of
                          Nothing -> wid
                          Just i -> setIdQual wid (getIdQual i)

        ifc_error t = err (write_pos, EAssignNotReg (pfpString t))
        -- x[i] <= v
        rebuild e_sel@(CSub pos select_lhs i) pre_ifc_cont ifc_cont pure_expr =
          rebuild
            select_lhs
            -- pre_ifc_cont
            (\_ -> do -- don't need the interior type for error reporting
               -- traceM("Cwrite select: " ++ ppReadable e_sel)
               t <- tiForType as (noRead e_sel)
               -- traceM ("Cwrite select t: " ++ ppReadable t)
               flags <- getFlags
               r <- getSymTab
               if writeableIfc flags r t || isTVar t then
                  return (ifc_cont t)
                else
                  pre_ifc_cont t)
            -- ifc_cont
            (\t ->
               let v' = pure_expr rhs -- finish feeding rhs into stacked updates
               in (CApply (CVar (idPrimWriteFn pos)) [posLiteral pos, (noRead select_lhs), i, v']))
            -- pure_expr
            (\rhs -> let v' = pure_expr rhs
                     in (CApply (CVar (idPrimUpdateFn pos)) [posLiteral pos, select_lhs, i, v']))

        -- x.a <= v
        rebuild e_dot@(CSelect expr id) pre_ifc_cont ifc_cont pure_expr =
          rebuild
            expr
            -- pre_ifc_cont
            (\_ -> do -- don't need the interior type for error reporting
               -- traceM("Cwrite struct: " ++ ppReadable e_dot)
               t <- tiForType as (noRead e_dot)
               -- traceM("Cwrite struct t: " ++ ppReadable e_dot)
               flags <- getFlags
               r <- getSymTab
               if writeableIfc flags r t || isTVar t then
                 return (ifc_cont t)
                else
                 pre_ifc_cont t)
          -- ifc_expr
          (\t ->
             let v' = pure_expr rhs
                 struct' = (CStructUpd (CSelect (noRead expr) (id_read (getPosition expr)))
                                     [(id, v')])
             in (CApply (CSelect expr (write_id t)) [struct']))
          -- pure_expr
          (\rhs -> let v' = pure_expr rhs
                   in (CStructUpd expr [(id, v')]))

        rebuild e_range@(CSub2 expr eh el) pre_ifc_cont ifc_cont pure_expr = do

          rebuild
            expr
            ifc_error
            (\t -> (CApply (CSelect expr (write_id t)) [range_update rhs]))
            range_update
         where pos = getPosition e_range
               range_update rhs = CSubUpdate pos expr (eh, el) v'
                  where v' = pure_expr rhs

        -- x <= v (base case)
        rebuild lhs pre_ifc_cont ifc_cont pure_expr = do
          t <- tiForType as (noRead lhs)
          -- traceM ("Cwrite base t: " ++ ppReadable t)
          flags <- getFlags
          r <- getSymTab
          if writeableIfc flags r t || isTVar t then
             return (ifc_cont t)
           else
             pre_ifc_cont t

tiExpr _ td exp = internalError ("TCheck.tiExpr: no match: " ++
                                 ppReadable (td, exp) ++
                                 "DEBUG:\n" ++
                                 ppDebug (td,exp) ++ "\n" ++
                                 (show exp))

tiAction :: [Assump] -> Type -> Position -> CStmts -> TI ([VPred], CExpr)
tiAction as td pos ss = do
    let ss' = case reverse ss of
                CSExpr _ _ : _ -> ss
                _ -> ss ++ [CSExpr Nothing $
                              cVApply (idReturn pos)
                                [CStruct (Just True) (setIdPosition pos idPrimUnit) []]]
    --trace (ppReadable (td, ss')) $ return ()
    unifyNoEq "tiAction" (Caction pos ss) tAction td
    ss'' <- recStmts ss'
    tiStmts tActionValue (Just tAction) as tAction ss''

-- system task checking functions
taskCheckNormal :: TaskCheckT
taskCheckNormal as td f es =
    do
      tiExpr as td (CApply f es)

litOne :: Position -> CExpr
litOne pos = CLit (CLiteral pos (LInt (ilDec 1)))

taskCheckRandom :: [Assump] -> Type -> CExpr -> [CExpr] -> TI ([VPred],CExpr)
taskCheckRandom as td f [] =
      do
        let pos = (getPosition f)
        let tav = TAp (tActionValueAt pos) (TAp tInt t32)
        eq_ps <- unify f tav td

        finishSWriteAV as td t32 f [] [] eq_ps

taskCheckRandom as td f es@[e] =
      do
        let pos = (getPosition f)
        let tav = TAp (tActionValueAt pos) (TAp tInt t32)
        eq_ps <- unify f tav td

        let pos' = getPosition e

        v <- newTVar "taskCheckRandom" KNum e
        let targ = TAp tInt v
        res <- tiExpr as targ e

        let e' = cVApply (setIdPosition pos' idPack) [e]
        let targ' = TAp tBit v
        res' <- tiExpr as targ' e'
        t' <- expandFullType targ'
        let pr =(res', t', [])

        finishSWriteAV as td t32 f es [pr] eq_ps

taskCheckRandom as td f es =
    do x <- err (getPosition f, (ETaskMismatchNumArgs "$random" "0 or 1" (toInteger (length es))))
       return x

taskCheckFinish :: [Assump] -> Type -> CExpr -> [CExpr] -> TI ([VPred],CExpr)
-- make finish() into finish(1)
taskCheckFinish as td f [] = tiExpr as td (CApply f [litOne pos])
  where pos = getPosition f
taskCheckFinish as td f es = tiExpr as td (CApply f es)

taskCheckFatal :: [Assump] -> Type -> CExpr -> [CExpr] -> TI([VPred], CExpr)
taskCheckFatal as td f [] = taskCheckFatal as td f [litOne pos]
  where pos = getPosition f
taskCheckFatal as td f (code:es) = do
  -- the code is really the same as a finish argument,
  -- so check is as Bit 2, but pass it on as Bit 32
  let pos    = getPosition f
  let code'  = CHasType code (CQType [] (tBitN 2 pos))
  let ext    = CVar (setIdPosition pos idPrimZeroExt)
  let code'' = CHasType (CApply ext [code']) (CQType [] bit32)
  taskCheckDisplay as td f (code'':es)

-- Checks on display param, and converts it to a "native" bit or string type along with
-- any other VPred as needed.
-- [VPred]
-- CExpr
-- Type
-- CStmts are generated for action value functions (e.g. $time) in argument list.
checkDisplayParam :: Bool -> Bool -> [Assump] -> CExpr
                  -> TI (([VPred], CExpr), Type, CStmts)
checkDisplayParam av_ok fmt_ok as e =
    do
      v <- newTVar "checkDisplayParam start" KStar e
      res@(ps, e') <- tiExpr as v e
      t <- expandFullType v
      let pos = getPosition e

      case t of
        _ | fmt_ok && isFmt t -> return (res, t, [])
        _ | isBit t || isString t || isReal t -> return (res, t, [])
        _ | isChar t ->
          do res' <- tiExpr as tString (cVApply (idPrimCharToString pos) [e])
             return (res', tString, [])
        -- if it is an Integer force to (signed) 32 bits
        -- XXX: should we force laundering through Int 32 (but maybe it is cleaner)
        _ | isInteger t ->
          do res' <- tiExpr as bit32 (CApply (CVar (idSigned pos)) [(cVApply (idFromInteger pos) [e])])
             return (res', bit32, [])
        -- force signed display of Int
        _ | isInt t ->
          do
            v' <- newTVar "checkDisplayParam pack Int" KStar e
            res' <- tiExpr as v' (CApply (CVar (idSigned pos))
                                       [(cVApply (setIdPosition pos idPack) [e])])
            t' <- expandFullType v'
            return (res', t', [])
        -- force unsigned display of UInt
        _ | isUInt t ->
          do
            v' <- newTVar "checkDisplayParam pack UInt" KStar e
            res' <- tiExpr as v' (CApply (CVar (idUnsigned pos))
                                       [(cVApply (setIdPosition pos idPack) [e])])
            t' <- expandFullType v'
            return (res', t', [])
        -- bind an ActionValue and display the result
        _ | av_ok && isActionValue t ->
          do
            -- traceM("ActionValue: " ++ ppReadable (t,e) )
            freshId <- newVar (getPosition e) "checkDisplayParam"
            let boundtype = getAVType t
            -- traceM("Bound type: " ++ ppReadable boundtype)
            let cqtype = CQType [] boundtype -- XXX what if there are provisos?
            -- traceM("CQType: " ++ ppReadable cqtype)
            let scheme = toScheme boundtype
            -- traceM("Scheme: " ++ ppReadable scheme)
            let stmt = CSBindT (CPVar freshId) Nothing [] cqtype e
            -- traceM("stmt: " ++ ppReadable stmt)
            (res', t', stmts) <- checkDisplayParam av_ok fmt_ok [freshId :>: scheme] (CVar freshId)
            -- the original expression will be rechecked as part of typechecking the resulting action block
            return (res', t', stmt:stmts)
        _ -> -- fall through and look at provisos
           do
             ps' <- apSubTI ps
             let ptvars = tv ps'
             case t of
               -- the original tvar has been constrained by a proviso
               TVar tvar | tvar `elem` ptvars -> do
                 -- traceM ("proviso variable: " ++ (ppReadable t))
                 bits <- bitCls
                 literal <- literalCls
                 realLiteral <- realLiteralCls
                 sizedLiteral <- sizedLiteralCls
                 stringLiteral <- stringLiteralCls
                 -- duplicate provisos are possible, so remove them
                 let preds = nub [ pred | (VPred _ pp) <-  ps',
                                          let pred = removePredPositions pp,
                                          tvar `elem` (tv pred)]
                 -- traceM("proviso predicates: " ++ (ppReadable preds))
                 let bitsprovisos = [tnum | (IsIn c [tbind, tnum]) <- preds,
                                            c == bits, tbind == t]
                 let literalprovisos = [p | p@(IsIn c [tbind]) <- preds,
                                            c == literal, tbind == t]
                 let rlprovisos = [p | p@(IsIn c [tbind]) <- preds,
                                       c == realLiteral, tbind == t]
                 let szprovisos = [tnum | (IsIn c [tbind, tnum]) <- preds,
                                          c == sizedLiteral, tbind == t]
                 let strprovisos = [p | p@(IsIn c [tbind]) <- preds,
                                        c == stringLiteral, tbind == t]
                 if (not . null) bitsprovisos then do
                     -- traceM("bits provisos: " ++ (ppReadable bitsprovisos))
                     -- XXX can we just let defaulting handle this?
                     let bit_t = TAp tBit (headOrErr "checkDisplayParam: bitsprovisos" bitsprovisos)
                     -- consider the value as unsigned
                     res' <- tiExpr as bit_t e
                     return (res', bit_t, [])
                  else if ((not . null) literalprovisos) then do
                     -- traceM("literal provisos: " ++ (ppReadable literalprovisos))
                     _ <- unify e bit32 t
                     -- consider the value signed
                     -- also: insert the fromInteger here, even though there
                     -- is one around the literals, because there may also be
                     -- operators and we want to force the conversion to bit32
                     -- at the last possible minute, in case the ops are only
                     -- defined for Integer (e.g. "2 ** -1")
                     res' <- tiExpr as bit32 (CApply (CVar (idSigned pos))
                                                     [cVApply (idFromInteger pos) [e]])
                     return (res', bit32, [])
                  else if ((not . null) rlprovisos) then do
                     -- traceM("real literal provisos: " ++ (ppReadable rlprovisos))
                     _ <- unify e tReal t
                     -- fromReal is not needed because the value is already Real
                     res' <- tiExpr as tReal e
                     return (res', tReal, [])
                  else if ((not . null) szprovisos) then do
                     -- traceM("sized literal provisos: " ++ ppReadable szprovisos)
                     -- XXX can we just let defaulting handle this?
                     let bit_t = TAp tBit (headOrErr "checkDisplayParam: szprovisos" szprovisos)
                     _ <- unify e bit_t t
                     -- fromSizedLiteral is not needed because the value is already Bit
                     res' <- tiExpr as bit_t e
                     return (res', bit_t, [])
                  else if ((not . null) strprovisos) then do
                     -- XXX let defaulting handle it?
                     _ <- unify e tString t
                     res' <- tiExpr as tString e
                     return (res', tString, [])
                  else do -- traceM("default to pack")
                          packResult as e
               -- default is to explicitly pack the result
               _ ->
                   do
                     packResult as e

checkAssertParam :: [Assump] -> CExpr -> TI (([VPred], CExpr), Type, CStmts)
checkAssertParam as e =
    do
      v <- newTVar "checkAssertParam start" KStar e
      res@(ps, e') <- tiExpr as v e
      t <- expandFullType v
      let pos = getPosition e

      case t of
        _ | isString t -> return (res, t, [])
        _ | isChar t ->
          do
            res' <- tiExpr as tString (cVApply (idPrimCharToString pos) [e])
            return (res', tString, [])
        _ | isBool t || isUInt t ->
          do
            v' <- newTVar "checkAssertParam pack" KStar e
            res' <- tiExpr as v' (cVApply (setIdPosition pos idPack) [e])
            t' <- expandFullType v'
            return (res', t', [])
        _ -> -- fall through and look at provisos
           do
             ps' <- apSubTI ps
             let ptvars = tv ps'
             case t of
               -- the original tvar has been constrained by a proviso
               TVar tvar | tvar `elem` ptvars -> do
                 -- traceM ("proviso variable: " ++ (ppReadable t))
                 do
                   -- duplicate provisos are possible, so remove them
                   let preds = nub [ pred | (VPred _ pp) <-  ps',
                                            let pred = removePredPositions pp,
                                            tvar `elem` (tv pred)]
                   -- traceM("proviso predicates: " ++ (ppReadable preds))
                   literal <- literalCls
                   stringLiteral <- stringLiteralCls
                   let literalprovisos = [p | p@(IsIn c [tbind]) <- preds,
                                              c == literal, tbind == t]
                   let stringprovisos = [p | p@(IsIn c [tbind]) <- preds,
                                             c == stringLiteral, tbind == t]
                   (if ((not . null) literalprovisos) then
                     do
                       -- traceM("literal provisos: " ++ (ppReadable literalprovisos))
                         _ <- unify e tInteger t
                         res' <- tiExpr as tInteger e
                            -- res' <- tiExpr as bit32 e
                         return (res', tInteger, [])
                    else if ((not . null) stringprovisos) then do
                       _ <- unify e tString t
                       res' <- tiExpr as tString e
                       return (res', tString, [])
                    else do internalError ("TCheck.SVAParam: " ++ show e))
               _ ->
                   do internalError ("TCheck.SVAParam: " ++ show t)

-- CStmts are null
-- the incantation to pack the result is repeated
packResult :: [Assump] -> CExpr -> TI (([VPred], CExpr), Type, CStmts)
packResult as e =
    do
      v' <- newTVar "checkDisplayParam packResult pack" KStar e
      let e' = (cVApply (setIdPosition (getPosition e) idPack) [e])
      res' <- tiExpr as v' e'
      t' <- expandFullType v'
      return (res', t', [])


-- Check a display task were the first argument must be of type File
taskCheckFDisplay :: [Assump] -> Type -> CExpr -> [CExpr] -> TI ([VPred],CExpr)
taskCheckFDisplay as td f []  = err (getPosition f, (EMissingFileArgument (ppReadable f) "File" "first" ))
taskCheckFDisplay as td f (file:es)  =
      do
        -- the first argument must be a file,  handle all rest in the same way
        _ <- tiExpr as tFile file
        --
        taskCheckDisplay as td f (file:es)

taskCheckDisplay :: [Assump] -> Type -> CExpr -> [CExpr] -> TI ([VPred],CExpr)
taskCheckDisplay as td f es =
      do
        _ <- unify f tAction td -- check type so fromPrimAction will succeed
                           -- f is used for its position only
        paramResults <- mapM (checkDisplayParam True True as) es
        finishDisplay as td f es paramResults

taskCheckAssert :: [Assump] -> Type -> CExpr -> [CExpr] -> TI ([VPred],CExpr)
taskCheckAssert as td f es =
      do
        _ <- unify f tAction td -- check type so fromPrimAction will succeed
                                -- f is used for its position only
        paramResults <- mapM (checkAssertParam as) es
        -- OK to use finishDisplay here:
        finishDisplay as td f es paramResults

-- Check a display task where the first argument must be an interface
-- with a write method.
taskCheckSWrite :: [Assump] -> Type -> CExpr -> [CExpr] -> TI ([VPred],CExpr)
taskCheckSWrite as td f es =
      do
        expr <- createAVExpr as td f es
        tiExpr as td expr

-- Convert a call to a standard swrite, etc into a call to the AV version
-- and an invocation of the write method on the supplied interface.
createAVExpr :: [Assump] -> Type -> CExpr -> [CExpr] -> TI CExpr
createAVExpr _  _  f []        = err (getPosition f, (EMissingFileArgument (ppReadable f) "interface" "first"))
createAVExpr as td f@(CVar task) (dest:es) =
      do
        let pos = (getPosition f)
        let id_av = toAVId(task)
        v <- newTVar "createAVExpr" KStar f
        _ <- tiExpr as v dest
        s' <- getSubst
        let ifc = (apSub s' v)
        let (con, args) = splitTAp ifc
        con_id <- case (leftCon con) of
                     Nothing -> err (pos, (EMissingFileArgument (ppReadable f) "interface" "first" ))
                     Just x  -> return x
        sy <- getSymTab
        info <- case (findFieldInfo sy con_id (id_write pos)) of
                     Nothing -> err (pos, (EMissingFileArgument (ppReadable f) "interface (with an _write method)" "first" ))
                     Just x  -> return x
        let (_ :>: (Forall _ qt)) = fi_assump info
        let (_ :=> tt) = inst args qt
        let rest = case getArrows tt of
                     ((_:r), _) -> r
                     _ -> internalError "TCheck.createAVExpr: getArrows"
        t <- case (rest) of
                [x] -> return x
                _   -> err (pos, (EMissingFileArgument (ppReadable f) "interface (with an _write method)" "first" ))
        id_new <- createIdNew dest pos
        let expr = (Caction pos [(CSBindT (CPVar id_new) Nothing []
                                  (CQType [] t)
                                  (CTaskApply (CVar id_av) es)),
                                 (CSExpr Nothing (Cwrite pos dest (CVar id_new)))])
        return expr
createAVExpr _ _ _ _ = internalError "TCheck.createAVExpr"

createIdNew :: CExpr -> Position -> TI Id
createIdNew dest pos =
    do
      let mkNewId id = setIdBase id (concatFString [getIdBase id, (mkFString "_AV")])
      id_new <- case (dest) of
                  (CApply (CVar f) [CVar id]) | ((getIdBase f) == (getIdBase idAsIfc))
                                                  -> return (mkNewId id)
                  (CApply (CVar f) [CVar id]) | ((getIdBase f) == (getIdBase idAsReg))
                                                  -> return (mkNewId id)
                  (CVar id) -> return (mkNewId id)
                  _         -> newVar pos "createIdNew"
      return id_new

taskCheckSWriteAV :: [Assump] -> Type -> CExpr -> [CExpr] -> TI ([VPred],CExpr)
taskCheckSWriteAV as td f es =
      do
        v <- newTVar "taskCheckSWriteAV" KNum f
        let pos = (getPosition f)
        let tav = TAp (tActionValueAt pos) (TAp tBit v)
        eq_ps <- unify f tav td

        paramResults <- mapM (checkDisplayParam True True as) es
        finishSWriteAV as td v f es paramResults eq_ps


finishDisplay :: [Assump] -> Type -> CExpr -> [CExpr] -> [(([VPred], CExpr), Type, CStmts)] -> TI ([VPred],CExpr)
finishDisplay as td f es paramResults =
     do
        s' <- getSubst

        -- want to squash all known type variables
        let paramResults' = (apSub s' paramResults)
        let (pses, tys, stmtss) = unzip3 paramResults'
        let stmts = concat stmtss

        -- pss are the provisos, es' are the transformed expressions
        let (pss, es') = unzip pses

        let taskty = foldr fn tPrimAction tys

        -- XXX: quantifying in IConv instead so free type vars are caught correctly
        -- duplicate provisos are possible so remove them
        -- let cpreds = ((map predToCPred) .  nub) [ pred | (VPred _ pred) <-  (concat pss), (not . null) ((tv taskty) `intersect` (tv pred))]
        -- let taskcqt = (CQType [] taskty)
        --traceM (ppReadable taskcqt)
        --traceM (ppReadable (tv taskcqt))

        -- XXX: using (tv taskcqt) would assume all type vars found are free in taskcqt
        -- but free in taskcqt does not imply free altogether (may be constrained externally)
        --                    [(CTaskApplyT (CVar task) taskcqt (map TVar (tv taskcqt)) es')])

        -- insert fromPrimAction so $display & friends have type Action
        let action_exp = (cVApply (setIdPosition (getPosition f) idFromPrimAction)
                                  [(CTaskApplyT f taskty es')])
        --let action_exp = (CTaskApplyT f taskty es')

        let exp' = if (null stmts) then
                      action_exp
                   else
                      (Caction (getPosition f) (stmts ++ [CSExpr Nothing action_exp]))


        (ps', exp'') <- tiExpr as td exp'
        -- traceM("finishDisplay done")
        -- duplicate provisos are possible so squash them
        return (concat (ps':pss), exp'')

finishSWriteAV :: [Assump] -> Type -> Type -> CExpr -> [CExpr] -> [(([VPred], CExpr), Type, CStmts)] -> [VPred] -> TI ([VPred],CExpr)
finishSWriteAV as td v f es paramResults eq_ps =
     do
        s' <- getSubst

        -- want to squash all known type variables
        let paramResults' = (apSub s' paramResults)
        let (pses, tys, stmtss) = unzip3 paramResults'
        let stmts = concat stmtss

        -- pss are the provisos, es' are the transformed expressions
        let (pss, es') = unzip pses

--        v <- newTVar "XXX" KNum f
        let tav = TAp tActionValue_ v
        let taskty = foldr fn tav tys

        -- XXX: quantifying in IConv instead so free type vars are caught correctly
        -- duplicate provisos are possible so remove them
        -- let cpreds = ((map predToCPred) .  nub) [ pred | (VPred _ pred) <-  (concat pss), (not . null) ((tv taskty) `intersect` (tv pred))]
        -- let taskcqt = (CQType [] taskty)
        --traceM (ppReadable taskcqt)
        --traceM (ppReadable (tv taskcqt))

        -- XXX: using (tv taskcqt) would assume all type vars found are free in taskcqt
        -- but free in taskcqt does not imply free altogether (may be constrained externally)
        --                    [(CTaskApplyT (CVar task) taskcqt (map TVar (tv taskcqt)) es')])

        -- insert fromActionValue_ so $swtriteAV & friends have type ActionValue
        let av_exp = (cVApply (setIdPosition (getPosition f) idFromActionValue_)
                                  [(CTaskApplyT f taskty es')])
        --let action_exp = (CTaskApplyT f taskty es')

        let exp' = if (null stmts) then
                  av_exp
                  else
--                (Caction (getPosition f) (stmts ++ [CSExpr Nothing av_exp]))
                  (Cdo False (stmts ++ [CSExpr Nothing av_exp]))

        (ps', exp'') <- tiExpr as td exp'

        -- duplicate provisos are possible so squash them
        return (concat (eq_ps:ps':pss), exp'')


-- $fflush can be either fflush :: PrimAction or fflush :: File -> PrimAction
taskCheckFFlush :: TaskCheckT
taskCheckFFlush as td f [] =
    do
      let fty = tPrimAction
          applied = (CTaskApplyT f  fty   [])
      let t = cVApply (setIdPosition (getPosition f) idFromPrimAction) [applied]
      --
      tiExpr as td t
taskCheckFFlush as td f [file] =
    do
      -- first arg must be file type
      _ <- tiExpr as tFile file
      ((vp,packedfile),tx,cm) <- packResult as file
      --
      let fty = tx `fn` tPrimAction
          applied = (CTaskApplyT f  fty   [packedfile])
      let t = cVApply (setIdPosition (getPosition f) idFromPrimAction) [applied]
      --
      (pred,exp) <- tiExpr as td t
      return (pred++vp, exp)
taskCheckFFlush as td f args = err (getPosition f, (EMissingFileArgument (ppReadable f) "File" "only" ))


-- Builds fromActionValue_ ( $fopen ( string {,string} ))
taskCheckFOpen :: TaskCheckT
taskCheckFOpen as td f [filen] =
    do
      (vp,filentc) <- tiExpr as tString filen
      --
      let avfile = (TAp (tActionValueAt (getPosition f)) tFile)
          tav32 = TAp (tActionValue_At (getPosition f))  t32
          fty = tString `fn` tav32
          applied = (CTaskApplyT f  fty    [filentc])
      let t = cVApply (setIdPosition (getPosition f) idFromActionValue_) [applied]
      --
      unifyNoEq "taskCheckFOpen"  f td avfile
      (preds,exp) <- tiExpr as td t
      return (preds++vp,exp)

taskCheckFOpen as td f [filen,mode] =
    do
      (vp1,filentc) <- tiExpr as tString filen
      (vp2,modetc)  <- tiExpr as tString mode
      --
      --
      let avfile = (TAp (tActionValueAt (getPosition f)) tFile)
          tav32 = TAp (tActionValue_At (getPosition f))  t32
          fty = tString `fn` tString `fn` tav32
          applied = (CTaskApplyT f  fty    [filentc,modetc])
      let t = cVApply (setIdPosition (getPosition f) idFromActionValue_) [applied]
      --
      unifyNoEq "taskCheckFOpen" f td avfile
      (preds,exp) <- tiExpr as td t
      return (preds++vp1++vp2,exp)


taskCheckFOpen as td f _ = err (getPosition f, (EMissingFileArgument (ppReadable f) "String" "first (two)" ))

taskCheckFormat :: [Assump] -> Type -> CExpr -> [CExpr] -> TI ([VPred],CExpr)
taskCheckFormat as td f es =
    do unifyNoEq "taskCheckFormat"  f tFmt td
       paramResults <- mapM (checkDisplayParam False True as) es
       finishFormat as td f es paramResults

finishFormat :: [Assump] -> Type -> CExpr -> a
             -> [(([VPred], CExpr), Type, CStmts)] -> TI ([VPred], CExpr)
finishFormat as td f es paramResults =
     do
        s' <- getSubst

        -- want to squash all known type variables
        let paramResults' = (apSub s' paramResults)
        -- it's OK to ignore the stmts here, because those only result from
        -- binding ActionValue arguments, which we disallowed
        let (pses, tys, _) = unzip3 paramResults'

        -- pss are the provisos, es' are the transformed expressions
        let (pss, es') = unzip pses

        let taskty = foldr fn tFmt tys

        let expr = CTaskApplyT f taskty es'

        (ps', exp'') <- tiExpr as td expr
        return (concat (ps':pss), exp'')

taskCheckMap :: [(Id, TaskCheckT)]
taskCheckMap = [(idTime,      taskCheckNormal),
                (idSTime,     taskCheckNormal),
                (idDumpon,    taskCheckNormal),
                (idDumpoff,   taskCheckNormal),
                (idDumpall,   taskCheckNormal),
                (idDumpvars,  taskCheckNormal),
                (idDumpfile,  taskCheckNormal),
                (idDumpflush, taskCheckNormal),
                (idDumplimit, taskCheckNormal),
                --
                (idDisplay,   taskCheckDisplay),
                (idDisplayo,  taskCheckDisplay),
                (idDisplayb,  taskCheckDisplay),
                (idDisplayh,  taskCheckDisplay),
                (idWrite,     taskCheckDisplay),
                (idWriteo,    taskCheckDisplay),
                (idWriteb,    taskCheckDisplay),
                (idWriteh,    taskCheckDisplay),
                --
                (idErrorTask, taskCheckDisplay),
                (idWarnTask,  taskCheckDisplay),
                (idInfoTask,  taskCheckDisplay),
                (idFatalTask, taskCheckFatal),
                --
                (idSVA,       taskCheckAssert),

                (idSVAsampled, taskCheckNormal),
                (idSVArose, taskCheckNormal),
                (idSVAfell, taskCheckNormal),
                (idSVAstable, taskCheckNormal),
                (idSVApast, taskCheckNormal),
                (idSVAonehot, taskCheckNormal),
                (idSVAonehot0, taskCheckNormal),
                (idSVAisunknown, taskCheckNormal),
                (idSVAcountones, taskCheckNormal),
                --
                (idRandom,    taskCheckRandom),
                --
                (idFDisplay,  taskCheckFDisplay),
                (idFDisplayo, taskCheckFDisplay),
                (idFDisplayb, taskCheckFDisplay),
                (idFDisplayh, taskCheckFDisplay),
                (idFWrite,    taskCheckFDisplay),
                (idFWriteo,   taskCheckFDisplay),
                (idFWriteb,   taskCheckFDisplay),
                (idFWriteh,   taskCheckFDisplay),
                (idSWriteAV,  taskCheckSWriteAV),
                (idSWrite,    taskCheckSWrite),
                (idSWritebAV, taskCheckSWriteAV),
                (idSWriteb,   taskCheckSWrite),
                (idSWriteoAV, taskCheckSWriteAV),
                (idSWriteo,   taskCheckSWrite),
                (idSWritehAV, taskCheckSWriteAV),
                (idSWriteh,   taskCheckSWrite),
                (idSFormatAV, taskCheckSWriteAV),
                (idSFormat,   taskCheckSWrite),
                --
                (idFormat  , taskCheckFormat),
                --
                (idFinish,    taskCheckFinish),
                (idStop,      taskCheckFinish),
                --
                (idFOpen,     taskCheckFOpen),
                (idFFlush,    taskCheckFFlush),
                --
                (idFGetc,     taskCheckNormal),
                (idUngetc,    taskCheckNormal),
                (idFClose,    taskCheckNormal),
                (idTestPlusargs, taskCheckNormal),
                --
                (idRealToBits, taskCheckNormal),
                (idBitsToReal, taskCheckNormal)]

tiApply :: [Assump] -> Type -> a -> CExpr -> CExpr -> TI ([VPred], CExpr)
tiApply as td exp f e = do
    -- give the tyvar the position of the argument?
    -- if the variable pos becomes the position of a pred, this could
    -- result in multiple positions (each argument) for one func call
    --te       <- newTVar "tiExpr CApply" KStar f
    te       <- newTVar "tiExpr CApply" KStar e
    (ps, f') <- tiExpr as (te `fn` td) f
    (qs, e') <- tiExpr as te e

    let ret_ps = ps ++ qs
    ret_ps' <- updateContexts (getPosition f) ret_ps

    --trace ("CApply " ++ ppReadable (exp,te,td)) $ return ()
    return ( ret_ps', cApply 3 f' [e'] )

-- apply register read method to a variable, if the type allows
-- The first argument is whether there is a surrounding selection already
-- being applied.  Do not apply the read selection if any method of the
-- interface is already being applied (a read, a write, or other method).
-- This avoids infinitely applying the read method and it allows users to
-- write to the reg and to apply other methods on Reg-like interfaces.
tiVar :: ImplReadTag -> [Assump] -> Type -> CExpr -> TI ([VPred], CExpr)
tiVar readTag as td exp@(CVar i) = do
    (i' :>: sc) <- findAssump i as

{-
    traceM ("tiVar " ++ pvpReadable i ++ " assumption (vart) " ++
            pvpReadable (apSub s vart) ++ " expects (td) " ++
            pvpReadable (apSub s td))
    traceM ("tiVar isReadType i = " ++
            pvpReadable (isReadType r (apSub s vart)))
    traceM ("tiVar isReadType td = " ++
            pvpReadable (isReadType r (apSub s td)))
-}

    -- prepare the base expression: typecheck the variable
    let base_expr = do
            (ps :=> t, ts) <- freshInstT "E" i sc td
            ps' <- concatMapM (mkVPred (getPosition exp)) ps
            when doRTrace2 $ traceM ("CVar " ++ ppReadable (i,sc,iAPs (CVar i) ts ps'))
            return (t,
                    ps',
                    iAPs (CVar (setIdPosition (getIdPosition i) i')) ts ps')

    let readTag' = if (isRenamingId i) then NoRead else readTag
    tryReadDesugar base_expr readTag' as td exp

{-
    -- Do automagic deref if the variable is a register type and the
    -- context is not a register type, and the variable is not a
    -- renamed identifier (introduced by the BSV parser)
    case (mfield, isReadType r (apSub s vart), isReadType r (apSub s td)) of
      (Just msel, Just ti, Nothing) | not (isRenamingId i) ->
        -- Do automagic deref (except for renamed identifiers)
        let -- the _read should have the same qualifier as the ifc type
            unqual_id_read = id_read (getPosition i)
            qual_id_read = setIdQual unqual_id_read (getIdQual ti)
            -- the result of typechecking i._read
            res = tiExpr as td (CSelectTT ti exp qual_id_read)
        in
            -- don't add _read if a method is being called on the reg ifc
            case (msel, getIfcFields ti r) of
                (Just method, Just fs) ->
                    -- do an unqualified comparison, because the qualifier
                    -- has probably been added by the surrounding typecheck
                    let unqual_fs = map unQualId fs
                    in  if (unQualId method `elem` unqual_fs)
                        then def_res  -- don't insert _read
                        else res      -- insert _read
                _ -> res  -- no surrounding method call, so insert _read
      _ -> def_res
-}

tiVar _ _ _ _ = internalError "TCheck.tiVar"

-- tiVar_NoImplRead = tiVar NoRead

-- tiVar_WithImplRead sel = tiVar (ImplRead sel)

noDesugar :: Type -> TI (Type, [VPred], CExpr)
          -> CExpr -> TI ([VPred], CExpr)
noDesugar td base_expr orig_expr = do
  (t, ps, e) <- base_expr
  eq_ps <- unify orig_expr t td
  s <- getSubst
  return (eq_ps ++ apSub s ps, apSub s e)

tryReadDesugar :: TI (Type, [VPred], CExpr) -> ImplReadTag -> CheckT CExpr
tryReadDesugar base_expr NoRead _ td orig_expr = noDesugar td base_expr orig_expr
tryReadDesugar base_expr (ImplRead msel) as td orig_expr = do
   (t, ps, e) <- base_expr
   let def_res = noDesugar td base_expr orig_expr

   r <- getSymTab
   s <- getSubst

   case (isReadType r (apSub s t), isReadType r (apSub s td)) of
     (Just ti, Nothing) -> do
       let unqual_id_read = id_read (getPosition e)
       -- qualify by the package of the type constructor
       -- so that the desugaring works even if the _read field is not in scope
       let qual_id_read   = setIdQual unqual_id_read (getIdQual ti)
       let read_res = tiExpr as td (CSelectTT ti orig_expr qual_id_read)
       case (msel, getIfcFields ti r) of
         -- compare unqualified because we just care that there is
         -- a matching field - scope is taken care of elsewhere
         -- by the read or write desugaring or normal typechecking
         (Just sel, Just fs) | (unQualId sel) `elem` (map unQualId fs) -> def_res
         _ -> read_res
     _ -> def_res

tiSub :: ImplReadTag -> [Assump] -> Type -> Position -> CExpr -> CExpr
      -> TI ([VPred], CExpr)
tiSub readTag as td pos e1 e2 = tryReadDesugar (tiWithType as exp) readTag as td exp
  where exp = (cVApply (idPrimSelectFn pos) [posLiteral pos, e1, e2])

-----------------------------------------------------------------------------

type TiStmts = Type -> Maybe Type -> [Assump] -> Type -> [CStmt] -> TI ([VPred], CExpr)

-- Transform recursive statements as follows:
-- Let x1,...,xk be the identifiers in forward reference
-- s1; ... sn; e
--   -->
-- n <- mfix (\ t -> let (r,x1,...,xk) = t in do s1; ...; sn; r <- e; return (r, x1, ... xk))
-- return r

recStmts :: [CStmt] -> TI [CStmt]
recStmts = return
{-
recStmts ss = do
    let vs = S.fromList (concatMap getStmtBind ss)
        rchk s r@(rvs, vs) =
            case s of
            CSBindT p _ e -> (rvs `S.union` (snd (getFVE e) `S.intersection` vs), S.difference vs (getPV p))
            CSBind  p   e -> (rvs `S.union` (snd (getFVE e) `S.intersection` vs), S.difference vs (getPV p))
            CSletrec      ds -> let vs' = set_deleteMany (concatMap getLDefs ds) vs
                             in  (rvs `S.union` ((S.unions (map (snd . getFVDl) ds) `S.intersection` vs')), vs')
            _             -> r
        (rvs, _) = foldr rchk (S.empty, vs) (reverse ss)
        ls = S.toList rvs
    -- XXX check dupl
    if null ls then
        return ss
     else do
        let re = case last ss of
                 CSExpr x -> x
                 other -> internalError $ "[BUG #23] recStmts: at " ++ ppString (getPosition other) ++ ":\n" ++ ppReadable other
            pos = getPosition re
        r <- newVar pos
        tid <- newVar pos
        nid <- newVar pos
        let ids = r : ls
            ss' = init ss ++ [CSBind (CPVar r) re, CSExpr (cVApply (idReturn pos) [mkTuple pos (map CVar ids)])]
            ptup = pMkTuple pos (map CPVar ids)
            lame = CLam tid (Cletrec [CLMatch ptup (CVar tid)] (Cdo False ss'))
            rss = [CSBind (CPVar nid) (cVApply idMfix [lame]), CSExpr (cVApply (idReturn pos) [CSelect (CVar nid) idPrimFst])]
--        trace (ppReadable (S.toList vs, ls)) $ return ()
--        trace (ppReadable rss) $ return ()
        return rss
-}

tiStmts :: TiStmts
--tiStmts mon mt as td ss = trace (concatMap (("\nDEBUG: " ++) . show) ss) $ tiStmts' chke mon mt as td ss
tiStmts mon mt as td ss = tiStmts' chke mon mt as td ss
  where chke mon mt as td (CSExpr name e : ss) = do
                v <- newTVar "tiStmts" KStar e
                tiStmtsExpr chke mon mt as td (TAp mon v) name e ss
        chke _ _ _ _ _ = internalError "TCheck.tiStmts chke"

addStateName :: Maybe CExpr -> CExpr -> CExpr
addStateName Nothing e = e
addStateName (Just nameExpr) e =
    let pos = getPosition nameExpr
    in  CApply (CVar (idSetStateNameAt pos)) [nameExpr, e]

tiStmts' :: TiStmts -> TiStmts
tiStmts' chke mon _ as td [CSExpr name e] =
        -- XXX can "name" ever be non-Nothing here?
        tiExpr as td (addStateName name e)
tiStmts' chke mon _ as td [s] = err (getPosition s, ENotExpr)
tiStmts' chke mon mt@(Just te) as td (CSExpr name e : ss) =
        tiStmtsExpr chke mon mt as td te name e ss
tiStmts' chke mon mt as td ss@(CSExpr _ _ : _) = chke mon mt as td ss
tiStmts' chke mon _ as td (e@(CSBindT _ _ _ (ty@(CQType (_:_) _)) _) : _) =
        -- XXX this used to report the position of "ty"
        -- XXX is that ever the right thing to do?
        err (getPosition e, EStmtContext (pfpString ty))
tiStmts' chke mon mt as td (CSBindT (CPVar i) maybeName pprops (CQType [] ty) e : ss) = do
        bs <- getBoundTVs
        -- Of the type variables in the explicit declaration, separate the
        -- free type variables (fvs) from those bound by the context (bvs)
        let (bvs, fvs) = partition (\x -> elem x bs) (tv ty)
        -- Check that the variables bound in this declaration (bvs)
        -- have the same kind as where they were bound
        let kindCheckBV v =
              case (find (== v) bs) of
                Nothing -> internalError ("tiStmts': find should not fail")
                Just u -> if (kind u == kind v)
                          then return ()
                          else errBoundTyVarKindMismatch i v u
        mapM_ kindCheckBV bvs
        -- check that there are no free vars in ty
        unless (null fvs) $
            let v = case fvs of
                      (TyVar v _ _ : _) -> v
                      _ -> internalError "TCheck.tiStmts' CSBindT CPVar: fvs"
            in  err (getPosition v,  EUnboundTyVar (pfpString v))
        tiStmtBind chke mon mt as td i maybeName pprops e ss ty
tiStmts' chke mon mt as td (CSBindT p name pprops qt e : ss) = do
        nid <- newVar (getPosition p) "tiStmts1"
        tiStmts' chke mon mt as td (CSBindT (CPVar nid) name pprops qt e : CSletrec [CLMatch p (CVar nid)] : ss)
tiStmts' chke mon mt as td (CSBind (CPVar i) maybeName pprops e : ss) = do
        ty <- newTVar "tiStmts' CSBind" KStar e                -- XXX
        tiStmtBind chke mon mt as td i maybeName pprops e ss ty
tiStmts' chke mon mt as td (CSBind p name pprops e : ss) = do
        nid <- newVar (getPosition p) "tiStmts2"
        tiStmts' chke mon mt as td (CSBind (CPVar nid) name pprops e : CSletrec [CLMatch p (CVar nid)] : ss)
tiStmts' chke mon mt as td (CSletrec ds : ss) = do
        (ps, as', ds') <- tiDefls as ds
        (qs, ss')      <- tiStmts' chke mon mt (as' ++ as) td ss
        return (ps ++ qs, Cletrec ds' ss')
tiStmts' chke mon mt type_env expected_type (CSletseq defs : rest_stmts) = do
        defs_without_patterns <- mapM expCLMatch defs >>= return . concat
        (provisos_from_defs, type_env_from_defs, rewritten_defs)
            <- tiSeq tiLetseqDef type_env defs_without_patterns
        (provisos_from_stmts, rewritten_stmts)
            <- tiStmts' chke mon mt (type_env_from_defs ++ type_env)
                        expected_type rest_stmts
        return (provisos_from_defs ++ provisos_from_stmts,
                Cletseq rewritten_defs rewritten_stmts)
tiStmts' _ _ _ _ _ stmt = internalError ("TCheck.tiStmts': " ++ show stmt)

tiStmtsExpr :: TiStmts -> Type -> Maybe Type -> [Assump] -> Type -> Type ->
               Maybe CExpr -> CExpr -> [CStmt] -> TI ([VPred], CExpr)
tiStmtsExpr chke mon mt as td te name e ss = do
        (ps, e') <- tiExpr as te (addStateName name e)
        (qs, ss') <- tiStmts' chke mon mt as td ss
        (rs, f) <- tiVar NoRead as (te `fn` td `fn` td) (CVar (idBind_ (getPosition e)))
        return (ps ++ qs ++ rs, cApply 4 f [e', ss'])

tiStmtBind :: TiStmts -> Type -> Maybe Type -> [Assump] -> Type -> Id -> Maybe CExpr -> [(Position, PProp)] -> CExpr -> [CStmt] -> Type -> TI ([VPred], CExpr)
tiStmtBind chke mon mt as td i maybeName pprops e ss ty = do
        -- traceM ("mon: " ++ ppReadable mon)
        let te = TAp mon ty
            as' = (i :>: toScheme ty) : as
        -- inject state-naming primitive (if name is available)
        -- i.e. we are on a module monad
        let e0 = case pprops of
                   [] -> e
                   pps -> let -- take the first good position
                              pos = getPosition (map fst pprops)
                              ppropExpr = Cattributes pprops
                          in  cApply 19 (CVar (idSetStateAttribAt pos)) [ppropExpr, e]
        let e1 = case maybeName of
                   Nothing       -> e0
                   Just nameExpr ->  let pos = getPosition nameExpr
                                         hide = hasHide pprops
                                         hideAll = hasHideAll pprops
                                         nameExpr'  = if (hide || hideAll) then (applyToCExprIds setHideId nameExpr) else nameExpr
                                         nameExpr'' = if (hideAll) then (applyToCExprIds setHideAllId nameExpr') else nameExpr'
                                     in (cApply 18 (CVar (idSetStateNameAt pos)) [nameExpr'', e0])
        (ps, e') <- tiExpr as te e1
        (qs, ss') <- tiStmts' chke mon mt as' td ss
        let tl = ty `fn` td
        -- traceM ("tl: " ++ ppReadable tl)
        (rs, f) <- tiVar NoRead as (te `fn` tl `fn` td) (CVar (idBind (getPosition e)))
        --posCheck "E" i
        il <- newVar (getPosition i) "tiStmtBind1"
        -- traceM ("tl': " ++ ppReadable tl')
        let ee = Cletseq [CLValueSign (CDefT il [] (CQType [] tl) [CClause [CPVar i] [] ss']) []] (CVar il)
        return (ps ++ qs ++ rs, cApply 6 f [e', ee])

hasHide :: [(Position, PProp)] -> Bool
hasHide ((_, PPinst_hide):_) = True
hasHide (_:rest)             = hasHide rest
hasHide []                   = False

hasHideAll :: [(Position, PProp)] -> Bool
hasHideAll ((_, PPinst_hide_all):_) = True
hasHideAll (_:rest)             = hasHideAll rest
hasHideAll []                   = False

-----------------------------------------------------------------------------

tiRule :: [Assump] -> CRule -> TI ([VPred], CRule)
tiRule as cr = tiRecoveringFromError (tiRule' as cr)
               (return ([], cr))

tiRule' :: [Assump] -> CRule -> TI ([VPred], CRule)
tiRule' as cr@(CRule rps mi quals0 e) = do
    --trace ("TC rule " ++ ppReadable mi) $ return ()
    (ps, mi') <- case mi of Nothing -> return ([], Nothing); Just i -> do (ps, e) <- tiExpr as tString i; return (ps, Just e)

    qualss <- mapM rmQualLit quals0
    let quals = concat qualss
    (qs, as', quals') <- tiQuals as [] [] quals
    (rs, e') <- tiExpr as' tPrimAction (cVApply (setIdPosition (getPosition e) idToPrimAction) [e])

    return (ps ++ qs ++ rs, CRule rps mi' quals' e')

tiRule' as cr@(CRuleNest rps mi quals0 rs) = do
    --trace ("TC rule nest " ++ ppReadable mi) $ return ()
    (ps, mi') <- case mi of Nothing -> return ([], Nothing); Just i -> do (ps, e) <- tiExpr as tString i; return (ps, Just e)

    qualss <- mapM rmQualLit quals0
    let quals = concat qualss
    (qs, as', quals') <- tiQuals as [] [] quals

    psrs <- mapM (tiRule as') rs
    let (pss, rs') = unzip psrs

    return (ps ++ qs ++ concat pss, CRuleNest rps mi' quals' rs')

-----------------------------------------------------------------------------

-- XXX use less tyvars
tiSelect :: ImplReadTag -> [Assump] -> Type -> CExpr -> Id -> (Type -> Type) -> TI ([VPred], CExpr)
tiSelect readTag as td e i f = do
    -- For tracing:
    -- let exp = CSelect e i

    te        <- newTVar "tiSelect" KStar i
    let tf    =  te `fn` td
    let recReadTag = ImplRead (Just i)
    (ps, e')  <- case e of
                   -- Typechecking on a desugarable expression
                   -- Avoid an infinite loop! by passing "i" to
                   -- in recReadTag so it can decide whether to add "_read"
                   -- to register objects.  If the current selection is
                   -- already "_read" then it should not be added again.
                   -- Similarly, don't add "_read" if we're trying to
                   -- call "_write" or any other method on the reg ifc.
                   CVar _ ->
                     tiVar recReadTag as te e
                   CSub pos e1 e2 -> tiSub recReadTag as te pos e1 e2
                   CSelect e_in i_in -> tiSelect recReadTag as te e_in i_in id
                   _ ->
                     tiExpr as te e

    --do s <- getSubst; trace ("sel1 " ++ ppReadable ((exp, apSub s td), (e, apSub s te), (i, apSub s tf))) $ return ()
    (i' :>: sc, ti, n)  <- findFields (f te) i
    (qs :=> t, ts)  <- freshInstT "F" i sc tf
    -- do s <- getSubst; trace ("sel2 " ++ ppReadable (exp, apSub s t, apSub s tf)) $ return ()
    case t of
      TAp (TAp (TCon arr) te0) td0 | isTConArrow arr -> do
           eq_ps <- unify e te te0
           qs'             <- concatMapM (mkVPred (getPosition e)) qs
           let (tts, fts)  = splitAt n ts
           let base_expr = return (td0, eq_ps++ps++qs', iAPs (CApply (cTApply (CSelectT ti i') tts) [e']) fts qs')
           tryReadDesugar base_expr readTag as td (CSelect e i)
      _ -> internalError ("tiSelect non-function field type: " ++ ppReadable (te, i, t))

-----------------------------------------------------------------------------

{-
tiField :: Id -> [Id] -> CheckT (Id, CExpr)
tiField si fs as rt (i, e) =
    if i `notElem` fs then
        err (getPosition i, ENotField (pfpString si) (pfpString i))
    else
        tiField1 as rt (i, e)
-}

tiField1 :: CheckT (Id, CExpr)
tiField1 as rt (f, e) = do
    -- traceM("tiField1 enter")
    (f' :>: sc, _, n) <- findFields rt f
    (qs :=> ft0, xts) <- freshInstT "G" f sc rt
    -- Fields might be defined using type constructors (like SizeOf),
    -- so replace them with vars and return the preds that determine the vars
    -- XXX disable expanding of type synonyms until failures with TLM
    -- XXX (type synonyms which drop parameters) is resolved
    -- XXX (tcon_ps, ft) <- expPrimTCons (expandSyn ft0)
    (tcon_ps, ft) <- expPrimTCons ft0
    -- Unify the field type and the context expected return type,
    -- possibly returning preds which express type equality
    (t,eq_ps) <- unifyFnTo f e ft rt
    s                <- getSubst
    --posCheck "F" f
    i'               <- newVar (getIdPosition f) "tiField1"
    -- trace ("tiField1 " ++ ppReadable (f, i')) $ return ()
    let fvs = let getTyVar (TVar v) = v
                  getTyVar _ = internalError "TCheck.tiField1: fvs"
              in  map getTyVar (drop n xts)
        ft' = case ft of
                TAp _ t -> t
                _ -> internalError "TCheck.tiField1: ft'"
        fsc = quantify fvs (apSub s (qs :=> ft'))
        -- if "e" is just a wrapper for a tiExpl anyway, call tiExpl on
        -- the wrapped def (see comments for tiExpr on Cinterface)
        (alts, me) =
            case (e) of
                Cletseq [CLValue i1 clauses quals] (CVar i2) | (i1 == i2)
                  -> (clauses, quals)
                _ -> ([CClause [] [] e], [])
        as' = (i' :>: fsc) : as
    -- trace ("tiField1: " ++ ppReadable (apSub s rt, i', e, fsc)) $ return ()
    (ps, d')         <- tiExpl' as' (i', fsc, alts, me)
    let e' = case d' of
                CLValueSign (CDefT _ [] _ [CClause [] [] e]) [] -> e
                _ -> Cletseq [d'] (CVar i')

    -- A struct construction should not take on the contexts of its fields
    -- if the context is already part of the type declaration for the struct.
    -- The context should only appear when the field value is used.  So,
    -- don't add "qs" to the contexts introduced by the field:
    --   qs'              <- mapM (mkVPred (getPosition f)) qs
    --   return (ps ++ qs', (f', e'))

    --traces ("tiField1 " ++ ppReadable ((i, ft), (e'), rt, fsc)) $ return ()
    return (tcon_ps ++ eq_ps ++ps, (f', e'))

-----------------------------------------------------------------------------

{-
tiClauses :: CheckT [CClause]
tiClauses as td alts@(cl@(CClause ps _ e) : ralts) = do
    ts <- mapM (\ p -> newTVar KStar p) ps
    t  <- newTVar KStar e
    unify cl (foldr fn t ts) td

    let np = length ps
    case [ c | c@(CClause ps _ _) <- ralts, length ps /= np ] of
        c : _ -> err (getPosition c, EWrongArity)
        [] -> return ()
    pstcs <- mapM (tiClause as ts t) alts
    let (pss, cs) = unzip pstcs
    return (concat pss, cs)

--tiClause :: CheckT CClause
tiClause as ts t cl@(CClause pats quals e) = do
    (ps, as', pats', quals') <- tiPatsQuals as ts pats quals
    (qs, e')           <- tiExpr as' t e
    return (ps++qs, CClause pats' quals' e')
-}

-- tiClauses should always be called with at least one clause
-- otherwise generate an error at the call site (because it has the position for the error message)
tiClauses :: CheckT [CClause]
tiClauses as td alts@(CClause ps _ _ : ralts) = do
--    trace (ppReadable (alts, td)) $ return ()
    let np = length ps
    case [ c | c@(CClause ps _ _) <- ralts, length ps /= np ] of
        c : _ -> err (getPosition c, EWrongArity)
        [] -> return ()
    pstcs <- mapM (tiClause as td) alts
    let (pss, cs) = unzip pstcs
    --trace ("tiClauses " ++ ppReadable (zip pss alts)) $return ()
    return (concat pss, cs)

tiClauses as td [] = internalError("tiClauses: no clauses\n")

-- XXX use less tyvars
tiClause :: CheckT CClause
tiClause as td cl@(CClause pats quals e) = do
    --trace ("tiClause: " ++ ppReadable (td, cl)) $ return ()
    ts                 <- mapM (\ p -> newTVar "tiClause ts" KStar p) pats
    t                  <- newTVar "tiClause t" KStar e
    --trace ("tiClause " ++ ppReadable (e, td, t)) $ return ()
    eq_ps <- unify cl (foldr fn t ts) td
    (ps, as', pats', quals') <- tiPatsQuals as ts pats quals
    --s <- getSubst; trace (ppReadable (td,foldr fn t ts,s)) $ return ()
    (qs, e')           <- tiExpr as' t e
    --trace ("tiClause " ++ ppReadable (e', td)) $ return ()
    --s <- getSubst; trace (ppReadable s) $ return ()
    return (eq_ps++ps++qs, CClause pats' quals' e')

tiPatsQuals :: [Assump] -> [Type] -> [CPat] -> [CQual] -> TI ([VPred], [Assump], [CPat], [CQual])
tiPatsQuals as ts pats0 quals0 = do
    pqs                <- mapM rmPatLit pats0
    let (pats, pqualss) = unzip pqs
    qualss             <- mapM rmQualLit quals0
    let quals = concat pqualss ++ concat qualss
    (ps, as', pats')   <- tiPats ts pats
    (qs, as'', quals') <- tiQuals (as' ++ as) [] [] quals
    return (ps++qs, as'', pats', quals')

tiQuals :: [Assump] -> [VPred] -> [CQual] -> [CQual] -> TI ([VPred], [Assump], [CQual])
tiQuals as ps r [] = return (ps, as, reverse r)
tiQuals as ps r (q:quals) = do
    (rs, as',q') <- tiQual as q
    tiQuals (as' ++ as) (rs++ps) (q':r) quals

tiQual :: [Assump] -> CQual -> TI ([VPred], [Assump], CQual)
tiQual as (CQGen _ p e) = do
    t             <- newTVar "tiQual" KStar p
    (qs, e')      <- tiExpr as t e
    (ps, as', p') <- tiPat t p
    return (ps++qs, as', CQGen t p' e')
tiQual as (CQFilter e) = do
    (ps, e') <- tiExpr as tBool e
    return (ps, [], CQFilter e')

-----------------------------------------------------------------------------

type Expl = (Id, CQType, [CClause], [CQual])

tiExpl :: [Assump] -> Expl -> TI ([VPred], CDefl)
tiExpl as expl@(i, cqt, alts, me) =
    tiRecoveringFromError
      (tiExpl_1 as expl)
      (return ([],
               (CLValueSign (CDefT
                             i
                             (S.toList(getFQTyVarsT cqt))
                             cqt
                             alts)
                me)))


tiExpl_1 :: [Assump] -> Expl -> TI ([VPred], CDefl)
tiExpl_1 as (i, cqt, alts, me) = do
{-
    --trace ("tiExpl " ++ ppReadable i) $ return ()
    sc           <- mkScheme cqt
    tiExpl'' as i sc alts
-}

    -- Take the CSyntax type declaration and convert it into the
    -- internal data structure for a qualified type.  This does
    -- some kind checking, etc.
    qt@(qs :=> t) <- mkQualType cqt

    -- We're going to generalize this type over the type variables,
    -- so figure out which ones are bound.
    bs           <- getBoundTVs

    -- Of the type variables in the explicit declaration, separate the
    -- free type variables (vs) from those bound by the context (bvs)
    let (bvs, vs) = partition (\x -> elem x bs) (tv qt)

    -- Check that the variables bound in this declaration (bvs)
    -- have the same kind as where they were bound
    let kindCheckBV v =
            case (find (== v) bs) of
                Nothing -> internalError ("tiExpl: find should not fail")
                Just u -> if (kind u == kind v)
                          then return ()
                          else errBoundTyVarKindMismatch i v u
    mapM_ kindCheckBV bvs

    -- Generalize the qualified type to form a type scheme
    let sc       = quantify vs qt

    -- If there any explicit predicates with unsolvable variables,
    -- report an error
    -- XXX do we need to apply the subst?
    --s <- getSubst
    --let fvs = tv (apSub s as) `union` bs
    let fvs = tv as `union` bs
    checkForAmbiguousPreds i fvs qt

{-
    -- Make an instance "qt" and get back the names ("ts") of the type
    -- vars which were introduced in qt in place of the anonymous generics
    ii@(qt, ts)  <- freshInst "H" i sc

    -- Make a substitution from the "vs" of the original type decl
    -- to the "ts" as they are now named, and apply it to the definition
    -- (the clauses and condition)
    let s        = mkSubst (zip vs ts)
        alts'    = apSub s alts
        me'      = apSub s me

    -- Push the newly bound variables (the "ts") onto the bound var stack
    addBoundTVs (map (\ (TVar v) -> v) ts)

    -- Proceed to the next step
    --traceM ("tiExpl " ++ ppReadable (i, s, cqt, alts, alts'))
    tiExpl'' as i sc alts' me' ii
-}

    -- Convert "qs" into local instances
    eqs <- mapM (mkEPred . removePredPositions) qs

    -- Push the variables bound at this level onto the bound var stack
    addBoundTVs vs
    addExplPreds eqs

    -- Proceed to the next step
    tiExpl'' as i sc alts me (qt, map TVar vs)


-- This appears to be the entry point for situations where the type scheme
-- was worked out by the compiler, and does not need to be created from the
-- user-specified type declaration.  For example, once tiImpl has determined
-- the type.  Another caller is tiField, which has also done its own
-- quantifying.  This situation also does not have bound type variables.
tiExpl' :: [Assump] -> (Id, Scheme, [CClause], [CQual]) -> TI ([VPred], CDefl)
tiExpl' as (i, sc, alts, me) = do

    bvs <- getBoundTVs  -- vars bound outside

    ii@(qt@(qs :=> _), inst_types) <- freshInst "I" i sc -- create a copy of the type scheme

    eqs <- mapM (mkEPred . removePredPositions) qs

    -- the instantiated scheme creates bound type variables
    addBoundTVs (tv inst_types)
    addExplPreds eqs

    tiExpl'' as i sc alts me ii

-- tiExpl'' was added (by Lennart) as a front-end to tiExpl'''
-- to trim the substitution.  It takes advantage of the fact that
-- type variables are created in increasing numeric order.  It records
-- the current highest number, and after type-checking, it knows that it
-- can throw away all variables created during checking.  So it trims the
-- substitution back to the recorded point.
tiExpl'' :: [Assump] -> Id -> Scheme -> [CClause] -> [CQual] ->
            (Qual Type, [Type]) -> TI ([VPred], CDefl)
tiExpl'' as0 i sc alts me oqtvts = do
    -- Create a new variable to mark the start of the newly created
    (trim_point, _) <- newTVarId "tiExpl''" KStar i
    -- Typecheck
    r@(ps, d) <- tiExpl''' as0 i sc alts me oqtvts
    -- Get the substitution
    s <- getSubst

    --when (length (getSubstDomain s) > 100) $
    --    traceM (show (length (getSubstDomain s)) ++ "\n" ++ ppReadable s)

    -- Trim the substitution back to the recorded point
    updSubst (trimSubst trim_point)

    --s' <- getSubst
    --traceM (show (i, sizeSubst s, sizeSubst s'))

    let domain = S.fromList (getSubstDomain s)
    let fix_vars_rs = filter (flip S.member domain) (tv ps)
    when (doETrace && (not . null $ fix_vars_rs)) $
      traceM ("tiExpl'' fixup ps: " ++ ppReadable (fix_vars_rs, s, ps, apSub s ps))
    let fix_vars_d = filter (flip S.member domain) (tv d)
    when (doETrace && (not . null $ fix_vars_d)) $
      traceM ("tiExpl'' fixup d: " ++ ppReadable (fix_vars_d, s, d, apSub s d))

    -- Since the result "r" may contain some of the new (trimmed) variables
    -- which were found to be concrete types, we must apply the untrimmed
    -- substitution to remove any mention of the trimmed variables
    return r

--
-- as        the (local) environment
-- i        name of definition
-- sc        type signature of definition
-- alts        clauses of definition
-- me   the implicit condition patterns of an interface definition
--      (an empty list for non-interfaces)
-- oqt        instantiated scheme
-- vts        variables used to instantiate sc to oqt
tiExpl''' :: [Assump] -> Id -> Scheme -> [CClause] -> [CQual] ->
             (Qual Type, [Type]) -> TI ([VPred], CDefl)
tiExpl''' as0 i sc alts me (oqt@(oqs :=> ot), vts) = do

    etrace ("tiExpl: " ++ ppReadable (i, getIdPosition i, length as0, sc)) $
        return ()

    -- Typecheck the implicit condition (only for interfaces)
    -- mps = introduced predicates (VPred)
    -- as  = as0 plus new assumptions introduced
    -- me' = the conditions after checking
    (mps, as, me') <- tiQuals as0 [] [] me

    -- Typecheck the definition clauses
    -- ps    = introduced predicates (VPred)
    -- alts' = the clauses after checking
    (ps0, alts') <- tiClauses as ot alts

    satTraceM ("tiExpl " ++ ppReadable i ++ " ps0: " ++ ppReadable ps0)

    -- type functions like SizeOf could have crept into the predicates
    -- via unification, so we expand them out so that they can be satisfied
    ps <- concatMapM (expTConPred . expandSynVPred) ps0

    satTraceM ("tiExpl " ++ ppReadable i ++ " ps: " ++ ppReadable ps)

    -- ---------------

    -- locally bound tyvars and instances
    vs_bound_here <- getTopBoundTVs
    eqs0 <- getTopExplPreds

    -- drop local tyvars (but not instances)
    popBoundTVs

    bvs            <- getBoundTVs       -- and grab those bound outside

    s0 <- getSubst                      -- grab what we know now

    -- but put the tyvars bound here back on the stack, so that later
    -- calls to "satisfy" are aware of all the bound vars
    addBoundTVs vs_bound_here

    let eqs = apSub s0 eqs0

    ---- Begin: Section which Lennart marked with XXXX

    -- Try to solve as many of the constraints "ps" as possible,
    -- from the given constraints "eqs"
    -- ps' = the unsolved constraints
    -- bs2 = new bindings (new dictionaries defined from given dictionaries)
    (ps', bs2)     <- satisfy eqs (apSub s0 ps)

    satTraceM ("tiExpl " ++ ppReadable i ++ " ps'(satisfy): " ++ ppReadable ps')

    s              <- getSubst                        -- get full subst

    let
        -- Compute the fixed variables
        -- These are the variables in the assumptions and the bound vars
        fvs0       =  tv (apSub s as) `union` bvs
        -- Extend the fixed variables to include any variables which
        -- are fixed due to functional dependencies
        fvs        =  closeFD ps' fvs0 \\ vs_bound_here

        -- Apply the subst to the qualified type
        -- qt'@(qs' :=> t') = apSub s oqt
        qt'        = apSub s oqt

        -- Separate the unsolved predicates into two groups:
        -- ds2 = preds, all of whose tyvars are all fixed (we will
        --       defer them to the enclosing bindings)
        -- rs1 = preds which contain tyvars general/bound at this level
        -- "d" for deferred and "r" for retained
        (ds2, rs1) =  splitF fvs ps'                -- non-local, local constraints

        -- All the tyvars ("avs") = the vars of qt' ("lvs") and
        -- the fixed vars ("fvs")
        lvs        =  tv qt'                        -- local tyvars
        avs        =  lvs `union` fvs                -- all tyvars

    ----

    -- The "dvs" argument to "satisfyFV"
    let dvs = avs

    -- Try again to solve more constraints,
    -- this time, solving only for "rs1", the preds which contain
    -- tyvars bound at this level, and we don't generate TAdd, TLog, etc
    -- for the tyvars "dvs".
    -- ps' = the remaining unsolved constraints
    -- bs3 = new bindings for the solved constraints
    (ps', bs3)     <- satisfyFV dvs eqs (apSub s rs1)

    satTraceM ("tiExpl " ++ ppReadable i ++ " ps'(satisfyFV) " ++ ppReadable ps')

    s              <- getSubst                        -- get full subst

    let
        -- Compute the fixed variables
        -- These are the variables in the assumptions and the bound vars
        fvs0       =  tv (apSub s as) `union` bvs
        -- Extend the fixed variables to include any variables which
        -- are fixed due to functional dependencies
        fvs        =  closeFD ps' fvs0 \\ vs_bound_here

        -- Apply the subst to the qualified type
        qt'@(qs' :=> t') = apSub s oqt

        -- Separate the unsolved predicates into two groups:
        -- ds3 = preds, all of whose tyvars are all fixed (we will
        --       defer them to the enclosing bindings)
        -- rs2 = preds which contain tyvars general/bound at this level
        -- "d" for deferred and "r" for retained
        (ds3, rs2) =  splitF fvs ps'                -- non-local, local constraints

        -- All the tyvars ("avs") = the vars of qt' ("lvs") and
        -- the fixed vars ("fvs")
        lvs        =  tv qt'                        -- local tyvars
        avs        =  lvs `union` fvs                -- all tyvars

    let
        -- Bindings for solved constraints have been generated twice,
        -- consolidate them under one name
        bs23 = bs2 ++ bs3

        -- Constraints with only fixed variables have been removed twice,
        -- consolidate them under one name.  "d" for deferred
        --
        -- The constraints "ds" are those with variables which are
        -- all fixed (in "fvs").  Non-local contexts which have tyvars
        -- from an enclosing binding will be deferred, to be solved by
        -- the enclosing binding.  Contexts which have no vars at all
        -- may also appear in this list and are handled below as "uds".
        ds  = ds2 ++ ds3

    ---- End: Section which Lennart marked with XXXX

    ---- Begin: Added for defaulting

    -- Try to solve some remaining constraints by defaulting.
    -- rs  = remaining unsolved constraints
    -- bs4 = bindings for any constraints solved by defaulting
    (rs, bs4, amb_vars)
        <- if (null rs2)  -- whether there are any unresolved contexts
           then return (rs2,[],[])  -- don't do work if not necessary
           else defaultClasses avs eqs rs2

    -- defaulting extends the substitution
    s <- getSubst

    -- Consolidate the bindings under one final name
    let bs1 = bs23 ++ bs4

    -- The final remaining constraints are now named "rs"
    --trace ("tiExpl''': rs, rs2: " ++ ppReadable (rs,rs2)) $ return ()

    ---- End: Added for defaulting

    let
        -- Contexts which have no vars at all may also appear in the
        -- list "ds".  These contexts were not solved, which means a
        -- context reduction failure (no instance was found for those
        -- types).  Report an error if this list "uds" is not empty.
        uds        =  filter (null . tv) ds        -- no tyvars and not solvable

        -- Ambiguous predicates
        -- An expression is ill-formed if its most general type ps => t
        -- includes an ambiguous variable in "ps"; that is, a generic
        -- variable (one not in the assumptions) which does not appear in
        -- the base type "t".  The classic example is "show (read x)".
        -- The intermediate type is ambiguous.
        (rs_amb, rs_unamb) = partition (any (`elem` amb_vars) . tv) rs

    -- Apply the substitution to the code fragments
    let alts''     =  apSub s alts'             -- new alternatives
        abs        =  apSub s bs1               -- new dict bindings
        me''       =  apSub s me'               -- update guards

    -- Determine the generic variables and produce the inferred type scheme
    let
        -- The generic vars are the local vars ("tv t") which are not fixed
        gs = lvs \\ fvs
        -- The inferred type scheme quantifies over "gs"
        -- (note that qt' is just oqt with the subst applied)
        sc' = quantify gs qt'
        -- The expected type scheme (subst with the new info, first)
        xsc = apSub s sc

    rtrace ("tiExpl:\n" ++ (pretty 120 100 $ let d = PDReadable in
        (text "i =" <+> pPrint d 0 i) $+$
        (text "|as0| =" <+> pPrint d 0 (length as0)) $+$
        (text "as0 =" <+> pPrint d 0 as0) $+$
        (text "|as| =" <+> pPrint d 0 (length as)) $+$
        (text "as =" <+> pPrint d 0 as) $+$
        (text "alts =" <+> pPrint d 0 alts) $+$
        (text "(oqt, vts) =" <+> pPrint d 0 (oqt, vts)) $+$

        (text "s0 =" <+> pPrint d 0 s0) $+$
        (text "eqs0 = " <+> pPrint d 0 eqs0) $+$
        (text "eqs =" <+> pPrint d 0 eqs) $+$
        (text "dvs =" <+> pPrint d 0 dvs) $+$
        (text "ps,s.ps,ps' =" <+> pPrint d 0 (ps, apSub s0 ps, ps')) $+$
        (text "bs1 =" <+> pPrint d 0 bs1) $+$
        (text "alts' =" <+> pPrint d 0 alts') $+$

        (text "bvs =" <+> pPrint d 0 bvs) $+$
        (text "fvs0 =" <+> pPrint d 0 fvs0) $+$
        (text "fvs =" <+> pPrint d 0 fvs) $+$
        (text "qt' =" <+> pPrint d 0 qt') $+$
        (text "s =" <+> pPrint d 0 s) $+$
        (text "lvs =" <+> pPrint d 0 lvs) $+$
        (text "avs =" <+> pPrint d 0 avs) $+$

        (text "uds =" <+> pPrint d 0 uds) $+$
        (text "rs_amb =" <+> pPrint d 0 rs_amb) $+$

        (text "alts'' =" <+> pPrint d 0 alts'') $+$

        (text "ds,rs =" <+> pPrint d 0 (ds, rs)) $+$

        (text "gs =" <+> pPrint d 0 gs) $+$

        (text "abs =" <+> pPrint d 0 abs) $+$
        (text "sc,xsc,sc' =" <+> pPrint d 0 (sc, xsc, sc'))
        )) $ return ()

    -- Give better names to some variables
    let
        -- "n" stands for "new"?
        -- Here: nqt@(nqs :=> nt) = apSub s oqt
        nqt = qt'
        nqs = qs'
        nt = t'
        -- The generic variables
        ngs = gs
        -- The given type scheme
        nsc = sc'

        -- The dictionary names of the predicates
        vs = let getId (EPred (CVar i) _) = i
                 getId _ = internalError "TCheck.tiExpl''': vs getId"
             in  map getId eqs

    -- The predicates which will be returned, to be handled by the
    -- enclosing binding.  It includes the deferred predicates "ds"
    -- and the predicates for the interface method ready expression
    -- "mps" (if this is in an interface).
    let rds = mps ++ ds

    -- Does the expected type scheme match the given scheme?
    if xsc /= nsc then
        -- Report an error
        -- Use niceTypes to name the variables 'a', 'b', 'c', ...
        -- Use instSC2 to instantiate the generics with fresh tyvars not
        -- found in either type
        let (xsc', nsc') = niceTypes (instSC2 (xsc, nsc))
        in  err (getPosition i, ETooGeneral (pfpString xsc') (pfpString nsc'))
     else
     -- Are any of the retained predicates unsolved?
     if not (null rs_unamb) then
        -- Report errors for the contexts
        -- (later calls to "niceTypes" will replace generated tyvar names)
        let rs' = map toPredWithPositions rs
            ds' = map toPred ds
        in  handleWeakContext (getPosition i) t' qs' ds' rs'
     else
     -- any ambiguous variables?
     if not (null rs_amb) then
        handleAmbiguousContext (getPosition i) amb_vars rs_amb
     else
     -- Were any contexts without variables left unsatisfied?
     if not (null uds) then
        -- Report reduction errors
        handleContextReduction (getPosition i) uds
     else
        -- No ambiguous variables, so...
        -- Produce the return values (deferred preds, CDefl)
        do
           --traceM("tiExpl " ++ ppReadable (i,eqs,ps))

           -- remove the bound tyvars and instances for this level
           popBoundTVs
           popExplPreds

           -- XXX More comments and review needed beyond this point
           let
                -- inline simple bindings
                (vmap, rem_abs) = simplifyDictBindings abs
                -- we're only substituting variables, not constructors
                s :: CSEnv
                s = (M.empty, M.empty, vmap, M.empty)
                alts''' = cSubstN s alts''
                me''' = cSubstQualsN s me''
            in --traces (ppReadable s) $
               if null nqs && null rem_abs then
                   -- simplify special case (no context, no new bindings)
                   let ldef = CLValueSign
                                 (CDefT i ngs (CQType [] nt) alts''') me'''
                   in  return (rds, ldef)
               else do
                  --posCheck "G" i
                  ii <- newVar (getPosition i) "tiExpl"
                  let ldef = CLValueSign
                                 (CDefT ii [] (CQType [] nt) alts''') []
                      -- produce let in topologically sorted order
                      -- (since ldef uses bindings, but not vice-versa)
                      body = CClause (map CPVar vs) []
                                 (Cletrec (rem_abs ++ [ldef]) (CVar ii))
                  --traceM ("tiExpl''' " ++ ppReadable (i, ii, abs))
                  return (rds, CLValueSign
                                 (CDefT i ngs (CQType [] (qualToType nqt))
                                     [body]) me''')


-- The way we typecheck, sub-expr checking doesn't know what bindings
-- exist, so a fresh dict binding is made for each predicate even if a
-- dict already exists for it.  This leads to "silly bindings" (as
-- Lennart said in rev 2901) like this:
--    _tcdict1002 = _tcdict1001
-- This leads to problems for IConv when it substs these away.
--
-- In rev 2901, Lennart added an optimization, but was unsure of the
-- benefit.  In rev 2904, he commented it out, due to a bug.  In his
-- code, a simple binding included functions.  We don't include those,
-- and thus don't have to deal with recursive bindings.
simplifyDictBindings :: [CDefl] -> (M.Map Id CExpr, [CDefl])
simplifyDictBindings all_bs =
    let
        (simple_bs, rem_bs0) = partition simpleD all_bs

        simpleD (CLValueSign (CDefT _ [] (CQType [] _)
                                  [CClause [] [] e]) []) = simpleE e
        simpleD _ = False

        simpleE (CTApply e _) = simpleE e
        simpleE (CVar _) = True
        -- Lennart included this
        --simpleE (CApply f es) = all simpleE (f:es)
        simpleE _ = False

        -- sort the simple bindings in usage order
        -- (so that we can apply the subst once)
        defpairs =
            [ (i, e)
              | (CLValueSign (CDefT i _ _ [CClause _ _ e]) _) <- simple_bs ]
        defmap = M.fromList defpairs
        isdef i = i `M.member` defmap
        usegraph = [ (i, is) | (i, e) <- defpairs,
                               let is0 = fvSetToFreeVars (getFVE e),
                               let is = filter isdef is0 ]
        ordered_def_ids =
            case (GW.tSort usegraph) of
              Right is -> is
              Left sccs ->
                  internalError ("ordered_def_ids: " ++ ppReadable sccs)

        mkEnv vm = (M.empty, M.empty, vm, M.empty)

        vmap = let fn accum_map i =
                      let e0 = fromJustOrErr "vmap" (M.lookup i defmap)
                      in  M.insert i (cSubst (mkEnv accum_map) e0) accum_map
               in  foldl fn M.empty ordered_def_ids
    in
       (vmap, cSubstN (mkEnv vmap) rem_bs0)


{-
-- instantiate a type scheme on temporary type variables
instSC :: Scheme -> (Qual Type)
instSC (Forall ks t) = inst vars t
  where bad_tmptyvar_ids = map getTyVarId (tv t)
        tmptyvar_ids = [i | i <- tmpTyVarIds, not (i `elem` bad_tmptyvar_ids)]
        vars = zipWith (\ i k -> TVar (TyVar i noTyVarNo k)) tmptyvar_ids ks
-}

-- instantiate two type schemes on temporary type variables
instSC2 :: (Scheme, Scheme) -> (Qual Type, Qual Type)
instSC2 (Forall ks1 t1, Forall ks2 t2) =
    let bad_tmptyvar_ids = map getTyVarId (tv (t1,t2))
        tmptyvar_ids = [i | i <- tmpTyVarIds, not (i `elem` bad_tmptyvar_ids)]
        (tmptvs1, tmptvs2) = splitAt (length ks1) tmptyvar_ids
        vars1 = zipWith (\ i k -> TVar (TyVar i noTyVarNo k)) tmptvs1 ks1
        vars2 = zipWith (\ i k -> TVar (TyVar i noTyVarNo k)) tmptvs2 ks2
    in  (inst vars1 t1, inst vars2 t2)

-----------------------------------------------------------------------------

-- a definition without a type (i.e., with an "implicit" type)
type Impl   = (Id, ([CClause], [CQual]))

-- a function to typecheck a single definition
--   type_env  = current type environment
--   type_var  = the type variable for this def
--   clauses =   the clauses of the definition
--   quals =     the implicit condition patterns
--               (an empty list if the def is not for a method)
tiImpl :: [Assump] -> Type -> (Id, ([CClause], [CQual]))
       -> TI ([VPred], ([CClause], [CQual]))
tiImpl type_env type_var (_, (clauses, quals)) = do
        -- Typecheck the implicit condition (only for interfaces)
        -- pqs = introduced predicates (VPred)
        -- type_env_quals = type_env plus new assumptions from quals
        -- qs' = the conditions after checking
        (provisos_quals, type_env_quals, rewritten_quals)
            <- tiQuals type_env [] [] quals
        -- Typecheck the definition clauses
        -- provisos_clauses = introduced predicates (VPred)
        -- rewritten_clauses = the clauses after checking
        (provisos_clauses, rewritten_clauses)
            <- tiClauses type_env_quals type_var clauses
        -- return the predicates and the new defs
        return (provisos_quals ++ provisos_clauses,
                (rewritten_clauses, rewritten_quals))

-- typecheck a set of possibly interdependent definitions
tiImpls :: Bool -> Infer2 [Impl] [Assump] [CDefl]
tiImpls recursive as [] = return ([], [], [])
tiImpls recursive as ibs = do
    --trace ("IMPLICIT " ++ ppReadable (map fst ibs)) $ return ()

    -- Get the type variables which are bound by a surrounding context
    bvs            <- getBoundTVs

    -- create new type variables for the types of the definitions
    ts <- mapM (newTVar "tiImpls" KStar) ibs

    let
        -- the ids of the definitions
        is    = map fst ibs
        -- create a scheme for each definition
        scs   = map toScheme ts
        -- if the defs are interdependent/recursive:
        -- create an assumption from each scheme (associating id to scheme)
        -- and add them to the environment
        as_initial | recursive = zipWith (:>:) is scs ++ as
                   | otherwise = as

    -- typecheck all the defs
    pscs <- sequence (zipWith (tiImpl as_initial) ts ibs)

    -- pss = all the predicates
    -- altss' = all the new defs (clauses and quals)
    let (pss, altss') = unzip pscs

    s   <- getSubst

    let ps = apSub s (concat pss)
    when (not . null $ ps) $ satTraceM ("tiImpls " ++ ppReadable is ++ " ps: " ++ ppReadable ps)

    -- try to solve as many constraints as possible,
    --   ps' = unsolved predicates
    --   bs  = new bindings (for dictionaries of any predicates solved)

    -- We used to call "satisfy" with an empty list for eqs, but now we try
    -- to reduce predicates more aggressively, so that we generate better
    -- provisos when we re-type-check with tiExpl

    eqsFV <- getExplPreds
    (ps', bs1) <- satisfyFV bvs eqsFV ps

    when (not . null $ ps) $ do
      if (not . null $ ps') then
        satTraceM ("tiImpls " ++ ppReadable is ++ " ps': " ++ ppReadable ps')
       else
        satTraceM ("tiImpls " ++ ppReadable is ++ " satisfied")

    s   <- getSubst

    -- "satisfy" returns the original preds that could not be resolved;
    -- however, some preds may reduce to simpler provisos (which could not
    -- be resolved).  so we do that reduction here.

    let eqs = []
    (ps'', bs2, s_agg) <- reducePredsAggressive Nothing eqs ps'

    when (not . null $ ps') $ do
      if (not . null $ ps'') then
        satTraceM ("tiImpls " ++ ppReadable is ++ " ps'': " ++ ppReadable ps'')
       else
        internalError ("tiImpls aggressively reduced? " ++ ppReadable (ps', ps'', s, s_agg))

    extSubst "tiImpls reducePredsAgg" s_agg

    let
        -- Expand the types with any new information
        ts'     = apSub s ts

        -- Compute the free variables ("fixed" variables?)
        -- These are the variables in the assumptions
        fs      = tv (apSub s as) `union` bvs
        -- XXX we don't close them over functional dependencies, as in tiExpl?

        vss       = map tv ts'
        -- local variables
        lvs       = foldr1 union vss
        --gs      = lvs \\ fs

        -- Separate the unsolved predicates into two groups:
        -- ds = preds, all of whose tyvars are fixed (in fs)
        --      (we will defer them to the enclosing bindings)
        -- rs = preds which contains tyvars general/bound at this level
        -- "d" for deferred and "r" for retained
        (ds,rs) = splitF fs ps''                        -- non-local, local constraints


    -- Begin: find unresolvable variables

    (rs2, bs3, amb_vars)
        <- -- this will be a no-op if there are no ambiguous vars
           defaultClasses (fs `union` lvs) [] rs

    when (not (null amb_vars)) $
        let pos = getPosition (fst (headOrErr "tiImpls: pos" ibs))
        in  handleAmbiguousContext pos amb_vars rs2

    -- update the info we computed above
    s <- getSubst
    let bs_final = apSub s (bs1 ++ bs2 ++ bs3)
        ts_final = apSub s ts'
        fs_final = tv (apSub s as) `union` bvs
        vss_final = map tv ts_final
        lvs_final = foldr1 union vss_final
        rs_final = rs2

    -- End: find unresolvable variables

    -- Apply the substitution to the code fragments
    let altss_final = map (apSub s) altss'          -- new alternatives

    -- Determine the generic variables and produce the inferred type scheme
    let
        -- The generic vars are the local vars (tv of the ts and the rs)
        -- which are not fixed
        gs = (lvs_final `union` tv rs_final) \\ fs_final
        -- The inferred type scheme quantified over "gs"
        scs' =
            map (quantify gs . (map toPredWithPositions rs_final :=>)) ts_final

        -- The final assumptions (associating ids to schemes)
        res_as = zipWith (:>:) is scs'

    rtrace ("tiImpl:\n" ++ (pretty 120 100 $ let d = PDReadable in
        (text "s =" <+> pPrint d 0 s) $+$
        (text "ibs =" <+> pPrint d 0 ibs) $+$
        (text "pss,ps',ps'' =" <+> pPrint d 0 (pss, ps', ps'')) $+$
        (text "fs =" <+> pPrint d 0 fs) $+$
        (text "ds,rs_final =" <+> pPrint d 0 (ds, rs_final)) $+$
        (text "res_as =" <+> pPrint d 0 res_as)
        )) $ return ()

    -- Are there any local constraints?
    -- Either any retained (rs) or any predicates satisfied (bs)
    if (null rs_final) && (null bs_final) then
        -- no local constraints, so use bindings as is
        let
            -- Create an explicitly typed definition for a given i
            -- The generic variables are (tv t \\ fs_final)
            mkExpl (i,_) t (alts, me) =
                CLValueSign (CDefT i (tv t \\ fs_final) (CQType [] t) alts) me
            defs = zipWith3 mkExpl ibs ts_final altss_final
        in
            -- return the deferred predicates, the assumptions for the
            -- ids bound here, and the typed defs
            return (ds, res_as, defs)
     else do
        -- Else, we need to handle the proviso dictionaries and dict bindings.
{-
        -- This used to be done by converting to an explicitly-type let expr
        -- and re-typechecking, but that was inefficient
        --
        let (css, qss) = unzip (map snd ibs)
        -- re-check as explicitly-typed bindings, with the original "as"
        xs <- mapM (tiExpl' as) (zip4 is scs' css qss)
        -- qss = predicates to be propagated (like "ds"?)
        -- eds = the new explicit defs (after checking)
        let (qss, eds) = unzip xs
        return (concat qss, res_as, eds)
-}
        let
            mkExpl i t0 (alts, me) = do
              let
                  -- the "original" type, resulting from typecheck
                  qs0 = map toPredWithPositions rs_final
                  oqt = (qs0 :=> t0)

                  -- the variables in the type
                  vs = tv oqt
                  -- the generic variables in the type
                  -- (in the order they appear in "oqt")
                  gs_used_here = filter (`elem` gs) vs

              -- make new names for the generic variables
              -- XXX TODO: do we need to? or can we just continue to use "gs"?
              let mkFreshVar v = newTVar ("tiImpls fresh") (kind v) v
              vs_bound_here <- mapM mkFreshVar gs_used_here
              -- the same list, but as TyVar
              let vts_bound_here =
                    let getTyVar (TVar v) = v
                        getTyVar _ = internalError "TCheck.tiImpls: vts_bound_here getTyVar"
                    in  map getTyVar vs_bound_here
              -- a mapping from the old names to the new names
              -- (need to apply this subst to everything -- types and exprs)
              -- (CSubst was extended to support TVar specifically for this)
              let gs_map = zip gs_used_here vs_bound_here

              -- the new type for this let-binding
              let nqt@(_ :=> nt) = apSub (mkSubst gs_map) oqt

              -- the variable names for the dictionary arguments
              let dict_vs = let getVPredId (VPred i _) = i
                            in  map getVPredId rs_final

              let
                  -- inline simple dictionary bindings
                  (vmap, rem_bs_final) = simplifyDictBindings bs_final
                  -- substitute for the simple dict bindings (vmap)
                  -- and for the new generic variable names (gs_map)
                  csenv :: CSEnv
                  csenv = (M.empty, M.empty, vmap, M.fromList gs_map)
                  alts' = cSubstN csenv alts
                  me' = cSubstQualsN csenv me
                  -- the dict bindings can refer to "gs"
                  rem_bs_final' = cSubstN csenv rem_bs_final

              inner_i <- newVar (getPosition i) "tiImpl"
              let ldef = CLValueSign
                             (CDefT inner_i [] (CQType [] nt) alts') []
                  -- produce let in topologically sorted order
                  -- (since ldef uses bindings, but not vice-versa)
                  body = CClause (map CPVar dict_vs) []
                             (Cletrec (rem_bs_final' ++ [ldef]) (CVar inner_i))
              return (CLValueSign
                          (CDefT i vts_bound_here (CQType [] (qualToType nqt))
                               [body]) me')
        defs <- sequence $ zipWith3 mkExpl (map fst ibs) ts_final altss_final
        return (ds, res_as, defs)

-----------------------------------------------------------------------------

-- binding group: some explicitly typed and some implicitly typed definitions
type BindGroup  = ([Expl], [[Impl]])

-- typecheck a binding group, with possibly mutually recursive bindings
tiBindGroup :: Infer2 BindGroup [Assump] [CDefl]
tiBindGroup as (typed_bindings, untyped_bindingss) = do
                -- as': type env containing explicitly-typed bindings
                as' <- mapM (\ (v,t,_,_) -> do sc <- mkSchemeNoBVs t
                                               return (v:>:sc))
                            typed_bindings
                (ps, as'', ds')
                    <- tiSeq (tiImpls True) (as'++as) untyped_bindingss
                xs <- mapM (tiExpl (as''++as'++as)) typed_bindings  --- XXX
                let (qss, ds'') = unzip xs
                return (ps++concat qss, as''++as', ds' ++ ds'')

-- typecheck a list of sequentially dependent elements, such as letseq
-- definitions or independent binding groups from letrec
--   arguments:
--     ti:        the typechecker to use for the typechecking
--     type_env:  initial type environment
--     all_defs:  definitions or binding groups to check sequentially
--   returns:
--     (provisos, type_env, rewritten_defs) where
--       provisos:       provisos required by the definitions
--       type_env:       type environment with all definitions
--       rewritten_defs: original definitions, possibly rewritten
tiSeq :: Infer2 bg [Assump] [d] -> Infer2 [bg] [Assump] [d]
tiSeq ti type_env [] = return ([], [], [])
tiSeq ti type_env all_defs@(def : rest_defs) = do
    (provisos, type_env',  rewritten_defs) <- ti type_env def
    (provisos_rest, type_env'', rewritten_defs_rest)
        <- tiSeq ti (type_env'++type_env) rest_defs
    return (provisos ++ provisos_rest, type_env''++type_env',
            rewritten_defs ++ rewritten_defs_rest)

-- tiLetseqDef: type-check a single non-recursive let definition
--   arguments:
--     type_env: type environment assumptions
--     def:      definition to typecheck (must not be CLMatch)
--   returns:
--     (provisos, type_env, rewritten_defs) where
--       provisos:       provisos required by this definition
--       type_env:       a binding for this definition
--       rewritten_defs: original definition, possibly rewritten
tiLetseqDef :: [Assump] -> CDefl -> TI ([VPred], [Assump], [CDefl])
tiLetseqDef type_env def@(CLValueSign (CDef var_name def_type clauses) quals) =
    do -- check RHS without defining the variable it's assigned to;
       -- fix type variables in the explicit signature while checking RHS
       let explicit_def = (var_name, def_type, clauses, quals)
       (provisos, rewritten_def) <- tiExpl type_env explicit_def
       -- create a type scheme for this definition and return it
       def_type_scheme <- mkSchemeNoBVs def_type
       return (provisos, [var_name :>: def_type_scheme], [rewritten_def])
tiLetseqDef type_env def@(CLValueSign (CDefT _ _ _ _) _) =
  -- CDefT implies that the def has already been type-checked
  -- and so should not need re-typechecking
  internalError ("tiLetSeqDef: CDefT " ++ ppReadable def)
tiLetseqDef type_env def@(CLValue var_name clauses quals) =
    tiImpls False type_env [(var_name, (clauses, quals))]
tiLetseqDef type_env arm@(CLMatch pattern expression) =
    internalError
        ("TCheck.tiLetseqDef: CLMatch should have been desugared:\n" ++
         pfpReadable arm)

-- tiDefls: type-infer a set of letrec definitions
--   first argument:         assumptions about type environment
--   second argument (exp):  definitions to typecheck
-- returns: TI (provisos, type_env', defs') where
--   provisos:  context requirements
--   type_env': type environment, possibly extended with the definitions
--   defs':     definitions, possibly rewritten
tiDefls :: [Assump] -> [CDefl] -> TI ([VPred], [Assump], [CDefl])
tiDefls type_env defs = do
    dss        <- mapM expCLMatch defs -- convert pattern-matches to regular defs
    let ds = concat dss
    let -- impl: untyped (implicitly typed) definitions
        impl = doSCC ds
        -- expl: explicitly typed definitions
        expl = [ (i, t, cs, me) | CLValueSign (CDef i t cs) me <- ds ]
    case filter (not . null) (map chkIRec impl) of -- detect recursion
     all_is@(_:_) : _ ->
         -- XXX we only report one cycle?
         -- Don't report internal names that come from expanding
         -- pattern matches
         let user_is = filter (not . isBadId) all_is
             mkErr :: [Id] -> TI a
             mkErr is = err (getPosition is, ELocalRec (map pfpString is))
         in  case user_is of
               (_ : _) -> mkErr user_is
               _       -> mkErr all_is
     [] -> tiBindGroup type_env (expl, impl)
     _ -> internalError "TCheck.tiDefls"

-- find untyped definitions which refer to themselves
chkIRec :: [Impl] -> [Id]
chkIRec [(i, (cs, me))] =
    if S.member i (snd (getFVDl (CLValue i cs me))) then [i] else []
chkIRec ics = map fst ics

{- Unused:
chkERec d@(CLValueSign (CDef i _ _) _) = S.member i (snd (getFVDl d))
chkERec _ = False
-}

-- extract untyped let-defs and sort them into interdependent groups
doSCC :: [CDefl] -> [[Impl]]
doSCC ds =
        let g = [ (i, S.toList (snd (getFVDl d) `S.intersection` is)) | d@(CLValue i _ _) <- ds ]                -- XXX CLMatch
            is = S.fromList (map fst g)
            iss = scc g
            get i = (i, (headOrErr ("TCheck.doSCC: missing CLValue " ++
                                    pfpString i)
                         ([ (cs, me) | CLValue i' cs me <- ds, i == i'])))
        in  map (map get) iss

-----------------------------------------------------------------------------

-- funny, this sees a system task application
iAPs :: CExpr -> [Type] -> [VPred] -> CExpr
iAPs f ts ps = cApply 7 (cTApply f ts) (map (\ (VPred i _) -> CVar i) ps)

optTrivLet :: CExpr -> CExpr
optTrivLet (Cletseq [CLValueSign (CDefT x [] _ [CClause [] [] e]) []] (CVar x')) | x == x' = e
optTrivLet (Cletrec [CLValueSign (CDefT x [] _ [CClause [] [] e]) []] (CVar x')) | x == x' = e
optTrivLet e = e

ifcFieldIdToTConId :: Id -> SymTab -> CType -> Maybe Id
ifcFieldIdToTConId i r t =
    case leftCon (expandSyn t) of
    Nothing -> Nothing
    Just ti ->
        case findType r ti of
        -- this pattern requires that the type be an interface
        Just (TypeInfo _ _ _ (TIstruct (SInterface {}) is) _) ->
            if (unQualId i) `elem` map unQualId is
                then Just ti
                else Nothing
        _ -> Nothing

-- Whether _read/_write desugaring can be applied
-- (it is an interface type and it has _read/_write as a method)
isReadType :: SymTab -> CType -> Maybe Id
isReadType  = ifcFieldIdToTConId (id_read noPosition)
isWriteType :: SymTab -> CType -> Maybe Id
isWriteType = ifcFieldIdToTConId (id_write noPosition)

-- check if an interface has a ._write method
-- or is in PrimWriteable
writeableIfc :: Flags -> SymTab -> CType -> Bool
writeableIfc flags r t
    | Just _ <- isWriteType r t = True
    -- incoherent matches are resolved *after* reducePred
    | Right (Just _) <- fst3 $ runTI flags False r checkWriteable = True
    | otherwise = False
  where checkWriteable = do
          wCls <- findCls (CTypeclass idPrimWriteable)
          v <- newTVar "writeableIfc" KStar t
          vp <- mkVPredFromPred [] (IsIn wCls [t, v])
          reducePred [] Nothing vp

getIfcFields :: Id -> SymTab -> Maybe [Id]
getIfcFields ti sy =
    case findType sy ti of
    Just (TypeInfo _ _ _ (TIstruct SInterface{} fs) _) -> Just fs
    _ -> Nothing

chkSchedInfo :: [Id] -> VSchedInfo -> TI ()
chkSchedInfo field_ids si@(SchedInfo mci rms rbm ccm) = do
    -- traceM ("chkSchedInfo" ++ ppReadable si)
    let field_set = S.fromList field_ids
    -- check methodConflictInfo
    chkMethConf field_set mci
    -- check unsynchronized clock crossing methods
    chkUnsyncMeths field_set ccm
    -- check rulesBetweenMethods and rulesBeforeMethods
    -- XXX these should never come from the user, so it's an internal error?
    -- XXX also, we have no way of checking if the rule names exist
    -- XXX (if we allowed it in import-BVI, the rule name field would need
    -- XXX to be a different type)
    let unknown = [ i | ((i1,i2),rs) <- rms, i <- [i1, i2],
                        not (i `S.member` field_set) ] ++
                  [ i | (i,rs) <- rbm, not (i `S.member` field_set) ]
    case unknown of
        [] -> return ()
        i : _ -> err (getIdPosition i, EUnboundField (pfpString i))

chkMethConf :: S.Set Id -> MethodConflictInfo Id -> TI ()
chkMethConf field_set mci@(MethodConflictInfo cf sb me p sbr c ext) =
    let unknown =
            [ i | iis <- [cf, sb, p, sbr, c],
                  (i1,i2) <- iis, i <- [i1, i2], not (i `S.member` field_set) ] ++
            [ i | is <- me, i <- is, not (i `S.member` field_set) ] ++
            [ i | i <- ext, not (i `S.member` field_set) ]
    in  case unknown of
            [] -> return ()
            i : _ -> err (getIdPosition i, EUnboundField (pfpString i))

chkUnsyncMeths :: S.Set Id -> [Id] -> TI ()
chkUnsyncMeths field_set ms =
    let unknown = [ i | i <- ms, not (i `S.member` field_set) ]
    in  case unknown of
            [] -> return ()
            i : _ -> err (getIdPosition i, EUnboundField (pfpString i))

-----------------------------------------------------------------------------

cLet :: [(Id, CType, CExpr)] -> CExpr -> CExpr
cLet ites e = Cletrec [ CLValueSign (CDefT i [] (CQType [] t) [CClause [] [] e]) [] | (i, t, e) <- ites ] e

-- convert a CLMatch binding to non-pattern-matching let-bindings
expCLMatch :: CDefl -> TI [CDefl]
expCLMatch (CLMatch p e) =
    case expComma p of
    CPAny {} -> return []
    CPVar v -> return [bind v e]
    CPAs v p -> expand [bind v e] (CVar v) (expComma p)
    p' -> do
        --posCheck "H" p'
        v <- newVar (getPosition p) "expCLMatch"
        expand [bind v e] (CVar v) p'
  where bind i e = CLValue i [CClause [] [] e] []
        expand ds v (CPstruct mb ti fs)
          | mb /= (Just False) = do
                -- The check of 'mb' just confirms that the struct syntax was used.
                -- We also need to check that the name exists and is a struct type.
                checkTyConId ti
                -- Now it's safe to construct selection exprs using that name
                dss <- mapM (\ (f, p) -> expCLMatch (CLMatch p (CSelectTT ti v f))) fs
                return (concat (ds:dss))
        expand _ _ p = err (getPosition p, EBadMatch (pfpString p))
        -- Note, this is duplicating some of what 'disambiguateStruct' does
        checkTyConId i = do
          -- First check that the name is defined
          tc <- findTyCon i
          -- Then confirm that it is a struct
          case tc of
            (TyCon _ (Just {}) (TIstruct {})) -> return ()
            _ -> err (getPosition i, ENotStructId (pfpString i))
        expComma (CPCon comma [p1, p2]) | comma == idComma =
                CPstruct (Just True) (setIdPosition (getIdPosition comma) idPrimPair)
                    [(setIdPosition (getPosition p1) idPrimFst, p1),
                     (setIdPosition (getPosition p2) idPrimSnd, p2)]
        expComma p = p
expCLMatch d = return [d]

{-
posCheck s x =
    if getPosition x == noPosition then trace ("posCheck " ++ s) $ return () else return ()
-}

-------

-- XXX should do matching of t and td to avoid tyvars
freshInstT :: (HasPosition a, PPrint a, PVPrint a)
           => String -> a -> Scheme -> Type -> TI (Qual Type, [Type])
freshInstT msg x (Forall [] qt@(_ :=> t)) td = return (qt, [])
freshInstT msg x (Forall ks qt@(_ :=> t)) td = do
    s <- getSubst
    -- The whole purpose of fmatch is to avoid to create type variables when
    -- they are not needed.  It is purely an optimization; the Nothing branch
    -- of the case is always safe.
    case fmatch t (apSub s td) of
        Nothing -> do
--          traces ("freshInstT\n" ++ ppReadable t ++ ppReadable (apSub s td) ++ ppReadable (fmatch t (apSub s td))) return ()
            ts <- mapM (flip (newTVar ("freshInstT N " ++ msg)) x) ks
            return (inst ts qt, ts)
        Just its -> do
            let f (i, k) =
                    case [ t | (i', t) <- its, i == i' ] of
                        (t:ts) | kind t == k -> unifys t ts
                        _ -> newTVar ("freshInstT J " ++ msg) k x
                unifys t [] = return t
                unifys t (t':ts) = do _ <- unify x t t'; unifys t ts
            ts <- mapM f (zip [0..] ks)
            return (inst ts qt, ts)

fmatch :: Type -> Type -> Maybe [(Int, Type)]
fmatch _ _ = Nothing
{-
-- XXX broken, check /usr/users/lennart/proj/Sandburst/mojavebs/units/ma_am_uc/js
-- bsc +RTS -H100M -RTS -u -v PiDefs.bs
fmatch (TAp f a) (TAp f' a') = do
    fs <- fmatch f f'
    as <- fmatch a a'
    return (fs ++ as)
fmatch (TGen _ n) t = return [(n, t)]
fmatch (TCon tc) (TCon tc') | tc == tc' = return []
fmatch _ _ = Nothing
-}

-------

-- Error message for kind mismatch of bound type variables

errBoundTyVarKindMismatch :: Id -> TyVar -> TyVar -> TI ()
errBoundTyVarKindMismatch i v u =
    err (getPosition i, EBoundTyVarKindMismatch (pfpString v)
                            (pfpString (kind v)) (getPosition v)
                            (pfpString (kind u)) (getPosition u))

-------

-- typecheck and expression just to find out what type it has
-- trimming the substitution seems to be excessive work here
tiWithType :: [Assump] -> CExpr -> TI (Type, [VPred], CExpr)
tiWithType as e = do
   (v_id, v) <- newTVarId "tiForType" KStar e
   (ps, e') <- tiExpr as v e
   s <- getSubst
   let t = apSub s v
   -- when doTrim $ updSubst (trimSubst v_id)
   t' <- expandFullType t
   return (t', ps, e')

tiForType :: [Assump] -> CExpr -> TI (Type)
tiForType as e = fmap fst3 (tiWithType as e)

-------

findFieldDefault :: CType -> Id -> Id -> Id -> TI [(Id, CExpr)]
findFieldDefault td c c' qf = do
  sy <- getSymTab
  -- c might be an alias, where c' is the expanded type
  case (findFieldInfo sy c' qf) of
    Just (FieldInfo { fi_id = fid,
                      fi_assump = (_ :>: fscheme),
                      fi_default = cs }) ->
      if (null cs)
      then return []
      else do
        -- make the name for the Defl
        new_i <- newVar (getPosition c) "findFieldDefault"
        -- make the type for the Defl (if possible)
        -- (this is like what "convInst" does)
        td' <- expandFullType td
        let mqt = case (leftCon td') of
                    Nothing -> Nothing
                    Just tc ->
                      let structTVs = tyConArgs td'
                          (Forall ks qt) = fscheme
                          -- relying on the struct arguments being
                          -- the first vars
                          ks' = drop (length structTVs) ks
                          extraTVs = zipWith cTVarKind tmpVarIds ks'
                          ts = structTVs ++ extraTVs
                      in
                          -- drop the struct arguments
                          case (qualTypeToCQType (inst ts qt)) of
                            (CQType ps (TAp (TAp (TCon arr) a) r)) |
                                isTConArrow arr -> Just (CQType ps r)
                            x -> internalError ("findFieldDefault: inst: " ++
                                                ppReadable x)
        -- make the Defl
        let defl = case (mqt) of
                     Nothing -> CLValue new_i cs []
                     Just qt -> CLValueSign (CDef new_i qt cs) []
        -- XXX this is probably the wrong place to clean up the kinds,
        -- but it is convenient for now
        e <- ctxRed (Cletseq [defl] (CVar new_i))
        return [(unQualId qf, e)]
    Nothing -> internalError ("findFieldDefault: findFieldInfo: " ++
                              ppReadable (c,c',qf))

-------

checkMethodArgNames :: Id -> [CDefl] -> TI ()
checkMethodArgNames ti ds = do
    sy <- getSymTab

    -- -----------
    -- extract which fields of the ifc have names

    let
        -- Given a def for a field of the ifc, determine if it has
        -- explicit arguments.  Only accept fields defined by a single
        -- clause without argument qualifiers (since this is all that
        -- BSV accepts).
        getArgNames :: CDefl -> [(Id, [Id])]
        getArgNames (CLValue i [clause] _) = getArgNamesFromClause i clause
        getArgNames (CLValueSign (CDef i _ [clause]) _) =
            getArgNamesFromClause i clause
        getArgNames (CLValueSign (CDefT i _ _ [clause]) _) =
            getArgNamesFromClause i clause
        getArgNames _ = []

        getArgNamesFromClause :: Id -> CClause -> [(Id, [Id])]
        getArgNamesFromClause mId (CClause ps [] _) =
            let isPatVar (CPVar _) = True
                isPatVar _ = False
                getVarId (CPVar i) = i
                getVarId _ = internalError ("getVarId")
            in  if (not (null ps)) && (all isPatVar ps)
                then [(mId, map getVarId ps)]
                else []
        getArgNamesFromClause _ _ = []

    -- ----------
    -- look up each in the symtab and return the pairs which are found
    -- (any not found will be an error later)

    let checkNames qti (mId, def_ids) =
            let decl_ids = getMethodArgNames sy qti mId
                pairs = zip def_ids decl_ids
                areSame (a,b) = (a == b)
            in  case (partition areSame pairs) of
                  (_, []) -> return ()
                  (_, mismatches) ->
                      let toString (i1,i2) = (getIdString i1, getIdString i2)
                      in  twarn (getPosition mId,
                                 EMethodArgNameMismatch (getIdBaseString mId)
                                     (map toString mismatches))

    when (warnMethArgMismatch) $
      do -- make sure the interface name is qualified
         let qti = case (findType sy ti) of
                     Just (TypeInfo { ti_qual_id = Just i }) -> i
                     _ -> internalError ("tiExpr: Cinterface: " ++
                                         ppReadable ti)
         mapM_ (checkNames qti) (concatMap getArgNames ds)

-------
