module ACheck(aMCheck, aSMCheck, aSignalCheck, aSMethCheck) where

import Util(allSame)
import PPrint
import IntLit
import ErrorUtil(internalError)
import Prim
import ASyntax
import ASyntaxUtil
import Params(isConstAExpr)
import Data.Maybe(isNothing)
import qualified Data.Set as S
import Data.List(foldl', genericLength)
import PreIds(idInout_)
import Debug.Trace

-- type check the the state elements, definitions, rules and interface
aMCheck :: APackage -> Bool
aMCheck apkg =
        all chkAVInst (apkg_state_instances apkg)
        && all chkADef (apkg_local_defs apkg)
        && all chkARule (apkg_rules apkg)
        && all chkAIface (apkg_interface apkg)

        -- XXX when module parameters carry an expr for default value,
        -- XXX check that here

        -- XXX if we wanted, we could check that the port list and
        -- XXX the VArgInfo at the top-level agree on types
        -- XXX (e.g., clock to clock, reset to reset)


-- type check the state elements, definitions and foreign function calls
-- scheduled package
aSMCheck :: ASPackage -> Bool
aSMCheck asp =
        all chkAVInst (aspkg_state_instances asp)
        && all chkADef (aspkg_values asp)
        && all chkADef (aspkg_inout_values asp)
        && all chkAForeignBlock (aspkg_foreign_calls asp)
        && chkDupWires asp
        -- XXX when module parameters carry an expr for default value,
        -- XXX check that here

-- make sure a wire is never defined twice in an ASPackage
chkDupWires :: ASPackage -> Bool
chkDupWires asp = tracePP "chkDupWires" dup_set (S.null dup_set)
  where (dup_set, _) = foldl' step_sets (S.empty, S.empty) all_names
        step_sets (dup_set, name_set) i | i `S.member` name_set = (S.insert i dup_set, name_set)
                                        | otherwise = (dup_set, S.insert i name_set)
        def_names  = [ i | ADef i _ _ _ <- aspkg_values asp ]
        state_outs = map fst (aspkg_state_outputs asp)
        params     = map fst (aspkg_parameters asp)
        inputs     = map fst (aspkg_inputs asp)
        inouts     = map fst (aspkg_inouts asp)
        all_names  = def_names ++ state_outs ++ params ++ inputs ++ inouts

-----

chkAVInst :: AVInst -> Bool
chkAVInst aa =
  let
      chkParam e = let t = chkAExpr e
                   in  isConstAExpr [] e && (isBit t || isString t || isReal t)
  in
    (tracePP "chkAVInst Params" aa $ all chkParam (getParams aa)) &&
    (tracePP "chkAVInst Ports"  aa $ all (isBitOrInout_ . chkAExpr) (getPorts aa)) &&
    (tracePP "chkAVInst Clocks" aa $ all (isClock . chkAExpr) (getClocks aa)) &&
    (tracePP "chkAVInst Resets" aa $ all (isReset . chkAExpr) (getResets aa)) &&
    (tracePP "chkAVInst Inouts" aa $ all (isInout_ . chkAExpr) (getInouts aa))


chkADef :: ADef -> Bool
chkADef aa@(ADef _ t e _) =
    let et = chkAExpr e
    in if t == et
        then True
        else internalError ("chkADef "
                ++ ppReadable aa
                ++ ": (" ++ show aa ++ ") "
                ++ ppReadable t ++ " /= " ++ ppReadable et)

chkARule :: ARule -> Bool
chkARule aa@(ARule _ _ _ _ p as asmps _) =
    tracePP "chkARule" aa $ chkAExpr p == aTBool && all chkAAction as && all chkAAssumption asmps

chkAAssumption :: AAssumption -> Bool
chkAAssumption aa@(AAssumption p as) =
    tracePP "chkAAssumption" aa $ chkAExpr p == aTBool && all chkAAction as

chkAIface :: AIFace -> Bool
chkAIface aa@(AIDef { aif_value = d,
                      aif_assumps = asmps  }) =
    tracePP "chkAIface AIDef" aa $ chkADef d && all chkAAssumption asmps

chkAIface aa@(AIAction { aif_body = rs }) =
    tracePP "chkAIface AIAction" aa $ all chkARule rs

chkAIface aa@(AIActionValue { aif_value = d, aif_body = rs }) =
    tracePP "chkAIface AIActionValue" aa $ (all chkARule rs) && (chkADef d)
chkAIface aa@(AIClock { aif_clock = c }) =
    tracePP "chkAIface AIClock" aa $ chkAClock c

chkAIface aa@(AIReset { aif_reset = r }) =
    tracePP "chkAIface AIReset" aa $ chkAReset r

chkAIface aa@(AIInout { aif_inout = r }) =
    tracePP "chkAIface AIInout" aa $ chkAInout r

chkCond :: AType -> Bool
chkCond = isBit1

chkAAction :: AAction -> Bool
chkAAction aa@(ACall i m (c:es)) =
    tracePP "chkAAction ACall" aa $
        all (isBit . chkAExpr) es && chkCond (chkAExpr c)
chkAAction afc@(AFCall { aact_objid = i, aact_args = (c:es) }) =
    tracePP "chkAAction AFCall" afc $
        chkCond (chkAExpr c) && all (isForeignArg . chkAExpr) es
chkAAction ata@(ATaskAction { aact_args = (c:es) }) =
    tracePP "chkAAction ATaskAction" ata $
        chkCond (chkAExpr c) && all (isForeignArg . chkAExpr) es
chkAAction _ = False

chkAForeignBlock :: AForeignBlock -> Bool
chkAForeignBlock (clks, fcalls) = all chkAForeignCall fcalls

chkAForeignCall :: AForeignCall -> Bool
chkAForeignCall afc@(AForeignCall id fun (c:es) _ _) =
    tracePP "chkAForeignCall" afc $ (chkCond (chkAExpr c)) && all (isForeignArg . chkAExpr) es
chkAForeignCall afc = False

chkAExpr :: AExpr -> AType
chkAExpr e@(APrim _ t PrimMul es) =
        let ts = map chkAExpr es
            -- getBit (ATBit n) = n
            -- getBit _ = internalError("ACheck checkAExpr.getBit" ++ (show e))
        -- multiplication can widen or narrow the result
        in  if all isBit ts && isBit t  -- && sum (map getBit ts) == getBit t
            then
                t
            else
                internalError ("chkAExpr * : " ++ ppReadable e)
chkAExpr e@(APrim _ t PrimQuot es) =
        let ts = map chkAExpr es
            getBit (ATBit n) = n
            getBit _ = internalError("ACheck checkAExpr.getBit" ++ (show e))
        in  if all isBit ts && isBit t && (getBit t == getBit (ts!!0))
            then
                t
            else
                internalError ("chkAExpr * : " ++ ppReadable e)
chkAExpr e@(APrim _ t PrimRem es) =
        let ts = map chkAExpr es
            getBit (ATBit n) = n
            getBit _ = internalError("ACheck checkAExpr.getBit" ++ (show e))
        in  if all isBit ts && isBit t && (getBit t == getBit (ts!!1))
            then
                t
            else
                internalError ("chkAExpr * : " ++ ppReadable e)
chkAExpr e@(APrim _ t PrimConcat es) =
        let ts = map chkAExpr es
            getBit (ATBit n) = n
            getBit _ = internalError("ACheck checkAExpr.getBit" ++ (show e))
        in  if all isBit ts && isBit t && sum (map getBit ts) == getBit t
            then
                t
            else
                if not (isBit t) then internalError ("chkAExpr ++: result not bit type (" ++ ppString t ++ "): " ++ ppReadable e)
                else if not (all isBit ts) then internalError ("chkAExpr ++: some args not bit type (" ++ ppString ts ++ "): " ++ ppReadable e)
                else internalError ("chkAExpr ++: expression bitsize (" ++ ppString (getBit t) ++ ") does not match sum of args bitsizes (" ++ ppString (sum (map getBit ts)) ++ ") from (" ++ ppString ts ++ "): " ++ ppReadable e)
chkAExpr e@(APrim _ t op es) | isRelOp op =
        let ts = map chkAExpr es
        in  if t == aTBool && all isBit ts && allSame ts
                then t
                else internalError ("chkAExpr: relop " ++ ppReadable (e, t, ts))
chkAExpr e@(APrim _ t op [v]) | op == PrimSignExt || op == PrimZeroExt =
        case (chkAExpr v, t) of
        (ATBit n, ATBit m) | n <= m -> t
        _ -> internalError ("chkAExpr: " ++ ppReadable (e, chkAExpr v, t))
chkAExpr e@(APrim _ t PrimIf (c:es)) =
    if all ((compatTypesWthStr t) . chkAExpr) es && chkAExpr c == aTBool
    then t
    else internalError ("chkAExpr: if " ++ ppReadable (e, t))
chkAExpr e@(APrim _ t op es) | op == PrimPriMux || op == PrimMux =
        if f es
                then t
                else internalError ("chkAExpr: mux " ++ ppReadable t ++ ppReadable e)
  where f [] = True
        f (c:x:xs) = chkAExpr c == aTBool && compatTypesWthStr (chkAExpr x)  t && f xs
        f _ = internalError "chkAExpr mux"
-- XXX could check a little more
chkAExpr e@(APrim _ t PrimCase (x:v:ces)) =
        if compatTypesWthStr (chkAExpr v) t && chk ces
                then t
                else internalError ("chkAExpr: case " ++ ppReadable e)
  where chk [] = True
        chk (c:e:ces) = chkAExpr c == te && compatTypesWthStr (chkAExpr e) t && chk ces
        chk _ = False
        te = chkAExpr x


chkAExpr e@(APrim _ t PrimExtract es) =
        if all (isBit . chkAExpr) es
                then t
                else internalError ("chkAExpr: extract " ++ ppReadable e)
chkAExpr e@(APrim _ t op [e1, e2]) | isShift op =
        if chkAExpr e1 == t {- XXX && chkAExpr e2 == aTNat-}
                then t
                else internalError ("chkAExpr: shift " ++ ppReadable e)

chkAExpr e@(APrim _ arr_ty PrimBuildArray elem_es) =
    case arr_ty of
      ATArray sz elem_ty ->
          if (genericLength elem_es /= sz)
          then internalError ("chkAExpr: array size: " ++ ppReadable e)
          else if all ((compatTypesWthStr elem_ty) . chkAExpr) elem_es
               then arr_ty
               else internalError ("chkAExpr: array elems: " ++ ppReadable e ++
                                   ppReadable elem_ty ++
                                   ppReadable (map chkAExpr elem_es))
      _ -> internalError ("chkAExpr: array type: " ++ ppReadable (arr_ty, e))
chkAExpr e@(APrim _ ret_ty PrimArrayDynSelect es) =
  let err = internalError ("chkAExpr: array select: " ++ ppReadable e)
  in  case es of
        [arr_e, idx_e] ->
            case (chkAExpr arr_e) of
              (ATArray sz elem_ty) ->
                  if ((compatTypesWthStr ret_ty elem_ty) &&
                      isBit (chkAExpr idx_e))
                  then ret_ty
                  else err
              _ -> err
        _ -> err
chkAExpr e@(APrim _ ret_ty PrimArrayDynUpdate es) =
  -- These should not exist after IExpand
  internalError ("chkAExpr: array update: " ++ ppReadable e)
{-
  let err = internalError ("chkAExpr: array update: " ++ ppReadable e)
  in  case es of
        [arr_e, idx_e, val_e] ->
            case (chkAExpr arr_e) of
              arr_ty@(ATArray sz elem_ty) ->
                  if ((compatTypesWthStr ret_ty arr_ty) &&
                      (compatTypesWthStr elem_ty (chkAExpr val_e)) &&
                      isBit (chkAExpr idx_e))
                  then ret_ty
                  else err
              _ -> err
        _ -> err
-}

chkAExpr e@(APrim _ t PrimStringConcat es)
   | all isStringType (t : map chkAExpr es) = t
   | otherwise = internalError ("chkAExpr: string prim " ++ ppReadable (e, t, map chkAExpr es))

-- all other primitives
chkAExpr e@(APrim _ t op es) =
        if all ((== t) . chkAExpr) es
                then t
                else internalError ("chkAExpr: other " ++ ppReadable (e, t, map chkAExpr es))

chkAExpr e@(AMethCall t _ _ es) =
        if all (isBit . chkAExpr) es
                then t
                else internalError ("chkAExpr: methcall " ++ ppReadable e)
chkAExpr e@(AFunCall { ae_type = t, ae_args = es }) =
        if all (isForeignArg . chkAExpr) es
                then t
                else internalError ("chkAExpr: funcall " ++ ppReadable e)

chkAExpr (ASInt _ _ (IntLit _ _ i)) | i < 0 =
        internalError ("chkAExpr: negative constant: " ++ show i)
chkAExpr (ASInt _ t@(ATBit sz) (IntLit _ _ i)) =
        -- check that "log2(i+1) <= sz"
        -- or, in otherwords, "2^sz >  i"
        if (2^sz > i)
        then t
        else internalError ("chkAExpr: integer does not fit in size: " ++
                            ppReadable (i,sz))
chkAExpr (ASInt _ t (IntLit _ _ i)) =
        internalError ("chkAExpr: non-bit integer: " ++ ppReadable (t,i))

chkAExpr e@(ASClock t c) =
         if chkAClock c
           then t
           else internalError ("chkAExpr: invalid clock: " ++ ppReadable e)

chkAExpr e@(ASReset t r) =
        if chkAReset r
           then t
           else internalError ("chkAExpr: invalid reset: " ++ ppReadable e)

chkAExpr e@(ASInout t r) =
        if chkAInout r
           then t
           else internalError ("chkAExpr: invalid inout: " ++ show e)

chkAExpr e@(AMGate t _ _) =
        if isBit1 t
        then t
        else internalError ("chkAExpr: invalid clock gate: " ++ ppReadable e)

chkAExpr e = aType e

chkAClock :: AClock -> Bool
chkAClock (AClock { aclock_osc = osc, aclock_gate = gate }) = isBit1 (aType osc) && isBit1 (aType gate)

chkAReset :: AReset -> Bool
chkAReset (AReset { areset_wire = wire }) = isBit1 (aType wire)

chkAInout :: AInout -> Bool
chkAInout (AInout { ainout_wire = wire }) = isInout_ (aType wire)

isBit :: AType -> Bool
isBit (ATBit _) = True
isBit _ = False

isBit1 :: AType -> Bool
isBit1 (ATBit sz) = (sz == 1)
isBit1 _ = False

isString :: AType -> Bool
isString (ATString _) = True
isString _ = False

isReal :: AType -> Bool
isReal (ATReal) = True
isReal _ = False

isClock :: AType -> Bool
isClock t = t == aTClock

isReset :: AType -> Bool
isReset t = t == aTReset

isInout_ :: AType -> Bool
isInout_ (ATAbstract i _) = i == idInout_
isInout_ _ = False

isForeignArg :: AType -> Bool
isForeignArg  e = isBit e || isString e || isReal e
--isBitOrString :: AType -> Bool
--isBitOrString e = isBit e || isString e
isBitOrInout_ :: AType -> Bool
isBitOrInout_ e = isBit e || isInout_ e

-- compare 2 types considering string sizes
compatTypesWthStr :: AType -> AType -> Bool
compatTypesWthStr (ATString ms1) (ATString ms2) = isNothing ms1 || isNothing ms2 || ms1 == ms2
compatTypesWthStr (ATArray sz1 t1) (ATArray sz2 t2) = (sz1 == sz2) && (compatTypesWthStr t1 t2)
compatTypesWthStr t1 t2                         = t1 == t2


isRelOp :: PrimOp -> Bool
isRelOp p = p `elem` [ PrimEQ, PrimULE, PrimULT, PrimSLE, PrimSLT, PrimEQ3 ]

isShift :: PrimOp -> Bool
isShift p = p `elem` [ PrimSL, PrimSRL, PrimSRA ]

tracePP :: Show a => String -> a -> Bool -> Bool
tracePP s x True = True
tracePP s x False = trace ("acheck:" ++ s ++ "\n" ++ show x) False

------
-- Check that the names used in expression are all defined.
--
-- Available names:
--   ps = instantiation parameters
--   is = module inputs (clk, rst, method arguments, imported interface port)
--   ds = defined signals
--   souts = signal names created to attach to submodule ports
-- Expressions:
--   insts = expressions to instantiation
--   ds = expressions defining signals
--   fs = foreign function calls
--
-- Returns any names that are used but not defined.
--
aSignalCheck :: ASPackage -> [AId]
aSignalCheck (ASPackage _ fmod ps _ is ios insts souts ds iods fs _ _ _) =
    let
        pnames = [ i | (i,_) <- ps ]
        inames = [ i | (i,_) <- is ]
        ionames= [ i | (i,_) <- ios ]
        dnames = [ i | ADef i _ _ _ <- ds ]
        snames = [ i | (i,_) <- souts ]

        -- used in ASDef
        defs = dnames
        -- used in ASPort
        ports = inames ++ snames ++ ionames
        -- used in ASParam
        params = pnames

        -- XXX if parameters carried expressions for their default values,
        -- XXX we would check those uses here

        iexprs = concatMap avi_iargs insts
        dexprs = [ e | ADef i _ e _ <- ds ]
        iodexprs = [ e | ADef i _ e _ <- iods ]
        fexprs = concat [ clks ++ es ++ rsts | (clks, fcalls) <- fs,
                                               AForeignCall _ _ es _ rsts <- fcalls ]

        exprs = fexprs ++ iexprs ++ dexprs ++ iodexprs
        -- build set from the list
        defSet   = S.fromList defs
        portSet  = S.fromList ports
        paramSet = S.fromList params

    in
        checkUses defSet portSet paramSet exprs


-- return The list of all names not referenced in the given environments
checkUses :: S.Set AId -> S.Set AId -> S.Set AId -> [AExpr] -> [AId]
checkUses ds is ps es = concatMap (checkUse ds is ps) es

checkUse :: S.Set AId -> S.Set AId -> S.Set AId -> AExpr -> [AId]
checkUse ds is ps (APrim _ _ _ es)     = checkUses ds is ps es
checkUse ds is ps (AMethCall _ i m es) = checkUses ds is ps es  -- XXX check i and m ?
checkUse ds is ps (AMethValue _ i m)   = [] -- XXX check i and m ?
checkUse ds is ps (ATuple _ es)        = checkUses ds is ps es
checkUse ds is ps (ATupleSel _ e _)    = checkUse ds is ps e
checkUse ds is ps (ANoInlineFunCall _ _ _ es) = checkUses ds is ps es
checkUse ds is ps (AFunCall { ae_args = es }) = checkUses ds is ps es
-- because all of the expressions used are used by the ATaskAction
checkUse ds is ps (ATaskValue { })     = []
checkUse ds is ps (ASPort _ i)         = if (S.member i is) then [] else [i]
checkUse ds is ps (ASParam _ i)        = if (S.member i ps) then [] else [i]
checkUse ds is ps (ASDef _ i)          = if (S.member i ds) then [] else [i]
checkUse ds is ps (ASInt _ _ _)        = []
checkUse ds is ps (ASReal _ _ _)       = []
checkUse ds is ps (ASStr _ _ _)        = []
checkUse ds is ps (ASAny _ Nothing)    = []
checkUse ds is ps (ASAny _ (Just e))   = internalError ("aSignalCheck surviving ASAny: " ++ ppReadable e)
checkUse ds is ps (ASClock _ (AClock { aclock_osc = osc, aclock_gate = gate})) =
                                       (checkUse ds is ps osc) ++ (checkUse ds is ps gate)
checkUse ds is ps (ASReset _ (AReset { areset_wire = wire })) =
                                       checkUse ds is ps wire
checkUse ds is ps (ASInout _ (AInout { ainout_wire = wire })) =
                                       checkUse ds is ps wire
checkUse ds is ps (AMGate _ i c) = []  -- XXX check i and c ?

------

-- After aState, method calls should all have been converted to port
-- connections to submodules.  AMethCall and AMethValue should not
-- exist in the ASPackage.  Task and foreign function calls can still
-- exist.

-- AMOsc, AMGate, AMReset should also have been converted to port
-- connections.

aSMethCheck :: ASPackage -> Bool
aSMethCheck (ASPackage _ _ _ _ _ _ ss _ ds iods fs _ _ _) =
    all chkMethAVInst ss  &&
    all chkMethADef ds    &&
    all chkMethADef iods  &&
    all chkMethAForeignBlock fs


chkMethAExpr :: AExpr -> Bool
chkMethAExpr e@(AMethCall { }) =
    internalError ("chkMethAExpr: methcall " ++ ppReadable e)
chkMethAExpr e@(AMethValue { }) =
    internalError ("chkMethAExpr: methvalue " ++ ppReadable e)
chkMethAExpr e@(AMGate { }) =
    internalError ("chkMethAExpr: mgate " ++ ppReadable e)
chkMethAExpr (APrim _ _ _ es) = all chkMethAExpr es
chkMethAExpr (AFunCall { ae_args = es }) = all chkMethAExpr es
chkMethAExpr (ATaskValue { }) = True
-- Others don't have arguments to recurse
chkMethAExpr _ = True

-- Check the expressions in defs
chkMethADef :: ADef -> Bool
chkMethADef (ADef _ _ e _) = chkMethAExpr e

-- Check the expressions in instantiations
chkMethAVInst :: AVInst -> Bool
chkMethAVInst aa =
    all chkMethAExpr (getPorts aa) &&
    all chkMethAExpr (getInouts aa) &&
    all chkMethAExpr (getClocks aa) &&
    all chkMethAExpr (getResets aa)

-- Check the expressions in foreign blocks
chkMethAForeignBlock :: AForeignBlock -> Bool
chkMethAForeignBlock (clks, fcalls) = all chkMethAForeignCall fcalls

chkMethAForeignCall :: AForeignCall -> Bool
chkMethAForeignCall (AForeignCall _ _ es _ rsts) =
    all chkMethAExpr (es ++ rsts)
