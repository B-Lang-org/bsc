{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
module IExpandUtils(
        HPred, PExpr(..), pExprToHExpr, predToIExpr, pConj, pConjs,
        pAtom, pIf, pSel, normPConj,
        unsafeDerefHeap, HeapCell(..), uniqueStateName, newStateNo, getStateNo,
        HExpr, HeapData(..), HClock, HReset, HInout, HStateVar, HRules, HWireSet, HDef, HRule, HEFace,
        runG, G, GOutput(..),
        errG, errsG, deferErrors, eWarning, eWarnings, getElabProgressContext,
        eNoNF, addRules,
        pushTopModuleSchedNameScope, pushModuleSchedNameScope,
        popModuleSchedNameScope,
        pushRuleSchedNameScope, popRuleSchedNameScope,
        setRuleSchedNameScopeProgress, RuleElabProgress(..),
        pushIfcSchedNameScope, popIfcSchedNameScope,
        setIfcSchedNameScopeProgress, IfcElabProgress(..),
        addSubmodComments, {-getSubmodComments,-}
        addPort, getPortWires, savePortType,
        saveRules, getSavedRules, clearSavedRules, replaceSavedRules,
        setBackendSpecific, cacheDef,
        addStateVar, step, updHeap, getHeap, {- filterHeapPtrs, -}
        getSymTab, getDefEnv, getFlags, getCross, getErrHandle, getModuleName,
        getNewRuleSuffix, updNewRuleSuffix,
        mapPExprPosition,
        chkClockDomain, chkResetDomain, fixupActionWireSet,
        chkModuleArgument, chkModuleArgumentClkRst,
        getMethodsByClockDomain, getMethodsByReset,
        extractWireSet,
        addHeapCell, addHeapUnev, newClock, newReset,
        addHeapPred,
        addInputClock, addOutputClock, addInputReset, addOutputReset,
        getClkGateUses, clearClkGateUses, setClkGateUses,
        assertNoClkGateUses, addClkGateUse, addInhighClkGate,
        addGateUsesToInhigh, addGateInhighAttributes,
        chkClkArgGateWires, chkClkAncestry, chkClkSiblings,
        getInputResetClockDomain, setInputResetClockDomain,
        chkInputClockPragmas, chkIfcPortNames,
        getBoundaryClock, getBoundaryClocks, boundaryClockToName,
        getBoundaryReset, getBoundaryResets, boundaryResetToName, getInputResets,
        makeInputClk, makeInputRstn, makeOutputClk, makeOutputRstn,
        makeArgInout, makeIfcInout, getInoutWires,
        makeDomainToBoundaryIdsMap, getDomainToBoundaryIdsMap,
        findBoundaryClock, isClockAncestor,
        isPrimType, isParamOnlyType,
        HeapPointer, unheap, unheapU, shallowUnheap, unheapAll,
        toHeap, toHeapCon, toHeapWHNFCon,
        toHeapInferName, toHeapConInferName, toHeapWHNFConInferName,
        toHeapWHNF, toHeapWHNFInferName,
        realPrimOp,
        integerPrim, realPrim, stringPrim, charPrim, handleBoolPrim,
        strictPrim, condPrim,
        NameInfo, legalizeNameInfo,
        newIStateLoc, newIStateLocForRule,
        isNoInlinedFunc, isAggressive, setAggressive,
        getPragmas, setPragmas,
        cleanupFinalRules,
        heapCellToHExpr,
        canLiftCond,
        newFFCallNo,
        makeArgPortId, makeArgParamId,
        showTopProgress, showModProgress, showRuleProgress
) where

import Control.Monad(when, liftM)
import Control.Monad.State(StateT, runStateT, evalStateT, lift, liftIO,
                           gets, get, put, modify)
import Data.IORef
import System.IO.Unsafe
import Data.List
import Data.Maybe
import Data.Char(isAlphaNum)
import System.Time -- XXX: from old-time package
import Debug.Trace(traceM)
import qualified Data.Array as Array
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Generics as Generic

import Eval
import PPrint
-- import PVPrint
import PFPrint
import Flags
import Error(internalError, EMsg, ErrMsg(..), ErrorHandle, MsgContext,
             bsError, bsWarning, bsErrorWithContext, bsWarningWithContext,
             bsErrorWithContextNoExit, exitFail, closeOpenHandles)
import Position
import SymTab(SymTab, getIfcFlatMethodNames)
import PreStrings(s_unnamed)
import FStringCompat
import Id
import PreIds
import CType(TISort(..), StructSubType(..))
import VModInfo
import ISyntax
import ISyntaxUtil
import ISyntaxCheck(iGetKind)
import Prim
import Wires
import IWireSet
import Pragma(PProp(..), SPIdMap, substSchedPragmaIds,
              extractSchedPragmaIds, removeSchedPragmaIds)
import Util
import Verilog(vKeywords, vIsValidIdent)

import IOUtil(progArgs)
import ISyntaxXRef(mapIExprPosition, mapIExprPosition2)
import IStateLoc(IStateLoc, IStateLocPathComponent(..), StateLocMap,
                 newIStateLocTop, hasIgnore, isAddRules, isLoop, extendStateLocMap,
                 stateLocToPrefix, createSuffixedId,  hasHide, hasHideAll, stateLocToHierName)

{- DEBUGGING AIDS
import Util(getEnvDef,traces)
import System.IO.Unsafe(unsafePerformIO)

dump_hcells = unsafePerformIO $
    do env_bs_dump_hcells <- getEnvDef "BS_DUMP_HCELLS" ""
       return (read ("[" ++ env_bs_dump_hcells ++ "]"))
trace_hcell cell expr | cell `elem` dump_hcells = traceM ("hcell " ++ show cell ++ ": " ++ show expr)
                      | otherwise = return ()

-}

-----------------------------------------------------------------------------
-- Trace Flags

-- The comments for these flags are in IExpand

doProfile :: Bool
doProfile = elem "-trace-profile" progArgs
doTraceHeap :: Bool
doTraceHeap = elem "-trace-heap" progArgs
doTraceHeap2 :: Bool
doTraceHeap2 = length (filter (== "-trace-heap") progArgs) > 1
doTraceHeapAlloc :: Bool
doTraceHeapAlloc = elem "-trace-heap-alloc" progArgs
doTraceCache :: Bool
doTraceCache = elem "-trace-def-cache" progArgs
doTraceClock :: Bool
doTraceClock = elem "-trace-clock" progArgs
doDebugFreeVars :: Bool
doDebugFreeVars = elem "-debug-eval-free-vars" progArgs
doTracePortTypes :: Bool
doTracePortTypes = elem "-trace-port-types" progArgs
doTraceLoc :: Bool
doTraceLoc = elem "-trace-state-loc" progArgs

-----------------------------------------------------------------------------

type HPred = Pred HeapData

pAtom :: IExpr a -> Pred a
pAtom e = if isTrue e then PConj S.empty else PConj (S.singleton (PAtom e))

-- we're wrapping this in the G monad because pIf' should be in IO
-- using unsafePeformIO inside of it is a performance hack
pIf :: HExpr -> HPred -> HPred -> G HPred
pIf c t e = return $ pIf' c t e

-- expand heap references looking for PrimBNot to desugar
pIf' :: HExpr -> HPred -> HPred -> HPred
pIf' c@(IRefT _ _ (HeapData r)) t e =
  let (P p e') = heapCellToPExpr (unsafePerformIO (readIORef r))
  in case e' of
      (IAps (ICon _ (ICPrim _ PrimBNot)) [] [c']) ->
          pConj p (pIf' c' e t)
      _ -> pIf'' c t e
pIf' c t e = pIf'' c t e

pIf'' :: HExpr -> HPred -> HPred -> HPred
pIf'' (IAps (ICon _ (ICPrim _ PrimBNot)) [] [c]) t e = pIf' c e t
pIf'' c t@(PConj ts) e@(PConj es) =
    let te = ts `S.intersection` es
        ts' = ts `S.difference` te
        es' = es `S.difference` te
    in  if ts' == es' then t
        else PConj (S.insert (PIf c (PConj ts') (PConj es')) te)

pSel :: HExpr -> Integer -> [HPred] -> HPred
pSel idx idx_sz es =
  let getP (PConj p) = p
      common_ps = foldr1 S.intersection (map getP es)
      ps' = map (\ e -> (getP e) `S.difference` common_ps) es
  in  if (all S.null ps')
      then PConj common_ps
      else PConj (S.insert (PSel idx idx_sz (map PConj ps')) common_ps)

pConj :: Pred a -> Pred a -> Pred a
pConj (PConj ts1) (PConj ts2) = PConj (ts1 `S.union` ts2)

pConjs :: [Pred a] -> Pred a
pConjs ps = PConj (S.unions [ ts | PConj ts <- ps ])

isPAtom :: PTerm a -> Bool
isPAtom (PAtom _) = True
isPAtom _ = False

pairConj :: (Pred a, Pred b) -> (Pred a, Pred b) -> (Pred a, Pred b)
pairConj (t1, f1) (t2, f2) = (t1 `pConj` t2, f1 `pConj` f2)

-- like zipWith, but if one list is longer, keep those elements
listConj :: [Pred a] -> [Pred a] -> [Pred a]
listConj xs [] = xs
listConj [] ys = ys
listConj (x:xs) (y:ys) = (x `pConj` y) : listConj xs ys

-- normPConj inherits the performance hack of pIf
normPConj :: HPred -> G HPred
normPConj p = return $ normPConj' p

normPConj' :: HPred -> HPred
normPConj' (PConj ps) =
    let
        un (PConj ps) = S.toList ps

        f p@(PAtom _) = if p `elem` as then [] else [p]
        f (PIf c (PConj ts) (PConj es)) = un (pIf' c ts_norm es_norm)
          where ts' = map f (S.toList ts)
                ts_norm = PConj (S.fromList (concat ts'))
                es' = map f (S.toList es)
                es_norm = PConj (S.fromList (concat es'))
        f (PSel idx idx_sz es) = un (pSel idx idx_sz es_norm)
          where es' = map (map f . un) es
                es_norm = map (PConj . S.fromList . concat) es'

        -- the atoms
        (as, if_or_sels) = partition isPAtom (S.toList ps)

        -- merge all the PIf with common conditions
        ifmap = M.fromListWith pairConj
                    [(c, (t, e)) | PIf c t e <- if_or_sels ]
        mifs = [ PIf c t e | (c, (t, e)) <- M.toList ifmap ]
        -- remove the atoms that are already covered, and simplify
        mifs' = map f mifs

        -- merge all the PSel with common indices
        selmap = M.fromListWith listConj
                     [((idx, idx_sz), es) | PSel idx idx_sz es <- if_or_sels ]
        msels = [ PSel idx idx_sz es | ((idx, idx_sz), es) <- M.toList selmap ]
        -- remove the atoms that are already covered, and simplify
        msels' = map f msels

    in PConj (S.fromList (as ++ concat mifs' ++ concat msels'))

predToIExpr :: Pred a -> IExpr a
predToIExpr (PConj es) = foldr (ieAnd . pTermToIExpr) iTrue (S.toList es)

pTermToIExpr :: PTerm a -> IExpr a
pTermToIExpr (PAtom e) = e
pTermToIExpr (PIf c t e) = ieIfx itBit1 c (predToIExpr t) (predToIExpr e)
pTermToIExpr (PSel idx idx_sz es) =
    -- the default for out of range selection is True
    ieCase itBit1 idx_sz idx (map predToIExpr es) iTrue

-- An expression with an implicit condition.
data PExpr = P HPred HExpr
        deriving (Eq, Ord, Show, Generic.Data, Generic.Typeable)

instance PPrint PExpr where
    pPrint d prec (P p e) = pPrint d prec (iePrimWhen (iGetType e) (predToIExpr p) e)

pExprToHExpr :: PExpr -> HExpr
pExprToHExpr (P (PConj s) e) | S.null s = e
pExprToHExpr (P p e) = iePrimWhenPred (iGetType e) p e

---------------------------------------------------------------------------

-- test whether an expression is a valid condition to be lifted to the
-- predicate as part of aggressive implicit conditions
-- (method arguments cannot be lited and the value result of ActionValue
-- methods or foreign functions cannot be lifted)

-- XXX In rev 13458, this function was changed from monadic to use
-- XXX unsafePerformIO, as a workarounk for a mem leak (the same as is
-- XXX done for pIf).  Ravi suspected it might be a GHC bug?

-- Avoid exponential expansion by memoizing results.
-- XXX  Perhaps better would be to generate this info along with the p-term.

canLiftCond :: HExpr -> G Bool
canLiftCond e = return $ fst $ canLiftCond' M.empty e

canLiftCond' :: M.Map Int Bool -> HExpr -> (Bool, M.Map Int Bool)
-- value portion of an ActionValue
-- the select should only survive if it is surrounding a method call
-- or foreign function call, so no check of "e" is needed
canLiftCond' m (IAps (ICon i_sel ICSel { }) _ [e])
    | i_sel == idAVValue_ = (False, m)
-- dynamic selection from an array
-- (we could not treat this prim specially and instead just consider an
-- ICLazyArray liftable if all elements are liftable; but this is a more
-- aggressive optimization that only considers the selectable elems)
canLiftCond' m (IAps (ICon _ (ICPrim _ PrimArrayDynSelect))
                     [elem_ty, ITNum idx_sz] [arr_e, idx_e]) =
    case arr_e of
      ICon _ (ICLazyArray _ arr u) ->
          if (isJust u)
          then (False, m)
          else let cells = Array.elems arr
                   reachable_cells = take (2 ^ idx_sz) cells
                   cellToExpr (ArrayCell ptr ref) = IRefT elem_ty ptr ref
                   -- check the index and the reachable cells
                   es = (idx_e : map cellToExpr reachable_cells)
               in  canLiftCond'_List m es
      _ -> internalError ("canLiftCond': array: " ++ ppReadable arr_e)
canLiftCond' m (IAps f _ es) = canLiftCond'_List m (f:es)
-- method argument
canLiftCond' m (ICon _ (ICMethArg _)) = (False, m)
-- other arrays are unexpected
canLiftCond' m (ICon _ (ICLazyArray arr_ty arr u)) =
    internalError ("IExpandUtils.canLiftCond: unexpected array")
canLiftCond' m (ICon _ _) = (True, m)
canLiftCond' m ref@(IRefT t p r) =
    -- only follow references for which we haven't yet computed the answer
    case M.lookup p m of
      Nothing ->
          -- implicit conditions will have been dealt with previously,
          -- so we unheap with NoImp
          let (b, m') = canLiftCond' m (unheapNFNoImpEvil ref)
          in  (b, M.insert p b m')
      Just b  -> (b, m)
canLiftCond' m e =
    internalError ("IExpandUtils.canLiftCond unexpected " ++ (ppReadable e))

canLiftCond'_List :: M.Map Int Bool -> [HExpr] -> (Bool, M.Map Int Bool)
canLiftCond'_List m es =
    let fn e (b, accum_m) = if b then canLiftCond' accum_m e else (b, accum_m)
    in  foldr fn (True, m) es

-----------------------------------------------------------------------------


-- Test if a type is allowed in the residual program.

isPrimType :: IType -> Bool
-- Primitive interfaces
isPrimType (ITCon _ _ (TIstruct SInterface{} _)) = True
-- Primitive base types
isPrimType (ITCon i _ _) = i == idPrimAction ||
                           -- types allowed as module parameters
                           -- and foreign function arguments
                           i == idString ||
                           i == idReal ||
                           -- we could support Integer in some contexts
                           -- but choose not to
                           -- i == idInteger
                           i == idFmt || -- also not really a primitive
                           i == idClock ||
                           i == idReset
-- Primitive constructor applied to numeric type(s)
isPrimType (ITAp a t) | iGetKind t == Just IKNum = isPrimTAp a
-- Primitive arrays
isPrimType (ITAp (ITCon i _ _) elem_ty) | i == idPrimArray = isPrimType elem_ty
isPrimType _ = False

-- Primitive type applications
isPrimTAp :: IType -> Bool
isPrimTAp (ITCon _ _ (TIstruct SInterface{} _)) = True
isPrimTAp (ITCon i _ _) = i == idActionValue_ ||
                          i == idBit ||
                          i == idInout_
isPrimTAp (ITAp a t) | iGetKind t == Just IKNum = isPrimTAp a
isPrimTAp _ = False

isParamOnlyType :: IType -> Bool
isParamOnlyType t = t == itString || t == itReal

-----------------------------------------------------------------------------

type NameInfo = Maybe Id

legalizeNameInfo :: NameInfo -> NameInfo
legalizeNameInfo = liftM filterId
    where legalChar c = (isAlphaNum c) || (c == '_')
          filterId i = let b = filterFString legalChar (getIdBase i)
                           q = filterFString legalChar (getIdQual i)
                       in setIdBase (setIdQual i q) b

type HeapPointer = Int
-- type Heap s = STArray s HeapPointer (Maybe HeapCell)
-- immutable heap used at the end of evaluation
-- type IHeap = Array HeapPointer (Maybe HeapCell)
data HeapCell = HUnev { hc_hexpr :: HExpr, hc_name :: NameInfo }
              | HWHNF { hc_pexpr :: PExpr, hc_name :: NameInfo }
              | HNF { hc_pexpr :: PExpr, hc_wire_set :: HWireSet,
                      hc_name :: NameInfo }
              | HLoop { hc_name :: NameInfo }
        deriving (Show, Eq, Ord, Generic.Data, Generic.Typeable)

-- should I drop the predicate for better printing of error messages?
heapCellToHExpr :: HeapCell -> HExpr
heapCellToHExpr (HUnev { hc_hexpr = e }) = e
-- heapCellToHExpr (Harray { hc_hexpr = e }) = e
heapCellToHExpr (HWHNF { hc_pexpr = p }) = (pExprToHExpr p)
heapCellToHExpr (HNF { hc_pexpr = p }) = (pExprToHExpr p)
heapCellToHExpr (HLoop mn) = internalError ("heapCellToHExpr.HLoop: " ++ ppReadable mn)

heapCellToPExpr :: HeapCell -> PExpr
heapCellToPExpr (HWHNF { hc_pexpr = p }) = p
heapCellToPExpr (HNF { hc_pexpr = p }) = p
heapCellToPExpr (HUnev { hc_hexpr = e }) = internalError("heapCellToPExpr.HUnev: " ++ ppReadable e)
heapCellToPExpr (HLoop mn) = internalError ("heapCellToPExpr.HLoop: " ++ ppReadable mn)

instance PPrint HeapCell where
        pPrint d p (HUnev { hc_hexpr = e, hc_name = name}) =
            text "HUnev" <+> pPrint d p e <+> pPrint d 0 name
--        pPrint d p (Harray { hc_hexpr = e, hc_name = name}) =
--            text "Harray" <+> pPrint d p e <+> pPrint d 0 name
        pPrint d p (HWHNF { hc_pexpr = e, hc_name = name}) =
            text "HWHNF" <+> pPrint d p e <+> pPrint d 0 name
        pPrint d p (HNF { hc_pexpr = e, hc_name = name, hc_wire_set = ws}) =
            text "HNF" <+> pPrint d p e <+> pPrint d 0 name <+> pPrint d 0 ws
        pPrint d p (HLoop name) =
            text "HLoop" <+> pPrint d 0 name

newtype HeapData = HeapData (IORef (HeapCell))
  deriving (Generic.Data, Generic.Typeable)

{-
instance Eq HeapData where
  (==) a b = True

instance Ord HeapData where
  compare a b = EQ
-}

instance Show HeapData where
  show hd = ""

{-
instance PPrint HeapData where
  pPrint d p hd = text (show hd)
-}

instance Hyper HeapData where
  hyper (HeapData r) y = seq r y

-- Heap expressions are IExprs with the real heap reference type filled in
type HExpr = IExpr HeapData

-- other useful synonyms
type HClock = IClock HeapData
type HReset = IReset HeapData
type HInout = IInout HeapData
type HStateVar = IStateVar HeapData
type HRules = IRules HeapData
type HWireSet = IWireSet HeapData
type HRule = IRule HeapData
type HDef = IDef HeapData
type HEFace = IEFace HeapData

type RulesBlobs = [(Bool, (HClock, HReset), IStateLoc, HPred, HExpr)]

-- G is the main evaluator monad
-- a writer monad for expanding rules lazily (for PrimModuleFix)
-- it has a state monad (for result state)
-- layered on top of IO for IORefs and errors/warnings/progress messages
type G = StateT GState IO

-- only used for post-evaluation heap traversals
-- so unsafePerformIO is fine (the refs are no longer being modified)
unsafeDerefHeap :: HeapData -> HeapCell
unsafeDerefHeap (HeapData ref) = unsafePerformIO (readIORef ref)

-- read-only evaluator state
data GStateRO = GStateRO {
        errHandle :: !ErrorHandle,
        symtab :: !SymTab,
        -- lazy because computing the defenv may be expensive and (often) unnecessary
        defenv :: M.Map Id HExpr,
        checkMaxStep :: !Bool,
        maxStep :: !Integer,
        stepWarnInterval :: !Integer,
        flags :: !Flags
        }

-- full evaluator state
data GState = GState {
        stepNo       :: !Integer, -- evaluation step
        nextWarnStep :: !Integer, -- next step to issue an evaluation warning at
        profilingMap :: !(M.Map Id (M.Map Position Int)), -- map from definitions to number of entries for profiling

        stateNo      :: !Int, -- unique number for state variables

        -- Stores the pair "(x, next unique number to start with)".
        -- When "x" is instantiated a second time, to be named "x_1",
        -- we update the map to contain both "(x, 2)" and "(x_1, 1)".
        stateNameMap :: !(M.Map Id Int),

        -- Track names used within hierarchy for unquification of name of instances & loops
        stateLocMap    :: !StateLocMap,

        -- comments on submodule instances
        -- mapping an instance name to its user-added comments
        -- XXX we use Id, just to have a position around; String would do
        commentsMap    :: !(M.Map Id [String]),

        ffcallNo       :: !Int,   -- to generate unique names for ActionValue foreign function calls

        newClockId     :: !ClockId,  -- to generate unique ids for clocks
        newClockDomain :: !ClockDomain, -- to generate unique ids for clock families
        newResetId     :: !ResetId, -- to generate unique ids for resets

        hp             :: !HeapPointer, -- next unique id for a new heap reference

        -- This is a cache for "extractWires", so that it doesn't re-walk a
        -- a heap reference that we've already walked.
        -- XXX this could be stored in the heap cells?
        heapWires      :: !(M.Map HeapPointer HWireSet),

        -- XXX what is the Id? flattened name?
        vars           :: [(Id, HStateVar)], -- instantiated verilog modules
        portTypeMap    :: PortTypeMap, -- map of state var -> port -> type

        rules          :: HRules,    -- accumulated rules
        newRuleSuffix  :: Integer,   -- store for creating unique names when ruleNameCheck is off

        -- scope for scheduling attribute names
        schedNameScope  :: SchedNameScope,

        clock_domains  :: !(M.Map ClockDomain [HClock]), -- all clock objects
        all_resets     :: [HReset], -- all reset objects
        in_clock_info  :: [(HClock, InputClockInf)], -- input clock information
        out_clock_info :: [(HClock, OutputClockInf)], -- output clock information
        in_reset_info  :: [(HReset, ResetInf)], -- input reset information
        out_reset_info :: [(HReset, ResetInf)], -- output reset information

        ro             :: !GStateRO,      -- read-only state

        -- properties of the top-level def being compiled
        -- (these three fields could be in GStateRO, except that "pragmas"
        -- gets set when evaluating "primBuildModule" and we may eventually
        -- structure the evaluator to operate on multiple modules)
        mod_def_id :: Id,
        -- is the evaluation a no-lined function
        noinlined_func :: Bool,
        -- the pragmas for the top-level module
        pragmas :: [PProp],

        -- record when the gate of a clock is used
        used_clk_gates :: !(S.Set HClock),
        clk_gates_inhigh :: !(S.Set HClock),
        -- record when an input reset is used with a particular clock domain
        in_reset_clk_info :: !(M.Map HReset ClockDomain),
        -- map from clockdomain to the ids of boundary clocks in the domain
        -- (constructed after all input and output clocks are added)
        domain_to_boundary_id_map :: !(M.Map ClockDomain  [Id]),
        -- map of clock ancestry relationships
        -- entries are parent -> list of children
        clk_ancestry_map :: !(M.Map HClock [HClock]),
        -- the clock/reset for input ports
        port_wires    :: !(M.Map Id (HClock, HReset)),

        -- record whether the design is specific to a backend
        backend_specific :: !Bool,

        -- cache partially-evaluated top-level definitions
        defCache :: !(M.Map Id HExpr),

        -- used for moduleFix
        savedRules :: !RulesBlobs,

        -- whether a deferable error was reported
        badEvaluation :: !Bool,

        -- aggressive conditions
        aggressive_cond :: Bool
        }

initGState :: ErrorHandle -> Flags ->
              SymTab -> M.Map Id HExpr ->
              Id -> Bool -> [PProp] ->
              GState
initGState errh flags symt alldefs defId is_noinlined_func pps =
    let gsro = GStateRO { errHandle = errh,
                          symtab = symt,
                          checkMaxStep = redStepsMaxIntervals flags /= 0,
                          maxStep = redSteps flags,
                          stepWarnInterval = redStepsWarnInterval flags,
                          flags = flags,
                          defenv = alldefs
                        }
        gs = GState { stepNo = 0,
                      nextWarnStep = redStepsWarnInterval flags,
                      stateNo = 0,
                      stateNameMap = M.empty,
                      stateLocMap = M.empty,
                      commentsMap = M.empty,
                      ffcallNo = 0,
                      newClockId = initClockId,
                      newClockDomain = initClockDomain,
                      newResetId = initResetId,
                      hp = 0,
                      heapWires = M.empty,
                      vars = [],
                      portTypeMap = M.empty,
                      rules = iREmpty,
                      newRuleSuffix = 0,
                      schedNameScope = emptySchedNameScope,
                      profilingMap = M.empty,
                      clock_domains = M.empty,
                      all_resets = [],
                      in_clock_info = [],
                      out_clock_info = [],
                      in_reset_info = [],
                      out_reset_info = [],
                      ro = gsro,
                      mod_def_id =
                          -- convert the raw defId to the user-recognizable Id
                          setIdBaseString defId (init (getIdBaseString defId)),
                      noinlined_func = is_noinlined_func,
                      pragmas = pps,
                      used_clk_gates = S.empty,
                      clk_gates_inhigh = S.empty,
                      in_reset_clk_info = M.empty,
                      domain_to_boundary_id_map = M.empty,
                      clk_ancestry_map = M.empty,
                      port_wires = M.empty,
                      backend_specific = False,
                      defCache = M.empty,
                      savedRules = [],
                      badEvaluation = False,
                      aggressive_cond = aggImpConds flags
 }
    in  gs

data GOutput a = GOutput { go_clock_domains :: [(ClockDomain, [HClock])],
                           go_resets   :: [HReset],
                           go_state_vars :: [(Id, HStateVar)],
                           go_port_types :: PortTypeMap,
                           go_vclockinfo :: VClockInfo,
                           go_vresetinfo :: VResetInfo,
                           go_rules :: HRules,
                           go_steps :: Integer,
                           go_hp :: HeapPointer,
                           go_profile :: M.Map Id (M.Map Position Int),
                           go_comments_map :: [(Id,[String])],
                           go_backend_specific :: Bool,
                           go_ffcallNo :: Int,
                           goutput :: a }

runG :: ErrorHandle -> Flags ->
        SymTab -> M.Map Id HExpr ->
        Id -> Bool -> [PProp] -> G a ->
        IO (GOutput a)
runG errh flags symt alldefs defId is_noinlined_func pps gFn =
  do let gs = initGState errh flags symt alldefs defId is_noinlined_func pps
     (retval, gs') <- runStateT gFn gs
     -- convert the relevant info in the final GState into the GOutput
     do
         -- if any file handles were not closed, close them now
         closeOpenHandles errh
         -- this can produce warnings
         vresetinfo <- make_vresetinfo errh
                                       (in_reset_info gs')
                                       (out_reset_info gs')
                                       (in_reset_clk_info gs')
                                       (domain_to_boundary_id_map gs')
         let vclockinfo = make_vclockinfo (clk_gates_inhigh gs')
                                          (in_clock_info gs')
                                          (out_clock_info gs')
                                          (domain_to_boundary_id_map gs')
                                          (clk_ancestry_map gs')
         -- check that any gates marked as unused are not in the inhigh
         -- list (which accumulates gate uses)
         let should_be_unused = concat [ is | PPgate_unused is <- pps ]
             getClk hclk = do c <- lookup hclk (in_clock_info gs')
                              return (fst c)
             actually_used = mapMaybe getClk (S.toList (clk_gates_inhigh gs'))
             wrong_annotations = should_be_unused `intersect` actually_used
             mk_annotation_msg i = (getPosition i, EClkGateNotUnused (getIdBaseString i))
         when (not (null wrong_annotations)) $
             bsError errh (map mk_annotation_msg wrong_annotations)
         -- if there were deferred errors, they were reported to IO, so exit
         when (badEvaluation gs') $
             exitFail errh
         -- check that there is no fixed-point state that was left unhandled
         let rblobs = savedRules gs'
         when (not (null rblobs)) $
             internalError ("IExpandUtils.runG - unexpanded ruleblobs: " ++ ppReadable rblobs)
         return $ (GOutput {
                     go_clock_domains = (M.toList (clock_domains gs')),
                     go_resets = (all_resets gs'),
                     go_state_vars = reverse (vars gs'),
                     go_port_types = portTypeMap gs',
                     go_vclockinfo = vclockinfo,
                     go_vresetinfo = vresetinfo,
                     go_rules = rules gs',
                     go_steps = stepNo gs',
                     go_hp = hp gs',
                     go_profile = profilingMap gs',
                     go_comments_map = M.toList (commentsMap gs'),
                     go_backend_specific = backend_specific gs',
                     go_ffcallNo = ffcallNo gs',
                     goutput = retval
                    })

errG :: EMsg -> G a
errG emsg = errsG [emsg]

errsG :: [EMsg] -> G a
errsG emsgs = do
  errh <- getErrHandle
  ctx <- getElabProgressContext
  liftIO $ bsErrorWithContext errh ctx emsgs

-- report evaluation problems
-- defer exit until the end of evaluation
-- if there are no errors, this is a no-op
deferErrors :: [EMsg] -> G ()
deferErrors emsgs = when (not (null emsgs)) $ do
  s <- get
  put s { badEvaluation = True }
  let errh = errHandle (ro s)
  ctx <- getElabProgressContext
  liftIO $ bsErrorWithContextNoExit errh ctx emsgs

eWarning :: EMsg -> G ()
eWarning emsg = eWarnings [emsg]

eWarnings :: [EMsg] -> G ()
eWarnings emsgs = do
  errh <- getErrHandle
  ctx <- getElabProgressContext
  liftIO $ bsWarningWithContext errh ctx emsgs

-- compile-time expression failed to evaluate error utility
eNoNF :: HExpr -> G a
eNoNF e =
    let ty = iGetType e
        pos = getIExprPosition e
    in  errG (pos, ENoNF (ppString ty) (ppReadable e))
--    in  errG (pos, ENoNF (ppString ty) (show e))

-- depends on the invariant that
-- max steps is a multiple of stepWarnInterval (enforced by Flags)
-- and that stepWarnInterval > 0
step :: Id -> G ()
step i = do s <- get
            -- do common update
            let c = stepNo s
            let s' = s { stepNo = c + 1 }
            if (doProfile) then do
              let prof = profilingMap s
              let pos_map = M.singleton (getPosition i) 1
              let prof' = M.insertWith (M.unionWith (+)) i pos_map prof
              put (s' { profilingMap = prof' })
             else put s'

            let w = nextWarnStep s

            when (c == w) $ do
              let check = checkMaxStep (ro s)
              let m = maxStep (ro s)
              -- can only hit the max step if we would issue a warning
              if (check && c == m) then
                errG (getIdPosition i, ETooManySteps (pfpString i) (itos m))
               else do let w_i = stepWarnInterval (ro s)
                       let w' = w + w_i
                       when (badEvaluation s) $
                         errG (getIdPosition i, EStepsIntervalError (pfpString i) c w_i)
                       eWarning (getIdPosition i, WTooManySteps (pfpString i) c w' m)
                       s' <- get
                       when doProfile $ liftIO (putStrLn (ppReadable (profilingMap s')))
                       put s' { nextWarnStep = w' }

-- ---------------

addRules :: HRules -> G ()
addRules rs = do
  s <- get
  --traceM("AddRules: " ++ ppReadable rs)
  let curScope = schedNameScope s
      (curFrame, frames) = case curScope of
                             (f:fs) -> (f, fs)
                             _ -> internalError ("addRules: curFrame")
      cur_ns = snf_istateloc curFrame
      cur_cnt = snf_ignoreCount curFrame
      cur_nameMap = snf_nameMap curFrame
  -- we should not be in a rule/interface scope
  when (isJust (snf_elabProgress curFrame)) $
      internalError ("IExpandUtils.addRules: invalid elabProgress")

  flags <- getFlags
  suf <- getNewRuleSuffix
  -- this is like iRUnion, but with different attribute checking
  let cur_rules@(IRules sps1 rs1) = (rules s)
      (suf', rs') = uniquifyRules flags suf cur_rules rs
  updNewRuleSuffix suf'

  -- check the names in attributes of the new rules
  -- (any errors are deferred and it returns the rules without bad Ids)
  rs''@(IRules sps2 rs2) <- checkAddRulesAttributes cur_ns cur_nameMap rs'

  -- add the new rule names to the scope
  -- XXX The IRule should contain the right name to start with
  -- XXX rather than using remIStateLocPrefix (like popModuleSchedNameScope)
  let addFn (IRule { irule_name = rId } ) =
          (remIStateLocPrefix cur_ns rId, SNI_Rule rId)
      new_map_entries = map addFn rs2
      -- there should be no conflicts, when using remIStateLocPrefix
      conflictFn v1 v2 = internalError
                             ("addRules: conflict: " ++ ppReadable (v1,v2))
      cur_nameMap' = map_insertManyWith conflictFn new_map_entries cur_nameMap
      curFrame' = SchedNameFrame cur_ns cur_cnt cur_nameMap' Nothing
      newScope = (curFrame' : frames)
  --traceM("ADD: rs2 = " ++ ppReadable rs2)
  --traceM("ADD: new_map_entries = " ++ ppReadable new_map_entries)
  --traceM("ADD: map = " ++ ppReadable cur_nameMap')
  s <- get
  put (s { schedNameScope = newScope })
  -- add the rules themselves to the monad
  s <- get
  let new_rules =
          -- As the size of rs1 grows, it's more efficient to add to the front
          -- XXX We should consider a better data structure
          if (ruleNameCheck flags)
          then (IRules (sps1 ++ sps2) (rs1 ++ rs2))
          else (IRules (sps2 ++ sps1) (rs2 ++ rs1))
  put (s { rules = new_rules } )

checkAddRulesAttributes :: IStateLoc -> M.Map Id SchedNameInfo -> IRules a ->
                           G (IRules a)
checkAddRulesAttributes cur_ns idMap (IRules sps rs) =
  let
      mkErr i = (getIdPosition i, EUnknownRuleIdAttribute (pfpString i))
      mkWarn i = (getIdPosition i, WInlinedMethodIdAttribute (pfpString i))

      -- the rule Ids will be the global names (w/ hier and uniquified),
      -- the attributes on those rules will also have hierarchy prefixed
      -- to them, so we need to strip that off when checking for names
      -- in the scope.  (For names in "rs", use the global name, because
      -- "sps" will have been adjusted for uniquifiers in sync with "rs".)

      -- names of the rules being added (global names)
      definedIds = S.fromList $ map getIRuleId rs

      -- this folds over the attr names
      checkFn i accum@(accum_warns, accum_errs, accum_badIds) =
        if (S.member i definedIds)
        then accum
        else
          -- remove the hierarchy prefix
          let i' = remIStateLocPrefix cur_ns i
          in  case (M.lookup i' idMap) of
                Nothing ->
                    (accum_warns, ((mkErr i'):accum_errs), (i:accum_badIds))
                Just (SNI_Method False) ->
                    (((mkWarn i'):accum_warns), accum_errs, (i:accum_badIds))
                Just _ -> accum

      attrIds = extractSchedPragmaIds sps

      (warns, errs, badIds) = foldr checkFn ([], [], []) attrIds

      sps' = if (null badIds) then sps else removeSchedPragmaIds badIds sps
  in
      do --traceM("checkAddRules Attr: " ++ ppReadable (cur_ns, sps, rs))
         when (not (null warns)) $ eWarnings warns
         deferErrors errs
         --traceM("definedIds: " ++ ppReadable definedIds)
         --traceM("attrIds: " ++ ppReadable attrIds)
         return (IRules sps' rs)

-- ---------------

-- XXX Consider unifying the IStateLoc stack with this stack

-- XXX We also use this stack to keep track of elab progress, so
-- XXX consider giving it a better name (it's not just the schedname scope)

-- the lookup result for names in the current context
data SchedNameInfo =
         -- Method Name
         -- The Bool indicates whether it is at a synthesized boundary
         -- (if False, it is inlined, and we don't support references to
         -- inlined boundaries yet, so warn and ignore).
         -- If a rule is later added with the same name, warn about the
         -- name clash and have the rule shadow the method.
         SNI_Method Bool |
         -- Rule Name
         -- The Id is the qualified, uniquified name for the rule
         -- (its global name).  This is substituted into attributes in
         -- place of the name as it is visible in the attribute's scope.
         SNI_Rule Id
       deriving (Show, Eq, Ord)

instance PPrint SchedNameInfo where
    pPrint d p sni = text (show sni)

data SchedNameFrame =
         SchedNameFrame {
             -- hierarchy naming for this scope
             snf_istateloc :: IStateLoc,
             -- number of ignored levels that have been pushed
             -- (the number of pops remaining until this frame can be popped)
             -- (this is to avoid duplicating frames)
             snf_ignoreCount :: Integer,
             -- names available at this scope
             -- (populated by the parent, if any names remain visible,
             -- then with new names as they are added in the current scope)
             snf_nameMap :: M.Map Id SchedNameInfo,
             -- whether we are currently evaluating inside a rule/ifc;
             -- this should be Nothing when pushing/popping a frame
             snf_elabProgress :: Maybe ElabProgress
         }
       deriving (Show, Eq)

instance PPrint SchedNameFrame where
    pPrint d p snf =
          (text "SchedNameFrame" <+> pPrint d p ig <+> pPrint d p ns
                <+> pPrint d p ep) $$
          pPrint d p m
        where ig = snf_ignoreCount snf
              ns = snf_istateloc snf
              m = M.toList $ snf_nameMap snf
              ep = snf_elabProgress snf

data ElabProgress =
         EPRule
             Id       {- rule name/position -}
             Bool     {- has the "hide" property -}
             (Maybe RuleElabProgress) {- progress inside the rule -}
         |
         -- This should only occur at the top-level
         EPInterface
             (Maybe IfcElabProgress) {- progress inside the ifc -}
       deriving (Show, Eq)

instance PPrint ElabProgress where
    pPrint d p (EPRule i h rp) =
        pparen (p>0) $ text "Rule" <+> pPrint d 0 i <+>
                         pPrint d 0 h <+> pPrint d 0 rp
    pPrint d p (EPInterface ip) =
        pparen (p>0) $ text "Interface" <+> pPrint d 0 ip

data RuleElabProgress = REP_ExplicitCond | REP_Body | REP_ImplicitCond
       deriving (Show, Eq)

instance PPrint RuleElabProgress where
    pPrint d p (REP_ExplicitCond) = text "ExplicitCond"
    pPrint d p (REP_Body) = text "Body"
    pPrint d p (REP_ImplicitCond) = text "ImplicitCond"

data IfcElabProgress = IEP_OutputClock Id
                     | IEP_OutputReset Id
                     | IEP_OutputInout Id
                     | IEP_Method Id Bool {- MethodElabProgress -}
       deriving (Show, Eq)

instance PPrint IfcElabProgress where
    pPrint d p (IEP_OutputClock i) =
        pparen (p > 0) $ text "OutputClock" <+> pPrint d 0 i
    pPrint d p (IEP_OutputReset i) =
        pparen (p > 0) $ text "OutputReset" <+> pPrint d 0 i
    pPrint d p (IEP_OutputInout i) =
        pparen (p > 0) $ text "OutputInout" <+> pPrint d 0 i
    pPrint d p (IEP_Method i mp) =
        pparen (p > 0) $ text "Method" <+> pPrint d 0 i <+> pPrint d 0 mp

type SchedNameScope = [SchedNameFrame]

emptySchedNameScope :: SchedNameScope
emptySchedNameScope = []

incrSNFIgnoreCount :: SchedNameScope -> SchedNameScope
-- There should be a frame and it should not be in rule/ifc progress
incrSNFIgnoreCount (SchedNameFrame ns cnt nameMap Nothing : frames) =
    (SchedNameFrame ns (cnt + 1) nameMap Nothing : frames)
incrSNFIgnoreCount _ = internalError ("incrSNFIgnoreCount")


-- create the initial scope, in which only the top methods are visible
pushTopModuleSchedNameScope :: IType -> G ()
pushTopModuleSchedNameScope t = do
  symt <- getSymTab
  let ifcName = iGetIfcName $ iGetModIfcType t
      methNames = getIfcFlatMethodNames symt ifcName
      -- use True to indicate that these are top-level methods
      newNameMap = M.fromList [ (m, SNI_Method True) | m <- methNames ]
      newFrame = SchedNameFrame [] 0 newNameMap Nothing
  s <- get
  let -- the old scope should be empty, so ignore it
      newScope = [newFrame]
  put (s { schedNameScope = newScope })

-- When entering an inlined submodule, nothing from the parent is visible,
-- only the methods in the submodule's interface.
-- However, if this is an "ignore" level, then it's an internal BSC boundary
-- that the user should not be aware of, so it retains the parent visibility
-- (this handles the function "addRules" used internally by the compiler to
-- add user rules).
-- XXX If the user explicitly calls "addRules", we allow visibility to the
-- XXX parent, for backwards compatibility.
--
pushModuleSchedNameScope :: IStateLoc -> IType -> G ()
pushModuleSchedNameScope ns resTy = do
  symt <- getSymTab
  s <- get
  let oldScope = schedNameScope s
  let -- XXX For backwards compatibility, allow visibility in addRules.
      -- XXX For for-loops, we should create a new context and allow
      -- XXX indexing of iterations
      ign = (hasIgnore ns) || (isAddRules ns) || (isLoop ns)
      mIfcName = iMGetIfcName resTy
      methNames = case mIfcName of
                    Nothing -> []
                    Just ifcName -> getIfcFlatMethodNames symt ifcName
      newNameMap = M.fromList [ (m, SNI_Method False) | m <- methNames ]
      newFrame = SchedNameFrame ns 0 newNameMap Nothing
      -- if this is an "ignore" level, just update the old scope
      newScope = if ign
                 then incrSNFIgnoreCount oldScope
                 else (newFrame:oldScope)
  --traceM("PUSH: " ++ (ppReadable ((toTF ign, toTF (hasIgnore ns)), head newScope)))
  --traceM("PUSH: " ++ ppReadable (M.toList (snf_nameMap (head newScope))))
  put (s { schedNameScope = newScope })

pushRuleSchedNameScope :: Id -> Bool -> G ()
pushRuleSchedNameScope i hide = do
  s <- get
  let oldScope = schedNameScope s
  case oldScope of
    (curFrame@(SchedNameFrame { snf_elabProgress = Nothing }) : frames) -> do
      let newElabProgress = EPRule i hide Nothing
          newFrame = curFrame { snf_elabProgress = Just newElabProgress }
          newScope = (newFrame : frames)
      put (s { schedNameScope = newScope })
    _ -> internalError ("pushRuleSchedNameScope: " ++ ppReadable oldScope)

popRuleSchedNameScope :: G ()
popRuleSchedNameScope = do
  s <- get
  let oldScope = schedNameScope s
  case oldScope of
    (curFrame@(SchedNameFrame { snf_elabProgress = Just (EPRule {}) })
     : frames) -> do
      let newFrame = curFrame { snf_elabProgress = Nothing }
          newScope = (newFrame : frames)
      put (s { schedNameScope = newScope })
    _ -> internalError ("popRuleSchedNameScope: " ++ ppReadable oldScope)

setRuleSchedNameScopeProgress :: Maybe RuleElabProgress -> G ()
setRuleSchedNameScopeProgress mp = do
  s <- get
  let oldScope = schedNameScope s
  case oldScope of
    (curFrame@(SchedNameFrame { snf_elabProgress = Just (EPRule i h _) })
     : frames) -> do
      let newFrame = curFrame { snf_elabProgress = Just (EPRule i h mp) }
          newScope = (newFrame : frames)
      put (s { schedNameScope = newScope })
    _ -> internalError ("setRuleSchedNameScopeProgress: " ++ ppReadable oldScope)

pushIfcSchedNameScope :: G ()
pushIfcSchedNameScope = do
  s <- get
  let oldScope = schedNameScope s
  case oldScope of
    (curFrame@(SchedNameFrame { snf_elabProgress = Nothing }) : frames) -> do
      let newElabProgress = EPInterface Nothing
          newFrame = curFrame { snf_elabProgress = Just newElabProgress }
          newScope = (newFrame : frames)
      put (s { schedNameScope = newScope })
    _ -> internalError ("pushIfcSchedNameScope: " ++ ppReadable oldScope)

popIfcSchedNameScope :: G ()
popIfcSchedNameScope = do
  s <- get
  let oldScope = schedNameScope s
  case oldScope of
    (curFrame@(SchedNameFrame { snf_elabProgress = Just (EPInterface {}) })
     : frames) -> do
      let newFrame = curFrame { snf_elabProgress = Nothing }
          newScope = (newFrame : frames)
      put (s { schedNameScope = newScope })
    _ -> internalError ("popIfcSchedNameScope: " ++ ppReadable oldScope)

setIfcSchedNameScopeProgress :: Maybe IfcElabProgress -> G ()
setIfcSchedNameScopeProgress mp = do
  s <- get
  let oldScope = schedNameScope s
  case oldScope of
    (curFrame@(SchedNameFrame { snf_elabProgress = Just (EPInterface _) })
     : frames) -> do
      let newFrame = curFrame { snf_elabProgress = Just (EPInterface mp) }
          newScope = (newFrame : frames)
      put (s { schedNameScope = newScope })
    _ -> internalError ("setIfcSchedNameScopeProgress: " ++ ppReadable oldScope)

-- when exiting a submodule, put all the added rules from that scope
-- into the parent scope (adding the submodule qualifier, but making
-- sure that the names are still uniquified)
--
-- For backwards compatibility, we want uniquification to give the same
-- name at the top-level as it did before (uniquify in the order of eval).
-- The way we should add child rules to a parent is by prefixing the child
-- inst name to the child's rule names and then doing a new uniquify step
-- as if we were adding those rules with only the parent rules visible
-- (not with any rules above the parent).  That's because a module should
-- not have visibility into rules in the parent: a module should not have to
-- mysteriously refer to a rule "r_1" because a parent had a rule with the
-- same name.
-- XXX For now, we have that visibility; we need to clean this up.
--
popModuleSchedNameScope :: G ()
popModuleSchedNameScope = do
  s <- get
  let oldScope = schedNameScope s
  --traceM("POP: oldScope: " ++ ppReadable (head oldScope))
  case oldScope of
    -- when there are ignored levels to pop
    -- (and assert that the frame is not in rule/ifc progress)
    (SchedNameFrame ns cnt nameMap Nothing : frames) | (cnt > 0) -> do
        let newScope = (SchedNameFrame ns (cnt - 1) nameMap Nothing : frames)
        put (s { schedNameScope = newScope })
    -- otherwise, merge the current frame into its parent
    -- (and assert that neither frame is in rule/ifc progress)
    -- (actually, because of "primBuildModule", the parent could be in a rule)
    (curFrame : parentFrame : frames)
     | isNothing (snf_elabProgress curFrame)
       -- && isNothing (snf_elabProgress parentFrame)
       -> do
        let
            (SchedNameFrame _ _ cur_nameMap _) = curFrame
            -- preserve the parent's rule progress, b/c of "primBuildModule"
            (SchedNameFrame parent_ns parent_cnt parent_nameMap parent_ep)
                = parentFrame
            -- function to qualify cur names
            -- XXX This is what needs updating, to re-uniquify names
            rem_prefix = remIStateLocPrefix parent_ns
            -- remove method names while updating the rule names
            -- XXX the use of remIStateLocPrefix is what needs updating,
            -- XXX to re-uniquify names instead
            mkParentPair (i, SNI_Method {}) = Nothing
            mkParentPair (i, SNI_Rule ui) = Just (rem_prefix ui, SNI_Rule ui)
            -- update the parent frame
            new_map_entries = mapMaybe mkParentPair (M.toList cur_nameMap)
            -- there should not be conflicts
            -- XXX ignored levels can have conflicts when we try add to add
            -- XXX what was copied from the parent; this might argue for
            -- XXX keeping a separate list of just the new rules
            -- XXX (then we wouldn't do the filtering of methods, above)
            conflictFn v1 v2 | (v1 == v2) = v1
            conflictFn v1 v2 = internalError
                                 ("popModuleSchedNameScope: conflict: "
                                  ++ ppReadable (v1,v2))
            parent_nameMap' = map_insertManyWith conflictFn
                                  new_map_entries parent_nameMap
            parentFrame' =
                SchedNameFrame parent_ns parent_cnt parent_nameMap' parent_ep
            newScope = (parentFrame' : frames)
        --traceM("POP: add " ++ ppReadable (M.toList cur_nameMap))
        --traceM("POP: new " ++ ppReadable (M.toList parent_nameMap'))
        put (s { schedNameScope = newScope })
    _ -> internalError ("popModuleSchedNameScope: " ++ ppReadable oldScope)

-- XXX Functions to push and pop scope for for-loops?

remIStateLocPrefix :: IStateLoc -> Id -> Id
remIStateLocPrefix ns i =
  let prefix = getIdBaseString $ stateLocToPrefix ns
      i_str   = getIdBaseString i
      rem [] cs = cs
      rem (p:ps) (c:cs) | (p == c) = rem ps cs
      rem _ _ = internalError
                    ("remIStateLocPrefix: " ++ ppReadable (ns, (stateLocToPrefix ns, i)))
  in  setIdBaseString i (rem prefix i_str)

-- ---------------

addSubmodComments :: Id -> [String] -> G ()
addSubmodComments name [] = return ()
addSubmodComments name comments =
    do s <- get
       let oldmap = commentsMap s
       let newmap = M.insert name comments oldmap
       put (s { commentsMap = newmap })

{-
-- This code would be used if we wanted to remove entries from the table,
-- and attach comments directly to the IStateVar/AVInst.
-- Instead, we keep the entire table around in IModule.
getSubmodComments :: Id -> G (Maybe [String])
getSubmodComments name =
    do s <- get
       let cmap = commentsMap s
       case (M.lookup name cmap) of
           Nothing -> -- no comments for this submodule
                      return Nothing
           Just comments -> do
                      -- remove the comments from the map
                      let newcmap = M.delete name cmap
                      put (s { commentsMap = newcmap })
                      return (Just comments)
-}

-- ---------------

addPort :: Id -> HClock -> HReset -> G ()
addPort port_id hclk hrst = do
    s <- get
    let cmap = port_wires s
        cmap' = M.insert port_id (hclk, hrst) cmap
    put s { port_wires = cmap' }

getPortWires :: Id -> G HWireSet
getPortWires port_id = do
    s <- get
    let cmap = port_wires s
    case (M.lookup port_id cmap) of
        Nothing           -> return $ wsEmpty
        Just (hclk, hrst) -> return $ wsJoin (wsClock hclk) (wsReset hrst)

savePortType :: Maybe Id -> VName -> IType -> G ()
savePortType minst port t = do
  when doTracePortTypes $
    traceM ("savePortType " ++ ppString minst ++ "$"
            ++ ppString port ++ ": " ++ ppReadable t)
  s <- get
  let old_map = portTypeMap s
  let new_map = M.insertWith (flip M.union)
                         minst (M.singleton port t)
                         old_map
  put s { portTypeMap = new_map }

-- ---------------

saveRules :: (HClock, HReset) -> IStateLoc -> HPred -> HExpr -> G ()
saveRules curClkRstn ns p rs = do
  s <- get
  let agg = aggressive_cond s
  put (s { savedRules = (agg, curClkRstn, ns, p, rs) : savedRules s })


getSavedRules :: G RulesBlobs
getSavedRules = get >>= (return . savedRules)

clearSavedRules :: G ()
clearSavedRules = do
 s <- get
 put (s { savedRules = [] })

replaceSavedRules :: RulesBlobs -> G ()
replaceSavedRules blobs = do
 s <- get
 put (s { savedRules = blobs })

-- XXX where does this belong?
getInoutWires :: IInout a -> IWireSet a
getInoutWires inout =
    let hclk = getInoutClock inout
        hrst = getInoutReset inout
    in  wsAddReset hrst (wsClock hclk)

-- ---------------

setBackendSpecific :: G ()
setBackendSpecific =
  do s <- get
     put s { backend_specific = True }

-- ---------------

-- XXX check duplication of clock object
-- add a clock to the clock domain map for tracking
addClock :: HClock -> G ()
addClock c = do s <- get
                put s { clock_domains = M.insertWith (++) (getClockDomain c) [c] (clock_domains s) }

assertNoClkGateUses :: G ()
assertNoClkGateUses =
    do s <- get
       let gs = used_clk_gates s
       when (not (S.null gs)) $
           internalError
               ("unexpected unresolved clock gate uses")

-- get,set, clear primitives to manage clock gate uses around primBuildModule
getClkGateUses :: G (S.Set HClock)
getClkGateUses = get >>= (return . used_clk_gates)

clearClkGateUses :: G ()
clearClkGateUses = do
  s <- get
  put (s { used_clk_gates = S.empty })

setClkGateUses :: S.Set HClock -> G ()
setClkGateUses uses = do
  -- only reasonable to do if the use set is empty
  assertNoClkGateUses
  s <- get
  put (s { used_clk_gates = uses })

addClkGateUse :: HClock -> G ()
addClkGateUse c =
    do s <- get
       --traceM ("adding gate use = " ++ ppReadable c)
       put s { used_clk_gates = S.insert c (used_clk_gates s) }

addInhighClkGate :: HClock -> G ()
addInhighClkGate c =
    -- try to only add clocks which are input clocks
    case (getClockWires c) of
      -- It's a clock tuple of a module port for the oscillator and gate == 1
      IAps (ICon i (ICTuple {fieldIds = [i_osc, i_gate]})) []
           [osc@(ICon _ (ICModPort _)), gate] |
           i == idClock && i_osc == idClockOsc && i_gate == idClockGate &&
           isTrue gate
        -> do -- traceM ("is a boundary clock: " ++ ppReadable c)
              s <- get
              let old_set = clk_gates_inhigh s
              put s { clk_gates_inhigh = S.insert c old_set }
      _ -> do -- traceM ("not a boundary clock: " ++ ppReadable c)
              return ()

addGateUsesToInhigh :: G ()
addGateUsesToInhigh =
    do s <- get
       let gs = used_clk_gates s
       mapM_ addInhighClkGate (S.toList gs)
       s <- get
       put s { used_clk_gates = S.empty }

addGateInhighAttributes :: G()
addGateInhighAttributes =
  do s <- get
     pps <- getPragmas
     let inhigh_ids = concat [ is | PPgate_inhigh is <- pps ]
         inhigh_clocks = [ hc
                         | (hc,(i,_)) <- in_clock_info s
                         , i `elem` inhigh_ids
                         ]
     mapM_ addInhighClkGate inhigh_clocks
     return ()

-- XXX check duplication of name / wires / clock object
addInputClock :: HClock -> InputClockInf -> G ()
addInputClock clk ci = do
  s <- get
  let old_in_clock_info = in_clock_info s
  when doTraceClock $ traceM ("addInputClock: " ++ ppReadable (clk, getClockDomain clk, ci))
  put (s { in_clock_info = (clk, ci):old_in_clock_info})

-- XXX check duplication of name / wires / clock object
addOutputClock :: HClock -> OutputClockInf -> G ()
addOutputClock clk ci = do
  s <- get
  let old_out_clock_info = out_clock_info s
  when doTraceClock $ traceM ("addOutputClock: " ++ ppReadable (clk, getClockDomain clk, ci))
  put (s { out_clock_info = (clk, ci):old_out_clock_info})

getClockIds :: [(HClock, (Id, a))] -> [(HClock, Id)]
getClockIds = map (\ (c,(i,_)) -> (c, i))

getHClocks :: [(HClock, a)] -> [HClock]
getHClocks = map fst

-- returns Nothing if not found (could make that an internalError)
getBoundaryClock :: Id -> G (Maybe HClock)
getBoundaryClock i =
    do s <- get
       let clk_ids = getClockIds (out_clock_info s) ++
                     getClockIds (in_clock_info s)
       return (listToMaybe [c | (c, i') <- clk_ids, i' == i])

boundaryClockToName :: HClock -> G (Maybe Id)
boundaryClockToName c =
    do s <- get
       let clk_ids = getClockIds (out_clock_info s) ++
                     getClockIds (in_clock_info s)
       return (listToMaybe [i | (c', i) <- clk_ids, c == c'])

getBoundaryClocks :: G [HClock]
getBoundaryClocks =
    do s <- get
       let hclocks = getHClocks (out_clock_info s) ++
                     getHClocks (in_clock_info s)
       return hclocks

-- XXX check duplication of reset object
-- add a reset to the list of resets for tracking
addReset :: HReset -> G ()
addReset r = do s <- get
                put s { all_resets = r : (all_resets s) }

-- XXX check duplication of name / wires / reset object
addInputReset :: HReset -> ResetInf -> G ()
addInputReset rst ri = do
  s <- get
  let old_in_reset_info = in_reset_info s
  put (s { in_reset_info = (rst, ri):old_in_reset_info })

-- XXX check duplication of name / wires / reset object
addOutputReset :: HReset -> ResetInf -> G ()
addOutputReset rst ri = do
  s <- get
  let old_out_reset_info = out_reset_info s
  put (s { out_reset_info = (rst, ri):old_out_reset_info })

getResetIds :: [(HReset, (Id, a))] -> [(HReset, Id)]
getResetIds = map (\ (r,(i,_)) -> (r, i))

getHResets :: [(HReset, a)] -> [HReset]
getHResets = map fst

getBoundaryReset :: Id -> G (Maybe HReset)
getBoundaryReset i =
    do s <- get
       let rst_ids = getResetIds (out_reset_info s) ++
                     getResetIds (in_reset_info s)
       return (listToMaybe [r | (r, i') <- rst_ids, i' == i])

getBoundaryResets :: G [HReset]
getBoundaryResets =
    do s <- get
       let hresets = getHResets (out_reset_info s) ++
                     getHResets (in_reset_info s)
       return hresets

getInputResets :: G [HReset]
getInputResets =
    do s <- get
       return (getHResets (in_reset_info s))

boundaryResetToName :: HReset -> G (Maybe Id)
boundaryResetToName r =
    do s <- get
       let rst_ids = getResetIds (out_reset_info s) ++
                     getResetIds (in_reset_info s)
       return (listToMaybe [i | (r', i) <- rst_ids, r == r'])

setInputResetClockDomain :: HReset -> ClockDomain -> G ()
setInputResetClockDomain r clkdom = do
    s <- get
    let rc_map = in_reset_clk_info s
    let new_rc_map = M.insert r clkdom rc_map
    put (s { in_reset_clk_info = new_rc_map })

getInputResetClockDomain :: HReset -> G (Maybe ClockDomain)
getInputResetClockDomain r = do
    s <- get
    let rc_map = in_reset_clk_info s
    return (M.lookup r rc_map)

-- ---------------

maybeToPrefix :: Id -> Maybe String -> Id
maybeToPrefix def_prefix Nothing    = def_prefix
maybeToPrefix _          (Just str) = mkId noPosition (mkFString str)

findClockOscPrefix :: [PProp] -> Id
findClockOscPrefix pps =
    maybeToPrefix idCLK $ listToMaybe [ s | (PPCLK s) <- pps ]

findClockGatePrefix :: [PProp] -> Id
findClockGatePrefix pps =
    maybeToPrefix idCLK_GATE $ listToMaybe [ s | (PPGATE s) <- pps ]

findResetPortPrefix :: String -> [PProp] -> Id
findResetPortPrefix defRstName pps =
  let idrst = (mk_no . mkFString) defRstName
  in maybeToPrefix idrst $ listToMaybe [ s | (PPRSTN s) <- pps ]

findArgClockOscName :: [PProp] -> Id -> Maybe String
findArgClockOscName pps i =
    listToMaybe $ catMaybes [ lookup i ps | (PPclock_osc ps) <- pps ]

findArgClockGateName :: [PProp] -> Id -> Maybe String
findArgClockGateName pps i =
    listToMaybe $ catMaybes [ lookup i ps | (PPclock_gate ps) <- pps ]

findArgResetPortName :: [PProp] -> Id -> Maybe String
findArgResetPortName pps i =
    listToMaybe $ catMaybes [ lookup i ps | (PPreset_port ps) <- pps ]

findArgPortName :: [PProp] -> Id -> Maybe String
findArgPortName pps i =
    listToMaybe $ catMaybes [ lookup i ps | (PParg_port ps) <- pps ]

findArgParamName :: [PProp] -> Id -> Maybe String
findArgParamName pps i =
    listToMaybe $ catMaybes [ lookup i ps | (PParg_param ps) <- pps ]

-- ---------------

-- function to make clock/reset port Ids, for input clock/reset
makePrefixArgId :: Id -> Maybe String -> Id -> Id -> Id
makePrefixArgId id_base m_rename def_id prefix =
    let pos = getPosition id_base
        -- use this name if there's no explicit name
        name0 = if (id_base == def_id) then prefix else mkUSId prefix id_base
    in  case (m_rename) of
          Nothing         -> name0
          Just rename_str -> mkId pos (mkFString rename_str)

makeArgClockOscId :: [PProp] -> Id -> Id
makeArgClockOscId pps clk_id =
    let prefix = findClockOscPrefix pps
        m_rename = findArgClockOscName pps clk_id
    in  makePrefixArgId clk_id m_rename idDefaultClock prefix

makeArgClockGateId :: [PProp] -> Id -> Id
makeArgClockGateId pps clk_id =
    let prefix = findClockGatePrefix pps
        m_rename = findArgClockGateName pps clk_id
    in  makePrefixArgId clk_id m_rename idDefaultClock prefix

-- combine into one function
makeArgClockIds :: [PProp] -> Bool -> Id -> (Id, Maybe Id)
makeArgClockIds pps gated id_clk = (id_osc, toMaybe gated id_gate)
  where id_osc  = makeArgClockOscId pps id_clk
        id_gate = makeArgClockGateId pps id_clk


makeArgResetPortId :: String -> [PProp] -> Id -> Id
makeArgResetPortId defRstName pps rst_id =
    let prefix = findResetPortPrefix defRstName pps
        m_rename = findArgResetPortName pps rst_id
    in  makePrefixArgId rst_id m_rename idDefaultReset prefix

makeArgPortId :: [PProp] -> Id -> Id
makeArgPortId pps arg_id =
    let m_rename = findArgPortName pps arg_id
        pos = getPosition arg_id
    in  case (m_rename) of
          Nothing -> arg_id
          Just str -> mkId pos (mkFString str)

makeArgParamId :: [PProp] -> Id -> Id
makeArgParamId pps param_id =
    let m_rename = findArgParamName pps param_id
        pos = getPosition param_id
    in  case (m_rename) of
          Nothing -> param_id
          Just str -> mkId pos (mkFString str)

-- ---------------

makeIfcClockOscId :: [PProp] -> Id -> Id -> Id
makeIfcClockOscId pps clk_id rename_id =
    let prefix = findClockOscPrefix pps
    in  -- setPosition not needed because the rename id already has the pos
        mkUSId prefix rename_id

makeIfcClockGateId :: [PProp] -> Id -> Id -> Id
makeIfcClockGateId pps clk_id rename_id =
    let prefix = findClockGatePrefix pps
    in  -- setPosition not needed because the rename id already has the pos
        mkUSId prefix rename_id

-- combine into one function
makeIfcClockIds :: [PProp] -> Bool -> Id -> Id -> (Id, Maybe Id)
makeIfcClockIds pps gated id_clk rename_id = (id_osc, toMaybe gated id_gate)
  where id_osc  = makeIfcClockOscId pps id_clk rename_id
        id_gate = makeIfcClockGateId pps id_clk rename_id


makeIfcResetPortId :: String -> [PProp] -> Id -> Id -> Id
makeIfcResetPortId defRstName pps rst_id rename_id =
    let prefix = findResetPortPrefix defRstName pps
    in  -- setPosition not needed because the rename id already has the pos
        mkUSId prefix rename_id

makeIfcInoutPortId :: Id -> Id -> Id
makeIfcInoutPortId inout_id rename_id =
    -- setPosition not needed because the rename id already has the pos
    rename_id

-- ---------------

-- Given a clock Id, make a clock, the abstract input, and the VArgInfo.
-- (the default clock is assumed to be idDefaultClock)
makeInputClk :: Bool -> Id ->
                G (HClock, IAbstractInput, VArgInfo)
makeInputClk gated id_clk = do
  when doTraceClock $ traceM "makeInputClk\n"
  pps <- getPragmas

  let (id_osc, mid_gate) = makeArgClockIds pps gated id_clk

  let topClkOsc = ICon id_osc (ICModPort itBit1)
  let topClkGate = case mid_gate of
                     Just id_gate -> ICon id_gate (ICModPort itBit1)
                     Nothing -> iTrue
  let abs_input = IAI_Clock id_osc mid_gate
  let varginfo = ClockArg id_clk

  -- consult clock_family and clock_ancestors pragmas to determine
  -- if this input clock belongs in an existing family
  same_family_as <- findFamilyMember id_clk
  -- consult clock_ancestors pragmas to identify any relationships
  -- involving this clock
  ancestor_edges <- findParentsAndChildren id_clk
  clk <- newClock (makeClockWires topClkOsc topClkGate)
                  same_family_as ancestor_edges

  let vp_osc = id_to_vName id_osc
  let vp_gate = case (mid_gate) of
                    Nothing -> -- we assume the gate is unused, and adjust
                               -- it later if it needs to be inhigh
                               Left False
                    Just id_gate -> Right (id_to_vName id_gate)
  addInputClock clk (id_clk, Just (vp_osc, vp_gate))

  return (clk, abs_input, varginfo)

makeOutputClk :: Bool -> Id -> Id -> HClock -> G VFieldInfo
makeOutputClk gated id_clk port_id clk = do
   let gate_high = isTrue (getClockGate clk)
   when ((not gated) && (not gate_high)) $
        errG (getPosition id_clk,
              EUnexpectedOutputClkGate (getIdString (unQualId id_clk)))

   -- XXX unQualId VModInfo
   pps <- getPragmas

   let (id_osc, mid_gate) = makeIfcClockIds pps gated (unQualId id_clk) port_id

   let vp_osc = id_to_vName id_osc
   let vp_gate =
           case (mid_gate) of
               Nothing -> Nothing
               Just id_gate -> let portprops = if gate_high then [VPouthigh]
                                                            else []
                               in  Just (id_to_vName id_gate, portprops)
   -- XXX why use the qualified name here and not the others?
   -- XXX does the Id ever come qualified?
   addOutputClock clk (id_clk, Just (vp_osc, vp_gate))

   -- XXX unQualId VModInfo
   return (Clock (unQualId id_clk))

-- Given a reset Id, make a reset, the abstract input, and the VArgInfo.
-- (the default reset is assumed to be idDefaultReset)
-- Also, an optional clock Id is given, if the reset is to be associated
-- with a specific clock domain (the domain of that clock).
makeInputRstn :: Id -> Maybe Id ->
                 G (HReset, IAbstractInput, VArgInfo)
makeInputRstn id_rst mclk = do
  when doTraceClock $ traceM "makeInputRstn\n"
  flags <- getFlags
  pps <- getPragmas

  let id_wire = makeArgResetPortId (resetName flags) pps id_rst
  topRstnClock <- case mclk of
                    Nothing -> return noClock
                    Just n  -> do -- until we support recursive instantiation,
                                  -- this clock will only be an input clock
                                  c <- getBoundaryClock n
                                  let err = "IExpand.makeInputRstn: " ++
                                            "unknown boundary clock"
                                  return (fromJustOrErr err c)
  let topRstnWire = ICon id_wire (ICModPort itBit1)
  let abs_input = IAI_Reset id_wire
  let varginfo = ResetArg id_rst
  rstn <- newReset topRstnClock topRstnWire
  addInputReset rstn (id_rst, (Just (id_to_vName id_wire), mclk))
  return (rstn, abs_input, varginfo)

-- This requires that the domain_to_boundary_ids_map has been made
makeOutputRstn :: Position -> Id -> Id -> HReset -> G VFieldInfo
makeOutputRstn mod_pos id_rst port_id rstn = do
  -- XXX unQualId VModInfo
  flags <- getFlags
  pps <- getPragmas

  let id_wire = makeIfcResetPortId (resetName flags) pps (unQualId id_rst) port_id

  -- is the value an input reset
  top_in_resets <- getInputResets
  let isInputReset r = r `elem` top_in_resets

  -- the clock written in the reset value
  let rst_clk :: HClock
      rst_clk = getResetClock rstn

  -- if the rst is an input reset and the clock is no_clock,
  -- then look to see if we've deduced an associated clock domain
  -- and, if so, use that domain instead
  -- XXX check for (rst_clkdom == noClockDomain)?
  clkdom <- if (isInputReset rstn) && (rst_clk == noClock)
            then do deduced_clkdom <- do
                        mclkdom <- getInputResetClockDomain rstn
                        -- consider no uses of the reset to be noClock
                        return $ fromMaybe noClockDomain mclkdom
                    if (deduced_clkdom /= noClockDomain)
                      then return deduced_clkdom
                      else return (getClockDomain rst_clk)
            else return (getClockDomain rst_clk)

  -- find a boundary clock in the same domain
  domainToIdsMap <- getDomainToBoundaryIdsMap
  let mClkName = findBoundaryClock domainToIdsMap clkdom

  when (isNothing mClkName && clkdom /= noClockDomain) $
       eWarning (mod_pos,
                 WOutputResetNoBoundaryClock (getIdString (unQualId id_rst)))

  -- XXX why use the qualified name here and not the others?
  -- XXX does the Id ever come qualified?
  addOutputReset rstn (id_rst, (Just (id_to_vName id_wire), mClkName))

  -- XXX unQualId VModInfo
  return (Reset (unQualId id_rst))

-- Given an inout Id, make an inout, the abstract input, and the VArgInfo.
-- (the default clock/reset is assumed to be idDefaultClock/idDefaultReset)
-- Also, an optional clock Id and reset Id are given, if the inout is to be
-- associated with a specific clock domain (the domain of that clock) or
-- specific reset.
makeArgInout ::  Id -> Integer -> Maybe Id -> Maybe Id ->
                 G (HInout, IAbstractInput, VArgInfo)
makeArgInout id_iot sz mclk mrst = do
  when doTraceClock $ traceM "makeArgInout\n"
  -- to make a better Verilog name (based on user attributes)
  pps <- getPragmas

  let id_wire = makeArgPortId pps id_iot
  topIotClock <- case mclk of
                    Nothing -> return noClock
                    Just n  -> do -- until we support recursive instantiation,
                                  -- this clock will only be an input clock
                                  c <- getBoundaryClock n
                                  let err = "IExpand.makeArgInout: " ++
                                            "unknown boundary clock"
                                  return (fromJustOrErr err c)
  topIotReset <- case mrst of
                    Nothing -> return noReset
                    Just n  -> do -- until we support recursive instantiation,
                                  -- this clock will only be an input clock
                                  r <- getBoundaryReset n
                                  let err = "IExpand.makeArgInout: " ++
                                            "unknown boundary clock"
                                  return (fromJustOrErr err r)
  let topIotWire = ICon id_wire (ICModPort (itInout_N sz))
      iinout = makeInout topIotClock topIotReset topIotWire
  let abs_arg = IAI_Inout id_wire sz
  let varginfo = InoutArg (id_to_vName id_wire) mclk mrst
  return (iinout, abs_arg, varginfo)

makeIfcInout :: Position -> Id -> Id -> HInout ->
                G (WireProps, VFieldInfo)
makeIfcInout  mod_pos id_iot port_id inout = do
  let hclk = getInoutClock inout
      hrst = getInoutReset inout
  let id_wire = makeIfcInoutPortId id_iot port_id
  -- make the WireSet
  let clkdom = getClockDomain hclk
      rstid = getResetId hrst
      ws = WireProps (Just clkdom) [rstid]
  -- find the clock
  boundaryClocks <- getBoundaryClocks
  mclk <- if (hclk == noClock)
          then return Nothing
          else if hclk `elem` boundaryClocks
          then boundaryClockToName hclk
          else do eWarning (getPosition id_iot,
                            WIfcInoutNoBoundaryClock (pfpString id_iot))
                  return Nothing
  -- find the reset
  boundaryResets <- getBoundaryResets
  mrst <- if (hrst == noReset)
          then return Nothing
          else if hrst `elem` boundaryResets
          then boundaryResetToName hrst
          else do eWarning (getPosition id_iot,
                            WIfcInoutNoBoundaryReset (pfpString id_iot))
                  return Nothing
  -- make the VFieldInfo
  let fi = Inout { vf_name = id_iot,
                   vf_inout = id_to_vName id_wire,
                   vf_clock = mclk,
                   vf_reset = mrst }
  return (ws, fi)


-- For making the clock and reset parts of VModInfo, construct
-- a map from clockdomain to the boundary clock ids in that domain
makeDomainToBoundaryIdsMap :: G ()
makeDomainToBoundaryIdsMap = do
    s <- get
    let in_cinfos  = in_clock_info s
        out_cinfos = out_clock_info s
        clk_ids = getClockIds out_cinfos ++ getClockIds in_cinfos
        new_map = M.fromListWith (++)
                      [ (getClockDomain c, [n]) | (c, n) <- clk_ids ]
    put (s { domain_to_boundary_id_map = new_map })

getDomainToBoundaryIdsMap :: G (M.Map ClockDomain [Id])
getDomainToBoundaryIdsMap = do
    s <- get
    return (domain_to_boundary_id_map s)

-- Given a clock, find a boundary clock in the same domain
findBoundaryClock :: M.Map ClockDomain [Id] -> ClockDomain -> Maybe Id
findBoundaryClock domainToIdsMap clkdom =
    case (M.lookup clkdom domainToIdsMap) of
        Just (clk:_) -> Just clk
        _            -> Nothing


-- add a clock relationship to the clk_ancestry_map
addClockChild :: (HClock, HClock) -> G ()
addClockChild (parent,child) = do
    s <- get
    let cam = clk_ancestry_map s
        cam' = M.insertWith (++) parent [child] cam
    put (s { clk_ancestry_map = cam' })

-- test if one clock is an ancestor of another
isClockAncestor :: HClock -> HClock -> G Bool
isClockAncestor ancestor child = do
    s <- get
    return $ canReach (clk_ancestry_map s) child ancestor
  where canReach cam to from =
            (from == to) ||
            (any (canReach cam to) (M.findWithDefault [] from cam))

make_vclockinfo :: S.Set HClock ->
                   [(HClock, InputClockInf)] -> [(HClock, OutputClockInf)] ->
                   M.Map ClockDomain [Id] -> M.Map HClock [HClock] ->
                   VClockInfo
make_vclockinfo inhighs in_cinfos out_cinfos domainToIdsMap cam =
    ClockInfo (map snd in_cinfos') (map snd out_cinfos') ancestorPairs sameFamilyPairs
  where
        -- list of boundary clock names broken up by domain
        namesList = map snd (M.toList domainToIdsMap)
        namesToFamilyPairs []  =  []
        namesToFamilyPairs (a : rest) = map (pair a) rest
        sameFamilyPairs = concatMap namesToFamilyPairs namesList

        -- list of (ancestor,child) clock pairs in terms of boundary
        -- ids in the same family
        getHClock i = let in_matches  = [ hc | (hc,(i',_)) <- in_cinfos
                                             , i == i'
                                        ]
                          out_matches = [ hc | (hc,(i',_)) <- out_cinfos
                                             , i == i'
                                        ]
                      in headOrErr ("make_vclockinfo: unknown clock" ++ (show i))
                                   (in_matches ++ out_matches)
        all_pairs = [ (p,c)
                    | same <- namesList
                    , p <- same
                    , c <- same
                    , p /= c
                    ]
        can_reach to from =
            (from == to) ||
            (any (can_reach to) (M.findWithDefault [] from cam))
        ancestorPairs = [ (p,c) | (p,c) <- all_pairs
                                , let hc = getHClock c
                                , let hp = getHClock p
                                , hc /= hp
                                , can_reach hc hp
                        ]

        -- adjust the clockinfs of input clocks
        -- to indicate inhigh for appropriate gates
        adjustInhigh ci@(clk, clkinf) =
            let adjClkinf (i, Just (vp_osc, Left _)) =
                    (i, Just (vp_osc, Left True))
                adjClkinf x =
                    internalError ("adjustInhigh: unexpected clockinf: " ++
                                   ppReadable x)
            in  if (S.member clk inhighs)
                then (clk, adjClkinf clkinf)
                else ci
        in_cinfos' = map adjustInhigh in_cinfos

        -- output clock gates already have VPouthigh in their Clockinf,
        -- and an error has already been triggered for output clocks
        -- with no gate port where the gate value is not 1
        -- (this is done in makeOutputClock)
        out_cinfos' = out_cinfos


-- this is in IO so that it can issue warnings
make_vresetinfo :: ErrorHandle ->
                   [(HReset, ResetInf)] -> [(HReset, ResetInf)] ->
                   M.Map HReset ClockDomain ->
                   M.Map ClockDomain [Id] ->
                   IO VResetInfo
make_vresetinfo errh in_rinfos out_rinfos rstClkDomMap domainToIdsMap = do
    let getInRstClkDom r = M.lookup r rstClkDomMap
        -- find the boundary clock to be associated with an input reset
        updateInputResetClock (r, (i, (mp, Nothing))) =
            let default_result = (r, (i, (mp, Nothing)))
                mk_result clk = (r, (i, (mp, Just clk)))
                do_warn = do bsWarning errh
                               [(getPosition i,
                                 WInputResetNoBoundaryClock (getIdString i))]
            in  case (getInRstClkDom r) of
                  Just dom | (dom /= noClockDomain) ->
                      case (findBoundaryClock domainToIdsMap dom) of
                          Just clk -> return (mk_result clk)
                          Nothing -> do do_warn
                                        return default_result
                  _ -> return default_result
        updateInputResetClock ri = return ri

    -- update the input infos
    in_rinfos' <- mapM updateInputResetClock in_rinfos

    -- no change to output infos
    let out_rinfos' = out_rinfos

    return $ ResetInfo (map snd in_rinfos') (map snd out_rinfos')


-- This is used by IExpand.newState to both
-- (1) check that submodule gate ports are connected to True when required
-- (2) record any boundary clocks connected to input clocks which have the
--     requirement (for adding it to that clock at the end of evaluation)
chkClkArgGateWires :: String -> String -> Position ->
                      [InputClockInf] -> [(Id, HClock, Int)] -> G ()
chkClkArgGateWires modName instName pos clockinfs clockargnum_map =
    let
        -- whether a clock arg's gate is required to be 1
        clockGateInhigh clk_id =
            case (lookup clk_id clockinfs) of
              Nothing -> internalError ("IExpand.newState: " ++
                                        "clockarg not in clockinfo: " ++
                                        ppReadable clk_id)
              Just (Just (_, Left b)) -> b
              Just _ -> False
        gates_which_need_inhigh =
            let f (clk_id, _, _) = clockGateInhigh clk_id
            in filter f clockargnum_map

        -- clock args to be reported as errors
        bad_gates =
            let gateNotHigh (_, clk_expr, _) =
                    not (isTrue (getClockGate clk_expr))
            in  filter gateNotHigh gates_which_need_inhigh

        -- while we're at it, record which clocks were inhigh
        -- (addInhighClkGate will record only the ones which are
        -- boundary clocks with gate ports)
        gates_to_add = nub $ map snd3 gates_which_need_inhigh

        -- error for non-inhigh gates
        mkErr clkName = (pos, EClkGateNotInhigh modName instName clkName)
    in
        case (bad_gates) of
            [] -> mapM_ addInhighClkGate gates_to_add
            bs -> errsG $ map (mkErr . getIdString . fst3) bs


chkInputClockPragmas :: [VArgInfo] -> G ()
chkInputClockPragmas vargs = do
    pps <- getPragmas
    let
        getClkIds (PPgate_input_clocks is) = is
        getClkIds (PPclock_family is)      = is
        getClkIds (PPclock_ancestors ils)  = nub (concat ils)
        getClkIds _                        = []
        -- Ids referenced in input clock pragmas
        pp_ids = concatMap getClkIds pps
        -- Ids of actual clock inputs
        clk_ids = [ i | ClockArg i <- vargs ]
        -- pragma Ids which don't match any clocks
        bad_pp_ids = filter (\i -> not (elem i clk_ids)) pp_ids
        mkErr i = (getPosition i, EAttributeIdNotAnInputClock (getIdString i))
     in  case (bad_pp_ids) of
            [] -> return ()
            (b:_) -> -- XXX G only allows reporting one error?
                     errG $ mkErr b


-- This is used by IExpand.newState to check that clocks marked as
-- siblings are in the same clock domain.
chkClkSiblings :: String -> String -> Position -> [(Id,Id)] ->
                  [(Id, HClock, Int)] -> G ()
chkClkSiblings modName instName pos siblings clockargnum_map =
    let -- list of clock pairs that should be siblings but aren't
        not_actually_siblings = [(getIdString i1, getIdString i2)
                                | (i1, c1, n1) <- clockargnum_map
                                , (i2, c2, n2) <- clockargnum_map
                                , i1 /= i2
                                , not (sameClockDomain c1 c2)
                                , (i1,i2) `elem` siblings
                                ]
    in when (not (null (not_actually_siblings))) $
           errG (pos, EClockArgSiblings modName instName not_actually_siblings)


-- This is used by IExpand.newState to check that clocks marked as
-- ancestors actually have the stated ancestry relationship.
chkClkAncestry :: String -> String -> Position -> [(Id,Id)] ->
                  [(Id, HClock, Int)] -> G ()
chkClkAncestry modName instName pos ancestors clockargnum_map =
    do let to_check = [ (c1,c2) | (i1, c1, n1) <- clockargnum_map
                                , (i2, c2, n2) <- clockargnum_map
                                , i1 /= i2
                                , (i1,i2) `elem` ancestors
                      ]
       is_correct <- mapM (\(p,c) -> isClockAncestor p c) to_check
       cam <- gets clk_ancestry_map
       -- list of clock pairs that have incorrect ancestry
       let bad_relationships = [ x | (False,x) <- zip is_correct to_check ]
           clk_name c = case [ i | (i,c',_) <- clockargnum_map, c == c' ] of
                          [i] -> getIdString i
                          _   -> internalError $ "chkClkAncestry: could not find unique name for clock"
           err_pairs = [ (clk_name p, clk_name c)
                       | (p,c) <- bad_relationships
                       ]
       -- generate errors if any incorrect relationships were found
       when (not (null err_pairs)) $
           errG (pos, EClockArgAncestors modName instName err_pairs)

chkIfcPortNames :: ErrorHandle -> [IAbstractInput] -> [HEFace] -> VClockInfo -> VResetInfo -> IO ()
chkIfcPortNames errh args ifcs (ClockInfo ci co _ _) (ResetInfo ri ro) =
    when (not (null emsgs)) $ bsError errh emsgs
  where
    input_clock_ports i =
      case lookup i ci of
        Just (Just (VName o, Right (VName g))) -> [o, g]
        Just (Just (VName o, Left _)) -> [o]
        _ -> []
    output_clock_ports i =
      case lookup i co of
        Just (Just (VName o, Just (VName g, _))) -> [o, g]
        Just (Just (VName o, Nothing)) -> [o]
        _ -> []
    input_reset_ports i =
      case lookup i ri of
        Just (Just (VName r), _) -> [r]
        _ -> []
    output_reset_ports i =
      case lookup i ro of
        Just (Just (VName r), _) -> [r]
        _ -> []

    arg_port_names = [ (getIdBaseString i, i) | IAI_Port (i, _) <- args ]
    arg_inout_names = [ (getIdBaseString i, i) | IAI_Inout i _ <- args ]
    arg_clock_names = [ (n, i) | IAI_Clock i _ <- args, n <- input_clock_ports i ]
    arg_reset_names = [ (n, i) | IAI_Reset i <- args, n <- input_reset_ports i ]

    default_clock_names = [ (n, idDefaultClock) | n <- input_clock_ports idDefaultClock ]
    default_reset_names = [ (n, idDefaultReset) | n <- input_reset_ports idDefaultReset ]

    arg_names = sort $
      arg_port_names ++ arg_inout_names ++ arg_clock_names ++ arg_reset_names ++
      default_clock_names ++ default_reset_names

    ifc_port_names =
      [ (n, i)
      | IEFace {ief_fieldinfo = Method i _ _ _ ins out en} <- ifcs,
        (VName n, _) <- ins ++ maybeToList out ++ maybeToList en ]
    ifc_inout_names =
      [ (n, i) | IEFace {ief_fieldinfo = Inout i (VName n) _ _} <- ifcs ]
    ifc_clock_names =
      [ (n, i) | IEFace {ief_fieldinfo = Clock i} <- ifcs, n <- output_clock_ports i ]
    ifc_reset_names =
      [ (n, i) | IEFace {ief_fieldinfo = Reset i} <- ifcs, n <- output_reset_ports i ]
    ifc_names = sort $ ifc_port_names ++ ifc_inout_names ++ ifc_clock_names ++ ifc_reset_names

    -- ---------------
    -- check that no ifc port name clashes with another port name and
    -- check that no ifc port name clashes with a Verilog keyword and
    -- check that each ifc port name is a valid Verilog identifier
    ifc_same_name = filter (\xs -> (length xs) > 1) $
                        groupBy (\(n1,_) (n2,_) -> n1 == n2) ifc_names
    ifc_kw_clash  = filter (\(n,_) -> n `elem` vKeywords) ifc_names
    ifc_bad_ident = filter (\(n,_) -> not (vIsValidIdent n)) ifc_names
    emsgs0 = let mkErr xs =
                      let ns = [(n, getPosition i, getIdBaseString i)
                                    | (n,i) <- xs ]
                      in  case ns of
                            ((v,p1,m1):(_,p2,m2):_) ->
                                (p1, EPortNamesClashFromMethod m1 m2 v p2)
                            _ -> internalError ("emsg0: impossible")
              in  map mkErr ifc_same_name
    emsgs1 = let mkErr (n,i) = (getPosition i,
                                EPortKeywordClashFromMethod
                                    (getIdBaseString i) n)
              in  map mkErr ifc_kw_clash
    emsgs2 = let mkErr (n,i) = (getPosition i,
                                EPortNotValidIdentFromMethod
                                    (getIdBaseString i) n)
              in  map mkErr ifc_bad_ident

    -- ---------------
    -- check that no arg port clashes with an ifc port
    ifc_ports_map = M.fromList ifc_names

    findIfcPortName (p, a) =
        case M.lookup p ifc_ports_map of
            Nothing -> Nothing
            Just m -> Just (p, m, a)

    arg_ifc_dups = catMaybes $ map findIfcPortName arg_names
    emsgs3 = let mkErr (p,m,a) = (getPosition a,
                                  EPortNamesClashArgAndIfc
                                      p (getIdBaseString a) (getIdBaseString m) (getPosition m))
              in map mkErr arg_ifc_dups

    emsgs = emsgs0 ++ emsgs1 ++ emsgs2 ++ emsgs3

-- ---------------

{-# INLINE newStateNo #-}
newStateNo :: G Int
newStateNo = do s <- get
                let n = stateNo s
                put (s { stateNo = n+1 })
                return n

-- disambiguates state names using stateNameMap
uniqueStateName :: Id -> G Id
uniqueStateName i = do
  s <- get
  let snmap = stateNameMap s
  case (M.lookup i snmap) of
    Nothing -> -- id is unused
     do let snmap' = M.insert i (1 :: Int) snmap
        put (s {stateNameMap = snmap'})
        return i
    Just n -> let loop n = case M.lookup i' snmap of
                               Nothing -> do let snmap'  = M.insert i (n+1) snmap
                                             let snmap'' = M.insert i' (1 :: Int) snmap'
                                             put (s {stateNameMap = snmap''})
                                             return i'
                               -- already used i_n
                               Just n' -> loop (n+1)
                      where i' = (createSuffixedId i (toInteger n))
              in
                 loop n -- kick off with first candidate suffix




-- create a new IStateLoc objct.
newIStateLoc :: Id -> Id -> IType -> IStateLoc -> G IStateLoc
newIStateLoc inst_id ifc_id ifc_type ns = do
  map <- gets stateLocMap
  let  ns' = newIStateLocTop map inst_id ifc_id ifc_type ns
  when doTraceLoc $ traceM ("NewStateLoc: " ++ ppReadable ((inst_id, ifc_id), ns'))
  return ns'


newIStateLocForRule :: Id -> Bool -> IStateLoc -> G IStateLoc
newIStateLocForRule  id hide ns@(islpc:_) = do
  let id'  = if (hide) then setHideId id else id
  isl <- newIStateLoc id' id' (isl_ifc_type islpc) ns
  -- update the stateLocMap
  s <- get
  let newMap = extendStateLocMap  (stateLocMap s) isl
  when doTraceLoc $ traceM ("NewRule: " ++ ppReadable isl)
  put (s {stateLocMap = newMap})
  return isl

newIStateLocForRule id hide [] = internalError "newIStateLocForRule: Empty loc"

-- --------------

traceProgress :: String -> G ()
traceProgress str = liftIO $ do
  ct <- getClockTime
  now <- toCalendarTime ct
  traceM ("[" ++ calendarTimeToString now ++ "] elab progress: " ++ str)

showTopProgress :: String -> G ()
showTopProgress str = do
  flags <- getFlags
  when (showElabProgress flags) $ traceProgress str

showModProgress :: IStateLoc -> String -> G ()
showModProgress ns str = do
  flags <- getFlags
  let showHidden = tclShowHidden flags
      hide = if showHidden
             then False
             else (hasHide ns) || (hasHideAll ns)
      ign  = (hasIgnore ns)
  when ((showElabProgress flags) && (not (hide || ign))) $
      let mod = case (stateLocToHierName ns showHidden) of
                  Nothing -> ""
                  Just m -> "(" ++ m ++ ") "
      in  traceProgress $ mod ++ str

showRuleProgress :: IStateLoc -> Bool -> String -> String -> G ()
showRuleProgress ns rhide name str = do
  flags <- getFlags
  let showHidden = tclShowHidden flags
      hide = if showHidden
             then False
             else rhide || (hasHideAll ns)
  when ((showElabProgress flags) && (not hide)) $
      let mod = case (stateLocToHierName ns showHidden) of
                  Nothing -> ""
                  Just m -> "(" ++ m ++ ") "
      in traceProgress $ mod ++ str ++ " (" ++ name ++ ")"

-- --------------

-- When reporting an error message, construct the context from the stack
getElabProgressContext :: G MsgContext
getElabProgressContext = do
  let addPos pos | (pos == noPosition) = ""
      addPos pos = " at " ++ prPosition pos
  flags <- getFlags
  s <- get
  let showHidden = tclShowHidden flags
      scope = schedNameScope s
  case scope of
    (SchedNameFrame ns _ _ ep : _) -> do
       let modprog =
               case ep of
                 Nothing -> empty
                 Just (EPRule i rhide mrp) ->
                     -- replicate the decision-making in "showRuleProgress"
                     let hide = if showHidden
                                then False
                                else rhide || (hasHideAll ns)
                     in  case mrp of
                           _ | hide -> empty
                           Nothing ->
                               s2par("During elaboration of rule " ++
                                     quote (getIdBaseString i) ++
                                     addPos (getPosition i) ++ ".")
                           Just REP_ExplicitCond ->
                               s2par("During elaboration of the explicit " ++
                                     "condition of rule " ++
                                     quote (getIdBaseString i) ++
                                     addPos (getPosition i) ++ ".")
                           Just REP_Body ->
                               s2par("During elaboration of the body " ++
                                     "of rule " ++
                                     quote (getIdBaseString i) ++
                                     addPos (getPosition i) ++ ".")
                           Just REP_ImplicitCond ->
                               s2par("During elaboration of the implicit " ++
                                     "condition of rule " ++
                                     quote (getIdBaseString i) ++
                                     addPos (getPosition i) ++ ".")
                 Just (EPInterface mip) ->
                     case mip of
                       Nothing ->
                           s2par("During elaboration of the interface.")
                       Just (IEP_OutputClock i) ->
                           s2par("During elaboration of the interface " ++
                                 "output clock " ++
                                 quote (getIdBaseString i) ++
                                 addPos (getPosition i) ++ ".")
                       Just (IEP_OutputReset i) ->
                           s2par("During elaboration of the interface " ++
                                 "output reset " ++
                                 quote (getIdBaseString i) ++
                                 addPos (getPosition i) ++ ".")
                       Just (IEP_OutputInout i) ->
                           s2par("During elaboration of the interface " ++
                                 "inout " ++
                                 quote (getIdBaseString i) ++
                                 addPos (getPosition i) ++ ".")
                       Just (IEP_Method i False) ->
                           s2par("During elaboration of the interface " ++
                                 "method " ++
                                 quote (getIdBaseString i) ++
                                 addPos (getPosition i) ++ ".")
                       Just (IEP_Method i True) ->
                           s2par("During elaboration of the implicit " ++
                                 "condition of the interface method " ++
                                 quote (getIdBaseString i) ++
                                 addPos (getPosition i) ++ ".")
       -- replicate the decision-making in "showModProgress"
       -- (could this be more efficient by not using abstracted funcs?)
       let convLocs [] = []
           convLocs cur_ns@(cur_islpc:parent_ns) =
               let hide = if showHidden
                          then False
                          else (hasHide cur_ns) || (hasHideAll cur_ns)
                   ign = hasIgnore cur_ns
                   -- replicate how InstNodes names the hierarchy
                   name = isl_inst_id cur_islpc
                   pos = getPosition name
                   finalName = maybe name (mkId pos) (getIdDisplayName name)
               in  if (hide || ign)
                   then convLocs parent_ns
                   else (finalName : convLocs parent_ns)
           loc_ids = convLocs ns
           top_id = mod_def_id s
           ppLocId i =
               s2par("During elaboration of " ++
                     quote (getIdBaseString i) ++
                     addPos (getPosition i) ++ ".")
       return (vcat (modprog : map ppLocId (loc_ids ++ [top_id])))
    _ -> internalError ("getElabProgressContext: " ++ ppReadable scope)

-- #############################################################################
-- #
-- #############################################################################

newFFCallNo :: G Int
newFFCallNo = do s <- get
                 let n = ffcallNo s
                 put (s { ffcallNo = n + 1 })
                 return n

-- create a clock given an expression for the wires
-- and (maybe) a family to add it to
-- and a list of parent (Left) and child (Right) clocks
-- be careful about what to display because this is called from newState
newClock :: HExpr -> Maybe (HClock) -> [Either HClock HClock] -> G HClock
newClock wires mclock ancestors = do
  s <- get

  -- this trace sometimes leads to loops
  -- because state elements with output clocks point to themselves
  -- traceM ("new clock: " ++ ppReadable wires)
  let clockid = newClockId s
  let clockid' = nextClockId clockid
  domain <- case mclock of
              Just clock -> do
                when doTraceClock $ traceM ("existing domain: " ++ (show (getClockDomain clock)))
                put (s { newClockId = clockid'})
                return (getClockDomain clock)
              Nothing -> do
                when doTraceClock $ traceM ("new domain")
                let domain  = newClockDomain s
                let domain' = nextClockDomain domain
                put ( s {newClockId = clockid', newClockDomain = domain'})
                return domain
  when doTraceClock $ traceM ("new clock id: " ++ (show clockid) ++
                              " domain: " ++ (show domain))
  let clock = makeClock clockid domain wires
  addClock clock
  let addAncestor (Left p)  = addClockChild (p,clock)
      addAncestor (Right c) = addClockChild (clock,c)
  mapM_ addAncestor ancestors
  return clock

-- make a reset given an expression for the signal
-- and its associated clock (possibly noClock)
-- be careful about what to display because this is called from newState
newReset :: HClock -> HExpr -> G HReset
newReset clock wire = do
  s <- get
  let resetid  = newResetId s
  let resetid' = nextResetId resetid
  put (s { newResetId = resetid'})
  when doTraceClock $ traceM ("new reset id: " ++ (show resetid))
  let reset = makeReset resetid clock wire
  addReset reset
  return reset

-- Given an name for an input clock, attempt to find an existing
-- clock in the same family based on the clock_family and clock_ancestors
-- module pragmas.  The name can be "" to indicate the default clock.
findFamilyMember :: Id -> G (Maybe HClock)
findFamilyMember clk_id =
  do pps <- getPragmas
     let fams  = [ is | (PPclock_family is) <- pps ]
         ancs  = [ is | (PPclock_ancestors ils) <- pps, is <- ils ]
         -- all families implied by clock_family and clock_ancestors
         all_families = transitive_union (fams ++ ancs) []
         -- Maybe the family containing the desired clock
         the_family = find (elem clk_id) all_families
     -- if we found a clock family, search for an existing clock
     -- associated with any member of the family
     case the_family of
       Nothing  -> return Nothing
       (Just f) -> do input_clk_info <- gets in_clock_info
                      return (listToMaybe [ hc
                                          | (hc,(i,_)) <- input_clk_info
                                          , i `elem` f
                                          ])
  where transitive_union []        disjoint = disjoint
        transitive_union (xs:rest) disjoint =
          let (no_overlap,overlap) = partition (null . (intersect xs)) disjoint
          in transitive_union rest (((concat overlap) `union` xs):no_overlap)

-- Given an name for an input clock, attempt to find existing clocks
-- which are parent or children of the clock, based on the clock_ancestors
-- module pragmas.  The name can be "" to indicate the default clock.
-- Left is used for parent, Right for children.
findParentsAndChildren :: Id -> G [Either HClock HClock]
findParentsAndChildren clk_id =
  do pps <- getPragmas
     let ancs  = [ is | (PPclock_ancestors ils) <- pps, is <- ils ]
         -- get all lists which mention the clock
         relevant = filter (clk_id `elem`) ancs
         -- turn the lists into a list of (parent,child) pairs
         pairs = concatMap to_pairs relevant
         -- extract lists of parent and child clocks
         parents  = [ p | (p,c) <- pairs, c == clk_id ]
         children = [ c | (p,c) <- pairs, p == clk_id ]
     -- map the clock Ids to HClocks
     input_clk_info <- gets in_clock_info
     let get_hclk x = listToMaybe [ hc | (hc,(i,_)) <- input_clk_info, i == x ]
         parents'  = map Left  (mapMaybe get_hclk parents)
         children' = map Right (mapMaybe get_hclk children)
     return (parents' ++ children')
  where to_pairs []         = []
        to_pairs [x]        = []
        to_pairs (a:b:rest) = (a,b):(to_pairs (b:rest))

addStateVar :: (Id, HStateVar) -> G ()
addStateVar v@(id,hsv) = do
  s <- get
  -- update the stateLocMap with this hierarchy path to avoid conflicts later
  let newMap = extendStateLocMap (stateLocMap s) (isv_isloc hsv)
  --
  when doTraceLoc $ traceM $ ("New state var: " ++ ppReadable (id))
  put (s { vars = v : vars s
         ,stateLocMap = newMap})


{-
extendHeap :: G ()
extendHeap = do s <- get
                let oldtop = htop s
                let oldheap = heap s
                let newtop = 2 * oldtop
                newheap <- lift (lift (newArray (0, newtop - 1) Nothing))
                put s { heap = newheap, htop = newtop }
                let copycell  = \ (p :: HeapPointer) ->
                                   do c <- lift (lift (readArray oldheap p))
                                      lift (lift (writeArray newheap p c))
                mapM_ copycell ((uncurry enumFromTo) (bounds oldheap))
-}

addHeapCell :: String -> HeapCell -> G (HeapPointer, HeapData)
addHeapCell tag cell = do
  s <- get
  let p = hp s
  ref <- liftIO (newIORef (cell))
  put (s { hp = p+1 })
  when doTraceHeapAlloc $ traceM("addHeapCell(" ++ show p ++ "): " ++ tag ++ "\n")
  return (p, HeapData ref)

addHeapUnev :: String -> IType -> HExpr -> Maybe Id -> G HExpr
addHeapUnev tag t e cell_name = do
 let newcell = (HUnev { hc_hexpr = e, hc_name = cell_name })
 cross <- getCross
 (p, r) <- addHeapCell tag newcell
 -- trace_hcell p e
 let result = IRefT t p r
 when doTraceHeap $ traceM ("addHeapUnev " ++ ppString cell_name ++ " [" ++
                            prPositionConcise (getPosition cell_name) ++ "] " ++
                            ppReadable (result,t,e))
 return (mapIExprPosition cross (e, result))

-- add an expression to the heap, noting it is WHNF
addHeapWHNF :: String -> IType -> PExpr -> Maybe Id -> G HExpr
addHeapWHNF tag t pe cell_name = do
  let newcell = (HWHNF { hc_pexpr = pe, hc_name = cell_name })
  (p, r) <- addHeapCell tag newcell
  let result = IRefT t p r
  when doTraceHeap $ traceM ("addHeapWHNF " ++ ppString cell_name ++ " [" ++
                             prPositionConcise (getPosition cell_name) ++ "] " ++
                             ppReadable (result,t,pe))
  return result

{-
-- add an expression to the heap that is in NF
addHeapNF :: String -> IType -> PExpr -> HWireSet -> G HExpr
addHeapNF tag t pe ws = do
  let newcell = (HNF { hc_pexpr = pe, hc_wire_set = ws, hc_name = Nothing })
  (p, r) <- addHeapCell tag newcell
  let result = IRefT t p r
-- flags <- getFlags
-- mapIExprPosition flags?
  when doTraceHeap $ traceM ("addHeapNF " ++ ppReadable (result,t,pe))
  return result
-}

-- "evalPred" needs to create references for shared expressions.
-- It doesn't need to create full-fledged heap refs, since evaluation
-- is over at this point (the ref is NF, has no implicit condition and
-- no wireset), but heap refs are all that are available.
addHeapPred :: String -> HExpr -> G HExpr
addHeapPred _ e@(IRefT {}) = return e
addHeapPred tag e = do
  let t = itBit1       -- boolean condition
      pe = P pTrue e   -- no implicit condition
      ws = wsEmpty     -- no wire set
  let newcell = (HNF { hc_pexpr = pe, hc_wire_set = ws, hc_name = Nothing })
  (p, r) <- addHeapCell tag newcell
  let result = IRefT t p r
  when doTraceHeap $ traceM ("addHeapPred " ++ ppReadable (result,e))
  return result

{-# INLINE getHeap #-}
getHeap :: HeapData -> G HeapCell
getHeap (HeapData ref) = liftIO (readIORef ref)

{-# INLINE updHeap #-}
updHeap :: String -> (HeapPointer, HeapData) -> HeapCell -> G ()
updHeap tag (p, HeapData ref) e = do
   o <- getHeap (HeapData ref)
   when doTraceHeap2 $
      traceM ("old val [" ++ tag ++ "]: " ++ "(_" ++ show p ++ ", " ++ ppReadable o ++ ")")
   when doTraceHeap $
      traceM ("updHeap [" ++ tag ++ "] " ++ "(_" ++ show p ++ ", " ++ ppReadable e ++ ")")
   let old_name  = hc_name o
   let new_name  = hc_name e
   let best_name = maybe old_name Just new_name
   let e' = e { hc_name = best_name }
   hyper best_name $ liftIO (writeIORef ref e')

{-
filterHeapPtrs :: (HeapCell -> Bool) -> G [HeapPointer]
filterHeapPtrs accept =
    do  state <- get
        let next_unused_addr = hp state
            filter_loop addr | addr == next_unused_addr = return []
                             | otherwise =
                                 do cell <- getHeap (HeapData addr)
                                    rest <- filter_loop (addr+1)
                                    return (if accept cell
                                            then addr:rest else rest)
        filter_loop 0
-}

{-# INLINE getStateNo #-}
getStateNo :: G Int
getStateNo = do s <- get
                return (stateNo s)

{-# INLINE getSymTab #-}
getSymTab :: G SymTab
getSymTab = do s <- get
               return (symtab (ro s))

{-# INLINE getDefEnv #-}
getDefEnv :: G (M.Map Id HExpr)
getDefEnv = do s <- get
               return (defenv (ro s))

{-# INLINE getFlags #-}
getFlags :: G Flags
getFlags = do s <- get
              return (flags (ro s))

{-# INLINE getCross #-}
getCross :: G Bool
getCross = do flags <- getFlags
              return (crossInfo flags)

{-# INLINE getErrHandle #-}
getErrHandle :: G ErrorHandle
getErrHandle = do s <- get
                  return (errHandle (ro s))

{-# INLINE getWireSetCache #-}
getWireSetCache :: G (M.Map HeapPointer HWireSet)
getWireSetCache = do s <- get
                     return (heapWires s)

{-# INLINE updWireSetCache #-}
updWireSetCache :: HeapPointer -> HWireSet -> G ()
updWireSetCache p ws = do
  s <- get
  let cache' = M.insert p ws (heapWires s)
  put s { heapWires = cache' }

{-# INLINE getModuleName #-}
getModuleName :: G String
getModuleName = do
  mid <- gets mod_def_id
  return (getIdBaseString mid)

{-# INLINE getNewRuleSuffix #-}
getNewRuleSuffix :: G Integer
getNewRuleSuffix = do s <- get
                      return (newRuleSuffix s)

{-# INLINE updNewRuleSuffix #-}
updNewRuleSuffix :: Integer -> G ()
updNewRuleSuffix suf = do
  s <- get
  put s { newRuleSuffix = suf }

-----------------------------------------------------------------------------

{-# INLINE unheap #-}
unheap :: PExpr -> G PExpr
unheap (P p e_orig@(IRefT _ _ r)) = do
        e <- getHeap r
        cross <- getCross
        case e of
            (HUnev {}) -> internalError ("IExpandUtils.unheap: unevaluated")
            (HLoop name) -> internalError("IExpandUtils.unheap: HLoop " ++ ppReadable name)
            (HWHNF { hc_pexpr = P _ (IRefT _ _ _) }) ->
                internalError ("IExpandUtils.unheap: WHNF IRefT")
            (HWHNF { hc_pexpr = P p' e, hc_name = n } ) ->
                return (P (pConj p p') (mapIExprPosition cross (e_orig, e)))
            (HNF { hc_pexpr = P _ (IRefT _ _ _) }) ->
                internalError ("IExpandUtils.unheap: NF IRefT")
            (HNF { hc_pexpr = P p' e }) ->
                return (P (pConj p p') (mapIExprPosition cross (e_orig, e)))

unheap pe = return pe

{-# INLINE unheapU #-}
unheapU :: HExpr -> G HExpr
unheapU e_orig@(IRefT _ _ r) = do
        e <- getHeap r
        flgs <- getFlags
        let cross = (crossInfo flgs)
        case e of
            (HUnev { hc_hexpr = e }) -> return e
            (HLoop name) -> internalError ("unheapU: HLoop " ++ ppReadable name)
            (HWHNF { hc_pexpr = P _ (IRefT _ _ _) } ) ->
                internalError ("unheapU: IRefT")
            (HWHNF { hc_pexpr = e, hc_name = n }) ->
                return (mapIExprPosition cross (e_orig, (pExprToHExpr e)))
            (HNF { hc_pexpr = e }) ->
                return (mapIExprPosition cross (e_orig, (pExprToHExpr e)))
unheapU e = return e

-- unheap more than the first cell, but not much more than that
{-# INLINE shallowUnheap #-}
shallowUnheap :: HExpr -> G HExpr
shallowUnheap e= do
  e' <- unheapU e
  case e' of
    IAps f ts es -> do es' <- mapM unheapU es; return (IAps f ts es')
    _ -> return e'

{-# INLINE unheapNFNoImp #-}
-- unheap dropping (inaccurate) implicit conditions
-- since implicit conditions are not reduced to NF until evalPred
unheapNFNoImp :: HExpr -> G HExpr
unheapNFNoImp e_orig@(IRefT _ _ r) = do
        e <- getHeap r
        flgs <- getFlags
        let cross = (crossInfo flgs)
        case e of
            (HUnev { }) -> internalError ("unheapNFNoImp: HUnev " ++ ppReadable (e_orig, e))
            (HLoop name) -> internalError ("unheapNFNoImp: HLoop " ++ ppReadable name)
            (HWHNF { }) -> internalError ("unheapNFNoImp: HWHNF " ++ ppReadable (e_orig, e))
            (HNF { hc_pexpr = (P _ e) }) ->
                return (mapIExprPosition cross (e_orig, e))
unheapNFNoImp e = return e

-- XXX use unsafePerformIO to work around an apparent monadic recursion bug
unheapNFNoImpEvil :: HExpr -> HExpr
unheapNFNoImpEvil (IRefT _ _ (HeapData c)) =
   case cell of
     HNF { hc_pexpr = (P _ e) } -> e
     _ -> internalError ("unheapNFNoImp - unexpected: " ++ ppReadable cell)
 where cell = unsafePerformIO (readIORef c)
unheapNFNoImpEvil e = e

{-
unheapUH :: Heap -> HeapPointer -> HExpr
unheapUH heap p =
        case I.lookup p heap of
            Nothing -> internalError "unheapUH: Nothing"
            Just (HUnev e) -> e
            Just (HWHNF (P _ (IRefT _ _ _))) -> internalError ("unheapUH: IRefT")
            Just (HWHNF e) -> (pExprToHExpr e)
            Just (HNF   e) -> (pExprToHExpr e)
-}

unheapAll :: HExpr -> G HExpr
unheapAll e = do
    e' <- unheapU e
    case e' of
        ILam i t e -> do e' <- unheapAll e; return (ILam i t e')
        IAps f ts es -> do f' <- unheapAll f; es' <- mapM unheapAll es; return (IAps f' ts es')
        ILAM i t e -> do e' <- unheapAll e; return (ILAM i t e')
        ICon i (ICLazyArray arr_t arr u) -> do
            let elem_ty = case arr_t of
                            (ITAp c t) | (c == itPrimArray) -> t
                            _ -> internalError ("unheapAll: array type")
                mapFn (ArrayCell ptr ref) = do
                    unheapAll (IRefT elem_ty ptr ref)
            es <- mapM mapFn (Array.elems arr)
            let ic = case icPrimBuildArray (length es) of
                       (ICon _ ci) -> ICon i ci
                       _ -> internalError ("unheapAll: icPrimBuildArray")
            return (IAps ic [elem_ty] es)
        _ -> return e'

-- unheapAll for NF with no implicit conditions
-- used for error reporting (clock domains and multiple resets, etc.)
unheapAllNFNoImp :: HExpr -> G HExpr
unheapAllNFNoImp e = do
    e' <- unheapNFNoImp e
    case e' of
        ILam i t e -> do e' <- unheapAllNFNoImp e; return (ILam i t e')
        IAps f ts es -> do f' <- unheapAllNFNoImp f; es' <- mapM unheapAllNFNoImp es; return (IAps f' ts es')
        ILAM i t e -> do e' <- unheapAllNFNoImp e; return (ILAM i t e')
        _ -> return e'

{-# INLINE toHeap #-}
toHeap :: String -> HExpr -> Maybe Id -> G HExpr
-- foreign function calls must be forced onto the heap for
-- proper handling of actionvalues
toHeap tag e@(ICon i (ICForeign {iConType = t})) cell_name = addHeapUnev tag t e cell_name
-- definitions must be heaped for correct handling of actionvalues
-- a top-level definition should have no free variables by construction
toHeap tag (ICon i (ICDef t e)) cell_name = do
  e' <- cacheDef i t e
  toHeap tag e' cell_name
toHeap tag e@(ICon _ _) cell_name = return e
toHeap tag e@(IRefT _ _ _) cell_name = return e -- XXX name improvement?
toHeap tag e cell_name = do
        -- these errors have never happened, disable checks for now.
        when (doDebugFreeVars && not (null (fVars e))) $
             internalError ("toHeap: fv " ++ ppReadable (fVars e) ++ ppReadable e)
        when (doDebugFreeVars && not (null (ftVars e))) $
             internalError ("toHeap: ftv " ++ ppReadable (ftVars e) ++ ppReadable e)
        -- do the real work of adding the cell
        addHeapUnev tag (iGetType e) e cell_name

-- Used when you absolutely need to get an IRefT back
-- for arrays
{-# INLINE toHeapCon #-}
toHeapCon :: String -> HExpr -> Maybe Id -> G HExpr
-- expand out ICDef as in toHeap
toHeapCon tag (ICon i (ICDef t e)) cell_name = do
  e' <- cacheDef i t e
  toHeapCon tag e' cell_name
-- heap all other constants
toHeapCon tag e@(ICon _ _) cell_name = addHeapUnev tag (iGetType e) e cell_name
toHeapCon tag e cell_name = toHeap tag e cell_name

{-# INLINE toHeapWHNF #-}
toHeapWHNF :: String -> HExpr -> Maybe Id -> G HExpr
toHeapWHNF tag e@(ICon _ _) cell_name = return e
toHeapWHNF tag e@(IRefT _ _ _) cell_name = return e
toHeapWHNF tag (IAps (ICon _ (ICPrim _ PrimWhenPred)) [t] [ICon _ (ICPred _ p), e])
           cell_name = do let pe = P p e
                          -- IRefT is not WHNF
                          pe' <- unheap pe
                          addHeapWHNF tag t pe' cell_name
toHeapWHNF tag e cell_name = addHeapWHNF tag (iGetType e) (P pTrue e) cell_name

{-# INLINE toHeapWHNFCon #-}
toHeapWHNFCon :: String -> HExpr -> Maybe Id -> G HExpr
toHeapWHNFCon tag e@(ICon _ _) cell_name =
    addHeapWHNF tag (iGetType e) (P pTrue e) cell_name
toHeapWHNFCon tag e cell_name = toHeapWHNF tag e cell_name

{-# INLINE toHeapWHNFInferName #-}
toHeapWHNFInferName :: String -> HExpr -> G HExpr
toHeapWHNFInferName tag e = inferName e >>= toHeapWHNF tag e

{-# INLINE toHeapInferName #-}
toHeapInferName :: String -> HExpr -> G HExpr
toHeapInferName tag expr = inferName expr >>= toHeap tag expr

{-# INLINE toHeapConInferName #-}
toHeapConInferName :: String -> HExpr -> G HExpr
toHeapConInferName tag expr = inferName expr >>= toHeapCon tag expr

{-# INLINE toHeapWHNFConInferName #-}
toHeapWHNFConInferName :: String -> HExpr -> G HExpr
toHeapWHNFConInferName tag expr = inferName expr >>= toHeapWHNFCon tag expr

-- inferName: given an expression, try to infer a reasonable name from it
{-# INLINE inferName #-}
inferName :: HExpr -> G (Maybe Id)
inferName (IRefT _ _ heap_ref) =
    do heap_cell <- getHeap heap_ref
       return (hc_name heap_cell)
-- bit selection
inferName expr@(IAps (ICon _ (ICPrim { primOp = PrimSelect })) [ITNum bit_size, ITNum lowest_bit, _] [selected_object]) =
    do selected_object_name <- inferName selected_object
       let highest_bit = lowest_bit + bit_size - 1
           suffix | highest_bit == lowest_bit =
                        mkFString ("_BIT_" ++ show highest_bit ++ "_")
                  | otherwise =
                        mkFString ("_BITS_" ++ show highest_bit ++ "_TO_" ++
                                   show lowest_bit ++ "_")
       case selected_object_name of
         Just name -> return (Just (mkIdPost name suffix))
         Nothing -> return Nothing
-- register read sugar
inferName expr@(IAps (ICon con_name (ICSel {})) [_] [object])
    | con_name == idPreludeRead = inferName object
-- state instances
inferName expr@(ICon inst_name (ICStateVar {})) = return (Just inst_name)
inferName _ = return Nothing

unCacheableType :: IType -> Bool
unCacheableType (ITForAll _ _ _) = True
-- top-level pure values of Clock and Reset involve no work
-- and sometimes we want to play games (e.g. disabled clocks)
unCacheableType (ITCon i _ _) = i == idClock ||
                                i == idReset
unCacheableType t = isFunType t ||
                    isitActionValue t

--- caching of previously evaluated definitions
cacheDef :: Id -> IType -> HExpr -> G HExpr
cacheDef i t e | unCacheableType t = return e
cacheDef i t e@(ICon {}) = return e
cacheDef i t e = do
  s <- get
  let m = defCache s
  case (M.lookup i m) of
    Just e' -> do when doTraceCache $
                    traceM ("cache hit: " ++ ppReadable (i, e'))
                  return e'
    Nothing -> do e' <- toHeap "cache-def" e (Just i)
                  s <- get
                  let m' = M.insert i e' m
                  put (s { defCache = m' })
                  when doTraceCache $
                    traceM ("cache miss: " ++ ppReadable (i, e))
                  return e'

-- #############################################################################
-- #
-- #############################################################################

-- XXX This is old code that should go away
-- At the end of elaboration, this cleans up rule Ids by:
-- * filtering out bad characters in the base name and uniquifying the result
--   (the hierarchical prefixes have already been cleaned-up),
-- * prepending "RL_" to the names
-- * and adding the IdPRule property.
-- Scheduling attributes are updated to account for changes in the names.
cleanupFinalRules :: Flags -> IRules a -> IRules a
cleanupFinalRules flags (IRules sps rs) = IRules sps' (reverse rs')
  where (_, id_rename_map, rs') = foldl foldFn (S.empty, M.empty, []) rs
        -- rename Ids in the attributes, but keep their original positions
        -- (we want the Ids to point to the user-written names in the source)
        sps' = substSchedPragmaIds id_rename_map sps
        uniqueFn seen = if (ruleNameCheck flags)
                        then makeUniqueRuleString seen
                        else id
        -- fold over the list, keep tracking of names that have been seen
        -- and renaming duplicates
        foldFn :: (S.Set String, SPIdMap, [IRule a]) -> IRule a ->
                  (S.Set String, SPIdMap, [IRule a])
        foldFn (seen, rename_map, rs) r@(IRule { irule_name = i } ) =
            let fs = getIdBaseString i
                -- clean up non-alphanum characters;
                -- uniquify the name, if this introduced a clash
                fs' = uniqueFn seen $ cleanupRuleName fs
                -- add this to the list of seen names
                seen' = S.insert fs' seen
                -- add the RL_ prefix and mark with property
                new_i = mkIdRule (setIdBaseString i fs')
                -- update the rename map
                -- (always necessary, because we always add RL_
                rename_map' = M.insert i new_i rename_map
                rs' = (( r { irule_name = new_i } ):rs)
            in
                (seen', rename_map', rs')

-- For Classic, replace spaces with underscore.
-- All other non-alpha/num/underscore characters are filtered.
cleanupRuleName :: String -> String
cleanupRuleName i = filter legalChar $ map replace i
  where legalChar c = (isAlphaNum c) || c == '_'
        replace ' ' = '_'
        replace c = c

makeUniqueRuleString :: S.Set String -> String -> String
makeUniqueRuleString seen str =
    if (S.notMember base_str seen)
    then base_str else makeUniqueString 1
  where
    -- XXX replacing with "unnamed" here may not be necessary
    base_str = if (str == "") then s_unnamed else str
    makeUniqueString :: Integer -> String
    makeUniqueString n =
          let str' = base_str ++ "_" ++ itos n
          in  if (S.notMember str' seen)
              then str'
              else makeUniqueString (n+1)

-- #############################################################################
-- #
-- #############################################################################

-- check the clock set discovered during elaboration
chkClockDomain :: String -> Id -> HWireSet -> HExpr -> G ()
chkClockDomain object id ws e =
  do when doTraceClock $
       traceM ("check clock domain: " ++ (ppReadable id) ++ "\n " ++ (ppReadable ws) ++ (ppReadable e))
     when (not (wsCheckClocks ws)) $ do
       when doTraceClock $ do
         e' <- unheapAllNFNoImp e
         traceM (ppReadable e')
       ms <- getMethodsByClockDomain e
       deferErrors [(getIdPosition id, EClockDomain object (pfpString id) ms)]

chkResetDomain :: String -> Id -> HWireSet -> HExpr -> G ()
chkResetDomain object id ws e =
  do when doTraceClock $
       traceM ("check reset domain: " ++ (ppReadable id) ++ "\n" ++ (ppReadable ws) ++ (ppReadable e))
     when (not (wsCheckResets ws)) $ do
       when doTraceClock $ do
         e' <- unheapAllNFNoImp e
         traceM (ppReadable e')
       ms <- getMethodsByReset e
       eWarning (getPosition id, WMultipleResets object (pfpString id) ms)

-- For the body of a rule or Action/ActionValue method that otherwise has no
-- associated clock (or is associated with "noClock"), we (silently) associate
-- it with the default clock.  If the default is noClock or if there is no
-- default clock, then something else needs to be done
fixupActionWireSet :: HClock -> HWireSet -> Maybe HWireSet
fixupActionWireSet dflt_clk ws =
    case (wsGetClockDomain ws) of
      Just d | (d == noClockDomain)
        -> if (isMissingDefaultClock dflt_clk) || (isNoClock dflt_clk)
           then Nothing
           else Just $ wsAddClock dflt_clk ws
      _ -> Just ws

-- The Id argument is to provide more info for error messages.
-- It is the name of the submodule instance whose arguments are being check,
-- and its position is used for reporting errors (since a good position for
-- the argument expression doesn't exist).
chkModuleArgument :: Id -> (HExpr, HWireSet, VArgInfo) ->
                     G (Maybe (Maybe Id, Maybe Id, HWireSet))
-- handle ports (which can be dynamic)
chkModuleArgument inst_id (e, ws, varginfo) | isPort varginfo =
  do when doTraceClock $ traceM ("check Port module argument: " ++
                                 (ppReadable e) ++ (ppReadable ws))
     -- make an Id for error messages with the position of the instance
     -- but the name of the port
     let inst_pos = getIdPosition inst_id
         --inst_name = pfpString inst_id
         port_id = setIdPosition inst_pos (getVArgInfoName varginfo)
     -- check that the expression does not cross clock domains
     chkClockDomain "instance parameter" port_id ws e
     -- warn if the expression is associated with multiple resets
     chkResetDomain "instance parameter" port_id ws e
     -- find the clock name for the port
     -- (without the clockmap from "newState",
     --  we can't find the associated clock domain)
     let arg_clk = getVArgPortClock varginfo
         arg_rst = getVArgPortReset varginfo
     -- return the port info found
     return (Just (arg_clk, arg_rst, ws))

-- handle inouts (which have associated clock and reset that need checking)
chkModuleArgument inst_id (e, ws, varginfo) | isInout varginfo =
  do when doTraceClock $ traceM ("check Inout module argument: " ++
                                 (ppReadable e) ++ (ppReadable ws))
     -- XXX sanity check that the "ws" doesn't have multiple domains
     -- XXX or multiple resets?

     -- find the clock name for the inout
     -- (without the clockmap from "newState",
     --  we can't find the associated clock domain)
     let arg_clk = getVArgInoutClock varginfo
         arg_rst = getVArgInoutReset varginfo
     -- return the port info found
     return (Just (arg_clk, arg_rst, ws))

-- handle the static arguments (clock, reset, parameter)
chkModuleArgument inst_id (e, ws, varginfo) =
  do when doTraceClock $ traceM ("check other module argument: " ++
                                 (ppReadable e) ++ (ppReadable ws))
     let port_name = getIdString (getVArgInfoName varginfo)
         inst_name = getIdString inst_id
         inst_pos = getPosition inst_id
     when (not (wsIsEmpty ws)) $ do
       e' <- unheapAllNFNoImp e
       let errmsg =
               case varginfo of
                   Param _    -> EModParameterDynamic inst_name port_name
                   ClockArg _ -> EDynamicInputClock inst_name port_name
                   ResetArg _ -> EDynamicInputReset inst_name port_name
                   InoutArg {} -> EDynamicArgInout inst_name port_name
                   Port _ _ _ -> internalError "chkModuleArgument: errmsg"
       -- This used to report (getIExprPosition e') which for mkReg is
       -- in the prelude! So we report the position of the instance name,
       -- which is known to be a better position:
       deferErrors [(inst_pos, errmsg)]
     -- XXX iParams could be inlined here
     -- these have no port info
     return Nothing

-- After the clock map is available, we call this:
chkModuleArgumentClkRst ::
    Id -> HStateVar ->
    (VArgInfo, HExpr, Maybe (Maybe Id, Maybe Id, HWireSet)) ->
    G ()
chkModuleArgumentClkRst inst_id isvar
    (varginfo, e, Just (mclk, mrst, ws)) | (isPort varginfo) =
  do
     let inst_pos = getPosition inst_id
         port_name = getIdString (getVArgInfoName varginfo)
     let expr_clkdom =
             case (wsGetClockDomain ws) of
                 Just d -> d
                 Nothing -> noClockDomain
         arg_clkdom =
             case (mclk) of
                 Nothing -> noClockDomain
                 Just clk -> getClockDomain (getNamedClock clk isvar)
     -- check that the expr clock matches the port clock
     -- (a noClock expr is OK in any clock domain, but if the port is
     -- expected to be noClock, then the expr better have no clock)
     when ( (expr_clkdom /= noClockDomain) &&
            (arg_clkdom /= expr_clkdom) ) $ do
         let (port_clknames, port_hclks) =
                 unzip $ [ (pfpString c, ic)
                             | (c, ic) <- getClockMap isvar,
                               getClockDomain ic == arg_clkdom ]
             expr_hclks = wsGetClocks ws
         let port_clks = nub $ map getClockOscString port_hclks
             expr_clks = nub $ map getClockOscString expr_hclks
         -- if the port is noClock, the clock info will be empty,
         -- so just tell the user "noClock"; otherwise, include
         -- some useful info
         let port_clkinfo =
                 if (arg_clkdom == noClockDomain)
                 then Nothing
                 else Just (port_clknames, port_clks)
         -- XXX instead of just listing the expr_clks, should we list the
         -- XXX methods which contributed those clocks?
         deferErrors [(inst_pos,
                       EPortExprClockDomain port_name port_clkinfo expr_clks)]
     -- warn if the reset of the expr doesn't match the reset of the port
     -- (note that we already warned if the expr has multiple resets)
     -- (a noReset value is OK for any port, but if the port is expected
     -- to be noReset, then the expr better have no reset, or we warn)
     let arg_rst =
             case (mrst) of
                 Nothing -> noReset
                 Just rst -> getNamedReset rst isvar
     case (wsGetResets ws) of
         [expr_rst] ->
             -- the expr has one reset; check if it matches the port
             -- (we could join the "arg_rst" to the wires
             -- and call wsCheckResets here, to not duplicate code)
             when ( (not (isNoReset expr_rst)) &&
                    (arg_rst /= expr_rst) ) $
               do e' <- unheapAllNFNoImp e
                  rms <- getMethodsByReset e'
                  let ms = case rms of
                               ((_, ms):_) -> ms
                               _ -> [] -- internalError ?
                      rst_name = case mrst of
                                     Just rst_id -> pfpString rst_id
                                     Nothing -> "no_reset"
                  eWarning (inst_pos,
                            WPortExprReset port_name rst_name ms)
         [] -> -- the expr has no reset, so it is OK to use anywhere
               return ()
         rs -> -- the expr has multiple resets, so we've already reported a
               -- warning to the user
               return ()
chkModuleArgumentClkRst inst_id isvar
    (varginfo, e, Just (mclk, mrst, ws)) | (isInout varginfo) =
  do
     let inst_pos = getPosition inst_id
         port_name = getIdString (getVArgInfoName varginfo)
     let expr_clkdom =
             case (wsGetClockDomain ws) of
                 Just d -> d
                 Nothing -> noClockDomain
         arg_clkdom =
             case (mclk) of
                 Nothing -> noClockDomain
                 Just clk -> getClockDomain (getNamedClock clk isvar)
     -- check that the expr clock matches the port clock
     -- (there is no exception for noClock)
     when ( (arg_clkdom /= expr_clkdom) ) $ do
         let (port_clknames, port_hclks) =
                 unzip $ [ (pfpString c, ic)
                             | (c, ic) <- getClockMap isvar,
                               getClockDomain ic == arg_clkdom ]
             expr_hclks = wsGetClocks ws
         let port_clks = nub $ map getClockOscString port_hclks
             expr_clks = nub $ map getClockOscString expr_hclks
         -- if the port is noClock, the clock info will be empty,
         -- so just tell the user "noClock"; otherwise, include
         -- some useful info
         let port_clkinfo =
                 if (arg_clkdom == noClockDomain)
                 then Nothing
                 else Just (port_clknames, port_clks)
             expr_clkinfo =
                 if (expr_clkdom == noClockDomain)
                 then Nothing
                 else Just expr_clks
         deferErrors
             [(inst_pos,
               EInoutExprClockDomain port_name port_clkinfo expr_clkinfo)]
     -- warn if the reset of the expr doesn't match the reset of the port
     -- (there is no exception for noReset)
     let arg_rst =
             case (mrst) of
                 Nothing -> noReset
                 Just rst -> getNamedReset rst isvar
     case (wsGetResets ws) of
         [expr_rst] ->
             -- the expr has one reset; check if it matches the port
             if (arg_rst /= expr_rst)
             then  let rst_name = case mrst of
                                    Just rst_id -> pfpString rst_id
                                    Nothing -> "no_reset"
                   in  eWarning (inst_pos,
                                 WInoutExprReset port_name rst_name)
             else return ()
         [] -> if (arg_rst /= noReset)
               then let rst_name = case mrst of
                                    Just rst_id -> pfpString rst_id
                                    Nothing -> "no_reset"
                   in  eWarning (inst_pos,
                                 WInoutExprReset port_name rst_name)
               else return ()
         rs -> -- not possible for an Inout to have multiple resets?
               internalError ("chkModuleArgumentClkRst: " ++
                              "Inout with multiple resets: " ++ ppReadable rs)
-- Other inputs should not have port info
chkModuleArgumentClkRst inst_id isvar
    (varginfo, _, Nothing) | not ((isPort varginfo) ||
                                  (isInout varginfo)) = return ()
-- Any other combination is unexpected
chkModuleArgumentClkRst _ _ _ = internalError ("chkModuleArgumentClkRst")

-- -----

-- drop methods clocked by noClock
-- also remove duplicates and sort per clock (looking at string and position)
-- required unheaped input in normal form (see unheapAllNFNoImp)

getMethodsByClockDomain :: HExpr -> G [[(String, [(String, Position)])]]
getMethodsByClockDomain e = do
    blobs <- getMethodsWithWires e
    let
        -- find all the method uses with clock domains
        -- (uses are a pair of a user-readable string and position,
        -- with the string first for sorting)
        meths = [(clk_dom, (clk, (str, getIdPosition i)))
                    | (_, i, str, clk_dom, clk, _) <- blobs,
                      clk_dom /= noClockDomain]
        -- sort and group by clock domain
        meths_by_domain = joinByFst meths
        -- turn each domain into a list of the clocks
        mkDomPair (_, d_ms) = do
            let -- sort and group by clock
                ms_by_clock = joinByFst d_ms
                -- turn each clock into a pair of the clock osc wire and the uses,
                -- removing duplicates and sorting the uses
                mkClkPair (c, c_ms) = do
                    mcname <- boundaryClockToName c
                    let cname = case mcname of
                                  Just i -> pfpString i
                                  Nothing -> getClockOscString c
                    return (cname, nubSort c_ms)
            mapM mkClkPair ms_by_clock
    mapM mkDomPair meths_by_domain

-- -----

-- drop methods reset by noReset
-- also remove duplicates and sort per reset (looking at string and position)
-- required unheaped input in normal form (see unheapAllNFNoImp)

getMethodsByReset :: HExpr -> G [(String, [(String, Position)])]
getMethodsByReset e = do
    blobs <- getMethodsWithWires e
    let
        -- find all the method uses with associated reset
        -- (uses are a pair of a user-readable string and position,
        -- with the string first for sorting)
        meths = [(rst, (str, getIdPosition i))
                    | (v, i, str, _, _, rst) <- blobs,
                      not (isNoReset rst)]
        -- sort and group by reset
        meths_by_reset = joinByFst meths
        -- turn each reset into a pair of the reset wire and the uses,
        -- removing duplicates and sorting the uses
        mkRstPair (r, ms) = do
            mrname <- boundaryResetToName r
            let rname = case mrname of
                          Just i -> pfpString i
                          Nothing -> getResetString r
            return (rname, nubSort ms)
    mapM mkRstPair meths_by_reset

-- -----

-- When we get the wires for an expression and it has more clocks or resets
-- than expected, then we want a list of the method calls that contributed
-- each clock and reset.  This data type contains the info for that.
--
--  * The object Id (or emptyId for input ports)
--  * The method Id (or port Id)
--  * User-readable string of the method application (or port name)
--  * The clock domain
--  * The clock
--  * The reset
--
type WireBlobTuple = (Id, Id, String, ClockDomain, HClock, HReset)

getMethodsWithWires :: HExpr -> G [WireBlobTuple]
getMethodsWithWires e =
    let
        ?mkvar = \ instId methId v ->
            let clk = getMethodClock methId v
                rst = getMethodReset methId v
                mstr = (getIdBaseString instId) ++ "." ++ (getIdBaseString methId)
                clk_dom = getClockDomain clk
            in  return [(instId, methId, mstr, clk_dom, clk, rst)]
        ?mkport = \ i -> do
          port_wire_map <- lift get >>= return . port_wires
          let (clk, rst) = fromMaybe (noClock, noReset) (M.lookup i port_wire_map)
              clk_dom = getClockDomain clk
              mstr = getIdBaseString i
          return [(emptyId, i, mstr, clk_dom, clk, rst)]
        ?mkinout = \ i inout ->
            let clk = getInoutClock inout
                rst = getInoutReset inout
                clk_dom = getClockDomain clk
                str = getIdBaseString i
            in  return [(emptyId, i, str, clk_dom, clk, rst)]
        ?mkws = \ _ -> Nothing
        ?z = []
        ?jn = concat
        -- XXX why do include the position in the key?
        ?st = \ p pos ws -> do
                visited <- get
                put (S.insert (p, pos) visited)
        ?lk = \ p pos -> do
                visited <- get
                return $ if (p, pos) `S.member` visited
                         then Just []
                         else Nothing
        ?upd = \ e_orig e -> do
                 flgs <- lift getFlags
                 return $ mapIExprPosition (crossInfo flgs) (e_orig, e)
    in
        evalStateT (extractWires e) S.empty

-- -----

-- extract the dynamic wires (e.g. clocks, reset, etc.) from an elaboration-time object

extractWireSet :: (Wireable a) => a -> G HWireSet
extractWireSet x =
    let
        ?mkvar = \ _ methId v ->
            let clk = getMethodClock methId v
                rst = getMethodReset methId v
            in  return $ wsAddReset rst (wsClock clk)
        ?mkport = \ i -> lift $ getPortWires i
        ?mkinout = \ _ inout -> return $ getInoutWires inout
        ?mkws = \ ws -> Just ws
        ?z = wsEmpty
        ?jn = wsJoinMany
        ?st = \ p _ ws -> lift $ updWireSetCache p ws
        ?lk = \ p _ -> do
                cache <- lift $ getWireSetCache
                return $ M.lookup p cache
        ?upd = \ e_orig e -> return e
    in
        evalStateT (extractWires x) S.empty

-- -----

type W = StateT (S.Set (Int, Position)) G

class Wireable a where
  extractWires :: (?mkvar :: Id -> Id -> HStateVar -> W b,
                   ?mkport :: Id -> W b,
                   ?mkinout :: Id -> HInout -> W b,
                   ?mkws :: HWireSet -> Maybe b,
                   ?z :: b,
                   ?jn :: [b] -> b,
                   ?st :: Int -> Position -> b -> W (),
                   ?lk :: Int -> Position -> W (Maybe b),
                   ?upd :: HExpr -> HExpr -> W HExpr)
                 => a -> W b

instance Wireable HExpr where
  extractWires (ILam i t e) = extractWires e

  -- method call
  extractWires (IAps (ICon methId (ICSel { })) _ ((ICon instId (ICStateVar { iVar = v })):es)) = do
    ws <- ?mkvar instId methId v
    wss <- mapM extractWires es
    return (?jn (ws:wss))

  -- don't walk unnecessary parts of a struct or interface
  extractWires (IAps f@(ICon i_sel (ICSel { selNo = n })) _ (a@(IRefT _ p r):as)) = do
    -- we don't look for "p" in the WireSet cache, because we don't want to
    -- include the wires from the unused fields
    -- (presumably the fields will have their own refs, which can be cached)
    cell <- lift $ getHeap r
    let (P p e) =
            case cell of
              (HUnev { hc_hexpr = he }) -> P pTrue he
              (HWHNF { hc_pexpr = pe }) -> pe
              (HLoop name) -> internalError ("IExpand.extractWires HLoop: " ++
                                             ppReadable name)
              (HNF { hc_pexpr = pe }) -> pe
    -- might "p" include wires from the other fields?
    p_ws <- extractWires p
    case e of
       (IAps (ICon i_tup (ICTuple {})) _ es) -> do
           let esel = if (length es > fromInteger n)
                      then es!!(fromInteger n)
                      else internalError("extractWires: ICSel: " ++
                                         ppReadable (n, es))
           a_wss <- mapM extractWires (esel:as)
           return (?jn (p_ws:a_wss))
       (ICon instId (ICStateVar { iVar = v })) -> do
           ws <- ?mkvar instId i_sel v
           wss <- mapM extractWires as
           return (?jn (p_ws:ws:wss))
       _ -> -- revert to the default handling of IAps
            -- (except no need to follow "f")
            do wss <- mapM extractWires (a:as)
               return (?jn wss)

  extractWires (IAps f _ es) = do
    ws <- mapM extractWires (f:es)
    return (?jn ws)

  extractWires (ILAM _ _ e) = extractWires e

  extractWires ref@(IRefT t p r) = do
    let pos = getIExprPosition ref
    cache_res <- ?lk p pos
    case cache_res of
      Just ws -> return ws
      Nothing -> do
        cell <- lift $ getHeap r
        ws <- case cell of
                -- XXX should be evaluated because clock ops are strict
                (HUnev { hc_hexpr = e }) -> ?upd ref e >>= extractWires
                (HWHNF { hc_pexpr = P p e }) -> ?upd ref e >>= \ e' -> extractWires (P p e')
                (HLoop name) ->
                    internalError ("IExpand.extractWires HLoop: " ++ ppReadable name)
                (HNF { hc_pexpr = P p e, hc_wire_set = ws}) ->
                    -- attempt to reuse the WireSet if possible
                    case (?mkws ws) of
                      Just v -> return v
                      Nothing -> ?upd ref e >>= \ e' -> extractWires (P p e')
        ?st p pos ws
        return ws

  extractWires (ICon i (ICModPort {})) = ?mkport i

  extractWires (ICon i (ICInout { iInout = inout })) = ?mkinout i inout

  extractWires _ = return ?z

instance Wireable (PTerm HeapData) where
  extractWires (PAtom e) = extractWires e
  extractWires (PIf c t e) = do ws1 <- extractWires c
                                ws2 <- extractWires t
                                ws3 <- extractWires e
                                return (?jn [ws1,ws2,ws3])
  extractWires (PSel idx _ es) = do ws1 <- extractWires idx
                                    wss <- mapM extractWires es
                                    return (?jn (ws1:wss))

instance Wireable HPred where
  extractWires (PConj ps) = do wss <- mapM extractWires (S.toList ps)
                               return (?jn wss)

instance Wireable PExpr where
  extractWires (P p e) = do ws1 <- extractWires p
                            ws2 <- extractWires e
                            return (?jn [ws1,ws2])

-----------------------------------------------------------------------------

realPrimOp :: PrimOp -> Bool
realPrimOp PrimAdd = True
realPrimOp PrimSub = True
realPrimOp PrimAnd = True
realPrimOp PrimOr = True
realPrimOp PrimXor = True
realPrimOp PrimMul = True
realPrimOp PrimQuot = True
realPrimOp PrimRem = True
realPrimOp PrimSL = True
realPrimOp PrimSRL = True
realPrimOp PrimSRA = True
realPrimOp PrimInv = True
realPrimOp PrimNeg = True
realPrimOp PrimEQ = True
realPrimOp PrimEQ3 = True
realPrimOp PrimULE = True
realPrimOp PrimULT = True
realPrimOp PrimSLE = True
realPrimOp PrimSLT = True
realPrimOp PrimSignExt = True
--realPrimOp PrimZeroExt = True        -- should not occur
--realPrimOp PrimTrunc = True        -- should not occur
realPrimOp PrimExtract = True
realPrimOp PrimConcat = True
realPrimOp PrimSplit = True
realPrimOp PrimBNot = True
realPrimOp PrimBAnd = True
realPrimOp PrimBOr = True
realPrimOp PrimIf = True
realPrimOp PrimSelect = True
realPrimOp PrimArrayDynSelect = True
realPrimOp PrimArrayDynUpdate = True
--
realPrimOp PrimJoinActions = True
realPrimOp PrimNoActions = True
realPrimOp PrimExpIf = True
realPrimOp PrimNoExpIf = True
realPrimOp PrimNosplitDeep = True
realPrimOp PrimSplitDeep = True
realPrimOp PrimFmtConcat = True
realPrimOp PrimSetSelPosition = True

realPrimOp PrimStringConcat = True

realPrimOp _ = False

-----------------------------------------------------------------------------

integerPrim :: PrimOp -> Bool
integerPrim PrimIntegerAdd = True
integerPrim PrimIntegerSub = True
integerPrim PrimIntegerNeg = True
integerPrim PrimIntegerMul = True
integerPrim PrimIntegerDiv = True
integerPrim PrimIntegerMod = True
integerPrim PrimIntegerQuot = True
integerPrim PrimIntegerRem = True
integerPrim PrimIntegerExp = True
integerPrim PrimIntegerLog2 = True
integerPrim PrimIntegerEQ = True
integerPrim PrimIntegerLE = True
integerPrim PrimIntegerLT = True
integerPrim PrimIntegerToReal = True
integerPrim PrimBitsToReal = True
integerPrim _ = False

-----------------------------------------------------------------------------

realPrim :: PrimOp -> Bool
realPrim PrimRealEQ = True
realPrim PrimRealLE = True
realPrim PrimRealLT = True
realPrim PrimRealToString = True
realPrim PrimRealAdd = True
realPrim PrimRealSub = True
realPrim PrimRealNeg = True
realPrim PrimRealMul = True
realPrim PrimRealDiv = True
realPrim PrimRealAbs = True
realPrim PrimRealSignum = True
realPrim PrimRealExpE = True
realPrim PrimRealPow = True
realPrim PrimRealLogE = True
realPrim PrimRealLogBase = True
realPrim PrimRealLog2 = True
realPrim PrimRealLog10 = True
realPrim PrimRealToBits = True
realPrim PrimBitsToReal = True
realPrim PrimRealSin = True
realPrim PrimRealCos = True
realPrim PrimRealTan = True
realPrim PrimRealSinH = True
realPrim PrimRealCosH = True
realPrim PrimRealTanH = True
realPrim PrimRealASin = True
realPrim PrimRealACos = True
realPrim PrimRealATan = True
realPrim PrimRealASinH = True
realPrim PrimRealACosH = True
realPrim PrimRealATanH = True
realPrim PrimRealATan2 = True
realPrim PrimRealSqrt = True
realPrim PrimRealTrunc = True
realPrim PrimRealCeil = True
realPrim PrimRealFloor = True
realPrim PrimRealRound = True
realPrim PrimSplitReal = True
realPrim PrimDecodeReal = True
realPrim PrimRealToDigits = True
realPrim PrimRealIsInfinite = True
realPrim PrimRealIsNegativeZero = True
realPrim _ = False

-----------------------------------------------------------------------------

-- ops that only take arguments (one or two) of type String
-- (IExpand uses this to handle multiple ops in one arm of "conAp'")
stringPrim :: PrimOp -> Bool
stringPrim PrimStringConcat = True
stringPrim PrimStringEQ = True
stringPrim PrimStringToInteger = True
stringPrim PrimStringLength = True
stringPrim PrimStringSplit = True
stringPrim PrimStringToChar = True
stringPrim PrimGetStringPosition = True
stringPrim _ = False

-- ops that only take an argument of type Char
-- (IExpand uses this to handle multiple ops in one arm of "conAp'")
charPrim :: PrimOp -> Bool
charPrim PrimCharToString = True
charPrim PrimCharOrd = True
charPrim _ = False

-----------------------------------------------------------------------------

-- ops that are Boolean queries on one argument of type Handle
-- (IExpand uses this to handle them all in one arm of "conAp'")
handleBoolPrim :: PrimOp -> Bool
handleBoolPrim PrimHandleIsEOF = True
handleBoolPrim PrimHandleIsOpen = True
handleBoolPrim PrimHandleIsClosed = True
handleBoolPrim PrimHandleIsReadable = True
handleBoolPrim PrimHandleIsWritable = True
handleBoolPrim _ = False

-----------------------------------------------------------------------------

strictPrim :: PrimOp -> Bool
strictPrim PrimAdd = True
strictPrim PrimSub = True
strictPrim PrimAnd = True
strictPrim PrimOr = True
strictPrim PrimXor = True
strictPrim PrimMul = True
strictPrim PrimQuot = True
strictPrim PrimRem = True
strictPrim PrimSL = True
strictPrim PrimSRL = True
strictPrim PrimSRA = True
strictPrim PrimInv = True
strictPrim PrimNeg = True
strictPrim PrimEQ = True
strictPrim PrimEQ3 = True
strictPrim PrimULE = True
strictPrim PrimULT = True
strictPrim PrimSLE = True
strictPrim PrimSLT = True
strictPrim PrimSignExt = True
strictPrim PrimZeroExt = True
strictPrim PrimTrunc = True
strictPrim PrimExtract = True
strictPrim PrimConcat = True
strictPrim PrimSplit = True
strictPrim PrimBNot = True
strictPrim PrimSelect = True
strictPrim PrimBitToInteger = True
strictPrim PrimValueOf = True
strictPrim PrimStringOf = True
strictPrim PrimOrd = True
strictPrim PrimChr = True
strictPrim PrimSameFamilyClock = True
strictPrim PrimIsAncestorClock = True
strictPrim PrimClockEQ = True
strictPrim PrimClockOf = True
strictPrim PrimClocksOf = True
strictPrim PrimResetOf = True
strictPrim PrimResetsOf = True
strictPrim PrimResetEQ = True
strictPrim PrimGetStringPosition = True
strictPrim PrimPrintPosition = True
strictPrim PrimPrintType = True
strictPrim PrimTypeEQ = True
strictPrim PrimIsIfcType = True
strictPrim PrimJoinNames = True
strictPrim PrimExtendNameInteger = True
strictPrim PrimGetNamePosition = True
strictPrim PrimGetNameString = True
strictPrim PrimMakeName = True
strictPrim PrimFmtConcat = True
strictPrim _ = False

-----------------------------------------------------------------------------

-- When eval to NF returns one of these primitives, it is because the user
-- wrote a dynamic expression; this is used to detect when to report a better
-- error than nfError
--
condPrim :: PrimOp -> Bool
condPrim PrimIf = True
condPrim PrimCase = True
condPrim PrimArrayDynSelect = True
condPrim _ = False

-- #############################################################################
-- # Methods for carrying along Id Position info through IExpr
-- # transformations.
-- #############################################################################

mapPExprPosition :: Bool -> (PExpr,PExpr) -> G PExpr
mapPExprPosition doit ((P pred_0 iexpr_0), (P pred_1 iexpr_1)) = do
                         return (P pred_1 (mapIExprPosition2 doit (iexpr_0, iexpr_1)))

-----------------------------------------------------------------------------

isNoInlinedFunc :: G Bool
isNoInlinedFunc =  gets noinlined_func

isAggressive :: G Bool
isAggressive =  gets aggressive_cond

setAggressive :: Bool -> G ()
setAggressive x =  modify (\s -> s{aggressive_cond=x})

getPragmas :: G [PProp]
getPragmas = gets pragmas

setPragmas :: [PProp] -> G ()
setPragmas x = modify (\s -> s {pragmas=x})

-----------------------------------------------------------------------------
