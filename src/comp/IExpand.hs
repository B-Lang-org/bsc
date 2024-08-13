{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, RelaxedPolyRec, PatternGuards, ScopedTypeVariables #-}
-- Todo
--  * Use a set to keep track of variable values to handle x==c1 || x==c2
--  * Don't generate x!=0 && x!=1 && x!= 2 ...
--    Can be done by generating the minimal test for an interval after processing.
--  * Generate a single decoder instead of many comparisons for equality?
--  * Truncate bit extraction positions to minimum width.
--  * Inline bit extraction?
--  * if x 0 maxBound  --> {n-bits}x
--  * if c 0 e  --> {n-bits}c & e
--  * flatten & (in asyntax)?
--  * check for name conflict in the generated IEFace
module IExpand(iExpand) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Data.List
import Data.Maybe
import Data.Foldable(foldrM)
import Numeric(showIntAtBase)
import Data.Char(intToDigit, ord, chr)
import Control.Monad(when, foldM, zipWithM, mapAndUnzipM)
import Control.Monad.Fix(mfix)
--import Control.Monad.Fix
import Control.Monad.State(State, evalState, liftIO, get, put)
import Data.Graph
import qualified Data.Generics as Generic
import System.IO(Handle, BufferMode(..), IOMode(..), stdout, stderr,
                 hSetBuffering, hIsOpen, hIsClosed)
import System.FilePath(isRelative)
import qualified Data.Array as Array
import qualified Data.IntMap as IM
import qualified Data.Map as M
import qualified Data.Set as S
import Debug.Trace(traceM)

import FileIOUtil(openFileCatch, hCloseCatch, hFlushCatch, hGetBufferingCatch,
                  hSetBufferingCatch, hPutStrCatch, hGetLineCatch,
                  hGetCharCatch, hIsEOFCatch, hIsReadableCatch,
                  hIsWritableCatch)
import GraphWrapper(tSortInt)
import IntegerUtil(mask)
import Util
import PFPrint
import IdPrint
import IntLit
import Undefined
import FStringCompat
import PreStrings(fsUnderscore)
import PreIds
import Flags
import SymTab(SymTab)
import Error(internalError, EMsg, ErrMsg(..), ErrorHandle,
             recordHandleOpen, recordHandleClose)
import Position
import Id
import Backend
import Prim
import IPrims(doPrimOp)
import CSyntax
import CSyntaxUtil
import qualified TIMonad as TM
import TypeCheck(topExpr)
import VModInfo
import Pragma
import ISyntax
import IConv(iConvT, iConvExpr)
import ISyntaxUtil
import ISyntaxCheck(iGetKind)
import IExpandUtils
import Wires
import IWireSet
import qualified IfcBetterInfo as BetterInfo

import ITransform(iTransExpr)

import IOUtil(progArgs)
import ISyntaxXRef(mapIExprPosition, mapIExprPositionConservative)
import IStateLoc

-----------------------------------------------------------------------------
-- Trace Flags

-- doProfile
--   Keep a map of the number of times a top-level def is entered in evalAp
--   (the number of unfolding steps), indexed by the position of the call Id,
--   and display the map on each step warning and at the end of evaluation.
doProfile :: Bool
doProfile = elem "-trace-profile" progArgs

-- doDebug
--   A generic trace flag that has been added to over the years.
--   Includes some basic call flow at the top of evaluating a module,
--   and debug info when evaluating various structures and primitives.
doDebug :: Bool
doDebug = elem "-trace-debug" progArgs

-- doFunExpand
--   On evaluating a top-level function call, display the call.
--   If the flag is used twice, the result of evaluation is displayed.
doFunExpand, doFunExpand2 :: Bool
doFunExpand = elem "-trace-fun-expand" progArgs
doFunExpand2 = length (filter (== "-trace-fun-expand") progArgs) > 1

-- doConAp
--   Trace the entrance and exit to "conAp" (called when evaluating ICon)
--   and when that calls "bldAp'" or "bldApUH'" (rebuilding the original expr)
doConAp :: Bool
doConAp = elem "-trace-conAp" progArgs

-- doTrans
--   Trace the entrance and exit to iTransExpr (when iExpand resorts
--   to iTransform for optimization)
doTrans :: Bool
doTrans = elem "-trace-eval-trans" progArgs

-- doTraceClock
--   Trace the creation and analysis of Clock and Reset (and some Inout),
--   here and in IExpandUtils.
doTraceClock :: Bool
doTraceClock = elem "-trace-clock" progArgs

-- doTraceSteps
--   At the end of evaluation, display the total number of evaluation steps
--   (the number of times a top-level function was evaluated, including
--   when using a cached value)
doTraceSteps :: Bool
doTraceSteps = elem "-trace-eval-steps" progArgs

-- doTraceHeap
--   In IExpandUtils, trace when adding an expr to the heap or updating a
--   heap value.  If the flag is used twice, the overwritten value is shown.
doTraceHeap :: Bool
doTraceHeap  = elem "-trace-heap" progArgs

-- doTraceHeapAlloc
--   In IExpandUtils, trace when a heap cell is created.
--   And trace in "evalUH" when the value to be unheaped is a reference
--   (which is considered a "wasted re-heap").
doTraceHeapAlloc :: Bool
doTraceHeapAlloc = elem "-trace-heap-alloc" progArgs

-- doTraceHeapSize
--   At the end of evaluation, print the size of the heap (number of cells).
doTraceHeapSize :: Bool
doTraceHeapSize = elem "-trace-heap-size" progArgs

-- doTraceCache
--   In IExpandUtils, trace cache hit/miss for top-level functions.
doTraceCache :: Bool
doTraceCache = elem "-trace-def-cache" progArgs

-- doTraceNF
--   Trace the entrance and exit of "walkNF".
doTraceNF :: Bool
doTraceNF = elem "-trace-eval-nf" progArgs

-- doTracePortTypes
--   In IExpandUtils, trace the saving of port types, via the primitive and
--   for the module arguments and interface.
doTracePortTypes :: Bool
doTracePortTypes = elem "-trace-port-types" progArgs

-- doTraceIf
--   Trace the "doIf" and "improveIf" functions for evaluating if exprs.
doTraceIf :: Bool
doTraceIf = elem "-trace-eval-if" progArgs

-- doTraceTypes
--   Add a check that the type of an expression before and after evaluation
--   (by "evalAp") doesn't match, with an internal error if not.
doTraceTypes :: Bool
doTraceTypes = elem "-trace-eval-types" progArgs

-- doTraceLoc
--   Here and in IExpandUtil, trace some operations on IStateLoc, such as
--   adding hierarchy for instantiation, rules, and leaf modules.
doTraceLoc :: Bool
doTraceLoc = elem "-trace-state-loc" progArgs

-- doDebugFreeVars
--   Add a check that expressions added to the heap do not have free variables,
--   with an internal error if so.
doDebugFreeVars :: Bool
doDebugFreeVars = elem "-debug-eval-free-vars" progArgs

-- We need to set the buffering of stdout and stderr
-- if any trace is on (including a trace only used in IExpandUtils)
-- so make sure that all trace flags are included in this list
doAnyTrace :: Bool
doAnyTrace = doProfile ||
             doDebug ||
             doFunExpand ||
             doConAp ||
             doTrans ||
             doTraceClock ||
             doTraceSteps ||
             doTraceHeap ||
             doTraceHeapAlloc ||
             doTraceHeapSize ||
             doTraceCache ||
             doTraceNF ||
             doTracePortTypes ||
             doTraceIf ||
             doTraceTypes ||
             doTraceLoc ||
             doDebugFreeVars

-- Before we had attributes for controlling whether input clocks have gates,
-- these backdoor flags were used to add gates.
-- XXX These can probably be retired now
gateClockInputs :: Bool
gateClockInputs = elem "-hack-gate-clock-inputs" progArgs
gateDefaultClock :: Bool
gateDefaultClock = elem "-hack-gate-default-clock" progArgs

iExpandPref :: String
iExpandPref = "__h"

-----------------------------------------------------------------------------

-- iExpand
--   Elaborate a toplevel module definition (for which RTL is being generated).
--   Heap references become local defs in the module (named with "__h"),
--   except when they are simple enough to be inlined.
--   The actual elaboration work is done by iExpandModuleDef
iExpand :: ErrorHandle -> Flags ->
           SymTab -> M.Map Id HExpr ->
           Bool -> [PProp] -> HDef ->
           IO (IModule HeapData)
iExpand errh flags symt alldefs is_noinlined_func pps def@(IDef mi _ _ _) = do
  -- unbuffer output if we're tracing
  when (doAnyTrace || showElabProgress flags) $
      do hSetBuffering stdout LineBuffering
         hSetBuffering stderr LineBuffering
  -- execute the static elaboration
  -- go is of type GOutput X, where X is the large tuple output of iExpandModuleDef
  go <- runG errh flags symt alldefs mi is_noinlined_func pps $
            iExpandModuleDef def
  -- trace the steps and heap size
  when doTraceSteps $ putStrLn ("expansion steps: " ++ (show (go_steps go)))
  when doTraceHeapSize $ putStrLn ("heap size: " ++ (show (go_hp go)))

  let (iks, args, varginfo, ifc) = goutput go
  let rules = go_rules go
  let insts = go_state_vars go

  -- turn heap into IDef definitions
  let
      -- collect a map of the heap pointers reachable from insts, rules, and ifc
      -- these will become defs in the resulting IModule
      -- Position information has been clobbered in iheap
      iheap = collPtrs (insts, rules, ifc) IM.empty
      -- a list of just the pointers
      ptrs0 = IM.keys iheap
      -- CSE the pointers and return a map from old pointers to the remaining
      -- canonical ones.  The pointers are returned in tsorted order.
      -- The tsort does a non-circularity check, which is a property we
      -- expect in IModule, but the function "pDef" below also relies on it
      -- (since "pDef" and "m" are recursively built)
      (tsorted_cse_ptrs, ptr_map) = eqPtrs iheap ptrs0
      -- function for translating old pointers to new ones
      ptran p = IM.findWithDefault p p ptr_map

      -- from a heap pointer, get the expression and its name info
      --   Note that wire info in dropped.  In the MCD merge (rev 6456),
      --   Ravi considered a new IEDef type that would contain the wires
      --   but that would require updating ITransform to handle it.
      heapOf :: Int -> (HExpr, NameInfo)
      heapOf p = case (IM.lookup p iheap) of
                    Just (HNF { hc_pexpr = P _ e, hc_name = name })
                         -> (e, legalizeNameInfo name)
                    hres -> internalError ("heapOf " ++ ppReadable (p, hres))

      pDef :: HeapPointer -> (HExpr, Maybe HDef)
      pDef p0 =
          let -- translate the old pointer to the new pointer
              p = ptran p0
              -- get the expression and its name info
              (e, expr_name) = heapOf p
              -- the type for the new IDef being created
              t = iGetType e
              -- the name for the new IDef being created
              i = case expr_name of
                    Just name ->
                        setKeepId $
                        mkIdPost name (mkFString (iExpandPref ++ show p))
                    _ ->
                        setBadId $
                        mkId noPosition (mkFString (iExpandPref ++ show p))
              -- update the body of the IDef that we're creating
              -- (this is recursive, since "m" is built with "pDef")
              e' = hToDef m e
              -- whether the expression is "simple" and therefore doesn't
              -- need to be lifted to an IDef
              simple (ICon _ _) = True
              simple _ = False
          in
              -- return the expression that should replace the heap pointer,
              -- and maybe a Def, if the expression is a def reference
              if simple e || isActionType t then
                  -- inline the expression, no def is created for this heap ptr
                  (e', Nothing)
              else
                  -- assign the expr to a def, and replace the ptr reference
                  -- with a module def reference (which is what ICValue is)
                  (ICon i (ICValue t e'), Just (IDef i t e' []))

      -- a map from the new pointers to their expressions
      --    Actually, a map to a pair of an expression and maybe an IDef;
      --    if the expr is a def reference, the maybe contains the def.
      ptr_info = [ (p, pDef p) | p <- tsorted_cse_ptrs ]

      -- a lookup function for the "ptr_info" map,
      -- returning just the expression to replace the ptr reference
      ptr_expr_map = IM.fromList [(p, e) | (p, (e, _)) <- ptr_info ]
      mget p = fromJustOrErr "iExpand.mget" (IM.lookup p ptr_expr_map)

      -- a map that is used by "hToDef" to convert expressions,
      -- replacing the old pointers with the expressions of the new pointers
      m = IM.fromList [(p, mget (ptran p)) | p <- ptrs0 ]

      -- replaces pointers in the insts, rules, and ifcs
      insts' = hToDef m insts
      rules_heap = hToDef m rules
      ifc'   = hToDef m ifc

      -- the final defs for the IModule
      -- (the entries in "ptr_info" that are not inlined, and contain a def)
      defs1 = [ d | (_, (_, Just d)) <- ptr_info ]

      -- XXX the rules names should be constructed properly
      -- XXX to begin with rather than fixed up at the end
      rules_cleanup = cleanupFinalRules flags rules_heap

      mpdefs = generateMethodPreds ( methodConditions flags ) rules_cleanup
      defs = defs1 ++ mpdefs
      wi = WireInfo (go_vclockinfo go) (go_vresetinfo go) varginfo
      comments_map = go_comments_map go
      mbe = if (go_backend_specific go)
            then Just $ fromJustOrErr "iExpand: backend" (backend flags)
            else Nothing

      -- the expanded module
      imod0 = IModule mi is_noinlined_func mbe wi [] iks args
                     (go_clock_domains go) (go_resets go)
                     insts' (go_port_types go)
                     defs rules_cleanup ifc'
                     (go_ffcallNo go) comments_map
      -- if preserving method conditions, then remove the book-keeping info
      imod = removeInlinedPositions flags imod0

  --let traceMethodPred (IDef i _ p props) =
  --        traceM ("Def: " ++ ppReadable (i, getPosition i, getIdProps i, p, props))
  --mapM_ traceMethodPred mpdefs

  when doDebug $ do
      traceM ("iExpand done\n" ++ ppReadable (sort (IM.toList iheap))
                               ++ ppReadable rules
                               ++ ppReadable ifc)
      traceM ("iExpand done mod\n" ++ ppReadable imod)
  when doProfile $
      traceM ("iExpand profile\n" ++ ppReadable (go_profile go))
  return imod

generateMethodPreds :: forall a . Bool -> IRules a -> [IDef a]
generateMethodPreds flag (IRules _ rs) =
  if (not flag) then [] else concatMap one_rule rs where
    one_rule :: IRule a -> [IDef a]
    one_rule r = gen_defs (irule_name r) $ collect_ifs $ irule_body r
    collect_ifs :: IExpr a ->
                   [(IExpr a, IExpr a)]  -- pred, meth call
    collect_ifs e = -- trace ("collect_ifs " ++ (show e) ) $
                     collect_ifs' e
    collect_ifs' :: IExpr a ->
                   [(IExpr a, IExpr a)]  -- pred, meth call
    collect_ifs' (IAps (ICon _ (ICPrim { primOp = PrimIf })) _ [cnd, thn, els]) =
      let true_branch = collect_ifs thn
          false_branch = collect_ifs els
      in ( map (add_to_pred cnd) true_branch) ++ (map (add_to_pred (ieNot cnd)) false_branch)
    collect_ifs' (IAps (ICon _ (ICPrim { primOp = PrimCase }))
                      [sz_idx, elem_ty] (idx:dflt:ces)) =
      -- XXX if the arms are not overlapping, we can simplify the conditions
      let foldFn (v, e) false_branch =
              let true_branch = collect_ifs e
                  c = iePrimEQ sz_idx idx v
              in  (map (add_to_pred c) true_branch) ++
                  (map (add_to_pred (ieNot c)) false_branch)
      in  foldr foldFn (collect_ifs dflt) (makePairs ces)
    collect_ifs' (IAps (ICon i_sel (ICPrim { primOp = PrimArrayDynSelect }))
                      [elem_ty, sz_idx] [arr, idx]) =
      case arr of
        (IAps (ICon _ (ICPrim { primOp = PrimBuildArray })) _ es) ->
            let pos = getPosition i_sel
                ty_idx = aitBit sz_idx
                mapFn (n, e) =
                    let n_lit = iMkLitAt pos ty_idx n
                        c = iePrimEQ sz_idx idx n_lit
                    in  map (add_to_pred c) (collect_ifs e)
            in  concatMap mapFn (zip [0..] es)
        _ -> internalError ("collect_ifs': PrimArrayDynSelect: " ++
                            ppReadable arr)
    collect_ifs' (IAps (ICon join (ICPrim{ primOp = op})) _t es)
      | join == idPrimJoinActions || op == PrimJoinActions
        = concatMap collect_ifs es -- search further for unlifted Ifs inside an action block
    collect_ifs' e@(IAps (ICon _method (ICSel { })) _t
                  ((ICon _state (ICStateVar { })):_methodargs)) =
      [(iTrue,e)] -- base case for unpack_method_call
    collect_ifs' (IAps (ICon _ (ICPrim _ pi)) _t [e]) | isIfWrapper pi
        = collect_ifs e
    -- need to recurse further into e? XXX
    collect_ifs' e = [(iTrue,e)]
    add_to_pred :: IExpr a -> (IExpr a, IExpr a) -> (IExpr a, IExpr a)
    add_to_pred new (old, action) = (ieAndOpt new old, action)

    -- tiny state monad to get unique numbers.  This is a lazy
    -- hack to avoid name collisions.  It is still
    -- theoretically possible to get name collisions.
    nextNumber :: State Integer Integer
    nextNumber = do
      n <- get
      put $ n+1
      return n
    gen_defs :: Id -> [(IExpr a, IExpr a)] -> [IDef a]
    gen_defs rulename predmethods = concat $ evalState (mapM (makeDef rulename) predmethods ) 1

    makeDef :: Id -> (IExpr a, IExpr a) -> State Integer [IDef a]
    makeDef rulename (predicate, expr)
      | not $ isTrue predicate =
        -- trace ("now evaluating " ++ ppReadable rulename ++ " " ++ ppReadable (predicate, expr)
        --   ++ show predicate ++ (show expr)
        -- ) $
        mapM (onepred rulename predicate) (unpack_method_call expr)
    makeDef _ _ = return [] -- isTrue, for actions with no conditions
    onepred :: Id -> IExpr a -> (Id, Id) -> State Integer (IDef a)
    onepred rulename predicate (state, method) = do
          -- traceM $ "onepred " ++ ppReadable (predicate, state, method)
          uniquenum <- nextNumber
          let poss = case (getIdInlinedPositions method) of
                      Nothing ->
                        --trace("no inlined position: " ++ ppReadable (state, method)) $
                        [getIdPosition state]
                      Just jposs ->
                        --trace("inlined positions: " ++ ppReadable (state, method, jposs)) $
                        -- preserve all the positions,
                        jposs
          let i = makename rulename state method uniquenum poss
          return $ IDef i itBit1 predicate
            [ DefP_NoCSE
              -- ^ put this first as an optimization for the calls to elem in defPropsHasNoCSE
            , DefP_Rule rulename
            , DefP_Instance state
            , DefP_Method method
            ]
    makename :: Id -> Id -> Id -> Integer -> [Position] -> Id
    makename rule state method num poss =
      -- COND_<rule>_<state>_<method>_<uniqueID>
      let fstr = concatFString [ mkFString "COND", fsUnderscore,
                                 getIdBase rule, fsUnderscore,
                                 getIdBase state, fsUnderscore,
                                 getIdBase method, fsUnderscore,
                                 mkFString $ show num ]
          props = [ IdPMethodPredicate,
                    IdP_keep,
                    IdP_keepEvenUnused,
                    IdPInlinedPositions poss ]
      in
          addIdProps (mkId noPosition fstr) props

unpack_method_call :: IExpr a -> [(Id,Id)]
unpack_method_call e = -- trace ("unpack_method_call " ++ (show e)) $
                       unpack_method_call' [] e
-- This accumulates a list of positions along the way, to support "avAction_"
-- wrappers; in some places we sanity check that it's an empty list, because
-- positions are not expected to be accumulated in those situations.
unpack_method_call' :: [Position] -> IExpr a -> [(Id,Id)]
-- no action
unpack_method_call' _ (ICon _ (ICPrim { primOp = PrimNoActions })) =
  []
-- action method call
unpack_method_call' poss e@(IAps (ICon i_method (ICSel { })) _ts
                            ((ICon i_state (ICStateVar { })):_methodargs))
  = let i_method' = addIdInlinedPositions i_method poss
    in  [(i_state, i_method')]
-- Most action have methods have an "avAction_" wrapper, but some do not
-- (Reg write does not -- is the difference Classic vs BSV?)
unpack_method_call' poss (IAps (ICon i_av (ICSel { })) _ts [e])
  | (i_av == idAVAction_)
  = let av_poss = fromMaybe [] $ getIdInlinedPositions i_av
        poss' = av_poss ++ poss
    in  unpack_method_call' poss' e
-- multiple actions
unpack_method_call' poss (IAps (ICon _ (ICPrim { primOp = PrimJoinActions }))
                          _ts es) =
  case poss of
    [] -> concatMap unpack_method_call es
    _ -> internalError ("unpack_method_call': JoinActions: " ++
                        ppReadable poss)
-- function with arguments (such as $display)
unpack_method_call' poss (IAps (ICon i_function _) _ts _es) =
  let i_function' = addIdInlinedPositions i_function poss
  in  [(mk_homeless_id "FUNCTION", i_function')]
-- function of no arguments
unpack_method_call' poss (ICon i_function _) =
  let i_function' = addIdInlinedPositions i_function poss
  in  [(mk_homeless_id "FUNCTION", i_function')]
  -- ^seen in Sudoku with high order functional programming (displayGrid)
unpack_method_call' _ e =
  internalError("unpack_method_call': unknown: " ++ ppReadable e)
  -- trace ("unpack_method_call unable to match " ++ show e) $
  --[(mk_homeless_id "NOSTATE", mk_homeless_id "NOMETHOD")]

removeInlinedPositions :: Flags -> IModule HeapData -> IModule HeapData
removeInlinedPositions flags imod0 | (not (methodConditions flags)) = imod0
removeInlinedPositions flags imod0 =
    let removeFn :: HExpr -> HExpr
        removeFn (ICon i ic) = (ICon (removeIdInlinedPositions i) ic)
        -- XXX do we need a recursive branch for IAps?
        removeFn e = e
    in  Generic.everywhere (Generic.mkT removeFn) imod0

-- -----

-- After the evaluator has run and the heap pointers have been collected,
-- this code does CSE and tsorts the defs, in preparation for converting
-- to IDefs in the resulting IModule.

-- eqPtrs has two outputs:
-- 1. a tsorted list of the heap pointers (used to build the output module)
-- 2. a heap-reference to heap-reference map that seems to be used to do
-- some sort of heap compression and/or CSE (is this still useful)?
eqPtrs :: IM.IntMap HeapCell -> [HeapPointer] ->
          ([HeapPointer], IM.IntMap HeapPointer)
eqPtrs heap ptrs =
    let getHeapCell p = case (IM.lookup p heap) of
                        Just cell -> cell
                        Nothing -> internalError("eqPtrs.getHeapCell " ++ ppReadable p)
        heapOf p =
                case (getHeapCell p) of
                HNF { hc_pexpr = P _ e } -> e
                e -> internalError ("eqPtrs.heapOf " ++ ppReadable e)
        hptrs (IAps f _ es) = foldr (union . hptrs) [] (f:es)
        hptrs (ICon _ (ICStateVar { iVar = IStateVar { isv_iargs = es } }))
                            = foldr (union . hptrs) [] es
        hptrs (IRefT _ p _) = [p]
        hptrs _ = []
        g = [(p, hptrs (heapOf p)) | p <- ptrs ]
        ptrs' = case tSortInt g of
                Left iss -> internalError ("eqPtrs: circular: " ++ ppReadable iss ++ "\n" ++
                                            (concatMap (ppReadable . heapCellToHExpr . getHeapCell)
                                                    (concatMap id iss)))
                Right ps -> ps
        step p (dsm, ptrm) =
                let e = sub (heapOf p)
                    sub (IAps f ts es) = IAps (sub f) ts (map sub es)
                    sub e@(IRefT t i _) =
                        case IM.lookup i ptrm of
                        Nothing -> e
                        -- hd_ref errors because we don't use it once we have the iheap
                        Just i' -> IRefT t i' (internalError "eqPtrs ref")
                    sub e = e
                in  case M.lookup e dsm of
                    Nothing -> (M.insert e p dsm, ptrm)
                    Just h -> (dsm, IM.insert p h ptrm)
        (dsm, ptrm) = foldr step (M.empty, IM.empty) (reverse ptrs')
    in  --traces (show (length ptrs, length (M.elems dsm))) $
        --traces (show (IM.toList ptrm)) $
        --traces (show (M.elems dsm)) $
        (M.elems dsm, ptrm)


-----------------------------------------------------------------------------

-- convert top level module definition for which code is being generated
iExpandModuleDef ::
    HDef ->
    G ([(Id, IKind)], [IAbstractInput], [VArgInfo], [IEFace HeapData])
iExpandModuleDef (IDef i t e _) = do
    -- this was to allow code-gen of modules with numeric parameters,
    -- but we don't support that, so set the list of such params to null
    let iks = []
    when doDebug $ traceM "iExpandModuleDef: expanding"
    let user_mod_name = init (getIdBaseString i)
    showTopProgress ("Elaborating module " ++ quote user_mod_name)

    let mod_id = i
        mod_pos = getPosition i

    -- create the initial scope for scheduling attributes
    -- (putting the top-level method names into scope)
    pushTopModuleSchedNameScope t
    fmod <- isNoInlinedFunc
    pps <- getPragmas

    (clkRst, default_args, default_vargs) <-
        if (fmod)
        then return ((missingDefaultClock, missingDefaultReset), [], [])
        else do
           let def_clk_id = setIdPosition mod_pos idDefaultClock
               def_rst_id = setIdPosition mod_pos idDefaultReset
               has_clk = hasDefaultClk pps
               has_rst = hasDefaultRst pps
               gated   = isGatedDefaultClk pps ||
                         -- continue to consult the trace flag
                         gateDefaultClock
           (topClk, clockargs, vclkargs) <-
               if has_clk
               then do (c, a, v) <- makeInputClk gated def_clk_id
                       return (c, [a], [v])
               else return (missingDefaultClock, [], [])
           -- associate the default reset with the default clock
           let reset_clock_family = if has_clk
                                    then (Just def_clk_id)
                                    else Nothing
           (topRstn, resetargs, vrstargs) <-
               if has_rst
               then do (r, a, v) <- makeInputRstn def_rst_id reset_clock_family
                       return (r, [a], [v])
               else return (missingDefaultReset, [], [])
           return ((topClk, topRstn), clockargs ++ resetargs, vclkargs ++ vrstargs)
    -- iExpandModuleLam elaborates the actual module
    (args, vargs, (P p_ifc ifc)) <- iExpandModuleLam i clkRst e

    showTopProgress "Elaborating interface"
    pushIfcSchedNameScope

    ifc' <- addPredG p_ifc (do (_, ifc_uh) <- evalUH ifc; return ifc_uh)

    -- iExpandIface:
    --   turns a struct of ILams into IEFace: evaluates method bodies and takes
    --   the methods out of the interface struct
    ifcs <- iExpandIface mod_id clkRst ifc'

    popIfcSchedNameScope

    let args'  = args  ++ default_args
    let vargs' = vargs ++ default_vargs
    -- XXX Assert here that args' and vargs' are the same length?

    chkInputClockPragmas vargs'

    showTopProgress ("Finished elaborating module " ++ quote user_mod_name)
    return (iks, args', vargs', ifcs)

-- ----------

-- Elaborate a (top-level) module with arguments
iExpandModuleLam :: Id -> (HClock, HReset) -> HExpr
                 -> G ([IAbstractInput], [VArgInfo], PExpr)
iExpandModuleLam i clkRst e = do
    -- the separation of the core expression from the ILam
    -- relies on the property that none of the ILam ids are the same
    -- (so the substitution is safe to do on just the core expression)
    -- (alternatively, we could have created an iExpandModuleArgsWith
    -- function which takes a function for clocks or resets or ports
    -- and walks the IExpr each time)

    -- evaluate the initial expression to resolve top-level
    -- dictionary bindings that weren't inlined
    e0 <- evaleUH e

    (its, mod_expr0) <- extractModuleArgs i e0

    -- use Either type to record the progress
    let as0 = map Right its
    -- process clocks
    (as1, mod_expr1) <- iExpandModuleClockArgs i as0 mod_expr0
    -- process resets
    (as2, mod_expr2) <- iExpandModuleResetArgs i as1 mod_expr1
    -- process inouts
    (as3, mod_expr3) <- iExpandModuleInoutArgs i clkRst as2 mod_expr2
    -- process ifc args
    (as4, mod_expr4) <- --iExpandModuleIfcArgs i as3 mod_expr3
                        return (as3, mod_expr3)
    -- process remaining args
    (as5, mod_expr5) <- iExpandModulePortArgs i clkRst as4 mod_expr4
    -- extract the results
    let mod_expr = mod_expr5
    let (absinps, vargs) =
            case (separate as5) of
                (processed_as, []) -> unzip processed_as
                (_, unprocessed_as) ->
                    internalError ("iExpandModuleLam: unprocessed args: " ++
                                   ppReadable unprocessed_as)
    -- elaborate the module body
    e' <- iExpandModule False clkRst [] pTrue mod_expr
    -- return the results
    return (absinps, vargs, e')

type ArgState = Either (IAbstractInput, VArgInfo) (Id, IType)

extractModuleArgs :: Id -> HExpr -> G ([(Id, IType)], HExpr)
extractModuleArgs i e@(ILAM {}) =
    -- If a module to be generated has type parameters, then it means that
    -- an argument to the module was not bitifiable (and thus typechecking
    -- left in a proviso, which was unsatisfied).  Report it as an error.
    errG (reportNonSynthTypeInModuleArg i e)
extractModuleArgs i
    lam@(ILam li t@(ITCon ti _ (TIstruct SInterface{} fs)) e) = do
  -- This should not be reached, since GenWrap now reports this error
  errG (getIExprPosition lam, EInterfaceArg (pfpString i))
extractModuleArgs i (ILam li t e) = do
    let a = (li, t)
    (as, e') <- extractModuleArgs i e
    return (a:as, e')
extractModuleArgs i (IAps (ICon _ (ICPrim _ PrimPoisonedDef)) _ _) =
  -- report without package qualifier to match other extractModuleArgs errors
  errG (getIdPosition i, EPoisonedDef (text (init (getIdBaseString i))))
extractModuleArgs i e = return ([], e)

iExpandModuleClockArgs :: Id -> [ArgState] -> HExpr -> G ([ArgState], HExpr)
iExpandModuleClockArgs i ((Right (clk_id,t)):as) e | t == itClock = do
  when (clk_id == emptyId) $
      internalError ("iExpandModuleClockArgs: empty clock argument name")
  -- XXX reserved clocks should be prohibited earlier
  when ((clk_id == idDefaultClock) || (getIdString clk_id == "no_clock")) $
      errG (getPosition clk_id, EReservedClock (getIdString clk_id))
  pps <- getPragmas
  let gated = isGatedInputClk pps (unQualId clk_id) ||
              -- continue to consult the trace flag
              gateClockInputs
  (clock, abs_input, varginfo) <- makeInputClk gated clk_id
  let a' = Left (abs_input, varginfo)
  let e' = eSubst clk_id (icClock i clock) e
  (as', e'') <- iExpandModuleClockArgs i as e'
  return (a':as', e'')
iExpandModuleClockArgs i (a:as) e = do
  (as', e') <- iExpandModuleClockArgs i as e
  return (a:as', e')
iExpandModuleClockArgs i [] e = return ([], e)

iExpandModuleResetArgs :: Id -> [ArgState] -> HExpr ->
                            G ([ArgState], HExpr)
iExpandModuleResetArgs i ((Right (rst_id,t)):as) e | t == itReset = do
  when (rst_id == emptyId) $
      internalError ("iExpandModuleResetArgs: empty reset argument name")
  -- XXX reserved resets should be prohibited earlier
  when ((rst_id == idDefaultReset) || (getIdString rst_id == "no_reset")) $
      errG (getPosition rst_id, EReservedReset (getIdString rst_id))

  pps <- getPragmas
  -- find the associated reset for the port, from any attributes
  -- (no_clock is assumed if no attributes are given, and the clock
  -- will be derived from the uses of the reset)
  let (has_attr, mclk_name) = findModArgClockedByAttr pps rst_id
  (reset, abs_input, varginfo) <- makeInputRstn rst_id mclk_name
  -- if the user specified a clock_by attribute, then mark that clock domain
  -- in the deriving information (we don't want deriving to give it a domain)
  when (has_attr) $ let cd = getClockDomain (getResetClock reset)
                    in  setInputResetClockDomain reset cd
  let a' = Left (abs_input, varginfo)
  let e' = eSubst rst_id (icReset i reset) e
  (as', e'') <- iExpandModuleResetArgs i as e'
  return (a':as', e'')
iExpandModuleResetArgs i (a:as) e = do
  (as', e') <- iExpandModuleResetArgs i as e
  return (a:as', e')
iExpandModuleResetArgs i [] e = return ([], e)

iExpandModuleInoutArgs :: Id -> (HClock, HReset) -> [ArgState] -> HExpr
                   -> G ([ArgState], HExpr)
iExpandModuleInoutArgs i clkRst ((Right (iot_id,t@(ITAp tc (ITNum sz)))):as) e
          | tc == itInout_ = do
  -- find the associated clock/reset for the port, from any attributes
  (mclk_name, mrst_name) <- findModArgClockReset clkRst iot_id
  (inout, abs_input, varginfo) <- makeArgInout iot_id sz mclk_name mrst_name
  let a' = Left (abs_input, varginfo)
  let e' = eSubst iot_id (icInout iot_id sz inout) e
  (as', e'') <- iExpandModuleInoutArgs i clkRst as e'
  return (a':as', e'')
iExpandModuleInoutArgs i clkRst ((Right (iot_id,(ITAp tc _)):as)) e
          | tc == itInout_ = do
                             internalError("IexpandmoduleInoutArgs")
iExpandModuleInoutArgs i clkRst (a:as) e = do
  (as', e') <- iExpandModuleInoutArgs i clkRst as e
  return (a:as', e')
iExpandModuleInoutArgs i clkRst [] e = return ([], e)

-- module arguments which are not clock, reset, or ifc arg
iExpandModulePortArgs :: Id -> (HClock, HReset) -> [ArgState] -> HExpr ->
                         G ([ArgState], HExpr)
iExpandModulePortArgs i clkRst ((Right (li,t)):as) e = do
    -- turn the argument into an ICModPort (module port), or into an
    -- ICModParam if the user specified that it be a module parameter
    pps <- getPragmas

    let isParam = isParamModArg pps li
        arg_id  = if isParam
                  then makeArgParamId pps li
                  else makeArgPortId pps li
        arg_str = getIdBaseString arg_id
        iconinfo = if isParam
                   then ICModParam t
                   else ICModPort t
        e'= eSubst li (ICon arg_id iconinfo) e

    when (isParamOnlyType t && not isParam) $
         deferErrors [(getPosition li, EParamOnlyType (getIdBaseString li) (pfpString t))]

    -- find the associated clock/reset for the port, from any attributes
    (mclk_name, mrst_name) <-
      if (isParam)
      then return (Nothing, Nothing)
      else findModArgClockReset clkRst arg_id

    let vname = VName arg_str
        -- XXX support VeriPortProps on arguments
        varginfo = if isParam
                   then Param vname
                   else Port (vname,[]) mclk_name mrst_name
        abs_input = IAI_Port (arg_id, t)
    let a' = Left (abs_input, varginfo)

    (as', e'') <- iExpandModulePortArgs i clkRst as e'
    return (a':as', e'')
iExpandModulePortArgs i clkRst (a:as) e = do
  (as', e') <- iExpandModulePortArgs i clkRst as e
  return (a:as', e')
iExpandModulePortArgs i clkRst [] e = return ([], e)

{- -- obsoleted support for interface arguments
iExpandModuleIfcArgs :: (?pps :: [PProp])
                   => Id -> [ArgState] -> HExpr
                   -> G ([ArgState], HExpr)
iExpandModuleIfcArgs i
    ((Right (li, arginfo,
             t@(ITCon ti _ (TIstruct SInterface{} fs))), a):as) e =
    do
        addMessage (getIdPosition i, swarning ++ ": " ++ prError (WInterfaceArg (pfpString i)))
        flags <- getFlags
        symt <- getSymTab
        let v = unQualId i
            mts = map (\ f -> tail (itSplit (lookupSelType flags ti f symt))) fs
            mus = [ (i, n) | (i, (n,_)) <- argMeths arginfo ]
            vinf = VModInfo {
                        vName = VName (getIdString v),
                        vClk = [], vRst = [],
                        vNParam = 0, vArgs = [],
                        vFields = [ (f, lookupWithDefault mus 1 f, zipWith (\ t n -> (argName f t n, [])) ts [0..]) | (f, ts) <- zip fs mts ],
                        vSched = argSched arginfo
                        }
            argName f _ i = VName (ifcArgName n ('_' : getIdString f) i)
        sv <- newState False t mts vinf [(v,t)] []
        let e' = eSubst li sv e
        iExpandModuleIfcArgs i as e'
iExpandModuleIfcArgs i (a:as) e = do
  (as', e') <- iExpandModuleIfcArgs i as e
  return (a:as', e')
iExpandModuleIfcArgs i [] e = return ([], e)
-}

-- -----

-- find the clock and reset for a port, from any attributes
-- (the clock/reset are added to the monad and the Ids for the VArgInfo
-- are returned)
findModArgClockReset :: (HClock, HReset) -> Id
                     -> G (Maybe Id, Maybe Id)
findModArgClockReset clkRst arg_id = do
    pps <- getPragmas
    (hclk, mclkId) <-
        case (findModArgClockedByAttr pps arg_id) of
            (False, _) -> do
                let curClk = let c = fst clkRst
                             in if (isMissingDefaultClock c)
                                then noClock
                                else c
                mId <- boundaryClockToName curClk
                return (curClk, mId)
            (True, Nothing) -> return (noClock, Nothing)
            (True, Just clk_id) -> do
                -- until we support recursive instantiation,
                -- this can only be an input clock
                mclk <- getBoundaryClock clk_id
                let clk_err = "iExpandModulePortArgs: bad clk: " ++
                              pfpString clk_id
                    clk = fromJustOrErr clk_err mclk
                return (clk, Just clk_id)
    (hrst, mrstId) <-
        case (findModArgResetByAttr pps arg_id) of
            (False, _) -> do
                let curRst = let r = snd clkRst
                             in  if (isMissingDefaultReset r)
                                 then noReset
                                 else r
                mId <- boundaryResetToName curRst
                return (curRst, mId)
            (True, Nothing) -> return (noReset, Nothing)
            (True, Just rst_id) -> do
                -- until we support recursive instantiation,
                -- this can only be an input reset
                mrst <- getBoundaryReset rst_id
                let rst_err = "iExpandModulePortArgs: bad rst: " ++
                              pfpString rst_id
                    rst = fromJustOrErr rst_err mrst
                return (rst, Just rst_id)
    addPort arg_id hclk hrst
    return (mclkId, mrstId)

findModArgClockedByAttr :: [PProp] -> Id -> (Bool, Maybe Id)
findModArgClockedByAttr pps arg_id =
    let attr_clk = listToMaybe [ c | PParg_clocked_by ps <- pps,
                                     (i, c) <- ps, i == arg_id ]
    in  case (attr_clk) of
            Nothing         -> (False, Nothing)
            Just "no_clock" -> (True, Nothing)
            Just clk_name   -> (True, Just (mk_homeless_id clk_name))

findModArgResetByAttr :: [PProp] -> Id -> (Bool, Maybe Id)
findModArgResetByAttr pps arg_id =
    let attr_rst = listToMaybe [ r | PParg_reset_by ps <- pps,
                                     (i, r) <- ps, i == arg_id ]
    in  case (attr_rst) of
            Nothing         -> (False, Nothing)
            Just "no_reset" -> (True, Nothing)
            Just rst_name   -> (True, Just (mk_homeless_id rst_name))

-- ----------

-- expands interface methods
-- iExpandField probably needs to be called in a type-driven order
-- (i.e. clocks, resets, other stuff) so that boundary clocks and resets can
-- be reconciled for each other and for methods
iExpandIface :: Id -> (HClock, HReset) -> PExpr -> G [IEFace HeapData]
iExpandIface modId clkRst (P pi e@(IAps c@(ICon _ (ICTuple { fieldIds = fs0 })) ts es)) = do
        flags <- getFlags
        symt <- getSymTab

        -- The field positions are generated in GenWrap from the position
        -- of the type in the symtab, so let's insert a better position for
        -- error messages.  In the absence of indicating the location of the
        -- def in the module, we just point to the module itself.
        let modPos = getIdPosition modId
            fs = map (setIdPosition modPos) fs0

        let ifcName = iGetIfcName (iGetType e)
        let betterInfo = BetterInfo.extractMethodInfo flags symt ifcName
        -- traceM ((ppReadable ifcName) ++ ": " ++ (ppReadable betterInfo))
        let newBetterInfo :: Id -> BetterInfo.BetterInfo
            newBetterInfo f = fromMaybe (BetterInfo.noMethodInfo f)
                              (find (BetterInfo.matchMethodName f) betterInfo )
        let betterInfoByField ::  [BetterInfo.BetterInfo]
            betterInfoByField = map newBetterInfo fs
        -- traceM (ppReadable (zip fs betterInfoByField))

        let fieldTypes = map iGetType es

        let fieldBlobs =
                zip4 (map unQualId fs) betterInfoByField es fieldTypes

        -- partition into output clocks, output resets, and methods
        let isClockField (_,_,_,t) = (t == itClock)
            isResetField (_,_,_,t) = (t == itReset)
            (clockfields, fs1) = partition isClockField fieldBlobs
            (resetfields, methodfields) = partition isResetField fs1

        let expFn = iExpandField modId pi clkRst

        -- handle clocks first
        clock_xs  <- mapM expFn clockfields
        -- now make the domainToBoundaryIds (used in handling output resets)
        makeDomainToBoundaryIdsMap
        -- handle resets next
        reset_xs  <- mapM expFn resetfields
        -- handle methods last
        method_xs <- mapM expFn methodfields

        return $ concat (clock_xs ++ reset_xs ++ method_xs)

iExpandIface _ _ (P pi (ICon _ (ICTuple { fieldIds = [] }))) | pi == pTrue =
    do -- need to make sure the map is made!
       makeDomainToBoundaryIdsMap
       return []
iExpandIface _ _ e = internalError ("iExpandIface: " ++ ppReadable e)


-- expand an interface field
iExpandField :: Id -> HPred -> (HClock, HReset) ->
                (Id, BetterInfo.BetterInfo, HExpr, IType) -> G [IEFace HeapData]
iExpandField _ implicitCond _ (i, bi, e, t) | t == itClock = do
  showTopProgress ("Elaborating output clock " ++ quote (pfpString i))
  setIfcSchedNameScopeProgress (Just (IEP_OutputClock i))
  when (implicitCond /= pTrue) $ do
      -- XXX this error message should be improved (see EModPortHasImplicit)
      deferErrors [(getIExprPosition e, EHasImplicit (ppReadable e))]
  (c, e') <- evalClock e
  -- if the output clock is defined as an input clock, that input clock
  -- must either have a gate port or the missing port must be inhigh
  addInhighClkGate c
  fi <- makeOutputClk True i (BetterInfo.mi_prefix bi) c
  setIfcSchedNameScopeProgress Nothing
  return [(IEFace i [] (Just (e',t)) Nothing emptyWireProps fi)]

iExpandField modId implicitCond _ (i, bi, e, t) | t == itReset = do
  showTopProgress ("Elaborating output reset " ++ quote (pfpString i))
  setIfcSchedNameScopeProgress (Just (IEP_OutputReset i))
  when (implicitCond /= pTrue) $
      -- XXX this error message should be improved (see EModPortHasImplicit)
      deferErrors [(getIExprPosition e, EHasImplicit (ppReadable e))]
  (r, e') <- evalReset e
  let modPos = getPosition modId
  fi <- makeOutputRstn modPos i (BetterInfo.mi_prefix bi) r
  setIfcSchedNameScopeProgress Nothing
  return [(IEFace i [] (Just (e',t)) Nothing emptyWireProps fi)]

iExpandField modId implicitCond clkRst (i, bi, e, t) | isitInout_ t = do
  showTopProgress ("Elaborating interface inout " ++ quote (pfpString i))
  setIfcSchedNameScopeProgress (Just (IEP_OutputInout i))
  when (implicitCond /= pTrue) $
      -- XXX this error message should be improved (see EModPortHasImplicit)
      deferErrors [(getIExprPosition e, EHasImplicit (ppReadable e))]
  (iinout, e') <- evalInout e
  let modPos = getPosition modId
  (ws, fi) <- makeIfcInout modPos i (BetterInfo.mi_prefix bi) iinout
  setIfcSchedNameScopeProgress Nothing
  return [(IEFace i [] (Just (e',t)) Nothing ws fi)]

iExpandField modId implicitCond clkRst (i, bi, e, t) | isRdyId i =
  return []

iExpandField modId implicitCond clkRst (i, bi, e, t) = do
   showTopProgress ("Elaborating method " ++ quote (pfpString i))
   setIfcSchedNameScopeProgress (Just (IEP_Method i False))
   (_, P p e') <- evalUH e
   let (ins, eb) = case e' of
        ICon _ (ICMethod _ ins eb) -> (ins, eb)
        _ -> internalError ("iExpandField: expected ICMethod: " ++ ppReadable e')
   (its, ((IDef i1 t1 e1 _), ws1, fi1), ((IDef wi wt we _), ws2, fi2))
       <- iExpandMethod modId 1 [] (pConj implicitCond p) clkRst (i, bi, ins, eb)
   let wp1 = wsToProps ws1 -- default clock domain forced in by iExpandField
   let wp2 = wsToProps ws2
   setIfcSchedNameScopeProgress Nothing
   return  [(IEFace i1 its (Just (e1,t1)) Nothing wp1 fi1),
            (IEFace wi [] (Just (we,wt)) Nothing wp2 fi2)]

-- expand a method
iExpandMethod :: Id -> Integer -> [Id] -> HPred ->
                 (HClock, HReset) -> (Id, BetterInfo.BetterInfo, [String], HExpr) ->
                 G ([(Id, IType)], (HDef, HWireSet, VFieldInfo),
                    (HDef, HWireSet, VFieldInfo))
iExpandMethod modId n args implicitCond clkRst@(curClk, _) (i, bi, ins, e) = do
    when doDebug $ traceM ("iExpandMethod " ++ ppString i ++ " " ++ ppReadable e)
    (_, P p e') <- evalUH e
    case e' of
     ILAM li ki eb ->
        -- must be due to a type which wasn't in Bits class
        -- (GenWrap checks for polymorphism, so this can only come from
        -- a GenWrap-added context that wasn't satisfied, and GenWrap
        -- should only be adding Bits)
        errG (reportNonSynthTypeInMethod modId i e')
     ILam li ty eb -> iExpandMethodLam modId n args implicitCond clkRst (i, bi, ins, eb) li ty p
     _ -> iExpandMethod' implicitCond curClk (i, bi, e') p

iExpandMethodLam :: Id -> Integer -> [Id] -> HPred ->
                 (HClock, HReset) -> (Id, BetterInfo.BetterInfo, [String], HExpr) ->
                 Id -> IType -> Pred HeapData ->
                 G ([(Id, IType)], (HDef, HWireSet, VFieldInfo),
                    (HDef, HWireSet, VFieldInfo))
iExpandMethodLam modId n args implicitCond clkRst (i, bi, ins, eb) li ty p = do
    -- traceM ("iExpandMethodLam " ++ ppString i ++ " " ++ show ins)
    let i' :: Id
        i' = mkId (getPosition i) $ mkFString $ head ins
        -- substitute argument with a modvar and replace with body
        eb' :: HExpr
        eb' = eSubst li (ICon i' (ICMethArg ty)) eb
    (its, (d, ws1, wf1), (wd, ws2, wf2)) <-
        iExpandMethod modId (n+1) (i':args) (pConj implicitCond p) clkRst (i, bi, tail ins, eb')
    let inps :: [VPort]
        inps = vf_inputs wf1
    let wf1' :: VFieldInfo
        wf1' = case wf1 of
                  (Method {}) -> wf1 { vf_inputs = ((id_to_vPort i'):inps) }
                  _ -> internalError "iExpandMethodLam: unexpected wf1"
    return ((i', ty) : its, (d, ws1, wf1'), (wd, ws2, wf2))

iExpandMethod' :: HPred -> HClock -> (Id, BetterInfo.BetterInfo, HExpr) ->
                  Pred HeapData ->
                 G ([(Id, IType)], (HDef, HWireSet, VFieldInfo),
                    (HDef, HWireSet, VFieldInfo))
iExpandMethod' implicitCond curClk (i, bi, e0) p0 = do
        -- want the result type, not a type including arguments
        let methType :: IType
            methType = iGetType e0
        (P p e', ws1) <- case e0 of
                         -- tuples are allowable for ActionValue methods only
                         IAps f@(ICon _ (ICTuple {})) ts [e1, e2] |
                                isActionType methType ->
                             do (P p1 e1', ws_a) <- evalUHNF e1
                                (P p2 e2', ws_b) <- evalUHNF e2
                                return (P (pConjs [p0, p1, p2]) (IAps f ts [e1', e2']),
                                        wsJoin ws_a ws_b)
                         _ -> do (P p' e', ws1) <- walkNF e0
                                 return (P (pConj p0 p') e', ws1)

        showTopProgress ("Elaborating method implicit condition")
        setIfcSchedNameScopeProgress (Just (IEP_Method i True))
        p_norm <- normPConj (pConj implicitCond p)
        (readySignal, ws2) <- evalPred p_norm
        setIfcSchedNameScopeProgress (Just (IEP_Method i False))

        let methExpr :: HExpr
            methExpr = (iePrimWhen methType readySignal e')

        -- The wireset for a method is really the combination of the
        -- wiresets for its body and its predicate
        let ws = wsJoin ws1 ws2
        chkClockDomain "method" i ws methExpr
        chkResetDomain "method" i ws methExpr

        when doDebug $ traceM ("field " ++ ppReadable (i, readySignal, e'))

        -- action methods get the default clock when there is no other
        -- XXX distinguish between "no clock" and "noClock"?
        let (final_e, final_ws) =
              if isActionType methType then
                case (fixupActionWireSet curClk ws) of
                  Just ws' -> (e', ws')
                  Nothing ->
                      case e' of
                        IAps f@(ICon _ (ICTuple {})) ts [e1, e2]
                          | isActionType methType
                          -> let pos = getIdPosition i
                                 vt = actionValue_BitN methType
                                 v = icUndetAt pos vt UNotUsed
                             in  (IAps f ts [v, icNoActions], ws)
                        _ -> internalError "iExpandMethod: fixupActionWireSet"
              else (e', ws)

        methClock <- methodClockName i methType final_ws
        when doTraceClock $ traceM ("methType: " ++ ppReadable methType ++
                                    "methClock: " ++ ppReadable methClock)
        methReset <- methodResetName i final_ws
        when doTraceClock $ traceM ("methReset: " ++ ppReadable methReset)

        let rdyId :: Id
            rdyId      = mkRdyId i
        let enablePort :: Maybe VPort
            enablePort = toMaybe (isActionType methType) (BetterInfo.mi_enable bi)
        let outputPort :: Maybe VPort
            outputPort = toMaybe (isValueType  methType) (BetterInfo.mi_result bi)
        let rdyPort :: VPort
            rdyPort    = BetterInfo.mi_ready bi

        -- split wire sets for more accurate tracking
        return ([],
                ((IDef i (iGetType final_e) final_e []), final_ws,
                 Method { vf_name = i,
                          vf_clock = methClock, vf_reset = methReset,
                          vf_mult = 1, vf_inputs = [],
                          vf_output = outputPort, vf_enable = enablePort }),
                ((IDef rdyId itBit1 readySignal []), final_ws,
                 Method { vf_name = rdyId,
                          vf_clock = methClock, vf_reset = methReset,
                          vf_mult = 1, vf_inputs = [],
                          vf_output = Just rdyPort, vf_enable = Nothing }))

-- deduce clock name for VFieldInfo
-- type required to control ancestry-checking with action methods
methodClockName :: Id -> IType -> HWireSet -> G (Maybe Id)
methodClockName i t ws = do
-- XXX clock-gating for action methods
  boundaryClocks <- getBoundaryClocks
  -- just put in something bogus if there is a clock-crossing error
  let methDomain = fromMaybe noClockDomain (wsGetClockDomain ws)
  if (methDomain == noClockDomain) then return Nothing else do
    let candidateClocks = filter (inClockDomain methDomain) boundaryClocks
    let returnClock c = do mId <- boundaryClockToName c
                           when (not (isJust mId)) $ internalError ("IExpand.methodClockName non-boundaryClock" ++ ppReadable c)
                           return mId
    case candidateClocks of
      []  -> do deferErrors [(getPosition i, EMethodNoBoundaryClock (pfpString i))]
                return Nothing -- pretend it is noClock because we'll die anyway
      -- only one clock in the domain, so no choice
      [c] -> returnClock c
      _ -> do let betterClocks = candidateClocks `intersect` (wsGetClocks ws)
              case (listToMaybe betterClocks) of
                Just c  -> returnClock c
                -- XXX pick a clock arbitrarily (should look at ancestry)
                Nothing -> returnClock (head candidateClocks)

methodResetName :: Id -> HWireSet -> G (Maybe Id)
methodResetName i ws = do
  boundaryResets <- getBoundaryResets
  let methodResets = wsGetResets ws
      pos = getPosition i
  case methodResets of
    []  -> return Nothing
    [r] -> if r `elem` boundaryResets then
               boundaryResetToName r
            else do eWarning (pos, WMethodNoBoundaryReset (pfpString i))
                    return Nothing
    _   -> case (listToMaybe (methodResets `intersect` boundaryResets)) of
             Nothing -> do eWarning (pos, WMethodNoBoundaryReset (pfpString i))
                           return Nothing
             Just r  -> do res <- boundaryResetToName r
                           eWarning (pos, WMethodMultipleBoundaryReset
                                            (pfpString i) (fmap pfpString res))
                           return res

-----------------------------------------------------------------------------

-- "run" the module monad, collecting rules, interfaces, and state
iExpandModule :: Bool -> (HClock, HReset) ->
                 IStateLoc -> HPred -> HExpr -> G PExpr
iExpandModule isMFix curClkRstn ns p e = do
        when doDebug $ traceM "iExpandModule"
        (_, P p e') <- evalUH e
        handlePrim isMFix curClkRstn ns p e'

handlePrim :: Bool -> (HClock, HReset) ->
              IStateLoc -> HPred -> HExpr -> G PExpr

handlePrim isMFix curClkRstn ns@(islpc:rest) p eee@(IAps prim@(ICon _ (ICPrim _ PrimStateName)) [ifc_t] [e, em]) = do
   when doDebug $ traceM "handlePrim: PrimStateName"
   e' <- evaleUH e -- extract name
   case e' of
     ICon _ (ICName {iName = i }) -> do
         when doDebug $ traceM ("name: " ++ ppReadable i)
         em_u <- shallowUnheap em
         -- rebuild IStateLoc with new id
         ns' <- newIStateLoc i (isl_ifc_id islpc) ifc_t rest
         showModProgress ns' "Elaborating module"
         pushModuleSchedNameScope ns' ifc_t
         res <- iExpandModule isMFix curClkRstn ns' p em
         popModuleSchedNameScope
         showModProgress ns' "Finished module"
         return res
     _ -> nfError "PrimStateName" e'

handlePrim isMFix curClkRstn ns p eee@(IAps prim@(ICon _ (ICPrim _ PrimStateAttrib)) ts [e, em]) = do
   when doDebug $ traceM "handlePrim: PrimStateAttrib"
   e' <- evaleUH e -- extract attributes
   case e' of
     ICon _ (ICAttrib {iAttributes = as }) -> do
         when doDebug $ traceM ("attributes: " ++ ppReadable (map snd as))
         em_u <- shallowUnheap em
         -- what is the name of the thing being instantiated here
         let instname = stateLocToId ns
         -- handle the attributes:
         --   doc attributes are added to the state,
         --   no other attributes are supported yet
         let comments = [line | PPdoc comment <- map snd as,
                                line <- lines comment]
         addSubmodComments instname comments
         iExpandModule isMFix curClkRstn ns p em
     _ -> nfError "PrimStateAttrib" e'

handlePrim isMFix curClkRstn ns p ea@(IAps (ICon _ (ICPrim { primOp = PrimModuleBind })) [t1, t2] [e1, e2]) = do
        -- expand monadic binding x <- e1; e2
        when doDebug $ traceM "handlePrim: PrimModuleBind"

        e1u <- shallowUnheap e1
        e2u <- shallowUnheap e2
        -- A little hack to try and figure out a good name for a
        -- lambda-bound state component
        (ns', do_msg) <-
            case (e2u) of
              (ILam i t _) -> do
                  new_ns <- newIStateLoc i i t ns
                  -- In some cases, "setStateName" will replace this value,
                  -- so don't print a progress message yet
                  case (e1u) of
                    (IAps (ICon f (ICDef {})) _ _)
                        | f == (idSetStateNameAt noPosition)
                        -> return (new_ns, False)
                    (IAps (ICon f1 (ICDef {})) _
                          (_:(IAps (ICon f2 (ICDef {})) _ _):_))
                        | (f1 == (idForceIsModuleAt noPosition)) &&
                          (f2 == (idSetStateNameAt noPosition))
                        -> return (new_ns, False)
                    _ -> return (new_ns, True)
              _ -> return (ns, False)
        when do_msg $ do
            showModProgress ns' "Elaborating module"
            pushModuleSchedNameScope ns' t1
        when doDebug $ traceM ("bind\n" ++ ppReadable e2u)
        when doDebug $ traceM ("bind " ++ ppReadable e1)
        when doDebug $ traceM ("bind " ++ ppReadable ea)
        P p1 e1' <- iExpandModule isMFix curClkRstn ns' p e1
        when do_msg $ do
            showModProgress ns' "Finished module"
            popModuleSchedNameScope
        iExpandModule isMFix curClkRstn ns p1 (IAps e2 [] [e1'])

handlePrim isMFix curClkRstn ns p ea@(IAps (ICon _ (ICPrim { primOp = PrimModuleReturn })) _ [e]) = do
        when doDebug $ traceM "handlePrim: PrimModuleReturn"
        if isMFix then {- lazy -} return (P p e) else {- strict -} eval1 (pExprToHExpr (P p e))

handlePrim isMFix curClkRstn ns p e_rs@(IAps (ICon _ (ICPrim { primOp = PrimAddRules })) _ [rs]) = do
        when doDebug $ traceM "handlePrim: PrimAddRules"
        if isMFix then saveRules curClkRstn ns p e_rs
         else iExpandRules curClkRstn ns p rs
        -- just need to return ()
        return (P p (icUndet itPrimUnit UNotUsed))

handlePrim isMFix (curClock, curReset) ns p ea@(ICon i (ICPrim { primOp = PrimCurrentClock })) = do
       when doDebug $ traceM "handlePrim: PrimCurrentClock"
       if (isMissingDefaultClock curClock) then do
         let err_pos = getPosition ns
         deferErrors [(err_pos, EUseMissingDefaultClock)]
         eval1 icNoClock
        else eval1 (pExprToHExpr (P p (icClock i curClock)))

handlePrim isMFix (curClock, curReset) ns p ea@(ICon i (ICPrim { primOp = PrimCurrentReset })) = do
       when doDebug $ traceM "handlePrim: PrimCurrentReset"
       if (isMissingDefaultReset curReset) then do
         let err_pos = getPosition ns
         deferErrors [(err_pos, EUseMissingDefaultReset)]
         eval1 icNoReset
        else eval1 (pExprToHExpr (P p (icReset i curReset)))

-- module fix: reorders, but does not handle mutually recursive bindings
handlePrim isMFix curClkRstn ns p ea@(IAps (ICon _ (ICPrim { primOp = PrimModuleFix })) [t] [e]) = do
        when doDebug $ traceM "handlePrim: enter PrimModuleFix"
        showModProgress ns ("Attempting recursive module instantiation")
        (ptr, ref) <- addHeapCell "prim-mod-fix" (HLoop (Just (stateLocToId ns)))
        let rt = IRefT t ptr ref
        stno <- getStateNo
        old_rblobs <- getSavedRules
        clearSavedRules
        P p' e' <- iExpandModule True curClkRstn ns p (IAps e [] [rt])
        new_rblobs <- getSavedRules
        -- correctly writing the recursive reference (making sure it is evaluated and unheaped)
        -- requires some contortions
        _ <- do e'' <- (addPredG p' $ eval1 e') >>= unheap
                updHeap "moduleFix" (ptr, ref) (HWHNF e'' Nothing)
        -- handle any recursively deferred rules
        oldAggressive <- isAggressive
        mapM_ (\(agg,a,b,c,d) -> do
                  setAggressive agg
                  _ <- handlePrim isMFix a b c d
                  setAggressive oldAggressive
                  ) new_rblobs

        stno' <- getStateNo
        -- updNStateVars (stno' - stno)
        replaceSavedRules old_rblobs
        when doDebug $ traceM ("handlePrim: exit PrimModuleFix\n" ++ ppReadable e')
        showModProgress ns ("Finished recursive module instantiation")
        return (pExpr rt)

handlePrim isMFix (_, rst) ns p ea@(IAps (ICon _ (ICPrim { primOp = PrimModuleClock })) _ [clke, e]) = do
        (clk, _) <- evalClock clke
        when doTraceClock $ traceM ("PrimModuleClock " ++ ppReadable (clk, rst))
        iExpandModule isMFix (clk, rst) ns p e

handlePrim isMFix (clk, _) ns p ea@(IAps (ICon _ (ICPrim { primOp = PrimModuleReset })) _ [rste, e]) = do
        (rst, _) <- evalReset rste
        when doTraceClock $ traceM ("PrimModuleReset " ++ ppReadable (clk, rst))
        iExpandModule isMFix (clk, rst) ns p e

-- instantiate a Verilog module
handlePrim isMFix (curClk, curRstn) ns p
    ea@(IAps (ICon _ x@(ICVerilog { vInfo = vmi,
                                    isUserImport = isImport }))
    _ (name:es)) =
     do
        when doDebug $ traceM ("handlePrim: module: " ++ ppString ns)
        -- XXX showProgress?
        -- remove argument types from type sig, to get actual module type
        let skip [] (ITAp _ t) = t
            skip (_:es) (ITAp _ t) = skip es t
            skip _ t = internalError ("IExpand.handlePrim: skip: " ++ show t)
            mod_type = skip (name:es) (iConType x)
        -- for error messages
        let inst_id = stateLocToId ns
            vargs = vArgs vmi
        (es', port_infos) <-
            -- if isMFix -- defer evaluation for PrimModuleFix
            -- then return (es, [])
            {- else -} mapAndUnzipM (iExpandSubmodArg inst_id) (zip vargs es)
        (estr, _) <- evalString name
        let info = (vInfo x) { vName = VName estr }
        --traceM ("new " ++ show x ++ "\n" ++ ppReadable es ++ ppReadable es')
        when doDebug $ do es'' <- mapM unheapAll es'
                          traceM ("handlePrim: module: args " ++ ppReadable es'')
        e <- newState True isImport mod_type (vMethTs x) info ns es'
        -- now that we have the clockmap, we can check the port uses
        let v = case e of
                    (ICon _ (ICStateVar { iVar = v })) -> v
                    _ -> internalError ("handlePrim: ICVerilog: " ++
                                        "newState didn't return ICStateVar")
        mapM_ (chkModuleArgumentClkRst inst_id v) (zip3 vargs es' port_infos)
        return (P p e)

handlePrim isMFix curClkRstn ns p e@(IAps (ICon _ (ICPrim { primOp = PrimSavePortType })) _ [e_mname, e_port, e_type]) = do
  mname <- do m <- evalMaybe e_mname
              case (m) of
                Nothing -> return Nothing
                Just e_name -> evalName e_name >>= return . Just
  (port, _) <- evalString e_port
  t <- evalType e_type
  savePortType mname (VName port) t
  -- just need to return ()
  return (P p (icUndet itPrimUnit UNotUsed))

handlePrim isMFix curClkRstn ns p e@(IAps (ICon _ (ICPrim { primOp = PrimChkClockDomain })) _ [e_name, e_object, e_chk]) = do
  name <- evalName e_name
  (object_str,_) <- evalString e_object
  (P _ e', ws) <- evalNF e_chk
  chkClockDomain object_str name ws e'
  return (P p (icUndet itPrimUnit UNotUsed))

handlePrim _ _ _ p e@(IAps (ICon _ (ICPrim { primOp = PrimOpenFile })) _ [e_fname, e_mode]) = do
  flags <- getFlags
  (fname0, _) <- evalString e_fname
  let fname = case (fdir flags) of
                Just path | (isRelative fname0)
                  -> path ++ "/" ++ fname0
                _ -> fname0
  mode <- do n <- evalInteger e_mode
             case n of
               0 -> return ReadMode
               1 -> return WriteMode
               2 -> return AppendMode
               _ -> internalError("primOpenFile mode")
  errh <- getErrHandle
  ctx <- getElabProgressContext
  h <- liftIO $ openFileCatch errh ctx fname mode
  liftIO $ recordHandleOpen errh h
  -- XXX give the handle a position from e?
  return (P p (iMkHandle h))

handlePrim _ _ _ p e@(IAps (ICon _ (ICPrim { primOp = PrimCloseHandle })) _ [e_hdl]) = do
  errh <- getErrHandle
  ctx <- getElabProgressContext
  h <- evalHandle e_hdl
  liftIO $ hCloseCatch errh ctx (getIExprPosition e) h
  liftIO $ recordHandleClose errh h
  return (P p (icUndet itPrimUnit UNotUsed))

handlePrim _ _ _ p e@(IAps (ICon _ (ICPrim { primOp = op })) _ [e_hdl]) | (handleBoolPrim op) = do
  errh <- getErrHandle
  ctx <- getElabProgressContext
  let pos = getIExprPosition e
  h <- evalHandle e_hdl
  b <- liftIO $
       case op of
         PrimHandleIsEOF      -> hIsEOFCatch errh ctx pos h
         PrimHandleIsOpen     -> hIsOpen h    -- does not error
         PrimHandleIsClosed   -> hIsClosed h  -- does not error
         PrimHandleIsReadable -> hIsReadableCatch errh ctx pos h
         PrimHandleIsWritable -> hIsWritableCatch errh ctx pos h
         _ -> internalError
                  ("IExpand: unexpected Handle prim: " ++ ppReadable op)
  return $ P p (iMkBoolAt pos b)

handlePrim _ _ _ p e@(IAps (ICon i (ICPrim { primOp = PrimSetHandleBuffering })) _ [e_hdl, e_mode]) = do
  errh <- getErrHandle
  ctx <- getElabProgressContext
  h <- evalHandle e_hdl
  m <- evalBufferMode e_mode
  liftIO $ hSetBufferingCatch errh ctx (getIExprPosition e) h m
  return (P p (icUndet itPrimUnit UNotUsed))

handlePrim _ _ _ p e@(IAps (ICon _ (ICPrim { primOp = PrimGetHandleBuffering })) _ [e_hdl]) = do
  errh <- getErrHandle
  ctx <- getElabProgressContext
  h <- evalHandle e_hdl
  mode <- liftIO $ hGetBufferingCatch errh ctx (getIExprPosition e) h
  return (P p (iMkBufferMode mode))

handlePrim _ _ _ p e@(IAps (ICon _ (ICPrim { primOp = PrimFlushHandle })) _ [e_hdl]) = do
  errh <- getErrHandle
  ctx <- getElabProgressContext
  h <- evalHandle e_hdl
  liftIO $ hFlushCatch errh ctx (getIExprPosition e) h
  return (P p (icUndet itPrimUnit UNotUsed))

handlePrim _ _ _ p e@(IAps (ICon _ (ICPrim { primOp = PrimWriteHandle })) _ [e_hdl, e_str]) = do
  errh <- getErrHandle
  ctx <- getElabProgressContext
  h <- evalHandle e_hdl
  (s, _) <- evalString e_str
  liftIO $ hPutStrCatch errh ctx (getIExprPosition e) h s
  return (P p (icUndet itPrimUnit UNotUsed))

handlePrim _ _ _ p e@(IAps (ICon _ (ICPrim { primOp = PrimReadHandleLine })) _ [e_hdl]) = do
  errh <- getErrHandle
  ctx <- getElabProgressContext
  h <- evalHandle e_hdl
  let pos = getIExprPosition e
  s <- liftIO $ hGetLineCatch errh ctx pos h
  return $ P p (iMkStringAt pos s)

handlePrim _ _ _ p e@(IAps (ICon _ (ICPrim { primOp = PrimReadHandleChar })) _ [e_hdl]) = do
  errh <- getErrHandle
  ctx <- getElabProgressContext
  h <- evalHandle e_hdl
  let pos = getIExprPosition e
  c <- liftIO $ hGetCharCatch errh ctx pos h
  return $ P p (iMkCharAt pos c)

handlePrim isMFix curClkRstn ns p e@(ICon i (ICUndet { iuKind=iuKind })) =
    let emsg = if (iuKind == UNoMatch)
               then EModuleUndetNoMatch
               else -- XXX should we handle UNotUsed separately too?
                    EModuleUndet
    in  errG (getIdPosition i, emsg)

-- it should have evaluated to a module
-- if it didn't it is because it didn't evaluate "all the way"
-- report if/case/dynsel as a friendly user error and others with nfError
handlePrim isMFix curClkRstn ns p e@(IAps (ICon _ (ICPrim { primOp = op })) _ _)
  | (condPrim op) =
    errG (getIExprPosition e, EDynamicModule)
handlePrim isMFix curClkRstn ns p e = do
  when doDebug $ traceM ("handlePrim: no match " ++ (ppReadable e))
  nfError "handlePrim" e
--        internalError ("iExpandModule handlePrim\n" ++ ppReadable e)

-- ----------

{-
updNStateVars :: Int -> G ()
updNStateVars n = do
        vs <- takeNStateVars n
        let f (ii, IStateVar b ui i vi es t tss nc nr l) = do
                es' <- mapM (iExpandSubmodArg) es
                return (ii, IStateVar b ui i vi es' t tss nc nr l)
        vs' <- mapM f vs
        addNStateVars vs'
-}
-- ----------

-- instantiate a state variable (Verilog module)
newState :: Bool -> Bool -> IType -> [[IType]] -> VModInfo ->
            IStateLoc -> [HExpr] -> G HExpr
newState b ui t tss vi ns es = do
    -- traceM("newState.tss: " ++ ppReadable tss ++ "|\n" ++ show tss);
    -- mfix is required because the resulting structure
    -- is recursive when there is an output clock
    sv@(ICon _ (ICStateVar {iVar = v})) <- mfix loopStateVar
    when doTraceClock $ traceM ("clock map\n" ++ (ppReadable (getClockMap v)))
    when doTraceClock $ traceM ("reset map\n" ++ (ppReadable (getResetMap v)))
    when doTraceClock $ traceM ("vmodinfo\n" ++ (ppReadable (getVModInfo v)))
    when doTraceLoc   $ traceM $ "NewState: " ++ ppReadable ns
    {-
    -- Note that we could get comments for this instance from the GState,
    -- and insert it into a new field in the IStateVar, which would then
    -- carry into a new field in the AVInst.  However, we don't do this,
    -- as it's easy enough to keep a table off to the side (in the IModule),
    -- which we need anyway for comments on submods which were inlined.
    -- This is the code we would use, if we wanted to extract the comments:
    let instname = stateLocToId ns
    comments <- getSubmodComments instname
    -}
    return sv
 where ClockInfo { input_clocks = in_clockinfs,
                   ancestorClocks = ancestors,
                   siblingClocks = siblings } = vClk vi
       ResetInfo { input_resets = in_reset_info,
                   output_resets = out_reset_info } = vRst vi

       -- group clocks by domain, using bidirectional edges
       domain_edges = ancestors ++ map swap ancestors ++
                      siblings  ++ map swap siblings
       domain_edges' = [(a, [b]) | (a, b) <- domain_edges]
       domain_graph = [(n,n,es) | (n, es) <- M.toList $ M.fromListWith (++) domain_edges']
       domain_sccs = stronglyConnComp domain_graph
       domain_groups = [ vs | CyclicSCC vs <- domain_sccs ]

       i0 = stateLocToId ns
       pos = getPosition i0 -- reasonable position for instantiation
       modName = getVNameString (vName vi)
       instName = pfpString i0

       -- -----
       loopStateVar :: HExpr -> G HExpr
       loopStateVar e = do
         no <- newStateNo
         when (doDebug || doTraceClock) $
             traceM ("newState " ++ ppReadable i0)
         clock_map <- handleClockConnections e
         reset_map <- handleResetConnections clock_map e
         let v  = IStateVar b ui no vi es t tss clock_map reset_map ns
         i <- uniqueStateName i0
         when doTraceLoc $  traceM("new state id: " ++ (ppString i))
         addStateVar (i, v)
         return $ ICon i (ICStateVar t v)

       -- -----

       handleClockConnections :: HExpr -> G [(Id, HClock)]
       handleClockConnections e = do
         es_clks <- mapM findClock es
         let clockargnum_map =
                 [ (id, c, n)
                      | (ClockArg id, ICon _ (ICClock {iClock = c}), n)
                            <- zip3 (vArgs vi) es_clks [0..] ]
             clockargs = [i | ClockArg i <- vArgs vi]
         when ((length clockargnum_map) /= (length clockargs)) $
             -- this may be ok because dynamic expressions should not be
             -- able to get here (because clocks and resets should not
             -- have wires attached)
             internalError
                 ("IExpand.newState: not all clock args have clocks " ++
                  ppReadable vi ++ ppReadable es)

         -- check that clock args whose gates are required to be True
         -- are connected to gates of value constant True
         chkClkArgGateWires modName instName pos in_clockinfs clockargnum_map

         -- check that arguments marked as ancestors really do have the
         -- right ancestry relationship
         chkClkAncestry modName instName pos ancestors clockargnum_map

         -- check that arguments marked as the same family really are
         -- in the same clock domain
         chkClkSiblings modName instName pos siblings clockargnum_map

         let clockarg_map = map fst2of3 clockargnum_map
         let clockwires_map =
                 let mkICSel n = ICSel { iConType = itClock,
                                         selNo = n,
                                         numSel = genericLength (vFields vi) }
                 in  [ (id, wires) |
                          -- index tuples from 0
                          (Clock id, n) <- zip (vFields vi) [0..],
                          let wires = {- trace ("id: " ++ show id) $ -}
                                      IAps (ICon id (mkICSel n)) [] [e]
                     ]

         when doTraceClock $ traceM ("domain_groups: " ++ ppReadable domain_groups)

         let makeOutClock :: [(Id,HClock)] -> (Id, HExpr) -> G [(Id,HClock)]
             makeOutClock clockMap (id, wires) = do
                 let same_domain_ids =  fromMaybe [] $ listToMaybe [ delete id vs | vs <- domain_groups, id `elem` vs ]
                     mclock = listToMaybe $ mapMaybe
                              ((flip lookup) clockMap) same_domain_ids
                     parent_ids = [p | (c,p) <- ancestors, id == c]
                     child_ids  = [c | (c,p) <- ancestors, id == p]
                     get_hclk   = flip lookup clockMap
                     parents    = map Left (mapMaybe get_hclk parent_ids)
                     children   = map Right (mapMaybe get_hclk child_ids)
                 when doTraceClock $ traceM ("makeOutClock " ++ ppReadable id)
                 when doTraceClock $ traceM ("siblings = " ++ (show same_domain_ids))
                 when doTraceClock $ traceM ("ancestors = " ++ (show ancestors))
                 clock <- newClock wires mclock (parents ++ children)
                 return ((id,clock):clockMap)

         -- add new clocks to map one-by-one
         foldM makeOutClock clockarg_map clockwires_map

       -- -----
       handleResetConnections :: [(Id, HClock)] -> HExpr -> G [(Id, HReset)]
       handleResetConnections clock_map e = do
         es_rsts <- mapM findReset es
         let resetarginfo_map =
                 let getRstInfo id =
                         fromJustOrErr
                             "IExpand.newstate: reset arg not in in_reset_info"
                             (lookup id in_reset_info)
                 in [ (id, r, info)
                         | (ResetArg id, ICon _ (ICReset {iReset = r}))
                               <- zip (vArgs vi) es_rsts,
                           let info = getRstInfo id ]
             resetargs = [i | ResetArg i <- vArgs vi]
         when ((length resetarginfo_map) /= (length resetargs)) $
              -- this may be ok because dynamic expressions should not be
              -- able to get here (because clocks and resets should not
              -- have wires attached)
              internalError
                  ("IExpand.newState: not all reset args have resets " ++
                   ppReadable vi ++ ppReadable es)

         -- check the associated clock domains of input resets to the submod
         -- (and update any info derived about the clock domains of input
         -- resets to the parent module which we are elaborating)
         top_in_resets <- getInputResets
         let isInputReset r = r `elem` top_in_resets
         let lookupResetClock rid cid =
                 fromJustOrErr
                    ("IExpand.newState: reset clock not in clock map " ++
                     ppReadable (rid,cid))
                    (lookup cid clock_map)
         -- input resets which require associated clock domains
         let resetArgsWithClk =
                 [ (i, mport, r, clkdom_e, clkdom_a)
                     | (i, r, (mport, Just clock_id)) <- resetarginfo_map,
                       -- clock of the expr
                       let clk_e    = getResetClock r,
                       let clkdom_e = getClockDomain clk_e,
                       -- clock of the arg
                       let clk_a    = lookupResetClock r clock_id,
                       let clkdom_a = getClockDomain clk_a
                 ]
         -- in the course of elaboration, we may have discovered the domain
         -- for a reset, which is not recorded in the reset expr but is
         -- recorded in the monad state.  so we update the clkdom_e
         -- (if the reset is marked "no_clock" by the user, we note that)
         let updateParentInClock x@(i, mp, r, clkdom_e, clkdom_a) =
                let def_res = (i, mp, r, False, clkdom_e, clkdom_a)
                in  if (clkdom_e == noClockDomain) && isInputReset r
                    then do
                       deduced_clkdom_e <- getInputResetClockDomain r
                       case (deduced_clkdom_e) of
                           Nothing -> return def_res
                           Just new_clkdom_e ->
                             return (i, mp, r, True, new_clkdom_e, clkdom_a)
                    else return def_res
         updatedResetArgsWithClk <- mapM updateParentInClock resetArgsWithClk
         -- first, report any mismatch errors between args and exprs
         -- which both have associated domains
         let mkRstErrPair (i, mport) =
                 let i_str = getIdString i
                     port_str = case mport of
                                    Nothing -> ""
                                    Just port -> getVNameString port
                 in  (i_str, port_str)
             resetClockErrors =
                 [ mkRstErrPair (i, mport)
                     | (i, mport, r, _, clkdom_e, clkdom_a)
                           <- updatedResetArgsWithClk,
                       -- noClock resets match anything
                       not ((clkdom_e == clkdom_a) ||
                            (clkdom_e == noClockDomain) ||
                            (clkdom_a == noClockDomain))
                 ]
         when (not (null resetClockErrors)) $
             deferErrors [(pos, EResetClocks modName instName resetClockErrors)]
         -- now, for reset exprs which are top-level input resets for
         -- which an associated clockdomain has not yet been decided,
         -- we'll record any info learned from the submodule args that
         -- it is connected to -- however, we need to report an error
         -- if it is connected to two args with different domains
         let deriveTopResetClocks =
                 let -- input resets whose domain is noClockDomain
                     -- but which are connected to an arg which has a domain
                     xs = [ (r, ((i, p), clkdom_a))
                             | (i, p, r, b, clkdom_e, clkdom_a)
                                   <- updatedResetArgsWithClk,
                               ( clkdom_e == noClockDomain &&
                                 clkdom_a /= noClockDomain &&
                                 isInputReset r &&
                                 -- the noClockDomain came from no use,
                                 -- not from a reset marked "no_clock"
                                 not b ) ]
                     -- group the args by the input reset
                     gs = joinByFst xs
                     -- for each group, if all the arg domains are the same,
                     -- mark the input reset with that domain, else error
                     deriveOneGroup (_, []) = internalError "deriveOneGroup 1"
                     deriveOneGroup (r, ps@((_, clkdom):rest)) =
                         if (all ((== clkdom) . snd) rest)
                         then do -- assumes that clkdom won't be noClockDomain
                                 setInputResetClockDomain r clkdom
                                 return []
                         else do let rst_pairs = map (mkRstErrPair . fst) ps
                                 mrst_id <- boundaryResetToName r
                                 let rst_id =
                                         case mrst_id of
                                             Just i -> i
                                             Nothing ->
                                               internalError "deriveOneGroup 2"
                                 return
                                    [(pos, EInResetToMultipleDomainArgs
                                               (getIdString rst_id)
                                               modName instName
                                               rst_pairs)]
                 in  do ess <- mapM deriveOneGroup gs
                        let es = concat ess
                        when (not (null es)) $ errsG es
         _ <- deriveTopResetClocks

         let findOutputResetClock i =
                 -- XXX unQualId VModInfo
                 case (lookup (unQualId i) out_reset_info) of
                     Just (_, Nothing) -> noClock
                     Just (_, Just c ) -> lookupResetClock i c
                     Nothing -> internalError
                                    ("IExpand.newState: " ++
                                     "reset not in out_reset_info: " ++
                                     ppReadable i)

         let resetwire_map =
                 let mkICSel n = ICSel { iConType = itReset,
                                         selNo = n,
                                         numSel = genericLength (vFields vi) }
                 in  [ (id, clock, wire) |
                          -- index tuples from 0
                          (Reset id, n) <- zip (vFields vi) [0..],
                          let clock = findOutputResetClock id,
                          let wire = {- trace ("id: " ++ show id) $ -}
                                     IAps (ICon id (mkICSel n)) [] [e]
                     ]

         let makeOutReset (id, clock, wire) = do
                 r <- newReset clock wire
                 return (id, r)

         reset_out_map <- mapM makeOutReset resetwire_map

         let reset_map = map fst2of3 resetarginfo_map ++ reset_out_map

         return reset_map


-----------------------------------------------------------------------------

-- returns the evaluated expression and maybe port info (for ports)
--
iExpandSubmodArg :: Id -> (VArgInfo, HExpr) ->
                 G (HExpr, Maybe (Maybe Id, Maybe Id, HWireSet))
iExpandSubmodArg inst_id (varg, e) = do
    -- evaluate the argument
    (e', ws) <- evaleNF_ModArg inst_id (varg, e)
    -- check the clocks
    -- (Check that there are not multiple domains in the expr and warn
    -- if there are multiple resets in the expr.  Checking of the clock
    -- and reset against the expected clk/rst of the VModInfo is delayed
    -- until the clock_map is available.  This returns info used for
    -- that later check.)
    portinfo <- chkModuleArgument inst_id (e', ws, varg)
    return (e', portinfo)

-----------------------------------------------------------------------------
-- agg controls the aggressiveness in the implicit conditions that are converted

iExpandRules :: (HClock, HReset) ->
                IStateLoc -> HPred -> HExpr -> G ()
iExpandRules curClkRstn ns p r = do
        assertNoClkGateUses
        r' <- convRules curClkRstn ns p r
        addGateUsesToInhigh
        addGateInhighAttributes
        addRules r'


convRules :: (HClock, HReset) -> IStateLoc -> HPred -> HExpr -> G HRules
convRules curClkRstn@(curClk, _) ns p0 e = do
    (_, P p e') <- evalUH e
    let p' = pConj p0 p
    case e' of
      (IAps (ICon _ (ICPrim { primOp = PrimJoinRules })) _ [r1, r2]) -> do
        r1' <- convRules curClkRstn ns p' r1
        r2' <- convRules curClkRstn ns p' r2
        flags <- getFlags
        suf <- getNewRuleSuffix
        let (suf', res, errs) = iRUnion flags suf r1' r2'
        updNewRuleSuffix suf'
        deferErrors errs
        return res
      (IAps (ICon _ (ICPrim { primOp = PrimJoinRulesPreempt })) _ [r1, r2]) -> do
        r1' <- convRules curClkRstn ns p' r1
        r2' <- convRules curClkRstn ns p' r2
        flags <- getFlags
        suf <- getNewRuleSuffix
        let (suf', res, errs) = iRUnionPreempt flags suf r1' r2'
        updNewRuleSuffix suf'
        deferErrors errs
        return res
      (IAps (ICon _ (ICPrim { primOp = PrimJoinRulesUrgency })) _ [r1, r2]) -> do
        r1' <- convRules curClkRstn ns p' r1
        r2' <- convRules curClkRstn ns p' r2
        flags <- getFlags
        suf <- getNewRuleSuffix
        let (suf', res, errs) = iRUnionUrgency flags suf r1' r2'
        updNewRuleSuffix suf'
        deferErrors errs
        return res
      (IAps (ICon _ (ICPrim { primOp = PrimJoinRulesExecutionOrder })) _ [r1, r2]) -> do
        r1' <- convRules curClkRstn ns p' r1
        r2' <- convRules curClkRstn ns p' r2
        flags <- getFlags
        suf <- getNewRuleSuffix
        let (suf', res, errs) = iRUnionExecutionOrder flags suf r1' r2'
        updNewRuleSuffix suf'
        deferErrors errs
        return res
      (IAps (ICon _ (ICPrim { primOp = PrimJoinRulesMutuallyExclusive })) _ [r1, r2]) -> do
        r1' <- convRules curClkRstn ns p' r1
        r2' <- convRules curClkRstn ns p' r2
        flags <- getFlags
        suf <- getNewRuleSuffix
        let (suf', res, errs) = iRUnionMutuallyExclusive flags suf r1' r2'
        updNewRuleSuffix suf'
        deferErrors errs
        return res
      (IAps (ICon _ (ICPrim { primOp = PrimJoinRulesConflictFree })) _ [r1, r2]) -> do
        r1' <- convRules curClkRstn ns p' r1
        r2' <- convRules curClkRstn ns p' r2
        flags <- getFlags
        suf <- getNewRuleSuffix
        let (suf', res, errs) = iRUnionConflictFree flags suf r1' r2'
        updNewRuleSuffix suf'
        deferErrors errs
        return res
      (IAps (ICon _ (ICPrim { primOp = PrimRule })) _ [str, ICon _ (ICRuleAssert { iAsserts = rps }), c, a]) -> do
        (str', pos) <- evalString str

        -- create the rule name
        -- XXX why is this not created from ns'' below?
        let rId0 = stateLocAndNameToRuleId ns str' pos
            hide = hasRuleHide rps
            rId  = if (hide) then setHideId rId0 else rId0

        -- add a hierarchy level for this rule
        let locId = setKeepId (mkId pos (mkFString str'))
        ns' <- newIStateLocForRule locId hide ns

        showRuleProgress ns hide str' ("Elaborating rule")
        pushRuleSchedNameScope locId hide

        (c', a', ws) <- evalRule (ns, hide, str') rps rId p' c a

        let ruleExpr = iePrimWhen itAction c' a'
        chkClockDomain "rule" rId ws ruleExpr
        chkResetDomain "rule" rId ws ruleExpr

        -- if there is no associated clock, add the default clock
        -- XXX distinguish between "no clock" and "noClock"?
        let (final_a, final_ws) =
                case (fixupActionWireSet curClk ws) of
                  Just ws' -> (a', ws')
                  Nothing -> (icNoActions, ws)
        let wp  = wsToProps final_ws

        when doTraceClock $ traceM ("convRules2: " ++ ppReadable final_ws)
        showRuleProgress ns hide str' ("Finished rule")
        popRuleSchedNameScope
        return (IRules [] [IRule rId rps str' wp c' final_a Nothing ns'])
      (ICon _ (ICPrim { primOp = PrimNoRules })) ->
        return iREmpty
      (IAps (ICon _ (ICPrim { primOp = PrimAddSchedPragmas })) _ [ICon _ (ICSchedPragmas { iPragmas = sps1 }), rs]) -> do
        (IRules sps2 rs') <- convRules curClkRstn ns p' rs
        let sps1_flat = mapSPIds longnameToId sps1
            sps1_with_state = mapSPIds (addStateLocToPragmaRuleId ns) sps1_flat
        -- traceM ("scheduling pragma: " ++ ppReadable sps1_with_state)
        return (IRules (sps1_with_state ++ sps2) rs')
      -- otherwise, it didn't evaluate all the way
      -- report if/case/dynsel with a friendly user error and others with nfError
      (IAps (ICon _ (ICPrim { primOp = op })) _ _) | (condPrim op) ->
           -- or use "getPosition i"
           errG (getIExprPosition e', EDynamicRules)
      _ -> nfError "convRules" e'

-- agg controls whether to be aggressive about implicit conditions
evalRule :: (IStateLoc, Bool, String) ->
            [RulePragma] -> Id ->
            HPred -> HExpr -> HExpr -> G (HExpr, HExpr, HWireSet)
evalRule (ns, hide, name) asrts rId p c e = do
 module_agg <- isAggressive
 let rule_agg = (module_agg && not (RPconservativeImplicitConditions `elem` asrts)) || (RPaggressiveImplicitConditions `elem` asrts)
 setAggressive rule_agg
 do
        showRuleProgress ns hide name ("Elaborating rule explicit condition")
        setRuleSchedNameScopeProgress (Just REP_ExplicitCond)
        (P pc c', ws1) <- evalNF c

        showRuleProgress ns hide name ("Elaborating rule body")
        setRuleSchedNameScopeProgress (Just REP_Body)
        (P pe e', ws2) <- evalNF e

        showRuleProgress ns hide name ("Elaborating rule implicit condition")
        setRuleSchedNameScopeProgress (Just REP_ImplicitCond)
        ptot <- normPConj (pConjs [p, pc, pe])
        (pp, ws3) <- evalPred ptot

        setRuleSchedNameScopeProgress Nothing

        let ws = wsJoinMany [ws1, ws2, ws3]
        -- traceM (ppReadable pp)
        when ((RPnoImplicitConditions `elem` asrts) && not (isTrue pp)) $
            eAssertion rId RPnoImplicitConditions ""
        -- clock_crossing_rule implies no_implicit_conditions
        when ((RPclockCrossingRule `elem` asrts) && not (isTrue pp)) $
            eAssertion rId RPclockCrossingRule "because it has an implicit condition"

{-
        uc' <- unheapAll c'
        ue' <- unheapAll e'
        ue <- unheapAll e

        up <- unheapAll (predToHExpr p)
        upc <- unheapAll (predToHExpr pc)
        upe <- unheapAll (predToHExpr pe)
-}
--        upp <- unheapAll pp
--        traceM ("RULE " ++ ppReadable (c', e') ++ ppReadable upp)
--        traceM ("RULE " ++ ppReadable (map normPConj [p, pc, pe]))
        setAggressive module_agg
        return (ieAnd pp c', e', ws)

-----------------------------------------------------------------------------

type PMap = M.Map (PTerm HeapData) (HExpr, HWireSet)

-- Compute the final condition for a rule/method
-- (the choice of conservative vs aggressive is applied here)
-- The result for each pterm is memoized, so that it doesn't have to be
-- recomputed each time. (similar to how "canLiftCond" is memoized)
-- XXX Calls for other rules will not re-use these results.
-- XXX Consider storing this info in the heap, with NF expressions.
--
evalPred :: HPred -> (G (HExpr, HWireSet))
evalPred p = do (r,m) <- evalPred' M.empty p
                -- traceM ("evalPred map: " ++ ppReadable (M.keys m))
                return r

evalPred' :: PMap -> HPred -> G ((HExpr, HWireSet), PMap)
evalPred' m (PConj ps) = do
  let f (rs, m) p = do (r, m') <- evalPTerm m p
                       return (r:rs, m')
  (ress, m') <- foldM f ([], m) (S.toList ps)
  let (es, wss) = unzip (reverse ress)
      res = (foldr ieAnd iTrue es, wsJoinMany wss)
  --traceM ("evalPred " ++ ppReadable es)
  -- Note that we don't memoize the joined result
  return (res, m')

evalPTerm :: PMap -> PTerm HeapData -> G ((HExpr, HWireSet), PMap)
evalPTerm m op =
  case (M.lookup op m) of
  Just res -> return (res, m)
  Nothing ->
    case op of
    (PAtom e) -> do
        (P p e', ws) <- walkNF e
        ((p', ws'), m') <- evalPred' m p
        let res_e = ieAnd p' e'
        -- memoize the result
        -- creating a heap ref (if necessary) to avoid duplication
        res_r <- addHeapPred "aggr1" res_e
        let res = (res_r, wsJoin ws ws')
            m'' = M.insert op res m'
        --traceM ("evalPTerm PAtom " ++ ppReadable (e, (p', e')))
        return (res, m'')
    (PIf c t e) -> do
        -- use implicit parameter agg to decide if implicit conditions
        -- should be surfaced aggressively or conservatively
       ((t', ws_t), m1) <- evalPred' m t
       ((e', ws_e), m2) <- evalPred' m1 e
       agg <- isAggressive
       let conservative_res = (ieAnd t' e', wsJoin ws_t ws_e)
       ((res_e, res_ws), res_m) <-
         if agg
         then do
           (P pc c', ws_c) <- walkNF c
           ((pc', ws_c'), m3) <- evalPred' m2 pc
           --traceM ("evalPTerm PIf " ++ ppReadable (pc, c', t', e'))
           -- XXX the pred of the cond should be ANDd into the result,
           -- XXX not the condition?
           let c'' = (ieAnd pc' c')
               aggressive_res = (ieIfx itBit1 c'' t' e',
                                 wsJoinMany [ws_c, ws_c', ws_t, ws_e])
           -- revert to conservative condition if the aggressive form would
           -- lift an expression that can't be lifted (a method argument or
           -- an actionvalue)
           canLift <- canLiftCond c''
           let res = if canLift
                     then aggressive_res
                     else conservative_res
           return (res, m3)
         else
           return (conservative_res, m2)
       -- memoize the result
       -- creating a heap ref (if necessary) to avoid duplication
       res_r <- addHeapPred "aggr2" res_e
       let res = (res_r, res_ws)
           res_m' = M.insert op res res_m
       return (res, res_m')
    (PSel idx idx_sz es) -> do
       let foldFn (ews_acc, m_acc) e = do
               (ew, m_acc') <- evalPred' m e
               return ((ew:ews_acc), m_acc')
       (rev_ews, m1) <- foldM foldFn ([], m) es
       let (es', wss) = unzip (reverse rev_ews)
       agg <- isAggressive
       let conservative_res = (foldr ieAnd iTrue es', wsJoinMany wss)
       ((res_e, res_ws), res_m) <-
         if agg
         then do
           (P pidx idx', ws_idx) <- walkNF idx
           ((pidx', ws_idx'), m2) <- evalPred' m1 pidx
           -- XXX assert that pidx' is True?
           -- The array selection should return True if out of bounds
           let aggressive_res =
                   (ieAnd pidx' $ ieCase itBit1 idx_sz idx' es' iTrue,
                    wsJoinMany $ [ws_idx, ws_idx'] ++ wss)
           -- revert to conservative condition if the aggressive form would
           -- lift an expression that can't be lifted (a method argument or
           -- an actionvalue)
           canLift_idx <- canLiftCond idx'
           canLift_pidx <- canLiftCond pidx'
           let res = if (canLift_idx && canLift_pidx)
                     then aggressive_res
                     else conservative_res
           return (res, m2)
         else
           return (conservative_res, m1)
       -- memoize the result
       -- creating a heap ref (if necessary) to avoid duplication
       res_r <- addHeapPred "aggr3" res_e
       let res = (res_r, res_ws)
           res_m' = M.insert op res res_m
       return (res, res_m')

-----------------------------------------------------------------------------

evalString :: HExpr -> G (String, Position)
evalString e = do
        e' <- evaleUH e
        case e' of
            ICon _ (ICString { iStr = s }) -> return (s, getIExprPosition e')
            _ -> do e'' <- unheapAll e'
                    errG (getIExprPosition e'', EStringNF (ppString e''))

evalStringList :: HExpr -> G ([String], Position)
evalStringList e = do
  e' <- evaleUH e
  case e' of
    IAps (ICon _ c) _ [a] -> do
      a' <- evaleUH a
      -- XXX this is a horrible way of pulling apart a list, but I don't think there is a better way:
      case a' of
        IAps (ICon i' (ICTuple {})) _ [e_h, e_t] | getIdBaseString i' == "List_$Cons" -> do
          (h, _) <- evalString e_h
          (t, _) <- evalStringList e_t
          return (h:t, getIExprPosition e')
        ICon _ (ICInt _ (IntLit { ilValue = 0 })) ->
          return ([], getIExprPosition e')
        _ -> internalError ("evalStringList con: " ++ showTypeless a')
    _ -> do e'' <- unheapAll e'
            errG (getIExprPosition e', EStringListNF (ppString e'))

-----------------------------------------------------------------------------

evalHandle :: HExpr -> G Handle
evalHandle e = do
  e' <- evaleUH e
  case e' of
    ICon _ (ICHandle { iHandle = h }) -> return h
    _ -> nfError "evalHandle" e'

evalBufferMode :: HExpr -> G BufferMode
evalBufferMode e = do
  e' <- evaleUH e
  case e' of
    IAps (ICon _ (ICPrim _ PrimChr)) _ [e_n] -> do
      n <- evalInteger e_n
      case n of
        0 -> return NoBuffering
        1 -> return LineBuffering
        _ -> internalError("evalBufferMode: PrimChr: " ++ ppReadable n)
    IAps (ICon _ (ICCon { conTagInfo = cti })) _ [e_mdata] ->
      case (conNo cti) of
        0 -> return NoBuffering
        1 -> return LineBuffering
        2 -> do me_data <- evalMaybe e_mdata
                msz <- case me_data of
                         Nothing -> return Nothing
                         Just e_data -> do sz <- evalInt e_data
                                           return (Just sz)
                return $ BlockBuffering msz
        _ -> internalError("evalBufferMode: ICCon: " ++ ppReadable cti)
    _ -> nfError "evalBufferMode" e'

evalMaybe :: HExpr -> G (Maybe HExpr)
evalMaybe e = do
  e' <- evaleUH e
  case e' of
    IAps (ICon _ (ICPrim _ PrimChr)) _ [e_n] -> do
      n <- evalInteger e_n
      case n of
        0 -> return Nothing
        _ -> internalError("evalMaybe: PrimChr: " ++ ppReadable n)
    IAps (ICon _ (ICCon { conTagInfo = cti })) _ [e_data] ->
      case (conNo cti) of
        0 -> return Nothing
        1 -> return (Just e_data)
        _ -> internalError("evalMaybe: ICCon: " ++ ppReadable cti)
    _ -> nfError "evalMaybe" e'

evalInt :: HExpr -> G Int
evalInt e = do
  n <- evalInteger e
  let max_int = (maxBound :: Int)
      min_int = (minBound :: Int)
  let n' | n > toInteger max_int = max_int
         | n < toInteger min_int = min_int
         | otherwise             = fromInteger n
  return n'

-----------------------------------------------------------------------------

-- entry point for places that are expecting one position
evalPosition :: HExpr -> G Position
evalPosition e = do
  poss <- evalPositions e
  case poss of
    [pos] -> return pos
    _ -> internalError ("evalPosition: " ++ ppReadable poss)

evalPositions :: HExpr -> G [Position]
evalPositions e = do
  e' <- evaleUH e
  case e' of
    ICon _ (ICPosition { iPosition = poss }) -> return poss
    _ -> nfError "evalPositions" e'

-----------------------------------------------------------------------------

evalInteger :: HExpr -> G Integer
evalInteger e = do
  e' <- evaleUH e
  case e' of
    ICon _ (ICInt { iVal = IntLit { ilValue = l } })  -> return l
    _ -> nfError "evalInteger" e'

-----------------------------------------------------------------------------

evalName :: HExpr -> G Id
evalName e = do
  e' <- evaleUH e
  case e' of
    ICon _ (ICName { iName = i }) -> return i
    _ -> -- XXX internalError instead since names should always evaluate?
         nfError "evalName" e'

-----------------------------------------------------------------------------

evalType :: HExpr -> G IType
evalType e = do
  e' <- evaleUH e
  case e' of
    ICon _ (ICType{ iType = t }) -> return t
    _ -> nfError "evalType" e'

------------------------------------------------------------------------------

-- common code shared by "findClock", "findReset", "findInout", etc
findNF :: HExpr -> G HExpr
findNF (IAps (ICon _ (ICPrim _ PrimIf)) _ [c, t, _]) = findNF t
findNF (IAps (ICon _ (ICPrim _ PrimCase)) _ (idx:def:n0:e0:_)) = findNF e0
findNF (IAps (ICon _ (ICPrim _ PrimArrayDynSelect)) [elem_t, _] [a, _]) =
    let findNFInArray (ICon i (ICLazyArray _ arr _)) =
            case (Array.elems arr) of
              (ArrayCell ptr ref : _) -> findNF (IRefT elem_t ptr ref)
              _ -> internalError ("findNFInArray: no elements")
        findNFInArray e@(IRefT {}) = do P _ e' <- unheap (pExpr e)
                                        findNFInArray e'
        findNFInArray e = internalError ("findNFInArray: " ++ ppReadable e)
    in  findNFInArray a
findNF e@(IRefT {}) = do P _ e' <- unheap (pExpr e)
                         findNF e'
findNF e = return e

------------------------------------------------------------------------------

findClock :: HExpr -> G HExpr
findClock = findNF

-- evaluate a clock
-- requires no implicit conditions and
evalClock :: HExpr -> G (HClock, HExpr)
evalClock e = do
    e' <- evaleUH e
    case e' of
        (ICon _ (ICClock { iClock = c })) -> return (c, e')
        -- error conditions
        (IAps (ICon _ (ICPrim { primOp = op })) _ _) | (condPrim op) -> do
            deferErrors [(getIExprPosition e', EDynamicClock)]
            findClock e' >>= evalClock
        _ -> nfError "evalClock" e'

-----------------------------------------------------------------------------

findReset :: HExpr -> G HExpr
findReset = findNF

-- evaluate a reset
-- requires no implicit conditions and
-- no other wire connections (or errors out)
evalReset :: HExpr -> G (HReset, HExpr)
evalReset e = do
    e' <- evaleUH e
    case e' of
        (ICon _ (ICReset { iReset = r })) -> return (r, e')
        -- error condition
        (IAps (ICon _ (ICPrim { primOp = op })) _ _) | (condPrim op) -> do
            deferErrors [(getIExprPosition e', EDynamicReset)]
            findReset e' >>= evalReset
        _ -> nfError "evalReset" e'

-----------------------------------------------------------------------------

-- find a buried Inout, for continuing on after an error
findInout :: HExpr -> G HExpr
findInout = findNF

-- evaluate an inout
-- requires no implicit conditions and
-- no other wire connections (or errors out)
evalInout :: HExpr -> G (HInout, HExpr)
evalInout e = do
    e' <- evaleUH e
    case e' of
        (ICon _ (ICInout { iInout = r })) -> return (r, e')
        -- error condition
        (IAps (ICon _ (ICPrim { primOp = op })) _ _) | (condPrim op) -> do
            deferErrors [(getIExprPosition e', EDynamicInout)]
            findInout e' >>= evalInout
        _ -> nfError "evalInout" e'

-----------------------------------------------------------------------------

walkList :: (HExpr -> G (PExpr, HWireSet)) -> [HExpr] -> G (HPred, [HExpr], HWireSet)
walkList f es = do
        (pes, wss) <- mapAndUnzipM f es
        return (pConjs [ p | P p _ <- pes], [ e | P _ e <- pes], wsJoinMany wss)

-----------------------------------------------------------------------------

-- XXX noPosition is used for showPrimError and showPrimMessage
-- because the available position (post-isimplify) is bogus
-- the position of the def of error/message in the Prelude

showPrim :: (Position -> String -> G ()) -> Position -> HExpr -> G ()
showPrim cont pos e = do
  (str, _) <- evalString e
  cont pos str

showPrimError :: Position -> HExpr -> G ()
showPrimError pos e = do
   let msg = "Bluespec evaluation-time error: "
   let f pos' str = errG (pos', EGeneric (msg ++ str))
   showPrim f pos e

showGenerateError :: Integer -> Position -> HExpr -> G ()
showGenerateError num pos e = do
  let f pos' str = errG (pos', EGenerate num str)
  showPrim f pos e

showPrimMessage :: Position -> HExpr -> G ()
showPrimMessage pos e = do
   let prPos p = if (p == noPosition) then "" else prPosition p ++ ": "
       msg = "Compilation message: "
   let f pos' str = liftIO (putStrLn (msg ++ prPos pos' ++ str))
   showPrim f pos e

showPrimWarning :: Position -> HExpr -> G ()
showPrimWarning pos e = do
   let msg = "Bluespec evaluation-time warning: "
   let f pos' str = eWarning (pos', EGeneric (msg ++ str))
   showPrim f pos e

-----------------------------------------------------------------------------

nfError :: String -> HExpr -> G a
nfError str e = do
    when doDebug $ traceM ("nfError: " ++ str)
    e' <- unheapAll e
    eNoNF e'

evalNF :: HExpr -> G (PExpr, HWireSet)
evalNF e = do
  (P p0 e') <- eval1 e
  (P p e'', ws) <- walkNF e'
  return (P (pConj p0 p) e'', ws)

evalUHNF :: HExpr -> G (PExpr, HWireSet)
evalUHNF e = do
  (_, P p0 e') <- evalUH e
  (P p e'', ws) <- walkNF e'
  return (P (pConj p0 p) e'', ws)

-- Compute an expression to NF.
-- NF can involve suspended primitives.
--   (e.g., it can contain things like "x + 1" if "x" is not compile-time)
-- implicit conditions are always surfaced aggressively here
-- they may be made conservative (controlled by compiler flag) by evalPred
-- the HWireSet returned only relates to the HExpr
-- the implicit condition's HWireSet will be returned by evalPred
walkNF :: HExpr -> G (PExpr, HWireSet)
walkNF e =
  if not (isPrimType (iGetType e)) then do
    when (doDebug || doTraceNF) $ traceM ("not prim type: " ++ ppReadable (e, iGetType e))
    nfError "walkNF" e
  else do
    cross <- getCross
    when (doDebug || doTraceNF) $ traceM ("walkNF " ++ ppReadable e)
    let upd p e@(IRefT _ _ _) ws = do
            P p' e' <- unheap (P p e)
            upd p' e' ws
        upd p n ws =
            let pn = P p n in
            case e of
            o@(IRefT _ ptr ref) -> do
              old_cell <- getHeap ref
              let old_name = hc_name old_cell
                  new_cell = HNF { hc_pexpr = P p (mapIExprPosition cross (o,n)),
                                   hc_wire_set = ws,
                                   hc_name = old_name }
              updHeap "walkNF" (ptr, ref) new_cell
              return (if isCon n then
                          (P p (mapIExprPosition cross (o,n)), ws)
                      else (P p (mapIExprPositionConservative cross (n,o)), ws))
            _ -> return (pn, ws)

        recurse p0 u =
            case u of
                -- remove PrimSetSelPosition
                IAps (ICon _ (ICPrim _ PrimSetSelPosition)) _ [_, e] -> do
                    (P pe e', ws_e) <- walkNF e
                    upd (pConj pe p0) e' ws_e

                -- The special cases for PrimIf, PrimCase, PrimArrayDynSelect,
                -- PrimBAnd, PrimBOr are for more accurate implicit conditions.
                IAps f@(ICon _ (ICPrim _ PrimIf)) [ty] [c, t, e] -> do
                    (P pc c', ws_c) <- walkNF c
                    (P pt t', ws_t) <- walkNF t
                    (P pe e', ws_e) <- walkNF e
                    p_if <- pIf c' pt pe
                    let p = pc `pConj` p_if
                    upd (pConj p0 p) (ieIfx ty c' t' e') (wsJoinMany [ws_c, ws_t, ws_e])

                IAps f@(ICon _ (ICPrim _ PrimCase))
                         [sz_idx, elem_ty]
                         (idx:dflt:ces) -> do
                    (P p_idx idx', ws_idx) <- walkNF idx
                    (P p_dflt dflt', ws_dflt) <- walkNF dflt
                    -- XXX if the case arms are integer, then we can use pSel,
                    -- XXX but in the general case we can only use pIf
                    let foldFn (v, e) (ce_res, p_res, wss_res) = do
                            (P p_v v', ws_v) <- walkNF v
                            (P p_e e', ws_e) <- walkNF e
                            let c = iePrimEQ sz_idx idx' v'
                            p_if <- pIf c p_e p_res
                            let ce_res' = ((v',e'):ce_res)
                                wss_res' = (ws_v:ws_e:wss_res)
                            return (ce_res', p_if, wss_res')
                    (ce_pairs', p_arms, wss)
                        <- foldrM foldFn ([], p_dflt, [ws_dflt]) (makePairs ces)
                    -- XXX use an equivalent to "ieIfx" but for case?
                    let ces' = flattenPairs ce_pairs'
                        e' = IAps f [sz_idx, elem_ty] (idx':dflt':ces')
                    upd (pConj p_idx p_arms) e' (wsJoinMany (ws_idx:wss))

                IAps f@(ICon _ (ICPrim _ PrimArrayDynSelect))
                         ts@[elem_t, ITNum idx_sz]
                         [arr_e, idx_e] -> do
                    (P pidx idx_e', ws_idx) <- walkNF idx_e
                    case arr_e of
                      (ICon i (ICLazyArray arr_t arr u)) -> do
                        let cells = Array.elems arr
                        let mapFn (ArrayCell ptr ref) = do
                                (P p _, ws) <- walkNF (IRefT elem_t ptr ref)
                                return (p, ws)
                        (ps, wss) <- mapAndUnzipM mapFn cells
                        let e' = IAps f ts [arr_e, idx_e']
                        let p = pConjs [pidx, pSel idx_e' idx_sz ps]
                        upd (pConj p0 p) e' (wsJoinMany (ws_idx:wss))
                      _ -> internalError ("walkNF: dynsel: arr = " ++
                                          ppReadable arr_e)

                IAps f@(ICon _ (ICPrim _ PrimBAnd)) _ [e1, e2] -> do
                    (P pe1 e1', ws1) <- walkNF e1
                    (P pe2 e2', ws2) <- walkNF e2
                    p_if <- pIf e1' pe2 pTrue
                    let p = pe1 `pConj` p_if
                    upd (pConj p0 p) (ieAnd e1' e2') (wsJoin ws1 ws2)

                IAps f@(ICon _ (ICPrim _ PrimBOr)) _ [e1, e2] -> do
                    (P pe1 e1', ws1) <- walkNF e1
                    (P pe2 e2', ws2) <- walkNF e2
                    p_if <- pIf e1' pTrue pe2
                    let p = pe1 `pConj` p_if
                    upd (pConj p0 p) (ieOr e1' e2') (wsJoin ws1 ws2)

                IAps f@(ICon _ (ICPrim _ p)) ts es | realPrimOp p -> do
                    (p, es', ws) <- walkList walkNF es
                    cross <- getCross
                    upd (pConj p0 p) (IAps f ts (map (mapIExprPosition cross) (zip es es'))) ws

                IAps f@(ICon i_sel (ICSel { })) ts es -> do
                    (p, es', ws) <- walkList walkNF es

                    -- handle method calls (ICSel of a ICStateVar)
                    let handleMethod meth_id svar = do
                            let c = getMethodClock meth_id svar
                            let r = getMethodReset meth_id svar
                            let p_gate =
                                    if isActionType (iGetType u)
                                    then if (inClockDomain noClockDomain c)
                                         then pAtom (iFalse)
                                         else pAtom (getClockGate c)
                                    else pTrue
                            when doTraceClock $ traceM ("Method: " ++ ppReadable meth_id ++
                                                        "Clock: " ++ ppReadable c ++
                                                        "Reset: " ++ ppReadable r ++
                                                        "Clock gate: " ++ ppReadable p_gate)
                            when (isActionType (iGetType u)) $
                                addClkGateUse c
                            upd (pConjs [p0, p, p_gate]) (IAps f ts es') (wsAddReset r (wsAddClock c ws))

                    case es' of
                        st@(ICon i (ICStateVar { iVar = v })) : _ ->
                            handleMethod i_sel v

                        -- foreign function has no additional clocks
                        ff@(ICon i (ICForeign { })) : _ ->
                            upd (pConj p0 p) (IAps f ts es') ws

                        -- This is for the preservation of the clock-gating signal
                        -- XXX is adding the clock to the wire set redundant?
                        clk@(ICon i (ICClock { iClock = c })) : _  -> upd (pConj p0 p) (IAps f ts es') (wsAddClock c ws)

                        -- if the outer selector is avValue_ or avAction_
                        -- and the inner is a method call
                        [(IAps sel@(ICon i_sel2 (ICSel { })) ts_2 es_2)]
                            | (i_sel == idAVValue_ || i_sel == idAVAction_) -> do
                            case es_2 of
                                st@(ICon i (ICStateVar { iVar = v })) : _ ->
                                    handleMethod i_sel2 v
                                _ -> internalError ("walkNF: selector should be a method call")

                        -- the inner selector can wind up on the heap
                        -- because of "move" in evalHeap
                        [e_ref@(IRefT t ptr ref)] | (isitActionValue_ t) || (isitAction t)
                            ->  do (P p' e', ws) <- walkNF e_ref
                                   upd (pConj p0 p') (IAps f ts [e']) ws
                        _ ->    do when doDebug $ traceM "not stvar or foreign\n"
                                   when doDebug $ traceM (show u ++ "\n")
                                   when doDebug $ traceM (show es' ++ "\n")
                                   nfError "walkNF sel" u

                IAps f@(ICon i (ICForeign { })) ts es -> do
                    (p, es', ws) <- walkList walkNF es
                    upd (pConj p0 p) (IAps f ts es') ws

                IAps f@(ICon i (ICPrim _ PrimWhenPred)) _ [(ICon _ (ICPred _ p)), e] -> do
                   _ <- internalError ("PrimWhenPred" ++ ppReadable e)
                   (P p' e', ws) <- walkNF e
                   upd (pConjs [p0, p, p']) e' ws

                -- Any other application is not in NF (which is unexpected?)
                IAps f ts es -> do
                    _ <- internalError ("walkNF fall-through: " ++ ppReadable (f,ts,es))
                    -- XXX what is the code below this line?
                    --(P pf f') <- eval1 f
                    (P pf f', ws') <- walkNF f
                    (p, es', ws) <- walkList walkNF es
                    -- XXX A hack to allow polymorphic methods
                    case f' of
                        IAps (ICon _ (ICSel { })) _ _ -> upd (pConjs [p0, pf, p]) (IAps f' ts es') (wsJoin ws ws')
                        _ ->
                                do when doDebug $ traceM ("ap:\n" ++ show f' ++ "\n" ++ show ts ++ "\n" ++ show es')
                                   nfError "walkNF ap" u

                -- recurse cannot be called with an IRefT because of guard code in walkNF
                -- and because IRefT cannot be evaluated WHNF or HNF (see unheap)
                IRefT _ _ _ -> internalError ("evalNF: IRefT " ++ ppReadable (e, u))
                -- ref@(IRefT _ _ r) -> do (P p e', ws) <- walkNF ref
                --                        upd (pConj p0 p) e' ws
                (ICon i (ICModPort {})) -> do
                    ws <- getPortWires i
                    upd p0 e ws
                (ICon _ (ICInout { iInout = inout })) -> do
                    let ws = getInoutWires inout
                    upd p0 e ws
                (ICon _ (ICLazyArray arr_t arr _)) -> do
                    internalError "walkNF array"
                -- any remaining constants, etc. cannot have a HWireSet attached
                _ -> upd p0 e wsEmpty

    case e of
        ref@(IRefT _ _ r) -> do
            hc <- getHeap r
            case hc of
                HUnev { hc_hexpr = e } -> do
                    e' <- unheapAll e
                    internalError ("walkNF unev: " ++ ppReadable (e, e'))
                HLoop name ->
                    internalError ("walkNF loop: " ++ ppReadable name)
                -- reuse ref for better CSE
                -- duplication of pred in ref is harmless because of set-based predicates
                HNF { hc_pexpr = P p e, hc_wire_set =  ws} -> do
                    when doTraceNF $ traceM("walkNF done: " ++ ppReadable hc)
                    return (P p ref, ws)
                HWHNF { hc_pexpr = P p e, hc_name = name } -> do
                    when doTraceNF $ traceM ("walkNF enter: " ++ ppReadable hc)
                    (P p' e', ws) <- recurse p e
                    return (P p' e', ws)
        _ -> recurse pTrue e

{-
-- Evaluate an expr to NF and check that it has no implicit conditions.
-- If there are implicit conditions, a generic error is reported.
-- Otherwise returns an expression and a wire set
-- for external checking (clock-consistency or unclocked).
evaleNF :: HExpr -> G (HExpr, HWireSet)
evaleNF e = do
        (P p e', ws) <- evalNF e
        when (p /= pTrue) $ do
          e' <- unheapAll e
          -- XXX this error is ugly
          deferErrors [(getIExprPosition e, EHasImplicit (ppReadable e'))]
        return (e', ws)
-}

-- Evaluate an expr for a module argument,
-- report a specific error (for module arguments) if the expr has an
-- implicit condition.  Otherwise, returns an expression and a wire site
-- for external checking (clock-consistency or unclocked).
evaleNF_ModArg :: Id -> (VArgInfo, HExpr) -> G (HExpr, HWireSet)
evaleNF_ModArg inst_id (varg, e) = do
    (P p e', ws) <- evalNF e
    when (p /= pTrue) $ do
      -- If we had a good PVPrint for ISyntax,
      -- would this provide any useful information?
      --let e_str = pfpString e'
      let varg_id = getVArgInfoName varg
      deferErrors [(getPosition inst_id,
                    EModPortHasImplicit (pfpString inst_id) (pfpString varg_id))]
    return (e', ws)

fuse :: (Integer, HExpr) -> (Integer, HExpr) -> (Integer, HExpr)
fuse (sz1, e1) (sz2, e2) = (sz3, e)
  where e = IAps icPrimConcat [ITNum sz2, ITNum sz1, ITNum sz3] [e2, e1]
        sz3 = sz1 + sz2

-- Evaluate to WHNF and follow heap pointer
-- (WHNF = top-level expression is not an application)
-- pexpr is returned by eval, iexpr is pexpr converted into iexpr
--   for convenience
-- note that iexpr is a "heaped" version of the expression
evalUH :: HExpr -> G (HExpr, PExpr)
evalUH e = do
        let isRef (IRefT _ _ _) = True
            isRef _             = False
        pe@(P p0 e0) <- eval1 e
        when (doTraceHeapAlloc && isRef e) $
            traceM ("wasted re-heap: " ++ ppReadable (e, pe))
        let specialArr t (Just _) = True
            specialArr t _ = isBitType t
        case e0 of
          ICon i (ICLazyArray t arr u) | specialArr t u -> do
            P p' e' <- case u of
                         Just (pos, name) -> do
                           -- raw uninitialized to force error
                           let icon = icPrimRawUninitialized
                           evalAp "Uninit Vector" icon [T t, E pos, E name]
                         _ | isBitType t -> do
                           let cells = Array.elems arr
                           let f (ArrayCell p r) = (1, IRefT itBit1 p r)
                           let e_szs = map f cells
                           let fused = snd $ foldl1 fuse e_szs
                           eval1 fused
                         _ -> internalError ("evalUH - bad special array: " ++ show e0)
            -- traceM ("specialArr: " ++ ppReadable (e, e0, e'))
            let pe = P (pConj p' p0) e'
            case e of
              IRefT _ p r -> do updHeap "evalUH-array" (p, r) (HWHNF pe Nothing)
                                return (e, pe)
              _ -> do e'' <- toHeapWHNFInferName "eval-uh" (pExprToHExpr pe)
                      return (e'', pe)
          _ -> do
            pe' <- unheap pe
            when (doTraceHeapAlloc && isRef e0) $
                traceM ("wasted re-heap 2: " ++ ppReadable (e, e0, pe'))
            e' <- toHeapWHNFInferName "eval-uh" (pExprToHExpr pe)
            -- could use isRef here to preserve the original reference
            return (e', pe')

-- Like evalUH, but check for implicit conditions.
-- This is used to evaluate static exprs:
--    Integer, String, Clock, Reset, Position, Name, Attribute
-- which should not have implicit conditions.
--
-- When an implicit condition is found, this reports a generic error.
-- XXX It would be good to improve the error for specific contexts,
-- XXX as is done with evaleNF_ModArg.
-- Most of these could be reported as an internal error (rather than
-- a user error) because they are inserted by the compiler:
--   * positions, names, attributes,
--   * Integer is for primGenerateError (to indicate the tag)
--   * String is for rule names and module names and error messages
-- Some are written by the user, and should therefore have good errors:
--   * Clock and Reset with wires should imply a dynamic selection,
--     so we could report the dynamic selection instead.
--   * The user can specify strings with "error", "message", "warning", etc
--
evaleUH :: HExpr -> G HExpr
evaleUH e = do
  (_, P p e') <- evalUH e
  when (p /= pTrue) $ do
    e' <- unheapAll e
    -- XXX this error message should be improved
    -- XXX (see EModPortHasImplicit)
    deferErrors [(getIExprPosition e, EHasImplicit (ppReadable e'))]
  return e'

{-
evalUHn :: Int -> HExpr -> G PExpr
evalUHn 0 e = evalUH e
evalUHn n e = do
        pe <- evalUH e
        case pe of
-- XXX should we eval or just unheap?
            P p (IAps f ts es) -> do
--                f' <- evalUHn (n-1) f
                (p', es') <- evalList (evalUHn (n-1)) es
                return (P (pConj p p') (IAps f ts es'))
            _ -> return pe
-}

-- evaluate a static operator with potentially dynamic (or undetermined) arguments
-- XXX When the same heap ref appears twice, this does twice the work!
{-# INLINE evalStaticOp #-}
evalStaticOp :: HExpr -> IType -> (HExpr -> G PExpr) -> G PExpr
evalStaticOp e resultType handler =
    let handler' _ (p, e) = addPredG p $ handler e
    in  evalStaticOp' True True True e resultType handler'

-- doUH = use "evalUH" (which forces evaluation of ICLazyArray)
--        (when False, non-forcing "eval1" is used)
-- doBK = recurse inside book-keeping ops (PrimSetSelPosition)
--        (when False, these exprs are left to the handler)
-- doUndet = return a default answer for ICUndet
--           (when False, this is left to the handler)
--
{-# INLINE evalStaticOp' #-}
evalStaticOp' :: Bool -> Bool -> Bool ->
                 HExpr -> IType ->
                 (HExpr -> (HPred, HExpr) -> G PExpr) -> G PExpr
evalStaticOp' doUH doBK doUndet e resultType handler = do
  (ee, pe@(P p e')) <-
      -- for some array ops, we don't want to force the array (in evalUH)
      if doUH
      then evalUH e
      else do pe <- eval1 e >>= unheap
              -- we could return "pExprToHExpr pe", but better to just
              -- make sure the handler only uses "pe"
              let ee = internalError ("evalStaticOp: doUH == False")
              return (ee, pe)
  res <-
   case e' of
    ICon i (ICUndet { iuKind = k }) | doUndet -> do
      let kind_integer = undefKindToInteger k
      addPredG p $ doBuildUndefined resultType (getPosition i) kind_integer []

    -- found dynamic expression
    IAps f@(ICon _ (ICPrim _ PrimIf)) [t] [cnd, thn, els] -> do
      P pthn thn' <- evalStaticOp' doUH doBK doUndet thn resultType handler
      P pels els' <- evalStaticOp' doUH doBK doUndet els resultType handler
      when doTraceIf $ traceM("evalStaticOp: improveIf try: " ++ ppReadable (t,thn',els'))
      (e'', _) <- improveIf f resultType cnd thn' els'
      when doTraceIf $ traceM("evalStaticOp: improveIf result: " ++ ppReadable e'')
      p' <- pIf cnd (pConj p pthn) (pConj p pels)
      return (P p' e'')
    IAps ic@(ICon _ (ICPrim _ PrimArrayDynSelect))
             [_, ITNum idx_sz] [arr_e, idx_e] -> do
      addPredG p $
          evalStaticOpInArray' doUH doBK doUndet
                               ic idx_e idx_sz arr_e resultType handler

{-
    -- XXX this situation doesn't occur, because we don't use evalStaticOp
    -- XXX for any prims that take an arg of type PrimAction
    -- found a wrapper around a dynamic expression (of type PrimAction)
    IAps f@(ICon _ (ICPrim _ pi)) [] [e2] | isIfWrapper pi ->
      P p2 e2' <- evalStaticOp' doUH doBK doUndet e2 resultType handler
      let p' = pConj p p2
          e'' = IAps f [] [e2']
      return (P p' e'')
-}

    -- push inside book-keeping operators
    IAps f@(ICon _ (ICPrim _ PrimSetSelPosition)) [ty] [e_pos, e_res]
      | doBK -> do
      P p_res e_res' <- evalStaticOp' doUH doBK doUndet e_res resultType handler
      let p' = pConj p p_res
      -- try reapplying the prim, in case it can apply now
      addPredG p' $
          evalAp "static-op set-sel-pos" f [T resultType, E e_pos, E e_res']

    -- otherwise, apply the static op's handler
    _ -> -- rather than "addPredG p", which would be redundant if the handler
         -- uses "ee", we pass "p" in for the handler to use with "e'"
         handler ee (p, e')

  if doBK
    then return res
    else -- it's a bookkeeping no-op, so preserve the heap name if any
      case e of
        IRefT _ _ r -> do
            old_cell <- getHeap r
            let old_name = hc_name old_cell
            res' <- toHeapWHNF "set-sel-pos" (pExprToHExpr res) old_name
            return $ P pTrue res'
        _ -> return res

{-# INLINE evalStaticOpInArray' #-}
evalStaticOpInArray' :: Bool -> Bool -> Bool ->
                        HExpr -> HExpr -> Integer ->
                        HExpr -> IType ->
                        (HExpr -> (HPred, HExpr) -> G PExpr) -> G PExpr
evalStaticOpInArray' doUH doBK doUndet
                     ic idx_e idx_sz arr_e resultType handler = do
  -- doUH doesn't apply here
  (_, P arr_p arr_e') <- evalUH arr_e
  case arr_e' of
    ICon arr_i (ICLazyArray arr_ty arr Nothing) -> do
        let (elem_ty, arr_ty') =
                case arr_ty of
                  (ITAp c t) | (c == itPrimArray) -> (t, ITAp c resultType)
                  _ -> internalError ("evalStaticOpInArray': type: " ++
                                      ppReadable arr_ty ++
                                      show arr_ty)
        -- leave the preds in the array elems, walkNF will collect them
        let cells = Array.elems arr
            mapFn (ArrayCell ref_p ref_r) = do
                let ref_e = IRefT elem_ty ref_p ref_r
                ref_pe' <- evalStaticOp' doUH doBK doUndet
                                         ref_e resultType handler
                return (pExprToHExpr ref_pe')
        cell_es' <- mapM mapFn cells
        (e', _) <- improveDynSel ic idx_e idx_sz
                        arr_i arr_ty' (Array.bounds arr) cell_es'
        return $ P arr_p e'
    _ -> internalError ("evalStaticOpInArray': fall through: " ++
                        ppReadable arr_e')

-- Evaluate an expression to WHNF
-- WHNF can involve top level suspended primitives (handled later by handlePrim)
eval1 :: HExpr -> G PExpr
eval1 e = evalAp "eval" e []

data Arg = E HExpr | T IType deriving (Eq, Show)

getArgPosition :: Arg -> Position
getArgPosition (E e) = getIExprPosition e
getArgPosition (T t) = getITypePosition t

evalArgUH :: Arg -> G Arg
evalArgUH (T t) = return (T t)
evalArgUH (E e) = do (e', _) <- evalUH e
                     return (E e')

instance PPrint Arg where
    pPrint d p (E e) = pPrint d p e
    pPrint d p (T t) = text"\183" <> pPrint d p t

mkAp :: HExpr -> [Arg] -> HExpr
mkAp f [] = f
mkAp f (E e : as) = mkAp (iAp f e) as
mkAp f (T t : as) = mkAp (iAP f t) as

mkApUH :: HExpr -> [Arg] -> G HExpr
mkApUH f es = do es' <- mapM evalArgUH es
                 return (mkAp f es')

-- Evaluate a function applied to some number (possibly 0) of arguments
-- (types and expressions)
-- calls evalAp' to do the actual work, and corrects the cross-ref info
evalAp :: String -> HExpr -> [Arg] -> G PExpr
evalAp str e es = do
  cross <- getCross
  let str' = str ++ " (" ++ show (length es) ++ ")"
  when doDebug $
      -- cannot "show (mkAp e es)" or "show e" or else it goes in an infinite loop
      traceM ("evalAp enter " ++ str' ++ " [:\n" ++ ppReadable (mkAp e es))
  r_orig@(P pred iexpr) <- evalAp' e es
  -- when "cross" is False, this just returns "r_orig"
  r <- mapPExprPosition cross ((P pred e), r_orig)
  when doTraceTypes $ do
      let unev = mkAp e es
      let unev_t = iGetType unev
      let r_t = iGetType iexpr
      when (unev_t /= r_t) $
          internalError ("bad types: " ++ ppReadable (unev_t, unev, r_t, r))
  when doDebug $
      traceM ("evalAp exit  " ++ str' ++ " ]:\n"++ ppReadable (mkAp e es, r))
  return r

-- evaluate a function application
-- [arg] is a stack of application arguments on the left spine of the expression
evalAp' :: HExpr -> [Arg] -> G PExpr

-- simplify numeric types involving SizeOf
evalAp' e (T t : as) | not $ simpT t = do
    flags <- getFlags
    symt <- getSymTab
    case iConvT flags symt (iToCT t) of
      t'@(ITNum _) -> evalAp "simpNumT" e (T t' : as)
      _ -> errG (getIExprPosition e, EValueOf (ppString t))
  where simpT (ITNum _) = True
        simpT t = iGetKind t /= Just IKNum

evalAp' f@(ICon i (ICDef t e)) as = do
        -- recurse into evaluating e
        step i
        e' <- cacheDef i t e
        when doFunExpand $ do
            traceM ("expand " ++ ppReadable (mkAp f as))
        r <- evalAp "ICDef" e' as
        when doFunExpand2 $ do
            let P _ re = r
            traceM ("expand done\n" ++ ppReadable (mkAp f as, re))
        return r
evalAp' e@(ICon i ic)          as = conAp i ic e as
-- it's WHNF
evalAp' e@(ILam _ _ _)         [] = return (pExpr e)
-- place arg onto heap, substitute arg with heap reference in function body
evalAp'   (ILam i t e)   (E a:as) = do
        a' <- toHeap "apply" a (Just i)
        -- position information is clobbered by this point
        when doDebug $ traceM ("apply arg=" ++ ppReadable (a', a))
        let e' = eSubst i a' e
        evalAp "ILam" e' as
evalAp'   f@(ILam _ _ _) (T t:as) = internalError("evalAp' ILam: " ++ ppReadable (f,t))

-- it's WHNF
evalAp' e@(ILAM _ _ _)         [] = return (pExpr e)
-- substitute type
evalAp'   (ILAM i k e)   (T t:as) = evalAp "ILAM" (etSubst i t e) as
evalAp'   f@(ILAM _ _ _) (E e:as) = internalError ("evalAp' ILAM:" ++ ppReadable (f,e))
-- place applications args on the stack and evaluate function
evalAp' e@(IAps f tys es)      as =
      evalAp "IAps" f (map T tys ++ map E es ++ as)

-- look up heap references for constants, but leave as heap reference for others
-- XXX Lennart is not sure why
-- Ravi: I think this is so conAp and friends can "see" all the relevant constants
evalAp' e@(IRefT _ ptr ref)            [] = do
        pe <- evalHeap (ptr, ref)
        case pe of
            P _ (ICon _ _) -> return pe                -- expand constants
            _ -> return (pExpr e)                -- keep heap pointer for rest
evalAp' (IRefT t ptr ref)              as = do
        (P p e) <- evalHeap (ptr, ref)
--        when (p /= pTrue) $ traceM ("implicit function condition lost: " ++ ppReadable (p, e)) -- XXX
        let e' = iePrimWhenPred t p e
        when doDebug $ traceM ("iref ap " ++ ppReadable (mkAp e as))
        evalAp "IRefT" e' as
-- (there are no variables because they have been turned into IModVars)
-- XXX redundant, as it's caught by last clause?
evalAp' e@(IVar i)             as = internalError ("evalAp IVar: " ++ ppReadable (i,as))

evalHeap :: (HeapPointer, HeapData) -> G PExpr
evalHeap (ptr, ref) = do
    hc <- getHeap ref
    cross <- getCross
    case hc of
     HLoop (Just name) -> errG (getPosition name, EModuleLoop (pfpString name))
     -- XXX should not be possible (we hope)
     HLoop (Nothing)   -> errG (noPosition, EModuleLoop "<unknown>")
     HWHNF { hc_pexpr = e } -> return e
     HNF { hc_pexpr = e } -> return e
     HUnev { hc_hexpr = e, hc_name = expr_name } -> do
        -- updHeap (ptr, ref) (internalError "blackHole")
        when doDebug $ traceM ("evalHeap " ++ ppReadable (ptr, e))
        -- we don't use evalUH here because we don't want to trigger
        -- lazy bit-array fusing
        pe' <- eval1 e >>= unheap
        when doDebug $ traceM ("evalHeap " ++ ppReadable (ptr, pe'))
        case pe' of
            P _ (IAps (ICon _ (ICUndet { })) _ _) -> internalError ("evalHeap: " ++ ppReadable (ptr, pe'))
            -- create IRefs for ICTuple fields to prevent repeat evaluation after selection
            P p (IAps f@(ICon con_name (ICTuple { fieldIds = field_names })) ts as) -> do
                let prefix | Just pfx <- expr_name = mkUSId (unQualId pfx)
                           | otherwise = id
                    struct_field_names =
                         [Just (prefix (unQualId name)) | name <- field_names]
                as' <- zipWithM (toHeap "move-tuple") as struct_field_names
                when doDebug $ traceM ("evalHeap move #1\n" ++ ppReadable (zip as' as))
                let pe'' = P p (mapIExprPosition cross
                                ((heapCellToHExpr hc),
                                 (IAps f ts (map (mapIExprPosition cross) (zip as as')))))
                let new_cell = HWHNF { hc_pexpr = pe'', hc_name = expr_name }
                updHeap "evalHeap-tuple" (ptr,ref) new_cell
                return pe''
            -- create IRefs for arguments of other potentially non-strict
            -- applications (e.g., ICCon) to prevent repeat evaluation later
            P p (IAps f ts as) -> do
                let isLazyOp (ICon _ (ICCon {})) = True
                    isLazyOp (ICon _ (ICTuple {})) = True
                    isLazyOp (ICon _ (ICPrim _ p)) | p == PrimChr ||
                                                     realPrimOp p = False
                                                   | strictPrim p = internalError ("evalHeap - prim should be evaluated:" ++ ppReadable (p, pe'))
                                                   | otherwise = True
                    isLazyOp _ = False
                let th = if (isLazyOp f) then toHeapInferName else toHeapWHNFInferName
                as' <- mapM (th "move-ap") as
                when doDebug $ traceM ("evalHeap move #2\n" ++ ppReadable (zip as' as))
                let pe'' = P p (mapIExprPosition cross
                                ((heapCellToHExpr hc),
                                 (IAps f ts (map (mapIExprPosition cross) (zip as as')))))
                let new_cell = HWHNF { hc_pexpr = pe'', hc_name = expr_name }
                updHeap "evalHeap-IAps" (ptr,ref) new_cell
                return pe''
            _ -> do
                let new_cell = HWHNF {hc_pexpr = pe', hc_name = expr_name }
                updHeap "evalHeap" (ptr,ref) new_cell
                return pe'

-- used when IAps expr@(ICon name coninfo) ...
-- so Id is name, IConInfo is coninfo, IExpr is expr, as are the accumulated arguments
conAp :: Id -> IConInfo HeapData -> HExpr -> [Arg] -> G PExpr
conAp i ic e as = do
  when doConAp $
      traceM ("conAp enter: " ++ ppReadable i ++ "\n" ++ ppReadable (mkAp e as))
  r <- conAp' i ic e as
  when doConAp $
      traceM ("conAp exit " ++ ppReadable i ++ "\n" ++ ppReadable (mkAp e as, r))
  return r

bldAp' :: String -> HExpr -> [Arg] -> G PExpr
bldAp' s f as = do
        when doConAp $ traceM ("bldAp' " ++ s ++ " " ++ ppReadable (mkAp f as))
        return (P pTrue (mkAp f as))

-- build application and unheap
-- convenient way of evaluating further for strict applications
-- (e.g. method calls and other primitives which are not already evaluated)
bldApUH' :: String -> HExpr -> [Arg] -> G PExpr
bldApUH' s f as = do
        e <- mkApUH f as
        when doConAp $ traceM ("bldApUH' " ++ s ++ " " ++ ppReadable e)
        return (P pTrue e)

conAp' :: Id -> IConInfo HeapData -> HExpr -> [Arg] -> G PExpr

-- Delta rules: execute primitives (constants)

-- Variables are already in WHNF
conAp' _ (ICStateVar { }) e as = bldApUH' "ICStateVar" e as
conAp' _ (ICMethArg { })  e as = bldApUH' "ICMethArg" e as
conAp' _ (ICModPort { })  e as = bldApUH' "ICModPort" e as
conAp' _ (ICModParam { }) e as = bldApUH' "ICModParam" e as
conAp' _ (ICValue { })    e as = bldApUH' "ICValue" e as

-- Constants
conAp' _ (ICInt { })    e as = bldApUH' "ICInt" e as
conAp' _ (ICReal { })   e as = bldApUH' "ICReal" e as
conAp' _ (ICString { }) e as = bldApUH' "ICString" e as
conAp' _ (ICChar { })   e as = bldApUH' "ICChar" e as
conAp' _ (ICHandle { }) e as = bldApUH' "ICHandle" e as
conAp' _ (ICName { })   e as = bldAp' "ICName" e as
conAp' _ (ICAttrib { }) e as = bldAp' "ICAttrib" e as
conAp' _ (ICPosition { }) e as = bldAp' "ICPosition" e as

-- Actions
conAp' i (ICPrim _ PrimJoinActions) f [E a1, E a2] = do
  P p1 a1' <- eval1 a1
  P p2 a2' <- eval1 a2
  case (a1', a2') of
    (ICon _ (ICPrim _ PrimNoActions), _) -> return $ P (pConj p1 p2) a2'
    (_, ICon _ (ICPrim _ PrimNoActions)) -> return $ P (pConj p1 p2) a1'
    _ -> return $ P (pConj p1 p2) (IAps f [] [a1', a2'])

-- Undefined
conAp' i (ICPrim _ PrimRawUndefined) _ (T t : E pos_e : E kind_e : as) = do
  pos <- evalPosition pos_e
  i <- evalInteger kind_e
  let kind = case (integerToUndefKind i) of
               Just k -> k
               -- we used to return UDontCare here
               Nothing -> internalError ("primRawUndefined kind: " ++ itos i)
  evalAp "PrimRawUndefined" (icUndetAt pos t kind) as

conAp' i (ICPrim _ PrimBuildUndefined) _ (T t : E pos_e : E kind_e : as) = do
  pos <- evalPosition pos_e
  kind_integer <- evalInteger kind_e
  doBuildUndefined t pos kind_integer as

conAp' i (ICPrim _ PrimIsRawUndefined) _ (T t : E e : as) = do
  -- XXX should we propagate the implicit condition here?
  (P p e') <- eval1 e
  -- traceM ("IsRawUndefined: " ++ show e')
  case e' of
    ICon _ (ICUndet { }) -> -- do traceM ("IsRawUndefined: True")
                               return (P p iTrue)
    _ -> -- do traceM ("IsRawUndefined: False")
            return (P p iFalse)

conAp' i (ICPrim _ PrimMethod) _ [T t, E eInNames, E meth] = do
  (inNames, _) <- evalStringList eInNames
  P p meth' <- eval1 meth
  return $ P p $ ICon (dummyId noPosition) $ ICMethod {iConType = t, iInputNames = inNames, iMethod = meth'}

-- XXX is this still needed?
conAp' i (ICUndet { iConType = t })  e as | t == itClock =
   errG (getIdPosition i, EUndeterminedClock)
conAp' i (ICUndet { iConType = t })  e as | t == itReset =
   errG (getIdPosition i, EUndeterminedReset)
conAp' i (ICUndet { iConType = t })  e as | (isitInout_ t) =
   errG (getIdPosition i, EUndeterminedInout)
conAp' i (ICUndet { iConType = t })  e as | t == itRules =
   errG (getIdPosition i, EUndeterminedRules)
conAp' _ (ICUndet { }) f as0@(E _ : as) = internalError ("conAp' undet: " ++ ppReadable (mkAp f as0))
conAp' _ (ICUndet { })  e as = bldApUH' "ICUndet" e as

-- Verilog
conAp' _ (ICVerilog { })    e as = bldApUH' "ICVerilog" e as

-- Clocks
conAp' _ (ICClock { })      e as = bldApUH' "ICClock" e as

-- Resets
conAp' _ (ICReset { })      e as = bldApUH' "ICReset" e as

-- Inouts
conAp' _ (ICInout { })      e as = bldApUH' "ICInout" e as

-- Data types
conAp' _ (ICIs { conTagInfo = cti }) i as =
    case dropT as of
      [ E e ] -> do
          let tys = takeT as
              ty = itBit1
          evalStaticOp' True True False e ty (doIs i tys cti)
      _ -> internalError ("conAp': ICIs: " ++ ppReadable (mkAp i as))
conAp' c (ICOut { iConType = outty, conTagInfo = cti }) o as =
    case dropT as of
      E e : as' -> do
          let tys = takeT as
              ty = case itInst outty tys of
                     (ITAp _ t) -> t
                     _ -> internalError "IExpand.conAp' ICOut: ty"
              resType = dropArrows (length as') ty
{-        -- XXX do we need to heap the args, to avoid duplication?
          let toHeapArg (E e) = toHeapInferName "out-arg" e >>= return . E
              toHeapArg a = return a
          as'' <- mapM toHeapArg as'
-}
          evalStaticOp' True True False e resType (doOut o c tys ty cti as')
      _ -> internalError ("conAp': ICOut: " ++ ppReadable (mkAp o as))
conAp' c (ICSel { iConType = selty, selNo = n }) sel as =
    case dropT as of
      E e : as' -> do
          let tys = takeT as
              ty = case itInst selty tys of
                     (ITAp _ t) -> t
                     _ -> internalError "IExpand.conAp' ICSel: ty"
              resType = dropArrows (length as') ty
{-        -- XXX do we need to heap the args, to avoid duplication?
          let toHeapArg (E e) = toHeapInferName "sel-arg" e >>= return . E
              toHeapArg a = return a
          as'' <- mapM toHeapArg as'
-}
          evalStaticOp' True True False e resType (doSel sel c tys ty n as')
      _ -> internalError ("conAp': ICSel: " ++ ppReadable (mkAp sel as))

-- constructors are non-strict

-- turn all unit-argument / no-argument constructiors into PrimChr
-- this is safe because the difference is not observable, and it helps with
-- improveIf
conAp' i (ICCon ict cti) _ as | hasNoArg =
    evalAp "ICCon Enum" icPrimChr (T sizeNum :  T resultType :  E bitExpr : as')
  where sizeNum    = mkNumConT (tagSize cti)
        bitExpr    = mkAp icPrimIntegerToBit [T sizeNum, E (iMkLit itInteger (conTag cti))]
        (hasNoArg, resultType, argsToDrop) =
            case (itGetArrows (itInst ict (takeT as))) of
                     ([t], resultType) | t == itPrimUnit -> (True, resultType, 1)
                     _ -> (False, internalError("no resultType"), internalError ("no argsToDrop"))
        as' = drop argsToDrop $ dropT as

conAp' _ (ICCon { }) c as = bldAp' "ICCon" c as
conAp' _ (ICTuple { }) c as = bldAp' "ICTuple" c as

-- When (represents implicit conditions)
conAp' i (ICPrim _ PrimWhen) _ (T t : E p : E e : as) = do
        when doDebug $ traceM ("WHEN " ++ ppReadable (p, e))
        -- XXX canLiftCond expects NF
        (P p_p p', _) <- evalNF p
        let p'' = pConj p_p (pAtom p')
        -- Check that the user has not applied "when" to an invalid expr
        -- XXX This will also check compiler-generated PrimWhen for rules/methods
        canLift <- canLiftCond p'
        when (not canLift) $ deferErrors [(getIdPosition i, EInvalidWhen)]
        addPredG p'' $ evalAp "PrimWhen" e as
conAp' _ (ICPrim _ PrimWhen) _ as = internalError ("compAp' PrimWhen: " ++ ppReadable as)

-- When (represents implicit conditions)
conAp' _ (ICPrim _ PrimWhenPred) _ (T t : E (ICon _ (ICPred { iPred = p })) : E e : as) = do
        when doDebug $ traceM ("WHEN Pred " ++ ppReadable (p, e))
        addPredG p $ evalAp "PrimWhenPred" e as
conAp' _ (ICPrim _ PrimWhenPred) _ as = internalError ("compAp' PrimWhenPred: " ++ ppReadable as)

-- strictness
conAp' _ (ICPrim _ PrimSeq) _ (T _ : T _ : E e1 : E e2 : as) = do
   -- XXX should I unheap here to make sure bit arrays are forced?
   -- Or do I not bother because there shouldn't be a space leak either way?
   _ <- eval1 e1
   evalAp "PrimSeq" e2 as

-- implicit-condition strictness
conAp' _ (ICPrim _ PrimSeqCond) _ as0@(T t1 : T _ : E e1 : E e2 : as) = do
   when (not (isAbstractType t1)) $
     internalError ("PrimSeqCond not abstract: " ++ ppReadable as0)
   -- unheap to make sure we get the full implicit condition
   -- forcing bit-arrays is a nice side effect
   (_, P p e) <- evalUH e1
   p_buried <- getBuriedPreds e
   let p_tot = pConj p p_buried
   addPredG p_tot $ evalAp "PrimSeqCond" e2 as

conAp' _ (ICPrim _ PrimImpCondOf) fe (T t : E e : as) = do
  eWarning (getIExprPosition fe, WExperimental "primImpCondOf")
  let ce = CLam (Right id_x) (CApply (CVar idPrimDeepSeqCond) [CVar id_x, CVar id_x])
  let it = t `itFun` t
  let ct = iToCT it
  P p  f <- evalCExpr "PrimImpCondOf" ce ct as
  -- only UH here because PrimDeepSeqCond should do the rest
  (_, P p' e') <- evalUH (mkAp f (E e : as))
  -- XXX this is duplicate work if primSeqCond was employed?
  p_buried <- getBuriedPreds e'
  -- This line is needed to simplify away if-exprs so that we return the
  -- simplest expression (so it won't pick up unnecessary implicit conditions)
  pFinal <- normPConj $ pConj p (pConj p' p_buried)
  -- XXX This conversion produces the aggressive form
  -- XXX we should get the choice of aggressive vs conservative from the
  -- XXX context, or at least via an argument to impCondOf?
  let eFinal = predToIExpr pFinal
  return $ P pTrue eFinal

-- errors, messages and warnings

conAp' i (ICPrim _ PrimMessage) _ (T t : E pos_e : E s : E e : as) = do
  pos  <- evalPosition pos_e
  showPrimMessage pos s
  evalAp "PrimMessage - result" e as

conAp' i (ICPrim _ PrimError) _ (T t : E pos_e : E s : as) = do
  pos  <- evalPosition pos_e
  showPrimError pos s
  internalError "IExpand: unhandled PrimError"

conAp' i (ICPrim _ PrimGenerateError) _ (T t : E num_e : E pos_e : E s : as) = do
  num <- evalInteger num_e
  pos <- evalPosition pos_e
  showGenerateError num pos s
  internalError "IExpand: unhandled PrimGenerateError"

conAp' i (ICPrim _ PrimWarning) _ (T t : E pos_e : E s : E e : as) = do
  pos  <- evalPosition pos_e
  showPrimWarning pos s
  evalAp "PrimWarning - result" e as

conAp' i (ICPrim _ PrimUninitialized) _ (T t : as) = do
  let it = itPosition `itFun` itString `itFun` t
  -- polymorphism should be resolved
  let ct = iToCT it
  let ce = CVar idPrimMakeUninitialized
  evalCExpr "PrimUninitialized" ce ct as

conAp' i (ICPrim _ PrimRawUninitialized) _ (T t : E pos_e : E name : as) = do
  -- note that we don't fall back to PrimUninitialized
  -- because PrimRawUninitialized can also be invoked by a compound type
  -- (e.g. Bit#(n) or Vector) to make a more user-friendly error
  pos  <- evalPosition pos_e
  (name, _) <- evalString name
  deferErrors [(pos, EUninitialized name)]
  doBuildUndefined t pos uNotUsedInteger as

conAp' _ (ICPrim _ PrimMarkArrayUninitialized) _ (T t : E pos_e : E name_e : E arr : as) = do
  P p e <- eval1 arr
  case e of
    (ICon i ci@(ICLazyArray { uninit = Nothing })) -> do
      let ci' = ci { uninit = Just (pos_e, name_e) }
      addPredG p $ evalAp "PrimMarkArrayUninitialized" (ICon i ci') as
    _ -> internalError ("PrimMarkArrayUninitialized unexpected: " ++ ppReadable e)

conAp' _ (ICPrim _ PrimMarkArrayInitialized) _ (T t : E arr : as) =
    -- use evalStaticOp, but don't have it call "evalUH",
    -- because we don't want to trigger lazy array evaluation / fusing
    evalStaticOp' False True False arr arr_ty doMarkArrayInit
  where
    arr_ty = ITAp itPrimArray t
    doMarkArrayInit :: HExpr -> (HPred, HExpr) -> G PExpr
    doMarkArrayInit _ (p, e) =
      case e of
        (ICon i ci@(ICLazyArray { })) -> do
          let ci' = ci { uninit = Nothing }
          addPredG p $ evalAp "PrimMarkArrayInitialized" (ICon i ci') as
        -- don't force evaluation of an undet
        -- XXX is this needed?
        (ICon i (ICUndet { iuKind = k })) -> return $ P p e
        (IAps (ICon _ (ICPrim _ PrimArrayDynUpdate)) _ _) ->
          -- there should be another call to PrimMarkArrayInitialized
          -- so let that call do the work
          return $ P p e
        _ -> internalError ("doMarkArrayInit: " ++ ppReadable e)

conAp' i (ICPrim _ PrimPoisonedDef) _ (T t : E id_e : _) = do
  name <- evalName id_e
  errG (getIdPosition name, EPoisonedDef (pfpId PDReadable name))

-- "run" the module monad to build a pure value
conAp' i (ICPrim _ PrimBuildModule) _ [T t, E name, E clock, E reset, E mod_expr]  = do
  n      <- evalName name
  (c, _) <- evalClock clock
  (r, _) <- evalReset reset
  ns' <- newIStateLoc n n t []

  -- save and restore clock gate uses so that there are no unresolved
  -- uses at iExpandRules
  old_clk_gate_uses <- getClkGateUses
  clearClkGateUses

  env_pps <- getPragmas
  setPragmas []

  showModProgress ns' "Elaborating module"
  pushModuleSchedNameScope ns' t

  pe <- iExpandModule False (c,r) ns' pTrue mod_expr

  popModuleSchedNameScope
  showModProgress ns' "Finished module"

  setPragmas env_pps
  setClkGateUses old_clk_gate_uses

  -- XXX do not like making primBuildModule non-tail-recursive
  return (pe)

conAp' i (ICPrim _ PrimInoutUncast) _ [T sz, T t, E inout] = do
  (_,e) <- evalInout inout
  case e of
    (ICon i ci@(ICInout {})) -> return $ pExpr (ICon i ci { iConType = itInoutT t })
    _ -> internalError "PrimInoutUncast"

conAp' i (ICPrim _ PrimInoutCast) _ [T t, T (ITNum sz), E inout] = do
  (_,e) <- evalInout inout
  case e of
    (ICon i ci@(ICInout {})) -> return $ pExpr (ICon i ci { iConType = itInout_N sz })
    _ -> internalError "PrimInoutCast"

-- get names from ILam so we can replicate lambda-bound hack for augmented module monads
conAp' i (ICPrim _ PrimGetParamName) e [T _, T _, E fun] = do
  fun' <- evaleUH fun
  case fun' of
    (ILam i _ _) -> return $ pExpr (iMkName idPrimGetParamName i)
    otherwise    -> eNoNF e

-- get the name of a state instance
conAp' _ (ICPrim _ PrimGetModuleName) _ [T t, E e] = do
  e' <- evaleUH e
  case e' of
    (ICon i (ICStateVar {})) -> return $ pExpr (iMkName i i)
    _ -> do
     e'' <- unheapAll e'
     let err = "PrimGetModuleName: no state var - " ++ ppReadable e''
     -- we don't check that all the names we find match because this is
     -- an internal primitive (that should be used carefully)
     let i = headOrErr err (getStateVarNames e'')
     return $ pExpr (iMkName i i)

conAp' _ (ICPrim _ PrimGetModuleName) _ as = internalError ("PrimGetModuleName " ++ ppReadable as)

-- ord (chr e)  -->  e
-- ord C_n  -->  n
-- ord (if c t e)  -->  if c (ord t) (ord e)
-- ord _  -->  _
conAp' _ (ICPrim _ PrimOrd) o [T f, T sz, E e] = evalStaticOp e (aitBit sz) handleOrd
  where handleOrd (IAps (ICon _ (ICPrim _ PrimChr)) _ [e']) = eval1 e'
        handleOrd (IAps (ICon _ (ICCon { conTagInfo = cti })) _ _) =
            return $ pExpr $ iMkLitAt (getIExprPosition e) (aitBit sz) (conTag cti)
        handleOrd e' = nfError "primOrd" e'

-- chr (ord e)  -->  e
-- chr (if c t e)  -->  if c (chr t) (chr e)
conAp' _ (ICPrim _ PrimChr) o [T sz, T to, E e] = evalStaticOp e to handleChr
  where handleChr (IAps (ICon _ (ICPrim _ PrimOrd)) [to', _] [e']) | to == to' = eval1 e'
        handleChr e' = return $ pExpr $ mkAp o [T sz, T to, E e']

-- valueOf, fast case for ITNum
conAp' i (ICPrim _ PrimValueOf) _ [T (ITNum n), _] =
    return $ pExpr $ iMkLitAt (getPosition i) itInteger n
-- valueOf, for non-expanded type operators
-- errors here because we handle it in evalAp'
conAp' i (ICPrim _ PrimValueOf) _ [T t, _] = internalError ("PrimValueOf unsimplified: " ++ ppReadable t)

-- stringOf, fast case for ITStr
conAp' i (ICPrim _ PrimStringOf) _ [T (ITStr s), _] =
    return $ pExpr $ iMkStringAt (getPosition i) $ getFString s
-- stringOf, for non-expanded type operators
-- errors here because we handle it in evalAp'
conAp' i (ICPrim _ PrimStringOf) _ [T t, _] = internalError ("PrimStringOf unsimplified: " ++ ppReadable t)

-- typeOf needs to expand type operators like SizeOf that are implemented via
-- synonym-expansion - no other synonyms should survive in the evaluator
-- XXX using iToCT here means we're assuming the type is not polymorphic
conAp' i (ICPrim _ PrimTypeOf) _ [T t, _] = do
   flags <- getFlags
   symt <- getSymTab
   return $ pExpr (icType i (iConvT flags symt (iToCT t)))

-- Primitives that should be used downstream
conAp' _ (ICPrim _ PrimZeroExt) _ [t2@(T t), t1, t3, e] =
        evalAp "PrimZeroExt" icPrimConcat [t2, t1, t3,
                                           E (iMkLitAt (getArgPosition e) (aitBit t) 0),
                                           e]
conAp' i (ICPrim _ PrimTrunc) _   [_, n@(T _), m@(T _), e@(E _)] =
        evalAp "PrimTrunc" (icSelect (getIdPosition i)) [n, T (mkNumConT 0), m, e]

-- Special case of doPrimOp that checks bounds and keeps the base.
conAp' tfs (ICPrim _ PrimIntegerToBit) fe [T ty@(ITNum k), E e] = evalStaticOp e (itBitN k) handleInt
  where handleInt (ICon i (ICInt { iVal = il@(IntLit { ilValue = l, ilWidth = w, ilBase = b }) }))
            -- if structure tuned to avoid negative exponents in 2^k
            | k < 0            = err
            | k == 0 && l /= 0 = err
            | k == 0           = result
            | l >= 2^k         = err
            | l < -(2^(k-1))   = err
            | otherwise        = result
          where err = errG (getIdPosition i, EInvalidLiteral "Bit" k (pfpString il))
                result = return $ pExpr $ iMkLitWBAt (getIdPosition i) (itBitN k) w b (mask k l)
        handleInt e' = nfError "primIntegerToBit" $ mkAp fe [T ty, E e']

-- Special case of doPrimOp that checks bounds and keeps the base.
-- XXX we can now implement this in the prelude, with primIntegerToBits
conAp' tfs (ICPrim _ PrimIntegerToUIntBits) fe [T ty@(ITNum k), E e] = evalStaticOp e (itBitN k) handleInt
  where handleInt (ICon i (ICInt { iVal = il@(IntLit { ilValue = l, ilWidth = w, ilBase = b }) })) =
          if k < 0 || l >= 2^k || l < 0 then
            errG (getIdPosition i, EInvalidLiteral "UInt" k (pfpString il))
          else
            return $ pExpr $ iMkLitWBAt (getIdPosition i) (itBitN k) w b (mask k l)
        handleInt e' = nfError "primIntegerToUIntBits" $ mkAp fe [T ty, E e']

-- Special case of doPrimOp that checks bounds and keeps the base.
-- XXX we can now implement this in the prelude, with primIntegerToBits
conAp' tfs (ICPrim _ PrimIntegerToIntBits) fe [T ty@(ITNum k), E e] = evalStaticOp e (itBitN k) handleInt
  where handleInt (ICon i (ICInt { iVal = il@(IntLit { ilValue = l, ilWidth = w, ilBase = b }) }))
            -- structure tuned to avoid negative exponents in 2^k
            | k < 0            = err
            | k == 0 && l /= 0 = err
            | k == 0           = result
            | l >= 2^(k-1)     = err
            | l < -(2^(k-1))   = err
            | otherwise        = result
          where err = errG (getIdPosition i, EInvalidLiteral "Int" k (pfpString il))
                result = return $ pExpr $ iMkLitWBAt (getIdPosition i) (itBitN k) w b (mask k l)
        handleInt e' = nfError "primIntegerToIntBits" $ mkAp fe [T ty, E e']

-- XXX This could go in doPrimOp
conAp' tfs (ICPrim _ PrimIntegerToString) fe [E e] = evalStaticOp e itString handleInt
  where handleInt (ICon i (ICInt { iVal = IntLit { ilValue = l, ilBase = b }})) = do
          let result = if l < 0 then
                         localIntToString "-" (-l) b
                       else localIntToString "" l b
          return $ pExpr $ iMkStringAt (getIExprPosition fe) result
        handleInt e' = nfError "primIntegerToString" $ mkAp fe [E e']
        localIntToString s l b = s ++ (showIntAtBase b intToDigit l "")

conAp' tfs (ICPrim _ PrimIsStaticInteger) fe [E e] = do
  (_, P _ e') <- evalUH e
  -- traceM ("primIsStaticInteger " ++ ppReadable e)
  case e' of
    ICon i (ICInt { }) -> do -- traceM ("true\n")
                             return (pExpr iTrue)
    _                  -> do -- traceM ("false\n")
                             return (pExpr iFalse)

conAp' tfs (ICPrim _ PrimAreStaticBits) fe [T t, E e] = do
  (_, P _ e') <- evalUH e
  -- traceM ("primIsStaticInteger " ++ ppReadable e)
  case e' of
    ICon i (ICInt { }) -> do -- traceM ("true\n")
                             return (pExpr iTrue)
    _                  -> do -- traceM ("false\n")
                             return (pExpr iFalse)

conAp' tfs (ICPrim _ PrimIsBitArray) fe [T _, E e] = do
   -- don't evalUH since that will force fusing of the array
   P _ e' <- eval1 e
   case e' of
     ICon _ (ICLazyArray {}) -> return (pExpr iTrue)
     _ -> return (pExpr iFalse)

conAp' tfs (ICPrim _ PrimUpdateBitArray) fe [T (ITNum n), E bs, E i, E b] = do
   P p e' <- eval1 bs
   case e' of
     -- XXX check that it has been initialized here?
     -- library code should handle this
     ICon ci (ICLazyArray arr_ty arr _) -> do
       i' <- evalInteger i
       when ((i' < 0) || (i' >= n)) $
            internalError("primUpdateBitArray: index out of range: " ++ show i' ++
                          " >= " ++ show n)
       arr' <- iArrayUpdate arr i' b
       return (P p (ICon ci (ICLazyArray arr_ty arr' Nothing)))
     _ -> internalError ("PrimUpdateBitArray - not array: " ++ ppReadable e')

conAp' i (ICPrim _ PrimUninitBitArray) fe [T (ITNum len), E pos, E name] = do
  pos' <- toHeapInferName "uninit-bit" pos
  name' <- toHeapInferName "uninit-bit" name
  let uninit_bit n = mkArrayCell $ IAps icPrimUninitialized [itBit1] [pos', name'']
        where name'' = iMkStrConcat name' (iMkString ("[" ++ (show n) ++ "]"))
  elems <- mapM uninit_bit [0..len-1]
  let arr :: Array.Array Integer (ArrayCell HeapData)
      arr = Array.listArray (0, len-1) elems
  return (pExpr (ICon i (ICLazyArray (itBitN len) arr (Just (pos', name')))))

conAp' tfs (ICPrim _ PrimUIntBitsToInteger) fe [T (ITNum k), E e] = evalStaticOp e itInteger handleInt
  where handleInt (ICon i ci@(ICInt { })) = return $ pExpr $ ICon i (ci { iConType = itInteger })
        handleInt e' = do -- traceM "primUIntBitsToInteger";
                          -- traceM (show e ++ "\n")
                          -- traceM (show e' ++ "\n")
                          -- XXX consider EDynamicBits for the PrimIf case
                          nfError "primUIntBitsToInteger" e'

conAp' tfs (ICPrim _ PrimIntBitsToInteger) fe [T (ITNum k), E e] = evalStaticOp e itInteger handleInt
  where handleInt (ICon i ci@(ICInt { iVal = v@IntLit {ilValue = l} })) = do
          if l < 2^(k-1) then
            return $ pExpr $ ICon i (ci {iConType = itInteger})
           else
            return $ pExpr $ ICon i (ci {iConType = itInteger, iVal = v {ilValue = l - 2^k}})
        handleInt e' = do -- traceM "primIntBitsToInteger";
                          -- traceM (show e ++ "\n")
                          -- traceM (show e' ++ "\n")
                          -- XXX consider EDynamicBits for the PrimIf case
                          nfError "primIntBitsToInteger" e'

conAp' ci prim@(ICPrim _ PrimSetSelPosition) f (T _ : E pos_e : E res_e : as) = do
  poss <- evalPositions pos_e
  let res_e' = mkAp res_e as
      t' = iGetType res_e'
      icon = (ICon ci prim)
      handler = doSetSelPosition icon t' poss
  -- don't allow evalStaticOp to push through PrimSetSelPosition
  evalStaticOp' True False True res_e' t' handler

-- Dynamically unfold and evaluate string primitives of one argument
conAp' _ prim@(ICPrim _ op) fe@(ICon prim_id _) [E e] | stringPrim op =
    evalStaticOp e resType handleString
  where handleString e'@(ICon _ (ICString { iStr = s })) =
          let pos = getIExprPosition e'
          in case op of
               PrimStringToInteger -> return $ pExpr $ iStrToInt s pos
               PrimStringLength ->
                   return $ pExpr $ iMkLitAt pos itInteger (genericLength s)
               PrimGetStringPosition -> return $ pExpr $ iMkPosition pos
               PrimStringSplit ->
                   case s of
                     [] -> return $ pExpr $ iMkInvalid resType
                     (c:r) -> let e_c = iMkCharAt pos c
                                  e_r = iMkStringAt pos r
                                  e_pair = iMkPairAt pos
                                               itChar itString e_c e_r
                              in  return $ pExpr $ iMkValid resType e_pair
               PrimStringToChar ->
                   case s of
                     [c] -> return $ pExpr $ iMkCharAt pos c
                     _ -> errG (pos, EStringToChar s)
               _ -> internalError
                        ("conAp' unknown string prim: " ++ ppReadable op)
        handleString e' = nfError (show op) $ mkAp fe [E e']
        resType = dropArrows 1 (iConType prim)

conAp' _ prim@(ICPrim _  PrimSetStringPosition) fe@(ICon prim_id _) [E e1, E e2] = evalStaticOp e1 resType handleString1
  where handleString1 e1' = do evalStaticOp e2 resType (handleString2 e1')
        handleString2 (ICon _ (ICString { iStr = s }))
                      (ICon _ (ICPosition { iPosition = poss })) =
            let pos = getICPosition "PrimSetStringPosition" poss
            in  return $ pExpr $ iMkStringAt pos s
        handleString2 e1' e2' =
            nfError "primSetStringPosition" $ mkAp fe [E e1', E e2']
        resType = dropArrows 2 (iConType prim)

-- Dynamically unfold and evaluate string primitives of two arguments
conAp' _ prim@(ICPrim _ op) fe@(ICon prim_id _) [E e1, E e2] | stringPrim op =
    evalStaticOp e1 resType handleString1
  where handleString1 e1' = do evalStaticOp e2 resType (handleString2 e1')
        handleString2 (ICon _ (ICString {iStr = s1}))
                      e2'@(ICon _ (ICString {iStr = s2})) =
          case op of
            PrimStringEQ -> return $ pExpr $ iMkBool (s1 == s2)
            PrimStringConcat -> return $ pExpr $ iMkStringAt (getIExprPosition e2') (s1 ++ s2)
            _ -> internalError ("conAp' unknown string prim: " ++ ppReadable op)
        handleString2 e1' e2' =
          case op of
            PrimStringConcat -> return $ pExpr e'
            _ -> nfError "stringPrim" e'
          where e' = mkAp fe [E e1', E e2']
        resType = dropArrows 2 (iConType prim)

conAp' _ prim@(ICPrim _ PrimStringCons) fe@(ICon prim_id _) [E e1, E e2] =
    evalStaticOp e1 resType handleString1
  where handleString1 e1' = evalStaticOp e2 resType (handleString2 e1')
        handleString2 e1'@(ICon _ (ICChar { iChar = c }))
                      e2'@(ICon _ (ICString { iStr = s })) =
            let pos = bestPosition (getIExprPosition e1') (getIExprPosition e2')
            in  return $ pExpr $ iMkStringAt pos (c:s)
        handleString2 e1' e2' =
            nfError "primStringCons" $ mkAp fe [E e1', E e2']
        resType = dropArrows 2 (iConType prim)

conAp' _ prim@(ICPrim _ op) fe@(ICon prim_id _) [E e] | charPrim op =
    evalStaticOp e resType handleChar
  where handleChar e'@(ICon _ (ICChar { iChar = c })) =
          let pos = getIExprPosition e'
          in case op of
               PrimCharToString ->
                   return $ pExpr $ iMkStringAt pos [c]
               PrimCharOrd ->
                   return $ pExpr $ iMkLitAt pos itInteger (toInteger (ord c))
               _ -> internalError
                        ("ConAp' unknown char prim: " ++ ppReadable op)
        handleChar e' = nfError "charPrim" $ mkAp fe [E e']
        resType = dropArrows 1 (iConType prim)

conAp' _ prim@(ICPrim _ PrimCharChr) fe@(ICon prim_id _) [E e] =
    evalStaticOp e resType handleInt
  where handleInt e'@(ICon _ (ICInt { iVal = IntLit { ilValue = n } })) =
            let pos = getIExprPosition e'
            in  if ((n < 0) || (n > 255))
                then errG (pos, EIntegerToChar n)
                else return $ pExpr $ iMkCharAt pos (chr (fromInteger n))
        handleInt e' = nfError "primCharChr" $ mkAp fe [E e']
        resType = dropArrows 1 (iConType prim)

-- Dynamically unfold and evaluate integer/real primitives of one argument
conAp' _ prim@(ICPrim _ op) fe@(ICon prim_id _) [E e]
    | (integerPrim op || realPrim op)
    = evalStaticOp e resType handleLit
  where pos = getIExprPosition fe -- assuming the operator has a good position
        handleLit e' | (isIConInt e' || isIConReal e') = do
          case (doPrimOp pos op [] [e']) of
            Just (Right e) -> return $ pExpr $ e
            Just (Left errmsg) -> errG (pos, errmsg)
            Nothing -> internalError ("IExpand.conAp' - can't calculate: " ++
                                      ppReadable (op, e'))
                     | otherwise = nfError "integer/realPrim 1" $ mkAp fe [E e']
        -- if we touch a module parameter we can't evaluate further
        -- handleLit e' | isIConParam e' = nfError $ mkAp fe [E e']
        -- handleLit e' = return $ pExpr $ mkAp fe [E e']
        resType = dropArrows 1 (iConType prim)

-- Dynamically unfold and evaluate integer/real primitives of two arguments
conAp' _ prim@(ICPrim _ op) fe@(ICon prim_id _) [E e1, E e2]
    | (integerPrim op || realPrim op)
    = evalStaticOp e1 resType handleLit
  where pos = getIExprPosition fe -- assuming the operator has a good position
        handleLit e1' =
            do evalStaticOp e2 resType (handleLit2 e1')
        handleLit2 e1' e2' | (isIConInt e1' || isIConReal e1') &&
                             (isIConInt e2' || isIConReal e2') = do
          case (doPrimOp pos op [] [e1', e2']) of
            Just (Right e) -> return $ pExpr $ e
            Just (Left errmsg) -> errG (pos, errmsg)
            Nothing -> internalError ("IExpand.conAp' - can't calculate: " ++
                                      ppReadable (op, e1', e2'))
                           | otherwise = nfError "integer/realPrim 2" $ mkAp fe [E e1', E e2']
        -- if we touch a module parameter, we can't evaluate further
        -- handleLit2 e1' e2' | isIConParam e1 || isIConParam e2 = nfError $ mkAp fe [E e1', E e2']
        -- handleLit2 e1' e2' = return $ pExpr $ mkAp fe [E e1', E e2']
        resType = dropArrows 2 (iConType prim)

-- Strict primitives
conAp' _ (ICPrim _ op) fe@(ICon prim_id _) as | strictPrim op = do
        when doDebug $ traceM ("prim " ++ ppReadable (mkAp fe as))
        let f (E e) = do (ee, P p e') <- evalUH e; return $ (p, E ee, E e')
            f a     = return (pTrue, a, a)
        pas <- mapM f as
        let (ps, ees, as') = unzip3 pas
        let  p = pConjs ps

        -- the IType side of this is useless now, but included for completeness
        -- probably should use some of the xref position filtering logic
        let argPositions  = [(getArgPosition a) | a <- as']
        let goodPositions = [p | p <- argPositions, p /= noPosition]
        let bestPosition  = if (not (null goodPositions)) then
                              (head goodPositions)
                            else (head argPositions)

        let isDyn (IAps (ICon _ (ICPrim _ PrimArrayDynSelect)) _ _) = True
            isDyn (IAps (ICon _ (ICPrim _ PrimIf)) _ _) = True
            isDyn _ = False
        -- XXX we can also push the op into the arms of PrimIf/PrimArrayDynSelect
        -- XXX if all of the arms are IntLit, at least for single argument ops
        -- XXX (in the absence of this, we do a special case for PrimBNot, see below)
        if all isIntLit as' && not (null as') then
            case doPrimOp bestPosition op
                     [ t | T t@(ITNum _) <- as' ]
                     [ e | E e@(ICon _ (ICInt {})) <- as' ] of
            Just (Right e) -> return (P p e)
            Just (Left errmsg) -> errG (bestPosition, errmsg)
            Nothing ->
                --internalError ("conAp' strictPrim: " ++ ppReadable (op, as'))
                -- For now, make this arm a no-op, because some examples do
                -- reach here with prims that do not reduce (like PrimChr)
                -- (This uses the unheaped "ees", which includes the predicate.)
                bldAp' "Prim 1" fe ees
         else
            case (op, as') of
            (PrimBNot, [E e]) | isDyn e ->
                -- The iTransExpr catch-all will handle PrimIf but not arrays
                let handler e' =
                        case (doPrimOp bestPosition op [] [e']) of
                          Just (Right e_res) -> return (pExpr e_res)
                          Just (Left errmsg) -> errG (bestPosition, errmsg)
                          Nothing -> evalAp "Prim PrimBNot" fe [E e']
                in  addPredG p $ evalStaticOp e itBit1 handler
            -- name primitives
            (PrimJoinNames, [E (ICon _ (ICName { iName = n1 })),
                             E (ICon _ (ICName { iName = n2 }))]) ->
                let n' = setIdPosition (getIdPosition n1) (mkUSId n1 n2)
                in return (P p (iMkName prim_id n'))
            (PrimExtendNameInteger, [E (ICon _ (ICName { iName = n })),
                                     E (ICon _ (ICInt  { iVal  = IntLit { ilValue = l } }))]) ->
                let n' = setIdPosition (getIdPosition n) (mkUSId n (mkNumId l))
                in return (P p (iMkName prim_id n'))
            (PrimGetNamePosition, [E (ICon _ (ICName { iName = n }))]) ->
                return (P p (iMkPosition (getIdPosition n)))
            (PrimGetNameString, [E (ICon _ (ICName { iName = n }))]) ->
                -- no qualification because it is an instance name
                return (P p (iMkString (getIdBaseString n)))
            (PrimMakeName, [E estr,
                            E (ICon _ (ICPosition { iPosition = poss }))]) -> do
                (str, _) <- evalString estr
                let pos = getICPosition "PrimmakeName" poss
                    n = mkId pos (mkFString str)
                return (P p (iMkName prim_id n))

            -- position primitives
            (PrimPrintPosition, [E (ICon _ (ICPosition { iPosition = poss } ))]) -> do
                let pos = getICPosition "PrimPrintPosition" poss
                return (P p (iMkString (ppReadable pos)))

            -- reflective type primitives
            (PrimTypeEQ, [E (ICon _ (ICType {iType = t1 })), E (ICon _ (ICType {iType = t2}))]) ->
                return (P p (iMkBool (t1 == t2)))
            -- does not detect polymorphic (i.e. not fully applied) interface types by design
            (PrimIsIfcType, [E (ICon _ (ICType { iType = t }))]) ->
                return (P p (iMkBool (isIfcType t)))

            -- XXX we're inheriting the assumption of TypeOf
            --     that t is not polymorphic
            (PrimPrintType, [E (ICon _ (ICType { iType = t }))]) ->
                return (P p (iMkString (pfpString (iToCT t))))

            -- clock primitives
            (PrimSameFamilyClock, [E (ICon _ (ICClock {iClock = c1})), E (ICon _ (ICClock {iClock = c2}))]) ->
                return (P p (iMkBool (sameClockDomain c1 c2)))
            (PrimClockEQ, [E (ICon _ (ICClock {iClock = c1})), E (ICon _ (ICClock {iClock = c2}))]) ->
                return (P p (iMkBool (c1 == c2)))
            (PrimIsAncestorClock, [E (ICon _ (ICClock {iClock = c1})), E (ICon _ (ICClock {iClock = c2}))]) -> do
                res <- isClockAncestor c1 c2
                return (P p (iMkBool res))

            (PrimClockOf, _) -> do
              when doTraceClock $ traceM ("PrimClockOf: " ++ concatMap ppReadable as)
              -- want to pick up implicit conditions (should be exactly one expression in ees)
              let err = "conAp.PrimClockOf: no argument expression"
                  arg_e = firstE err ees
              ws <- extractWireSet arg_e
              case (wsGetClocks ws) of
               [c] -> return (P pTrue (icClock prim_id c))
               []  -> return (P pTrue icNoClock)
               (c:_) -> do minfos <- getMethodsByClockDomain arg_e
                           eWarning (getIExprPosition fe, WClockOfClocks minfos)
                           return (P pTrue (icClock prim_id c))
            (PrimClocksOf, _) -> do
              -- want to pick up implicit conditions (third expr is the one to extract clocks from)
              case (dropT ees) of
                es@[E nil, E cons, E e] -> do when doTraceClock $ traceM ("PrimClocksOf:\n" ++ intercalate "\n\n" (map show es))
                                              ws <- extractWireSet e
                                              eval1 (foldr (\c e ->
                                                             IAps cons [] [icClock prim_id c, e])
                                                          nil
                                                          (wsGetClocks ws))
                _ -> internalError ("conAp.PrimClocksOf illegal arguments " ++ (concatMap ppReadable as))

            -- reset primitives
            (PrimResetOf, _) -> do
              when doTraceClock $ traceM ("PrimResetOf: " ++ concatMap ppReadable as)
              -- want to pick up implicit conditions (should be exactly one expression in ees)
              let err = "conAp.PrimResetOf: no argument expression"
                  arg_e = firstE err ees
              ws <- extractWireSet arg_e
              case (wsGetResets ws) of
               [r] -> return (P pTrue (icReset prim_id r))
               []  -> return (P pTrue icNoReset)
               (r:_) -> do minfos <- getMethodsByReset arg_e
                           eWarning (getIExprPosition fe, WResetOfResets minfos)
                           return (P pTrue (icReset prim_id r))
            (PrimResetsOf, _) -> do
              -- want to pick up implicit conditions (third expr is the one to extract resets from)
              case (dropT ees) of
                es@[E nil, E cons, E e] -> do when doTraceClock $ traceM ("PrimResetsOf:\n" ++ intercalate "\n\n" (map show es))
                                              ws <- extractWireSet e
                                              eval1 (foldr (\r e ->
                                                             IAps cons [] [icReset prim_id r, e])
                                                          nil
                                                          (wsGetResets ws))
                _ -> internalError ("conAp.PrimResetsOf illegal arguments " ++ (concatMap ppReadable as))
            (PrimResetEQ, [E (ICon _ (ICReset {iReset = r1})), E (ICon _ (ICReset {iReset = r2}))]) ->
                return (P p (iMkBool (r1 == r2)))
            -- XXX - merge with doPrimOp case (which iTransform will do)?
            -- YYY - iTransform does not propagate positions
            _ -> do
              when doDebug $ traceM ("conAp: unknown prim! " ++ ppReadable op)
              when doTrans $ traceM ("conAp: iTransform fallthrough: " ++ ppReadable (op, mkAp fe as'))
              errh <- getErrHandle
              case (iTransExpr errh (mkAp fe as')) of
                  (e', True) -> do
                    -- we used to evaluate further here, but that shouldn't
                    -- be necessary (and probably indicates a bug elsewhere)
                    when (doDebug || doTrans) $ traceM ("conAp: iTransform result: " ++ ppReadable e')
                    return (P p e')
                  _ -> bldAp' "Prim 2" fe ees

-- sneaky position primitive
conAp' i ic@(ICPrim _ PrimGetEvalPosition) p [T t, E e] = do
  (e', _) <- evalUH e
  return (pExpr (iMkPosition (getIExprPosition e')))

-- genC
conAp' i ic@(ICPrim _ PrimGenC) p [] = do
  -- taint the module
  setBackendSpecific
  -- get the result from the flags
  flags <- getFlags
  let e = iMkRealBool (backend flags == Just Bluesim)
  return (pExpr e)

-- genVerilog
conAp' i ic@(ICPrim _ PrimGenVerilog) p [] = do
  -- taint the module
  setBackendSpecific
  -- get the result from the flags
  flags <- getFlags
  let e = iMkRealBool (backend flags == Just Verilog)
  return (pExpr e)

conAp' i ic@(ICPrim _ PrimGenModuleName) p [] = do
  modname <- getModuleName
  let e = iMkString modname
  return (pExpr e)

-- Non-strict primitives
-- (if c t e) ... --> if c (t ...) (e ...)
conAp' i ic@(ICPrim _ PrimIf) p (T ty : E c : E t : E e : as@(_:_)) = do
 --       traceM ("as: " ++ (show as))
 --       traceM ("ty: " ++ (show ty))
        as' <- mapM toHeapArg as
        when doDebug $ traceM ("if " ++ ppReadable (zip as' as))
        conAp i ic p [T ty', E c, E (mkAp t as'), E (mkAp e as')]
  where ty' = dropArrows (length as) ty
        -- avoid duplicating arguments to if
        toHeapArg (E e) = toHeapInferName "if-arg" e >>= return . E
        toHeapArg a = return a

conAp' i ic@(ICPrim _ PrimIf) f as@[T ty, E c, E t, E e] = doIf f as

conAp' i ic@(ICPrim _ PrimBAnd) f as@[E e1, E e2] = doAnd f as

conAp' i ic@(ICPrim _ PrimBOr) f as@[E e1, E e2] = doOr f as

-- PrimExpIf, PrimNoExpIf and PrimNoSplitDeep should be strict in their argument
conAp' _ (ICPrim _ pi) f as | isIfWrapper pi = bldApUH' "ICPrim" f as

-- evaluate PrimNoClock
conAp' _ (ICPrim _ PrimNoClock) f as = bldAp' "PrimNoClock" (icNoClock) as

-- evaluate PrimNoReset
conAp' _ (ICPrim _ PrimNoReset) f as = bldAp' "PrimNoReset" (icNoReset) as

-- evaluate PrimNoPosition
conAp' _ (ICPrim _ PrimNoPosition) f as = bldAp' "PrimNoPosition" (icNoPosition) as

conAp' i (ICPrim _ PrimArrayNew) f as = do
  when doDebug $ traceM ("conAp': Lazy PrimArrayNew")
  doArrayNew f as

conAp' i (ICPrim _ PrimArrayLength) f [T t, E e] = do
  when doDebug $ traceM ("conAp': Lazy PrimArrayLength!")
  doArrayLength f [T t, E e]

conAp' i (ICPrim _ PrimArraySelect) f as = do
  when doDebug $ traceM ("conAp': Lazy PrimArraySelect!")
  doArraySelect f as

conAp' i (ICPrim _ PrimArrayUpdate) f as = do
  when doDebug $ traceM ("conAp': Lazy PrimArrayUpdate!")
  doArrayUpdate f as

conAp' sel_i sel_c@(ICPrim _ PrimArrayDynSelect) _
           as@(T elem_ty: T sz_t@(ITNum idx_sz): E arr_e: E idx_e: as') = do
  (idx_e', _) <- evalUH idx_e
  let handleDynSel (ICon arr_i (ICLazyArray arr_ty arr Nothing)) = do
        -- check for constant index
        case idx_e' of
          ICon _ (ICInt { iVal = IntLit { ilValue = n } }) ->
              let (_, idx_max) = Array.bounds arr
              in  if (n > idx_max)
                  then let pos =  getPosition sel_i
                           u = undefKindToInteger UDontCare
                       in  doBuildUndefined elem_ty pos u as'
                  else let (ArrayCell ptr ref) = arr Array.! n
                       in  evalAp "DynSel const" (IRefT elem_ty ptr ref) as'
          _ -> do
            -- check if they're all the same
            -- (this will also convert selection from 1-element arrays
            -- into a simple PrimIf)
            let cells = Array.elems arr
                eqFn (ArrayCell p1 _) (ArrayCell p2 _) = (p1 == p2)
                all_eq = case cells of
                           (c:cs) -> all (eqFn c) cs
                           _ -> internalError ("doDynSel: empty array")
            if all_eq
              then let (ArrayCell ptr ref) = head cells
                       elem_e = IRefT elem_ty ptr ref
                       -- still need to check the bounds
                       sel_pos = getPosition sel_i
                       res_e = mkDynSelBoundsCheck sel_pos idx_sz
                                   (Array.bounds arr) idx_e' elem_ty elem_e
                   in  evalAp "DynSel1" res_e as'
              else do
                -- apply the elements to as' and eval
                let mapFn (ArrayCell ptr ref) = do
                        let r = IRefT elem_ty ptr ref
                        (pe, P p e') <- evalUH (mkAp r as')
                        return (pe, p, e')
                -- "pes" are used to construct the result if no progress is made
                (pes, ps, es) <- mapM mapFn cells >>= return . unzip3
                -- update the array type to account for applying to as'
                let elem_ty' =
                        let skip [] t = t
                            skip (_:as) (ITAp _ t) = skip as t
                            skip _ t = internalError ("conAp' DynSel: skip: " ++
                                                      ppReadable t)
                        in  skip as' elem_ty
                    arr_ty' =
                        case arr_ty of
                          (ITAp c _) | (c == itPrimArray) -> (ITAp c elem_ty')
                          _ -> internalError ("conAp' DynSel: type: " ++
                                              ppReadable arr_ty)
                    ic = (ICon sel_i sel_c)
                (e', b) <- improveDynSel ic idx_e' idx_sz
                               arr_i arr_ty' (Array.bounds arr) es
                if b
                  then do
                    -- "pSel" is smart enough to simplify the predicate
                    -- if all the arms are the same (or have common subpreds)
                    let p = pSel idx_e' idx_sz ps
                    return $ P p e'
                  else do
                    -- back out the change if a useful merge did not occur
                    -- XXX this is duplicating what "doIf" does, for preserving
                    -- XXX heap refs; does it really help?
                    let mkCell pe = do
                          IRefT _ ref_p ref_r
                              <- toHeapWHNFConInferName "DynSel" pe
                          return (ArrayCell ref_p ref_r)
                    cells' <- mapM mkCell pes
                    let arr' = Array.listArray (Array.bounds arr) cells'
                        arr_e'' = ICon arr_i (ICLazyArray arr_ty arr' Nothing)
                    return $ P pTrue $ IAps ic [elem_ty', sz_t] [arr_e'', idx_e']
      -- XXX consider reducing all DynUpd (e.g. put this code in conAp'
      -- XXX instead of here and in doArraySelect)
      handleDynSel (IAps (ICon _ (ICPrim _ PrimArrayDynUpdate))
                         [_, ITNum upd_idx_sz]
                         [upd_arr_e, upd_idx_e, upd_val_e]) = do
        -- Construct the result from expanding out PrimArrayDynUpdate:
        --    if (sel_idx == upd_idx) then upd_val else orig_arr[sel_idx]
        (P p0 res0) <- evalStaticOp upd_arr_e elem_ty handleDynSel
        let mkExtend in_sz out_sz e =
                let k = out_sz - in_sz
                    ts = [ITNum k, ITNum in_sz, ITNum out_sz]
                in  IAps icPrimZeroExt ts [e]
            eq_e = let (max_sz, e1, e2)
                         | idx_sz > upd_idx_sz = (idx_sz, idx_e, mkExtend upd_idx_sz idx_sz upd_idx_e)
                         | idx_sz < upd_idx_sz = (upd_idx_sz, mkExtend idx_sz upd_idx_sz idx_e, upd_idx_e)
                         | otherwise           =  (upd_idx_sz, idx_e, upd_idx_e)
                   in  iePrimEQ (ITNum max_sz) e1 e2
            if_e = ieIf elem_ty eq_e upd_val_e res0
        addPredG p0 $ evalAp "array-select-update" if_e as'
      handleDynSel arr_e' = do
        arr_e'' <- unheapAll arr_e'
        internalError ("doDynSel: array: " ++ ppReadable arr_e'')
  -- arr_e should only be an array or dyn-sel of an array,
  -- but we use evalStaticOp to avoid duplicating code
  evalStaticOp arr_e elem_ty handleDynSel


conAp' i (ICPrim _ PrimArrayDynUpdate) f
           as@(T elem_t: T sz_t: E arr_e: E idx_e: E val_e: as') = do
  -- don't force the arrayupdate does not force the elements of the array
  when (not (null as')) $
      internalError ("conAp' PrimArrayDynUpdate: " ++ ppReadable as')
  bldApUH' "DynUpd" f as

-- assuming any remaining primitives are non-strict
conAp' _ ic@(ICPrim { }) f as = do
  bldAp' "ICPrim" f as

-- tag each distinct foreign function call with its generated cookie
-- foreign function calls should be strict
conAp' i fc@(ICForeign { fcallNo = Nothing }) f as = do
  n' <- newFFCallNo
  let fc' = fc { fcallNo = Just (toInteger (n')) }
  bldApUH' "ICForeign" (ICon i fc') as

-- don't retag an already-tagged foreign call
conAp' _ fc@(ICForeign { fcallNo = Just _ }) f as = bldApUH' "ICForeign" f as

conAp' _ ac@(ICLazyArray {}) f as = do
  when doDebug $ traceM ("conAp' lazy array!")
  -- traceM ("ICLazyArray:" ++ show ac)
  -- traceM ("f: " ++ show f)
  -- traceM ("as: " ++ show as)
  bldAp' "ICLazyArray" f as

conAp' _ c e as = internalError ("conAp':\n" ++ show c ++ "\n" ++ ppReadable (mkAp e as))


-- This is like "walkNF" except that it doesn't require the expression
-- to be fully-evaluated to primitive types.  It is used to implement
-- impCondOf, which can be called on expressions of non-primitive type.
--
getBuriedPreds :: HExpr -> G HPred
getBuriedPreds r@(IRefT {}) = do
  --traceM("getBuriedPreds: following ref")
  (P p' e') <- unheap (pExpr r)
  p'' <- getBuriedPreds e'
  return (pConj p' p'')
getBuriedPreds (IAps (ICon _ (ICPrim _ PrimIf)) _ [cnd,thn,els]) = do
  --traceM("getBuriedPreds: pIf")
  pthn <- getBuriedPreds thn
  pels <- getBuriedPreds els
  pIf cnd pthn pels
getBuriedPreds (IAps (ICon i_case (ICPrim _ PrimCase))
                  [sz_idx, elem_ty]
                  (idx:dflt:ces)) = do
  --traceM("getBuriedPreds: case")
  -- XXX if the case arms are integer, then we can use pSel,
  -- XXX but in the general case we can only use pIf
  let foldFn (v, e) res =
          let c = iePrimEQ sz_idx idx v
          in  ieIf elem_ty c e res
  getBuriedPreds (foldr foldFn dflt (makePairs ces))
getBuriedPreds (IAps ic@(ICon _ (ICPrim _ PrimArrayDynSelect)) tys
                    [arr@(IRefT {}), idx]) = do
  --traceM("getBuriedPreds: arr-sel ref")
  (P p' arr') <- unheap (pExpr arr)
  p'' <- getBuriedPreds (IAps ic tys [arr', idx])
  return (pConj p' p'')
getBuriedPreds (IAps ic@(ICon _ (ICPrim _ PrimArrayDynSelect))
                  [elem_ty, ITNum idx_sz]
                  [(ICon _ (ICLazyArray _ arr u)), idx]) = do
  --traceM("getBuriedPreds: arr-sel")
  if (isJust u)
    then return pTrue
    else do
      let cells = Array.elems arr
          mapFn (ArrayCell ptr ref) = getBuriedPreds (IRefT elem_ty ptr ref)
      pidx <- getBuriedPreds idx
      pes <- mapM mapFn cells
      return (pConj pidx (pSel idx idx_sz pes))
getBuriedPreds (IAps ic@(ICon _ (ICPrim _ PrimArrayDynSelect)) tys args) = do
  internalError ("getBuriedPreds: " ++ ppReadable args)
-- should only be PrimWhenPred because it is already evaluated
getBuriedPreds (IAps (ICon _ (ICPrim _ PrimWhenPred)) _ [(ICon _ (ICPred _ p')), e']) = do
  --traceM("getBuriedPreds: when")
  p'' <- getBuriedPreds e'
  return (pConj p' p'')
getBuriedPreds (IAps a@(ICon _ (ICPrim _ PrimBAnd)) b [e1, e2]) = do
  --traceM("getBuriedPreds: AND")
  p1 <- getBuriedPreds e1
  p2 <- getBuriedPreds e2
  p_if <- pIf e1 p2 pTrue
  let p = p1 `pConj` p_if
  return p
getBuriedPreds (IAps a@(ICon _ (ICPrim _ PrimBOr)) b [e1, e2]) = do
  --traceM("getBuriedPreds: OR")
  p1 <- getBuriedPreds e1
  p2 <- getBuriedPreds e2
  p_if <- pIf e1 pTrue p2
  let p = p1 `pConj` p_if
  return p
-- the following are followed because they are strict,
-- and we want to unheap the references in their arguments
getBuriedPreds (IAps a@(ICon _ p@(ICPrim _ _)) b es) = do
  -- traceM("getBuriedPreds: prim")
  ps <- mapM getBuriedPreds es
  return (foldr1 pConj ps)
getBuriedPreds (IAps a@(ICon _ (ICForeign { })) b es) = do
  --traceM("getBuriedPreds: foreign")
  ps <- mapM getBuriedPreds es
  return (foldr1 pConj ps)
getBuriedPreds (IAps a@(ICon _ (ICSel { })) b (ICon _ (ICStateVar { }):es)) = do
  --traceM("getBuriedPreds: method")
  ps <- mapM getBuriedPreds es
  return (foldr pConj pTrue ps)
getBuriedPreds (IAps a@(ICon _ (ICSel { })) b (ICon _ (ICForeign { }):es)) = do
  --traceM("getBuriedPreds: AV foreign")
  ps <- mapM getBuriedPreds es
  return (foldr pConj pTrue ps)
-- ICSel AVValue/AVAction of ICSel of ICStateVar
-- (note that "e" can also be a ref that needs to be expanded)
getBuriedPreds (IAps ic@(ICon i_sel (ICSel { })) ts1 [e])
    | (i_sel == idAVValue_ || i_sel == idAVAction_) = do
  --traceM("getBuriedPreds: AV sel")
  getBuriedPreds e
getBuriedPreds (ICon _ (ICMethod _ _ eb)) = do
  -- traceM("getBuriedPreds: method")
  p <- getBuriedPreds eb
  return p
getBuriedPreds e@(ICon _ _) = do
  --traceM("getBuriedPreds: con: e = " ++ ppReadable e ++ show e)
  return pTrue
-- abstract types can still have complex structure:
-- functions, method calls, etc.
-- but the primitive piece should not add an implicit condition
getBuriedPreds e = do
  --traceM("getBuriedPreds: other: e = " ++ ppReadable e ++ show e)
  return pTrue

{-
-- Quick utility for printing the refs in an HPred or HExpr,
-- used for debugging
-- XXX Would be obsoleted by a PPrint version that follows heap refs

ppPConjRefs :: HPred -> G ()
ppPConjRefs (PConj ps) = mapM_ ppPTermRefs (S.toList ps)

ppPTermRefs :: PTerm HeapData -> G ()
ppPTermRefs (PAtom e) = ppExprRefs e
ppPTermRefs (PIf c t e) = do ppExprRefs c
                             _ <- ppPConjRefs t
                             ppPConjRefs e

ppExprRefs :: HExpr -> G ()
ppExprRefs (ILam _ _ e) = ppExprRefs e
ppExprRefs (IAps e _ es) = do _ <- ppExprRefs e
                              mapM_ ppExprRefs es
ppExprRefs (IVar _) = return ()
ppExprRefs (ILAM _ _ e) = ppExprRefs e
ppExprRefs (ICon _ _) = return ()
ppExprRefs r@(IRefT _ _ _) = do
  (P _ e) <- unheap (P pTrue r)
  traceM(ppString r ++ " = " ++ ppReadable e)
  ppExprRefs e
-}

-----------------------------------------------------------------------------

doArrayNew :: HExpr -> [Arg] -> G PExpr
doArrayNew f@(ICon cn (ICPrim {primOp = PrimArrayNew, iConType = conType })) [T t, E e1, E val] = do
     -- save val to prevent redundant evaluation
     val' <- toHeapInferName "array-new" val
     evalStaticOp e1 resultType (handleArrayNew val')
  where (_, resultType) = itGetArrows (itInst conType [t]) -- grab the result type
        handleArrayNew val' (ICon ci (ICInt { iVal = ln })) = do
          arr <- iMkArray t (ilValue ln) val'
          when doDebug $ traceM ("PrimArrayNew! " ++ show ci)
          return $ pExpr $ ICon ci (ICLazyArray resultType arr Nothing)
        handleArrayNew val' e1' =
          nfError "primArrayNew" $ mkAp f [T t, E e1', E val']

doArrayNew f as = internalError ("IExpand.doArrayNew : " ++ ppReadable f ++ ppReadable as)

doArrayLength :: HExpr -> [Arg] -> G PExpr
doArrayLength f as@[T elem_t, E arr_e] =
    evalStaticOp arr_e itInteger handleArrayLength
  where handleArrayLength (ICon ci (ICLazyArray {iArray = arr})) = do
          ln <- iArrayLength arr
          return $ pExpr $ ICon ci (ICInt { iConType = itInteger, iVal = ilDec ln })
        handleArrayLength (IAps (ICon _ (ICPrim _ PrimArrayDynUpdate))
                                ts [arr_e2, idx_e, val_e]) = do
          -- update does not change the array length, so recurse into arr_e2
          doArrayLength f [T elem_t, E arr_e2]
        handleArrayLength arr_e' =
          nfError "primArrayLength" $ mkAp f [T elem_t, E arr_e']

doArrayLength f as = internalError("IExpand.doArrayLength : " ++ ppReadable f ++ ppReadable as)

-- Perform static array selection
--
-- This used to call evalStaticOp to recurse into the leaves of both the index
-- and the array.  But, for now, the index will only ever be an ICInt, because
-- calls to PrimArraySelect are guarded with "isStaticIndex" (which uses
-- PrimIsStaticInteger and PrimAreStaticBits, which only return True for ICInt).
-- So the use of evalStaticOp was only for the evalUH call.
--
-- Eventually, we should merge PrimArraySelect and PrimArrayDynSelect into one
-- primitive, in which case we will want this code to recurse into the index.
-- We will have the choice of recursing into the index first or the array first.
-- It's unclear which is better, in situations like this:
--    select (c1 ? idx1 : idx2) (update idxU arr valU)
-- If we recurse into the index first, then we might be able to simplify the logic
-- for checking if the update value applies.  But is the hardware better?
-- And which way is better for reconstructing case-statements (in the index and
-- in the array)?  We'll need to experiment.
--
doArraySelect :: HExpr -> [Arg] -> G PExpr
doArraySelect f (T elem_t : E arr_e : E idx_e : as) = do
  (_, (P p idx_e')) <- evalUH idx_e
  case idx_e' of
    ICon idx_i idx_ic@(ICInt { iVal = IntLit { ilValue = index } }) -> do
        let handleArraySelect ic@(ICon _ (ICLazyArray { iArray = arr })) =
                if iArrayInRange arr index then do
                  (p, r) <- iArraySelect arr index
                  evalAp "array-select" (IRefT elem_t p r) as
                else
                  -- this is the same as the "paradox handling" in doOut
                  evalAp "array-select-paradox" (icUndet elem_t UNotUsed) as
            handleArraySelect (IAps (ICon _ (ICPrim _ PrimArrayDynUpdate))
                                    [_, ITNum upd_idx_sz]
                                    [upd_arr_e, upd_idx_e, upd_val_e]) = do
                -- Construct the result from expanding out PrimArrayDynUpdate:
                --    if (sel_idx == upd_idx) then upd_val else orig_arr[sel_idx]
                -- However, if the static selection index is greater than the max
                -- value of the update index, then we know it won't match, so
                -- just return the original value.
                (P p0 res0) <- evalStaticOp upd_arr_e elem_t handleArraySelect
                let upd_idx_t = aitBit (ITNum upd_idx_sz)
                    idx_bits_e = ICon idx_i (idx_ic { iConType = upd_idx_t })
                    eq_e = iePrimEQ (ITNum upd_idx_sz) upd_idx_e idx_bits_e
                    if_e = ieIf elem_t eq_e upd_val_e res0
                -- despite the name, this is actually 1 greater than the max
                let max_upd_idx = 2 ^ upd_idx_sz
                    res = if (max_upd_idx > index) then if_e else res0
                addPredG (pConj p0 p) $ evalAp "array-select-update" res as
            handleArraySelect arr_e' = do
                --traceM("Select: " ++ show arr_e')
                nfError "primArraySelect" $
                    mkAp f [T elem_t, E arr_e', E idx_e']
        addPredG p $ evalStaticOp arr_e elem_t handleArraySelect
    _ -> internalError ("IExpand.doArraySelect: index: " ++ ppReadable idx_e')

doArraySelect f as = internalError("IExpand.doArraySelect : " ++ ppReadable f ++ ppReadable as)

-- Perform static array update
--
-- See comments on doArraySelect.
--
doArrayUpdate :: HExpr -> [Arg] -> G PExpr
doArrayUpdate f@(ICon upd_i (ICPrim {iConType = opType}))
              as@[T elem_t, E arr_e, E idx_e, E val_e] = do
  (_, P idx_p idx_e') <- evalUH idx_e
  case idx_e' of
    ICon _ (ICInt { iVal = IntLit { ilValue = index } }) -> do
        -- heap val_e to prevent redundant evaluation
        val_e' <- toHeapInferName "array-upd-val" val_e
        -- this doesn't include "idx_p"; we add that to the result
        let handleArrayUpdate (ICon arr_i icarr@(ICLazyArray { iArray = arr })) =
                if iArrayInRange arr index then do
                  arr' <- iArrayUpdate arr index val_e'
                  return $ pExpr $
                      -- note that we mark the array as initialized
                      ICon arr_i (icarr { iArray = arr', uninit = Nothing })
                   -- paradoxical out-of-range update, just return the array
                else return $ pExpr $ ICon arr_i icarr
            handleArrayUpdate arr_e'@(IAps (ICon _ (ICPrim t PrimArrayDynUpdate)) ts _) = do
                -- XXX we should have PrimArrayUpdate evaluate away?
                return $ pExpr $
                    IAps (ICon upd_i (ICPrim t PrimArrayDynUpdate))
                        ts [arr_e', idx_e', val_e']
            handleArrayUpdate arr_e' = do
                --traceM("Update: " ++ show arr_e')
                nfError "primArrayUpdate" $
                    mkAp f [T elem_t, E arr_e', E idx_e', E val_e']
        let res_t = iGetType arr_e -- result type is (PrimArray t)
        addPredG idx_p $ evalStaticOp arr_e res_t handleArrayUpdate
    _ -> internalError ("IExpand.doArrayUpdate: index: " ++ ppReadable idx_e')

doArrayUpdate f as = internalError("IExpand.doArrayUpdate : " ++ ppReadable f ++ ppReadable as)

-- if without extra arguments
doIf :: HExpr -> [Arg] -> G PExpr
doIf f@(ICon _ (ICPrim _ PrimIf)) [T t, E cnd, E thn, E els] = do
    (ecnd, P p cnd') <- evalUH cnd
    when doDebug $ traceM ("if " ++ ppReadable (cnd, cnd'))
    --when doDebug $ traceM ("if2 " ++ show cnd')
    case cnd' of
      ICon _ (ICInt { iVal = IntLit { ilValue = 0 } }) -> addPredG p $ eval1 els
      ICon _ (ICInt { iVal = IntLit { ilValue = 1 } }) -> addPredG p $ eval1 thn
      _ ->
      -- The condition did not evaluate, but there is still a chance to proceed.
      -- If the then and else branch are "equal" the condition can be ignored.
      -- Should not be done via ITransform because of implicit condition handling
          if thn == els then
            eval1 thn
           else do -- evaluate to WHNF and try again
             (ethn, P pthn thn') <- evalUH thn
             if thn' == els then
              return (P pthn thn')
               else do
                (eels, P pels els') <- evalUH els
                -- additional equality tests have moved to improveIf
                when doTraceIf $ traceM("improveIf try: " ++ ppReadable(t,thn',els'))
                -- attempt to merge structure (constructor, array or tuple)
                -- return a flag about whether or not we were successful
                (e', b)  <- improveIf f t ecnd thn' els'
                when doTraceIf $ traceM("improveIf result: " ++ ppReadable (b, e'))
                case (b, pthn == pels) of
                  -- back out the change if a useful merge did not occur (for better "heaping")
                  (False, _) -> bldAp' "PrimIf" f [T t, E ecnd, E ethn, E eels]
                  -- if we merged and the implicit conditions match we can have a simple PExpr
                  (True, True) -> return (P pthn e')
                  -- if we merged, but the implicit conditions don't match we need to use pIf
                  (True, False) -> do
                      p_if <- pIf ecnd pthn pels
                      return (P p_if e')

doIf f as = internalError("IExpand.doIf : " ++ ppReadable f ++ ppReadable as)

-- improve the static elaboration of the output of an if
-- to prevent exponential growth with conditional assignments and updates
improveIf :: HExpr -> IType -> HExpr -> HExpr -> HExpr -> G (HExpr, Bool)
-- merge cells if the arrays have the same size (since our bounds are always 0 .. n - 1)
improveIf f t cnd (ICon i1 (ICLazyArray { iConType = ct1, iArray = arr1 }))
                  (ICon i2 (ICLazyArray { iConType = ct2, iArray = arr2 })) | Array.bounds arr1 == Array.bounds arr2 =
  do when doTraceIf $ traceM("improveIf array triggered" ++ show i1 ++ show i2)
     let elemType = case t of
                      ITAp _ te -> te -- type must be (PrimArray t)
                      _ -> internalError "IExpand.improveIf arrsz1 == arrsz2: elemType"
         refs1 = Array.elems arr1
         refs2 = Array.elems arr2
     refs' <- zipWithM (\ref1 ref2 -> if (ac_ptr ref1) == (ac_ptr ref2) then
                                       return ref1
                                      else do let e1 = IRefT elemType (ac_ptr ref1) (ac_ref ref1)
                                              let e2 = IRefT elemType (ac_ptr ref2) (ac_ref ref2)
                                              let cell' = IAps f [elemType] [cnd, e1, e2]
                                              IRefT _ p r <- toHeapConInferName "improve-if" cell'
                                              return (ArrayCell p r))
                       refs1 refs2
     -- XXX use i1 or i2?
     return ((ICon i1 (ICLazyArray { iConType = ct1, iArray = Array.listArray (Array.bounds arr1) refs', uninit = Nothing })), True)

-- XXX This can lead to a static array not evaluating away?
{-
-- XXX test if this ever gets used
improveIf f t cnd
    (IAps c1@(ICon _ (ICPrim _ PrimArrayDynSelect)) ts1@[_, sz] [e_arr1, e_idx1])
    (IAps c2@(ICon _ (ICPrim _ PrimArrayDynSelect)) ts2 [e_arr2, e_idx2])
    | (e_arr1 == e_arr2) &&
      -- make sure that the indices have the same type
      (ts1 == ts2)
    = do
  let idx_t = ITAp itBit sz
  (e_idx, _) <- improveIf f idx_t cnd e_idx1 e_idx2
  return (IAps c1 ts1 [e_arr1, e_idx], True)
-}

-- XXX This is not needed since we expand away PrimArrayDynUpdate
{-
-- XXX test if this ever gets used
improveIf f t cnd
    (IAps c1@(ICon _ (ICPrim _ PrimArrayDynUpdate)) ts1@[elem_t, _] [e_arr1, e_idx1, e_val1])
    (IAps c2@(ICon _ (ICPrim _ PrimArrayDynUpdate)) ts2 [e_arr2, e_idx2, e_val2])
    | (e_arr1 == e_arr2) &&
      (e_idx1 == e_idx2)
      -- no need to test the types
    = do
  (e_val, _) <- improveIf f elem_t cnd e_val1 e_val2
  return (IAps c1 ts1 [e_arr1, e_idx1, e_val], True)

-- XXX test if this ever gets used
improveIf f t cnd
    (IAps c1@(ICon _ (ICPrim _ PrimArrayDynUpdate)) ts1@[_, sz] [e_arr1, e_idx1, e_val1])
    (IAps c2@(ICon _ (ICPrim _ PrimArrayDynUpdate)) ts2 [e_arr2, e_idx2, e_val2])
    | (e_arr1 == e_arr2) &&
      (e_val1 == e_val2) &&
      -- make sure that the indices have the same type
      (ts1 == ts2)
    = do
  let idx_t = ITAp itBit sz
  (e_idx, _) <- improveIf f idx_t cnd e_idx1 e_idx2
  return (IAps c1 ts1 [e_arr1, e_idx, e_val1], True)
-}

-- push if improvement inside matching constructors
improveIf f t cnd (IAps (ICon i1 c1@(ICCon {conTagInfo = cti1})) ts1 es1)
                  (IAps (ICon i2 c2@(ICCon {conTagInfo = cti2})) ts2 es2) | conNo cti1 == conNo cti2
                                                           -- need to check that constructor numbers match
                                                           -- because that test is otherwise buried in i1 == i2
                                                           = do
  when doTraceIf $ traceM ("improveIf ICCon triggered" ++ show i1 ++ show i2)
  let realConType = itInst (iConType c1) ts1
      (argTypes, _) = itGetArrows realConType
  when (length argTypes /= length es1 || length argTypes /= length es2) $ internalError ("improveIf Con:" ++ ppReadable (argTypes, es1, es2))
  (es', bs) <- mapAndUnzipM (\(t, e1, e2) -> improveIf f t cnd e1 e2) (zip3 argTypes es1 es2)
  -- unambiguous improvement because the ICCon has propagated out
  return ((IAps (ICon i1 c1) ts1 es'), True)

-- push if improvement inside structs/tuples
improveIf f t cnd (IAps (ICon i1 c1@(ICTuple {})) ts1 es1)
                  (IAps (ICon i2 c2@(ICTuple {})) ts2 es2) -- tuple should match since types match
                                                             = do
  when doTraceIf $ traceM ("improveIf ICTuple triggered" ++ show i1 ++ show i2)
  let realConType = itInst (iConType c1) ts1
      (argTypes, _) = itGetArrows realConType
  when (length argTypes /= length es1 || length argTypes /= length es2) $ internalError ("improveIf Con:" ++ ppReadable (argTypes, es1, es2))
  (es', bs) <- mapAndUnzipM (\(t, e1, e2) -> improveIf f t cnd e1 e2) (zip3 argTypes es1 es2)
  -- unambiguous improvement since the ICTuple has propagated out
  return ((IAps (ICon i1 c1) ts1 es'), True)

-- push if improvement inside bit concatenations with matching boundaries
-- this is a post-pack version of the struct/tuple case above
improveIf f t cnd thn@(IAps concat@(ICon _ (ICPrim _ PrimConcat)) ts1@[ITNum sx, ITNum sy, _] [thn_x, thn_y])
                  els@(IAps        (ICon _ (ICPrim _ PrimConcat)) ts2                         [els_x, els_y])
  | ts1 == ts2 = do
  when doTraceIf $ traceM ("improveIf PrimConcat triggered " ++ ppReadable (cnd,thn,els))
  (x', _) <- improveIf f (itBitN sx) cnd thn_x els_x
  (y', _) <- improveIf f (itBitN sy) cnd thn_y els_y
  return (IAps concat ts1 [x', y'], True)

improveIf f t cnd thn@(IAps chr@(ICon _ (ICPrim _ PrimChr)) ts1 [chr_thn])
                  els@(IAps     (ICon _ (ICPrim _ PrimChr)) ts2 [chr_els]) = do
  when doTraceIf $ traceM ("improveIf PrimChr triggered " ++ show (cnd,thn,els))
  let chrArgType = iGetType chr_thn
  (e', _) <- improveIf f chrArgType cnd chr_thn chr_els
  return (IAps chr ts1 [e'], True)

-- Push if improvement inside constructors when one arm is undefined
-- and the type has only one constructor
--
-- Further down, a general improveIf rule optimizes 'if c e _' to just 'e'.
-- But that can cause poor code generation for if-else chains returning
-- the constructors of a union type, so an earlier improveIf rule catches
-- that situation (before the general rule can apply).
-- However, if there is only one constructor, we do want an optimization to apply,
-- so we put that here, prior to the blocking rule.
--
improveIf f t cnd thn@(IAps (ICon i1 c1@(ICCon {})) ts1 es1)
                  els@(ICon i2 (ICUndet { iuKind = u }))
  | numCon (conTagInfo c1) == 1
  = do
      when doTraceIf $ traceM ("improveIf ICCon/ICUndet triggered" ++ ppReadable (cnd,thn,els))
      let realConType = itInst (iConType c1) ts1
          (argTypes, _) = itGetArrows realConType
      when (length argTypes /= length es1) $ internalError ("improveIf Con/Undet:" ++ ppReadable (argTypes, es1))
      let mkUndet t = icUndetAt (getIdPosition i2) t u
      (es', bs) <- mapAndUnzipM (\(t, e1) -> improveIf f t cnd e1 (mkUndet t)) (zip argTypes es1)
      -- unambiguous improvement because the ICCon has propagated out
      return ((IAps (ICon i1 c1) ts1 es'), True)
improveIf f t cnd thn@(ICon i1 (ICUndet { iuKind = u }))
                  els@(IAps (ICon i2 c2@(ICCon {})) ts2 es2)
  | numCon (conTagInfo c2) == 1
  = do
      when doTraceIf $ traceM ("improveIf ICCon/ICUndet triggered" ++ ppReadable (cnd,thn,els))
      let realConType = itInst (iConType c2) ts2
          (argTypes, _) = itGetArrows realConType
      when (length argTypes /= length es2) $ internalError ("improveIf Con/Undet:" ++ ppReadable (argTypes, es2))
      let mkUndet t = icUndetAt (getIdPosition i1) t u
      (es', bs) <- mapAndUnzipM (\(t, e2) -> improveIf f t cnd (mkUndet t) e2) (zip argTypes es2)
      -- unambiguous improvement because the ICCon has propagated out
      return ((IAps (ICon i2 c2) ts2 es'), True)

-- Do not "optimize" constructors against undefined values because this can remove
-- the conditions required to optimize chains of ifs like these:
-- if (x == 0) 0 else if (x == 1) 1 else ... back to just x
-- These chains are commonly produced by derived Bits instances.
-- This covers ICCon and PrimChr because constructors of no arguments are turned into PrimChr.
improveIf f t cnd thn els
  | isUndet thn && blockUndet els || isUndet els && blockUndet thn = do
      when doTraceIf $ traceM("improveIf ICCon/ICUndet blocked: " ++ ppReadable (cnd, thn, els))
      return (mkAp f [T t, E cnd, E thn, E els], True)
  where isCon (IAps (ICon _ (ICCon {})) _ _)         = True
        isCon (IAps (ICon _ (ICPrim _ PrimChr)) _ _) = True
        isCon _                                      = False
        isUndet (ICon _ (ICUndet {})) = True
        isUndet _                     = False
        -- Exception: Allow undet simplification for two-constructor / Boolean-like types
        -- because they cannot have the != chains that are problematic for other types.
        -- This is a workaround for a small boolean optimization regression in
        -- bsc.evaluator/prims/impcondof with this change.
        isBoolLike (IAps (ICon _ (ICCon { conTagInfo = cti })) _ _)  = numCon cti == 2 &&
                                                                       tagSize cti == 1
        -- A one-bit PrimChr result is also Boolean-like
        isBoolLike (IAps (ICon _ (ICPrim _ PrimChr)) (ITNum n : _) _) = n == 1
        isBoolLike _ = False
        blockUndet e = isCon e && not (isBoolLike e)

improveIf f t cnd thn@(IAps ssp@(ICon _ (ICPrim _ PrimSetSelPosition)) ts1 [pos_thn, res_thn])
                  els@(IAps     (ICon _ (ICPrim _ PrimSetSelPosition)) ts2 [pos_els, res_els])
    | (pos_thn == pos_els) = do
  when doTraceIf $ traceM ("improveIf PrimSetSelPosition triggered " ++ show (cnd,thn,els))
  (res', improved) <- improveIf f t cnd res_thn res_els
  -- only push PrimIf inside PrimSetSelPosition if improvement can be done,
  -- otherwise, it's reversing the transformation that evalStaticOp does
  -- (of pushing PrimSetSelPosition inside PrimIf)
  return $
    if (improved)
    then -- we don't need to eval the prim on the improved result, because
         -- we know that it won't apply if it didn't apply to the arms
         (IAps ssp ts1 [pos_thn, res'], True)
    else (IAps f [t] [cnd, thn, els], False)

-- improve a subcomponent by checking for _ or equality
-- mildly duplicates some work in doIf (isUndet thn)
-- but the overlapping work for els has been moved here
improveIf f t cnd thn els | ICon _ (ICUndet { iuKind = u }) <- thn,
                            improveIfUndet u t = do
  let info = show thn ++ "\n" ++ ppReadable (cnd, thn, els)
  when doTraceIf $ traceM ("improveIf Undet (then) triggered " ++ info)
  return (els, True)
improveIf f t cnd thn els | ICon _ (ICUndet { iuKind = u }) <- els,
                            improveIfUndet u t = do
  let info = show els ++ "\n" ++ ppReadable (cnd, thn, els)
  when doTraceIf $ traceM ("improveIf Undet (els) triggered " ++ info)
  return (thn, True)

improveIf f t cnd thn els = do
  when doTrans $ traceM ("improveIf: iTransform fallthrough: " ++ ppReadable (cnd, thn, els))
  errh <- getErrHandle
  let (e', improved) = iTransExpr errh (mkAp f [T t, E cnd, E thn, E els])
  when (doTrans && improved) $ traceM ("improveIf: iTransform improved: " ++ ppReadable e')
  return $ if improved
           then (e', True) -- do we need to evaluate further?
           else (mkAp f [T t, E cnd, E thn, E els], False)
                -- XXX the above is just a convoluted way of writing this?
                -- (IAps f [t] [cnd, thn, els], False)

improveIfUndet :: UndefKind -> IType -> Bool
-- Always drop types that can survive downstream, but can't have don't cares
-- (Integer, String, Real, etc)
improveIfUndet _         t | isSimpleType t = True
-- Never remove a user-inserted don't care
improveIfUndet UDontCare _ = False
-- Removing undefined bits gets in the way of pack . unpack optimization
improveIfUndet _         t = not $ isBitType t

-- simplify evaluated dyn-sel expressions, not just to reduce the order of
-- growth of elaboration, but also to avoid triggering elaboration errors
-- in those trimmed paths
--
improveDynSel :: HExpr -> HExpr -> Integer ->
                 Id -> IType -> (Integer, Integer) -> [HExpr] -> G (HExpr, Bool)
improveDynSel ic idx_e idx_sz arr_i arr_ty arr_bounds elem_es =
  let
      elem_ty =
          case arr_ty of
            (ITAp c t) | (c == itPrimArray) -> t
            _ -> internalError ("improveDynSel: type: " ++ ppReadable arr_ty)
      max_idx = (2 ^ idx_sz) - 1
      -- only the reachable elements
      -- XXX can we assume that "doDynSel" will have already reduced the array?
      arms :: [(Integer, HExpr)]
      arms = zip [0..max_idx] elem_es
      (elems_head, elems_tail) =
          case (map snd arms) of
            (e:es) -> (e, es)
            _ -> internalError ("improveDynSel: head")
      all_eq = all (== elems_head) elems_tail
  in
    if all_eq
    then -- still need to check the bounds
         let sel_pos = getIExprPosition ic
             res_e = mkDynSelBoundsCheck sel_pos idx_sz arr_bounds
                         idx_e elem_ty elems_head
         in  return (res_e, True)
    else
      case elems_head of
        -- improveIf handles ICLazyArray, but we don't want to do that here
        -- ... ICLazyArray...
{-
        -- XXX don't pull things out of the sel/array if other code is
        -- XXX pushing them in! check which things get pushed;
        -- XXX maybe all we want to do is check when the arms are the same?
        (IAps (ICon i0 c0@(ICCon { conTagInfo = cti})) ts0 es0) ->
            -- check if all the arms have the same constructor
            -- (allowing for some to be ICUndet?)
            ... (n == conNo cti) ...
        (IAps (ICon i0 c0@(ICTuple {})) ts0 es0) ->
            -- check if they're all ICTuple (allowing for ICUndet?)
            -- (since they're the same type, they'll be the same tuple)
            ...
        (IAps chr_ic@(ICon _ (ICPrim _ PrimChr)) ts0 [chr_arg]) ->
            -- check if they're all PrimChr (allowing for ICUndet?)
            ... move the array into the Chr ...
            -- improveIf has specific arms for Chr and Undet
-}
        _ -> do
          let mkCell e = do
                IRefT _ ref_p ref_r <- toHeapWHNFConInferName "improveDynSel" e
                return (ArrayCell ref_p ref_r)
          cells <- mapM mkCell elem_es
          let arr' = Array.listArray arr_bounds cells
              arr_e' = ICon arr_i (ICLazyArray arr_ty arr' Nothing)
              e' = IAps ic [elem_ty, ITNum idx_sz] [arr_e', idx_e]
          return (e', False)

-- shared func for creating the code for an array selection bounds check
mkDynSelBoundsCheck :: Position -> Integer -> (Integer, Integer) ->
                       HExpr -> IType -> HExpr -> HExpr
mkDynSelBoundsCheck sel_pos idx_sz arr_bounds idx_e elem_ty elem_e =
  let sz_t = ITNum idx_sz
      max_idx = (2 ^ idx_sz) - 1
      last_elem_idx = snd arr_bounds
      range_e = let lit = iMkLitAt sel_pos (aitBit sz_t) last_elem_idx
                in  iePrimULE sz_t idx_e lit
      undet_e = icUndetAt sel_pos elem_ty UDontCare
  in  if (max_idx <= last_elem_idx)
      then elem_e
      else ieIf elem_ty range_e elem_e undet_e


-- start trying to short-circuit and
doAnd :: HExpr -> [Arg] -> G PExpr
doAnd f as@[E e1, E e2] = do
    (ee1, pe1@(P p e1')) <- evalUH e1
    case e1' of
      ICon _ (ICInt { iVal = IntLit { ilValue = 0 } }) -> return $ P p iFalse
      ICon _ (ICInt { iVal = IntLit { ilValue = 1 } }) -> addPredG p $ eval1 e2
      _ -> doAnd2 f [E ee1, E e2] pe1 -- try to progress on arg 2

doAnd f as = internalError("IExpand.doAnd : " ++ ppReadable f ++ ppReadable as)

-- try to force and's second argument to progress
doAnd2 :: HExpr -> [Arg] -> PExpr -> G PExpr
doAnd2 f as@[E e1, E e2] pe1@(P p1 ie1) = do
    (ee2, P p e2') <- evalUH e2
    case e2' of
      ICon _ (ICInt { iVal = IntLit { ilValue = 0 } }) -> return $ P p iFalse
      ICon _ (ICInt { iVal = IntLit { ilValue = 1 } }) -> return $ P (pConj p1 p) ie1 -- don't reevaluate
      _ -> bldAp' "PrimBAnd" f [E e1, E ee2] -- e1 and ee2 have the implicit conditions

doAnd2 f as pe = internalError("IExpand.doAnd2 : " ++ ppReadable f ++ ppReadable as ++ ppReadable pe)

-- try to short-circuit or
doOr :: HExpr -> [Arg] -> G PExpr
doOr f as@[E e1, E e2] = do
    (ee1, pe1@(P p e1')) <- evalUH e1
    case e1' of
      ICon _ (ICInt { iVal = IntLit { ilValue = 0 } }) -> addPredG p $ eval1 e2
      ICon _ (ICInt { iVal = IntLit { ilValue = 1 } }) -> return $ P p iTrue
      _ -> doOr2 f [E ee1, E e2] pe1 -- try to progress on arg 2
doOr f as = internalError("IExpand.doOr : " ++ ppReadable f ++ ppReadable as)

-- try to force or's second argument to progress
doOr2 :: HExpr -> [Arg] -> PExpr -> G PExpr
doOr2 f as@[E e1, E e2] pe1@(P p1 ie1) = do
    (ee2, P p e2') <- evalUH e2
    case e2' of
      ICon _ (ICInt { iVal = IntLit { ilValue = 0 } }) -> return $ P (pConj p1 p) ie1 -- don't reevaluate
      ICon _ (ICInt { iVal = IntLit { ilValue = 1 } }) -> return $ P p iTrue
      _ -> bldAp' "PrimBOr" f [E e1, E ee2] -- e1 and ee2 have the implicit conditions
doOr2 f as pe = internalError("IExpand.doOr : " ++ ppReadable f ++ ppReadable as ++ ppReadable pe)

-----------------------------------------------------------------------------

doIs :: HExpr -> [IType] -> ConTagInfo ->
        HExpr -> (HPred,  HExpr) -> G PExpr
doIs is tys cti ee (p, e) =
    case e of
        -- C? (C' e)  -->  True/False
        IAps (ICon _ (ICCon { conTagInfo = cti' })) _ [_] ->
            addPredG p $
            return $ pExpr $ iMkBool (conNo cti == conNo cti')

        -- C_n? (primChr e) --> e == conTag
        IAps (ICon _ (ICPrim _ PrimChr)) [sz,_] [e] ->
            addPredG p $
            eval1 (iePrimEQ sz e n_lit)
          where pos = getIExprPosition e
                n_lit = iMkLitAt pos (aitBit sz) (conTag cti)

        -- C_n? _  -->  False
        ICon _ (ICUndet { }) -> addPredG p $ return $ pExpr iFalse

        -- v | C | .s
        _ | isCanon e -> bldAp' "doIs" is (map T tys ++ [E ee])

        -- otherwise fail
        _ -> internalError ("doIs: " ++ ppReadable (is, e))

doOut :: HExpr -> Id -> [IType] -> IType -> ConTagInfo -> [Arg] ->
         HExpr -> (HPred, HExpr) -> G PExpr
doOut out c tys ty cti as ee (p, e) =
    case e of
        -- outC (C e)  -->  e / _   (not error, because it's "convenient" -- L)
        IAps (ICon _ (ICCon { conTagInfo = cti' })) _ [e'] ->
            if conNo cti == conNo cti'
            then addPredG p $ evalAp "outC C" e' as
            else addPredG p $
                 evalAp "out-1" (icUndet ty UNotUsed) as

        -- outC (primChr e)  -->  _
        IAps (ICon _ (ICPrim _ PrimChr)) _ [_] ->
            addPredG p $ evalAp "out-2" (icUndet ty UNotUsed) as

        -- XXX evalStaticOp can't do this for us because of "as"
        -- outC _  -->  _
        ICon u (ICUndet { iuKind = k }) -> do
          let kind_integer = undefKindToInteger k
          addPredG p $ doBuildUndefined ty (getPosition u) kind_integer as

        -- v | C | .s
        _ | isCanon e && null as ->
                bldAp' "Out-3" out (map T tys ++ [E ee])

        -- otherwise fail
        _ -> internalError ("doOut: " ++ ppReadable (out, e, as))

doSel :: HExpr -> Id -> [IType] -> IType -> Integer -> [Arg] ->
         HExpr -> (HPred, HExpr) -> G PExpr
doSel sel s tys ty n as ee (p, e) =
    case e of
        -- (e1,...en).k  -->  ek
        IAps (ICon id (ICTuple ictup_ty _)) _ es -> do
            let tupleError id = internalError $ "indexing `" ++ show id ++ "' out of bounds; do you need to recompile dependencies?"
                index xs i id = if length xs > i then xs!!i else tupleError id
            let field_e = index es (fromInteger n) id
                dflt_res = addPredG p $ evalAp "sel k" field_e as
            -- if method conditions are not being preserved,
            -- just return the default result
            flags <- getFlags
            if (not (methodConditions flags))
              then dflt_res
              else do
                -- see if the selector has any positions that need preserving
                let inlined_poss = fromMaybe [] (getIdInlinedPositions s)
                -- see if the selector introduces a new position
                -- (only true for interface selection)
                let is_ifc =
                        let (_, con_ty) = itGetArrows (dropForAll ictup_ty)
                        in  case (leftmost con_ty) of
                              (ITCon _ _ (TIstruct (SInterface _) _))
                                -> True
                              _ -> False
                    sel_pos = if is_ifc then [getPosition s] else []
                -- the total set of positions
                let poss0 = sel_pos ++ inlined_poss
                    -- for efficiency, only do the work if there are actual
                    -- useful positions
                    keepFn p = (p /= noPosition) && (isUsefulPosition p)
                    poss = filter keepFn poss0
                if (null poss)
                  then dflt_res
                  else do
                    -- insert "primSetSelPosition" to record the position
                    let icon = icPrimSetSelPosition
                        poss_e = iMkPositions poss
                        args = (T ty : E poss_e : E field_e : as)
                    --traceM("doSel IFC: " ++ ppReadable s)
                    addPredG p $ evalAp "sel k ifc" icon args

        -- XXX evalStaticOp can't do this for us because of "as"
        -- _.s  -->  _
        ICon u (ICUndet { iuKind = k })  -> do
             let kind_integer = undefKindToInteger k
             addPredG p $ doBuildUndefined ty (getPosition u) kind_integer as

        -- select clocks out of state variables
        ICon id (ICStateVar {iVar = v}) | ty == itClock -> do
          let c = getNamedClock s v
          return (P p (icClock (mkUSId id s) c))

        -- select resets out of state variables
        ICon id (ICStateVar {iVar = v}) | ty == itReset -> do
          let r = getNamedReset s v
          return (P p (icReset (mkUSId id s) r))

        -- select inouts out of state variables
        e@(ICon id (ICStateVar {iVar = v})) | isitInout_ ty -> do
          let hclk = getIfcInoutClock s v
              hrst = getIfcInoutReset s v
              sz = getInout_Size ty
              wire = (IAps sel tys [e])
              inout = makeInout hclk hrst wire
          return (P p (icInout (mkUSId id s) sz inout))

        -- v | C_av.avAction_  || C_av.avValue_ ->
        -- AV_ selection must be a saturated application, no stray arguments
        _ | s == idAVValue_ && isCanonAV_ e && null as ->
            case e of
              -- drop arguments to value side of ActionValue method (see AMethValue)
              -- and fixup selector type (instantiating and dropping missing types)
              IAps csel@(ICon ic sel2@(ICSel { })) tys2 args@(sv@(ICon _ (ICStateVar { })):_) -> do
                let resType = dropArrows (length args) (itInst (iConType sel2) tys2)
                let newSelTy = (iGetType sv) `itFun` resType
                let sel2' = sel2 { iConType = newSelTy }
                let e'' = (IAps (ICon ic sel2') [] [sv])
                addPredG p $
                    bldApUH' "Sel AVValue_ 1" sel (map T tys ++ [E e''])
              _ -> addPredG p $
                       bldApUH' "Sel AVValue_ 2" sel (map T tys ++ [E e])
        -- action side of ActionValue method calls requires no fixup
        _ | s == idAVAction_ && isCanonAV_ e && null as ->
            addPredG p $ bldApUH' "Sel AVAction_" sel (map T tys ++ [E e])

        -- v | C | .s
        -- canonical applications are strict (e.g. method call applications)
        _ | isCanon e -> bldApUH' "Sel" sel (map T tys ++ (E ee : as))

        -- otherwise fail
        _ -> internalError ("doSel: " ++ ppReadable (sel, e, as))

isCanon :: HExpr -> Bool
isCanon (IVar _) = True
isCanon (ICon _ (ICStateVar { })) = True
isCanon (ICon _ (ICMethArg { })) = True
isCanon (ICon _ (ICModPort { })) = True
isCanon (ICon _ (ICModParam { })) = True
--isCanon (ICon _ (ICForeign { })) = True
isCanon (ICon _ (ICClock { })) = True
--isCanon (IAps (ICon _ (ICPrim _ PrimBlock)) _ _) = True                -- XXX is this the best way?
isCanon (IAps (ICon _ (ICSel { })) _ [_]) = True
isCanon (IAps (ICon _ (ICOut { })) _ [_]) = True
-- AV of foreign function application is canon
--isCanon (IAps (ICon _ (ICForeign { })) _ _) = True
isCanon (IRefT _ _ _) = True
isCanon _ = False

-- is the selected expression canonical for AV_ selection
isCanonAV_ :: HExpr -> Bool
isCanonAV_ (IAps (ICon _ (ICSel { })) _ ((ICon _ (ICStateVar { })):_)) = True
isCanonAV_ (ICon _ (ICForeign { })) = True
isCanonAV_ (IAps (ICon _ (ICForeign { })) _ _) = True
isCanonAV_  _ = False

dropT :: [Arg] -> [Arg]
dropT (T _ : as) = dropT as
dropT as = as

takeT :: [Arg] -> [IType]
takeT (T t : as) = t : takeT as
takeT _ = []

firstE :: String -> [Arg] -> HExpr
firstE err ((E e):_)  = e
firstE err ((T t):as) = firstE err as
firstE err []         = internalError err

--isUndet (ICon _ (ICUndet { iuKind = UNotUsed })) = True
--isUndet (ICon _ (ICUndet {  })) = True
--isUndet _ = False

isIntLit :: Arg -> Bool
isIntLit (E (ICon _ (ICInt { }))) = True
isIntLit (T (ITNum _)) = True
isIntLit _ = False

evalCExpr :: String -> CExpr -> CType -> [Arg] -> G PExpr
evalCExpr tag ce ct as = do
  --traceM("evalCExpr " ++ tag ++ "; ce: " ++ show ce ++ "; ct: " ++ show ct ++ "; as: " ++ show as)
  flags <- getFlags
  r <- getSymTab
  let err_tag = "evalCExpr " ++ tag
  -- built-in typeclass reflection only uses coherent typeclasses
  -- XXX there may be a corner case if we depend on user code that requires
  -- XXX incoherent matching
  case (fst $ TM.runTI flags False r (topExpr ct ce)) of
    Left errs -> internalError (err_tag ++ " errors: " ++ ppReadable errs)
    Right (ps, ce') -> do
      when (not (null ps)) $ internalError (err_tag ++ " unreduced: " ++ ppReadable ps)
      env <- getDefEnv
      errh <- getErrHandle
      flags <- getFlags
      let ie = iConvExpr errh flags r env ce'
      --traceM(err_tag ++ "; ce': " ++ ppReadable ce')
      --traceM(err_tag ++ "; ie: " ++ ppReadable ie)
      evalAp tag ie as

doBuildUndefined :: IType -> Position -> Integer -> [Arg] -> G PExpr
doBuildUndefined t pos i as = do
  -- safe because all polymorphism is resolved if an actual value is demanded
  let ct = iToCT t
  let ce = CApply (CVar idMakeUndef) [posLiteral pos, numLiteralAt pos i]
  evalCExpr "PrimBuildUndefined" ce ct as


-----------------------------------------------------------------------------

doSetSelPosition :: HExpr -> IType -> [Position] ->
                    HExpr -> (HPred, HExpr) -> G PExpr
-- record the positions on the sel
doSetSelPosition _ _ poss _ (p, (IAps (ICon i_sel s@(ICSel { })) ts es)) = do
  let i_sel' = addIdInlinedPositions i_sel poss
      e' = (IAps (ICon i_sel' s) ts es)
  --traceM("Setting sel position: " ++ ppReadable (i_sel, poss))
  return $ P p e'
doSetSelPosition _ _ poss _ (p, (ICon i_sel s@(ICSel { }))) = do
  let i_sel' = addIdInlinedPositions i_sel poss
      e' = (ICon i_sel' s)
  --traceM("Setting sel position (no args): " ++ ppReadable (i_sel, poss))
  return $ P p e'
-- combine positions
doSetSelPosition icon ty poss1 _
    (p, (IAps (ICon _ (ICPrim _ PrimSetSelPosition)) _ [e_pos, e_res])) =
  case e_pos of
    (ICon _ (ICPosition { iPosition = poss2 })) -> do
        let -- put the outer positions last
            poss = poss2 ++ poss1
            e' = IAps icon [ty] [iMkPositions poss, e_res]
        --traceM("Merging positions: " ++ ppReadable (poss1, poss2))
        return $ P p e'
    _ -> internalError ("handleSetSelPosition: ICPosition: " ++
                        ppReadable e_pos)
-- For any other expression:
-- We either need to (A) drop the position, (B) walk the sub-exprs to
-- find ICSels and insert the position there, or (C) leave the prim here
-- for now and return to it later when the expr is evaluated or applied.
-- We choose to leave the prim here (C).
--
-- However, in some cases there will not be an ICSel in the expr.
-- Rather than have other places (like evalClock) expect SetSelPosition,
-- we can remove SetSelPosition here, when we discover that there is no
-- selector in the expression.  It also improves elaboration to drop it.
-- We make this decision based on the type.
--
doSetSelPosition icon ty poss ee (p, e) = do
  let
      -- if we think it might contain a primitive action method call,
      -- then preserve the application of primSetSelPosition
      dflt_res = return $ P p $ IAps icon [ty] [iMkPositions poss, e]
      -- if it is unapplied, we can still check the final applied type
      rt = snd (itGetArrows (dropForAll ty))
  case (leftmost rt) of
    -- TIabstract is used for BSC's primitive types (Module, Integer, etc),
    -- and we know that the only primitive types of concern here are Action
    -- (because we're only collecting info about Action methods)
    (ITCon i _ TIabstract) | (i /= idActionValue) &&
                             (i /= idActionValue_)
                             -- XXX && (i /= idPrimAction)
      -> do -- non-Action abstract types can be ignored
            -- (instead of returning the unheaped expr, return the original,
            -- to avoid unnecessary unheaping)
            --traceM("ignoring prim: " ++ ppReadable (i, ee, e))
            return $ P pTrue ee
    -- struct, union, or Action
    _ -> do -- any other type might contain Action subfields
            --traceM("maintaining prim: " ++ ppReadable e)
            dflt_res

-----------------------------------------------------------------------------

-- After the evaluator has been run, this is used to determine which heap
-- references are being used in the result (collPtrs collects the pointers)
-- and to inline the defs in place of the heap pointers (with hToDef).

class HeapToDef a where
    collPtrs :: a -> IM.IntMap HeapCell -> IM.IntMap HeapCell
    hToDef :: IM.IntMap HExpr -> a -> a

    hToDef _ x = x

instance HeapToDef a => HeapToDef [a] where
    collPtrs [] = id
    collPtrs (x:xs) = collPtrs xs . collPtrs x
    hToDef m xs = map (hToDef m) xs

instance (HeapToDef a, HeapToDef b) => HeapToDef (a, b) where
    collPtrs (a, b) = collPtrs b . collPtrs a
    hToDef m (a, b) = (hToDef m a, hToDef m b)

instance (HeapToDef a, HeapToDef b, HeapToDef c) => HeapToDef (a, b, c) where
    collPtrs (a, b, c) = collPtrs c . collPtrs b . collPtrs a
    hToDef m (a, b, c) = (hToDef m a, hToDef m b, hToDef m c)

instance (HeapToDef a, HeapToDef b, HeapToDef c, HeapToDef d) => HeapToDef (a, b, c, d) where
    collPtrs (a, b, c, d) = collPtrs d . collPtrs c . collPtrs b . collPtrs a
    hToDef m (a, b, c, d) = (hToDef m a, hToDef m b, hToDef m c, hToDef m d)

instance HeapToDef HEFace where
    collPtrs (IEFace i x e rs wp fi)
        = collPtrs fi .
          collPtrs wp .
          collPtrs rs .
          collPtrs e .
          collPtrs x .
          collPtrs i
    hToDef m (IEFace i x e rs wp fi)
        = (IEFace (hToDef m i) (hToDef m x) (hToDef m e)
                  (hToDef m rs) (hToDef m wp) (hToDef m fi))

instance HeapToDef VFieldInfo where
    collPtrs i = id

instance HeapToDef Id where
    collPtrs i = id

instance HeapToDef IType where
    collPtrs t = id

instance HeapToDef WireProps where
    collPtrs t = id

instance (HeapToDef a) => HeapToDef (Maybe a) where
    collPtrs Nothing = id
    collPtrs (Just x) = collPtrs x
    hToDef m x = fmap (hToDef m) x

instance HeapToDef HDef where
    collPtrs (IDef i t e _) = collPtrs e
    hToDef m def = iDefMap (hToDef m) def

instance HeapToDef HExpr where
    collPtrs (IAps f ts es) m = collPtrs (f:es) m
--    collPtrs (ICon _ (ICStateVar { iVar = iv })) m = collPtrs iv m
    collPtrs (ICon _ (ICLazyArray _ arr _)) m =
        let elem_ty = (undefined :: IType)
            mkRef (ArrayCell p r) = IRefT elem_ty p r
            refs = map mkRef (Array.elems arr)
        in  collPtrs refs m
    collPtrs (ICon _ _) m = m
    collPtrs (IRefT _ p r) m =
        if p `IM.member` m then
            m
        else
            let c = unsafeDerefHeap r in
              case c of
                HNF { hc_pexpr = P _ e } -> collPtrs e (IM.insert p c m)
                HWHNF { hc_pexpr = P _ e } ->
--                traces ("collPtrs: " ++ ppReadable (p, e))
                  collPtrs e (IM.insert p c m)
                e -> internalError ("collPtrs: " ++ ppReadable e)
    collPtrs e m = internalError ("collPtrs: " ++ ppReadable e)

    hToDef m (IAps f ts es) = IAps f ts (hToDef m es)
    hToDef m (ICon i ic@(ICStateVar { })) = ICon i (ic { iVar = hToDef m (iVar ic) })
    hToDef m (ICon i (ICLazyArray arr_ty arr u)) =
        case u of
          Nothing ->
              let elem_ty = case arr_ty of
                              (ITAp c t) | (c == itPrimArray) -> t
                              _ -> internalError ("hToDef: array type")
                  mkRef (ArrayCell p r) = IRefT elem_ty p r
                  refs = map mkRef (Array.elems arr)
                  -- use library code to make the primitive, but preserve the Id
                  ic = case icPrimBuildArray (length refs) of
                         (ICon _ ci) -> ICon i ci
                         _ -> internalError ("hToDef: icPrimBuildArray")
                  ts = [elem_ty]
                  es = map (hToDef m) refs
              in (IAps ic ts es)
          _ -> internalError ("hToDef: uninitialized array")
    hToDef m r@(IRefT _ p _) =
        let value = case IM.lookup p m of
                    Just e -> (mapIExprPosition True (r, e))
                    Nothing -> internalError ("hToDef IRefT " ++ show p)
        in value
    hToDef m e = e

instance HeapToDef HStateVar where
    collPtrs    (IStateVar { isv_iargs = es }) = collPtrs es
    hToDef m sv@(IStateVar { isv_iargs = es }) = sv { isv_iargs = hToDef m es }

instance HeapToDef HRules where
    collPtrs (IRules sps rs) = collPtrs rs
    hToDef m (IRules sps rs) = IRules sps (hToDef m rs)

instance HeapToDef HRule where
    collPtrs r = collPtrs (irule_body r) . collPtrs (irule_pred r)

    hToDef m r = r { irule_pred = hToDef m $ irule_pred r ,
                     irule_body = hToDef m $ irule_body r }

-----------------------------------------------------------------------------

pExpr :: HExpr -> PExpr
pExpr e = P pTrue e

addPredG :: HPred -> G PExpr -> G PExpr
addPredG p m | p == pTrue = m
             | otherwise  = do (P p' e) <- m
                               return (P (pConj p p') e)

-----------------------------------------------------------------------------

{-
bIf :: IExpr -> IExpr -> IExpr -> IExpr
--ieIf ty (IAps (ICon _ (ICPrim _ PrimBNot)) _ [c]) t e = ieIf ty c e t
bIf c t e | isTrue c  = t
bIf c t e | isFalse c = e
bIf c t e | t == e    = t
bIf c t e | isTrue t  = ieOr c e
bIf c t e             = IAps icIf [itBit1] [c, t, e]
-}

eAssertion :: Id -> RulePragma -> [Char] -> G ()
eAssertion rId a str =
    let pos = getPosition rId
        reason = if (null str)
                 then Nothing
                 else Just (text str)
    in deferErrors [(pos, ERuleAssertion (pfpString rId) (getRulePragmaName a) reason)]

--ieIfu ty c t e = if isUndet t then e else if isUndet e then t else ieIfx ty c t e

isCon :: HExpr -> Bool
isCon (ICon _ _) = True
isCon _ = False

-- XXX keep track of lambda vars
{-
getStateVars :: ClockE -> [Id] -> [Id] -> [HExpr] -> G [Id]
getStateVars clk lvs vs [] = return []
getStateVars clk lvs vs (ILam i _ e : xs) = getStateVars clk (i:lvs) vs (e : xs)
getStateVars clk lvs vs (IAps e _ es : xs) = getStateVars clk lvs vs (e : es ++ xs)
getStateVars clk lvs vs (IVar i : xs) = do is <- getStateVars clk lvs vs xs
                                           if (i `elem` lvs) then
                                             return is
                                            else return (i:is)
getStateVars clk lvs vs (ILAM _ _ e : xs) = getStateVars clk lvs vs (e : xs)
getStateVars clk lvs vs (ICon i (ICDef _ e) : xs) = if i `elem` vs then
                                                      getStateVars clk lvs vs xs
                                                     else getStateVars clk lvs (i:vs) (e : xs)
getStateVars clk lvs vs (ICon i (ICStateVar _ (IStateVar _ _ _ vi es _ _ _ sl)) : xs) =
        do
           is <- getStateVars clk lvs vs (es' ++ xs)
           --trace (ppReadable (clks, clk)) $
           (if all (clk ==) clks then (return is) else (return (i:is)))
  where clks = [ e | (ClockArg i, e) <- ies ]
        isCR (ClockArg i) = True
        isCR (Port vn _ _) = vn `elem` vRst vi
        isCR _ = False
        ies = zip (vArgs vi) es
        es' = [ e | (a, e) <- zip (vArgs vi) es, not (isCR a) ]
getStateVars clk lvs vs (ICon i (ICModPort t) : xs) =
    do is <- getStateVars clk lvs vs xs
       return (i:is)
getStateVars clk lvs vs (ICon i (ICModParam t) : xs) =
    do is <- getStateVars clk lvs vs xs
       return (i:is)
getStateVars clk lvs vs (ICon _ (ICValue _ e) : xs) = getStateVars clk lvs vs (e : xs)
getStateVars clk lvs vs (ICon i (ICIFace { }) : xs) = do is <- getStateVars clk lvs vs xs
                                                         return (i:is)
getStateVars clk lvs vs (ICon _ _ : xs) = getStateVars clk lvs vs xs
getStateVars clk lvs vs (x@(IRefT _ _ _) : xs) = do uhx <- unheapU x
                                                  getStateVars clk lvs vs (uhx : xs)
-}

--------------------------------------------------------------------------

-- Primitive Arrays (Lazy)

iMkArray :: IType -> Integer -> HExpr -> G (ILazyArray HeapData)
iMkArray t ln val =
 do
   let n = ln - 1 :: Integer
   let ns = [0..n] :: [Integer]
   cell <- mkArrayCell val
   let zips = zip ns (replicate (fromInteger ln) cell)
   let arr = Array.array (0, n) zips
   when doDebug $ traceM ("iMkStArray: length " ++ (show ln) ++ " of type " ++ (ppReadable t))
   -- traceM ("goodarray: " ++ (show arr))
   return arr

iArrayLength :: ILazyArray HeapData -> G (Integer)
iArrayLength arr =
 do
   let (_, max) = Array.bounds arr
   when doDebug $ traceM ("iArrayLength: " ++ (show (max + 1)))
   return (max + 1)

iArraySelect :: ILazyArray HeapData -> Integer -> G (HeapPointer, HeapData)
iArraySelect arr ix =
 do
   let (max, min) = Array.bounds arr
   when doDebug $ traceM ("iArraySelect: " ++ (show ix) ++ " from array bounds " ++ (show (max, min)))
   let ptr = arr Array.! ix
   return (ac_ptr ptr, ac_ref ptr)

iArrayUpdate :: ILazyArray HeapData -> Integer -> HExpr -> G (ILazyArray HeapData)
iArrayUpdate arr ix pv =
 do
   -- traceM ("iArrayUpdate: " ++ (show ix) ++ " from array bounds " ++ (show (max, min)))
   cell <- mkArrayCell pv
   return (arr Array.// [(ix, cell)])

iArrayInRange :: ILazyArray HeapData -> Integer -> Bool
iArrayInRange arr = Array.inRange (Array.bounds arr)

mkArrayCell :: HExpr -> G (ArrayCell HeapData)
mkArrayCell e = do
   let hcell = HUnev e Nothing
   (p, r) <- addHeapCell "mk-array-cell" hcell
   return (ArrayCell p r)

-- ===============

reportNonSynthTypeInMethod :: Id -> Id -> IExpr a -> EMsg
reportNonSynthTypeInMethod modId methId methExpr =
    let modPos = getPosition modId
        -- drop the trailing "_" (from the wrapper name)
        -- and don't display the package qualifier
        modName = init (getIdBaseString modId)
        mkEMsg v =
            let str = "The interface method " ++ quote (pfpString methId) ++
                      " uses type " ++ quote (pfpString v) ++
                      " which is not in the Bits class."
            in  (modPos, EBadIfcType modName str)
    in  case (getNonSynthTypes methExpr) of
            [] -> -- this shouldn't happen
                  (modPos, EPolyField)
            (v:_) -> -- XXX report all the bad types?
                     -- XXX (but we're only reporting for one method
                     -- XXX anyway, not for all methods)
                     mkEMsg v


reportNonSynthTypeInModuleArg :: Id -> IExpr a -> EMsg
reportNonSynthTypeInModuleArg modId modExpr =
    let modPos = getPosition modId
        -- drop the trailing "_" (from the wrapper name)
        -- and don't display the package qualifier
        modName = init (getIdBaseString modId)
        mkEMsg v =
            let str = "A parameter of the module uses the type " ++
                      quote (pfpString v) ++
                      " which is not in the Bits class."
            in  (modPos, EBadIfcType modName str)
    in  case (getNonSynthTypes modExpr) of
            [] -> internalError
                    ("IExpand: unexplained module with type parameter: " ++
                     ppReadable modId)
            (v:_) -> -- XXX report all the bad types?
                     -- XXX (but we're only reporting for one method
                     -- XXX anyway, not for all methods)
                     mkEMsg v


getNonSynthTypes :: IExpr a -> [IType]
getNonSynthTypes expr =
    let
        -- we only want to catch types which are fully known (no variables)
        isAllTCon (ITCon {}) = True
        isAllTCon (ITNum {}) = True
        isAllTCon (ITAp t1 t2) = isAllTCon t1 && isAllTCon t2
        isAllTCon _ = False

        -- the ILAM should be the first things
        getTyVars ts (ILAM t _ e) = getTyVars (t:ts) e
        getTyVars ts e = (ts,e)

        -- the ILam should be next
        getVars vts (ILam _
                          (ITAp (ITAp (ITCon c _ _)
                                      v)
                                (ITVar t))
                          eb)
            | (c == idBits) && (isAllTCon v)
            = getVars ((t,v):vts) eb
        getVars vts (ILam _ _ eb) = getVars vts eb
        getVars vts _ = vts

        -- for each tyvar, look up any matching Bits type
        (ts, expr') = getTyVars [] expr
        vts = getVars [] expr'
    in
        mapMaybe (`lookup` vts) ts

-- ===============
