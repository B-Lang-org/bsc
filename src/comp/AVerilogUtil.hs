{-# LANGUAGE PatternGuards #-}
{-# OPTIONS_GHC -fwarn-name-shadowing -fwarn-missing-signatures -Werror #-}


module AVerilogUtil (
                     -- basic conversion functions
                     vId,
                     vExpr,
                     vMethId,
                     vNameToTask,

                     -- less basic (might belong in AVerilog?)
                     vDefMpd,

                     -- higher level conversion functions
                     -- XXX these might belong in AVerilog?
                     vState, InstInfo, wiredInstance,
                     vForeignBlock, vForeignCall,

                     -- separate decls and defs
                     -- (could go in AVerilog, but needed by vForeignBlock
                     expVVDWire,

                     -- Id routines
                     suff, pref,

                     -- size routine
                     vSize,
                     isNotZeroSized,
                     flagsToVco,
                     VConvtOpts(..)
                    ) where

import Data.List(nub, partition, genericLength, union, intersect, (\\),
                 uncons)
import Data.Maybe

import FStringCompat(FString, getFString)
import ErrorUtil
import Flags(Flags, readableMux, unSpecTo, v95, systemVerilogTasks, useDPI)
import PPrint
import IntLit
import Id
import PreIds( idInout_, idSVA )
import Position( Position )

import VModInfo(vArgs, vName, vFields, VName(..), VeriPortProp(..),
                getIfcIdPosition, VArgInfo(..), VFieldInfo(..))
import Prim
import ASyntax
import ASyntaxUtil
import Verilog
import VPrims(verilogInstancePrefix, viWidth)
import BackendNamingConventions(createVerilogNameMapForAVInst,
                                xLateFStringUsingFStringMap)
import ForeignFunctions(ForeignFunction(..), ForeignFuncMap,
                        isPoly, isWide, isMappedAVId)

import Util
import IntegerUtil

import qualified Data.Map as M
import qualified Data.Set as S
import GraphUtil(reverseMap, extractOneCycle_map)
import SCC(tsort)

--import Debug.Trace
--import Util(traces)


-- Define a structure which controls Verilog conversions
data VConvtOpts = VConvtOpts {
                              vco_unspec      :: String,
                              vco_v95         :: Bool,
                              vco_v95_tasks   :: [String],
                              vco_readableMux :: Bool,
                              vco_sv_tasks    :: Bool,
                              vco_use_dpi     :: Bool
                              }


flagsToVco :: Flags -> VConvtOpts
flagsToVco flags = VConvtOpts {
                               vco_unspec = unSpecTo flags,
                               vco_v95    = v95 flags,
                               vco_v95_tasks = ["$signed", "$unsigned"],
                               vco_readableMux = readableMux flags,
                               vco_sv_tasks = systemVerilogTasks flags,
                               vco_use_dpi = useDPI flags
                              }

-- This has been abolished from the compiler everywhere but the Verilog backend
dummy_string_size :: Integer
dummy_string_size = 666


-- ==============================
-- separate (EXPand/EXPlode) the declaration and its definition

expVVDWire :: [VMItem] -> ([VMItem], [VMItem])
expVVDWire defs =
  let explode (VMDecl (VVDWire r v@(VVar i) e)) =
                   ([VMDecl (VVDecl VDWire r [v])],
                    [VMAssign (VLId i) e])
      explode vm@(VMDecl _) = ([vm], [])
      explode vm = ([], [vm])

      (decls, others) = unzip (map explode defs)
  in  (concat decls, concat others)


-- ==============================
-- convert foreign functions

-- Returns a faked return type (always 1 bit) for foreign functions with
-- output types that have be provided as an argument instead of returned
-- (e.g. polymorphic or, if using DPI, also wide).  For anything else,
-- returns Nothing.
isAForeignCallWithRetAsArg :: VConvtOpts -> ForeignFuncMap -> AForeignCall -> Maybe AType
isAForeignCallWithRetAsArg vco ffmap fc@(AForeignCall { afc_writes = [lv] }) =
  let name = getIdString (afc_name fc)
  in  case M.lookup name ffmap of
      (Just ff) -> if (isPoly (ff_ret ff)) || ((vco_use_dpi vco) && isWide (ff_ret ff))
                   then Just aTBool else Nothing
      Nothing -> Nothing
isAForeignCallWithRetAsArg _ _ _ = Nothing

-- If there are any calls in the domain, it returns the Verilog
-- always-block for it, and a list of IDs which need to be declared
-- as reg because their assignments were inlined into the block.
vForeignBlock :: VConvtOpts -> ForeignFuncMap ->
                 [ADef] -> AForeignBlock -> Maybe ([VMItem], [AId])
vForeignBlock vco ffmap ds (_, []) = Nothing
vForeignBlock vco ffmap ds (clks, fcalls) =
  let
      -- make a def map
      def_map = M.fromList [(i, d) | d@(ADef i _ _ _) <- ds]
      findDef i = let err = internalError ("vForeignBlock findDef: " ++
                                           ppReadable i)
                  in  M.findWithDefault err i def_map

      -- make a def dependency map
      dep_map = M.fromList [(i, aVars d) | d@(ADef i _ _ _) <- ds]
      -- make a reverse dependency map
      rev_dep_map = reverseMap dep_map

      -- find the defs which depend on the value of an ActionValue fcall
      av_depend_defs = getAVDependDefs rev_dep_map fcalls
      -- find the defs which fcalls depend on
      fcall_depend_defs = getFCallDependDefs dep_map fcalls
      -- the intersection of these lists is the defs that we need to inline
      inline_def_ids = av_depend_defs `intersect` fcall_depend_defs

      -- convert from the ids back to the defs
      inline_defs = map findDef inline_def_ids

      -- tsort these inlined defs among the fcalls
      fcalls_and_defs = tsortForeignCallsAndDefs inline_defs fcalls

      -- convert the sorted list to VStmts
      convert :: Either ADef AForeignCall -> [VStmt]
      convert (Right fcall) = [vForeignCall vco fcall ffmap]
      convert (Left adef) =
          let -- some of the defs that we inline might not be simple
              -- assignments, so use vDefMpd instead of vExpr, but drop
              -- the declaration part, and convert the VMItems to VStmts
              vdef_items = snd $ expVVDWire $ vDefMpd vco adef ffmap
              itemToStmt :: VMItem -> VStmt
              itemToStmt (VMAssign i e) = VAssign i e
              itemToStmt (VMStmt { vi_body = Valways (VAt _ body) }) = body
              itemToStmt item = internalError ("vForeignBlock convert: " ++
                                               ppReadable item)
          in  map itemToStmt vdef_items

      -- the always block statements
      fcall_stmts0 = concatMap convert fcalls_and_defs
      -- separate out the SVAssertions
      isAss :: VStmt -> Bool
      isAss (VTask i _) = (vidToId i)==idSVA
      isAss _ = False
      (asses, fcall_stmts) = partition isAss fcall_stmts0
      -- the always block sensitivity list
      sensitivity_list =
          -- foreign function calls trigger at the negative clock edge so
          -- values are ready (at the positive edge) from input system tasks
          foldr1 VEEOr (map (VEEnegedge . (vExpr vco)) clks)
      -- the always block
      -- (starting the block with "#0" is a hack to pacify VCS and NC)
      always_stmt = Valways
                       (VAt sensitivity_list
                         (VSeq (VZeroDelay : fcall_stmts)))
      -- the assertions' sensitivity list
      ass_sensitivity_list =
          -- foreign function calls trigger at the negative clock edge so
          -- values are ready (at the positive edge) from input system tasks
          foldr1 VEEOr (map (VEEposedge . (vExpr vco)) clks)
      mkVAssert :: VStmt -> VMItem
      mkVAssert (VTask _ es) =
          VMStmt { vi_translate_off = True,
                   vi_body = VAssert ass_sensitivity_list es }
      mkVAssert x = internalError("mkVAssert: " ++ (show x))
      ass_stmts = map mkVAssert asses
  in -- put it together, with translate_off, since it is for sim only
     Just ((if null fcall_stmts then [] else
                     [VMStmt { vi_translate_off = True,
                               vi_body = always_stmt }])++
           (if null asses then [] else ass_stmts),

           inline_def_ids)

vForeignCall :: VConvtOpts -> AForeignCall -> ForeignFuncMap -> VStmt
vForeignCall vco f@(AForeignCall aid taskid (c:es) ids resets) ffmap =
  -- only go when none of the connected resets are active (except for $SVA)
  -- traces ("vfc " ++ show resets) $
  if aid==idSVA then fcall es
                  else foldr (Vif . mkNotEqualsReset . vExpr vco) fcall_body resets
  where
    vtaskid = VId (vCommentTaskName vco taskid) aid Nothing
    (ids',es') = let lv = headOrErr "vForeignCall: missing return value" ids
                 in case isAForeignCallWithRetAsArg vco ffmap f of
                     (Just ty) -> ([], (ASDef ty lv) : es)
                     Nothing   -> (ids,es)

    fcall exprs | Just (cnd, es_T, es_F) <- splitString exprs =
       Vifelse (vExpr vco cnd) (fcall es_T) (fcall es_F)
    fcall exprs = case ids' of
                 []  -> (buildVerilogTask vco vtaskid (map (vExpr vco) exprs))
                 [i] -> (VSeq [(VAssign (VLId (vId i))
                                (VEFctCall vtaskid (map (vExpr vco) exprs))),
                               VZeroDelay])
                 _   -> internalError("AVerilog.vForeignCall" ++ (show f))
    -- if c is trivial (i.e. 0 or 1), verilog pretty printing will optimize it:
    fcall_body = Vif (vExpr vco c) (fcall es')

    -- splitString is used because $display etc. don't treat naked String arguments correctly
    -- (i.e. they treat them as bits not strings).
    -- splitString is not needed however if we know the String argument is being consumed by a %s
    -- That's hard to know in general but we will detect a few special cases here and in those cases skip
    -- splitString
    isSpecialFormatString ASStr { ae_strval = s} | s == "%0s" = True
    isSpecialFormatString ASStr { ae_strval = s} | s == "%s"  = True
    isSpecialFormatString _                                   = False
    splitString [] = Nothing
    splitString (p:e@(APrim _ ty PrimIf _):rest) | isStringType ty && isSpecialFormatString p
                = fmap (\(cnd, es_T, es_F) -> (cnd, p:e:es_T, p:e:es_F)) (splitString rest)
    splitString ((APrim _ ty PrimIf [cnd,t,e]):rest) | isStringType ty = Just (cnd, t:rest, e:rest)
    splitString (e:rest) = fmap (\(cnd, es_T, es_F) -> (cnd, e:es_T, e:es_F)) (splitString rest)

vForeignCall vco call _ =
    internalError ("unexpected foreign call" ++ ppReadable call)

vFatalTask :: VId
vFatalTask  = mkVId "$fatal"

vErrorTasks :: [VId]
vErrorTasks = map mkVId ["$error", "$warning", "$info"]

vDisplayTask :: VId
vDisplayTask = mkVId "$display"

vFinishTask :: VId
vFinishTask = mkVId "$finish"

-- hook to desugar away SystemVerilog tasks for older simulators
buildVerilogTask :: VConvtOpts -> VId -> [VExpr] -> VStmt
buildVerilogTask vco fatal (code:es) | vco_sv_tasks vco == False &&
                                       fatal == vFatalTask =
  VSeq [VTask vDisplayTask es,
        VTask vFinishTask [code]]
buildVerilogTask vco etask es | vco_sv_tasks vco == False &&
                                etask `elem` vErrorTasks =
  -- add $error, $warning, $info here?
  VTask vDisplayTask es
-- if task is $swrite (or friends) add a #0 to get "expected" blocking assignment behavior
buildVerilogTask vco taskid es | isMappedAVId (vidToId taskid) = VSeq [VTask taskid es, VZeroDelay]
buildVerilogTask vco taskid es = VTask taskid es

tsortForeignCallsAndDefs :: [ADef] -> [AForeignCall] ->
                            [Either ADef AForeignCall]
-- if there are no defs, just return the fcalls
tsortForeignCallsAndDefs [] fcalls = map Right fcalls
tsortForeignCallsAndDefs ds fcalls =
    let
        -- we will create a graph where the edges are:
        -- * "Left AId" to represent a def (by it's name)
        -- * "Right Integer" to represent an fcall (by it's position)

        -- The use of Left and Right was chosen to make Defs lower in
        -- the Ord order than ForeignCalls.  This way, tsort puts them first.

        -- ----------
        -- Defs

        -- the Ids of the defs
        -- (we only want to make edges for variable uses from this list)
        ds_ids = map adef_objid ds
        -- for efficiency, make it a set
        s = S.fromList ds_ids

        -- make edges for def-to-def dependencies
        def_edges = [ (Left i, map Left uses)
                          | ADef i _ e _ <- ds,
                            let uses = filter (`S.member` s) (aVars e) ]

        -- map def ids back to their defs
        defmap = M.fromList [ (i,d) | d@(ADef i _ _ _) <- ds ]
        getDef i =
            case (M.lookup i defmap) of
                Just d -> d
                Nothing -> internalError "tsortForeignCallsAndDefs: getDef"

        -- ----------
        -- ForeignCalls

        -- give the fcalls a unique number and make a mapping
        -- (numbering in order sets the Ord order for tsort)

        numbered_fcalls :: [(Integer, AForeignCall)]
        numbered_fcalls = zip [1..] fcalls

        fcall_map = M.fromList numbered_fcalls
        getFCall n =
            case (M.lookup n fcall_map) of
                Just d -> d
                Nothing -> internalError "tsortForeignCallsAndDefs: getFCall"

        -- ----------
        -- ForeignCall-to-ForeignCall edges
        -- (to maintain the user-specified order of the ForeignCalls)

        -- (are these still needed now that we use Ord to bias tsort?)
        fcall_edges =
          case (uncons numbered_fcalls) of
            Nothing -> []
            Just (_, tail_numbered_fcalls) ->
              let mkEdge (n1,_) (n2,_) = (Right n2, [Right n1])
              in  zipWith mkEdge
                      numbered_fcalls -- last element will be unused
                      tail_numbered_fcalls

        -- ----------
        -- ForeignCall to Def edges

        -- any defs used by an fcall have to be computed before the
        -- fcall is called
        fcall_def_edges = [ (Right n, map Left uses)
                                | (n,f) <- numbered_fcalls,
                                  let uses = filter (`S.member` s) (aVars f) ]

        -- any def which uses a value set by an fcall must be computed
        -- after the fcall is called
        def_fcall_edges =
            let
                -- find the values set by the fcalls
                avalue_pairs = [ (val, n) | (n,f) <- numbered_fcalls,
                                            val <- afc_writes f ]
                avalue_map = M.fromList avalue_pairs
                findNum i =
                    let err = internalError
                                  ("tsortForeignCallsAndDefs def_fcall_edges")
                    in  M.findWithDefault err i avalue_map
                -- and just the set of ids, for testing membership
                avalue_set = M.keysSet avalue_map
                isAV i = S.member i avalue_set
                -- find the defs that depend on the avalues
                aval_refs = [ (i, refs)
                                 | (ADef i _ e _) <- ds,
                                   let refs = filter isAV (aVars e),
                                   not (null refs) ]
            in  -- make the edges
                [ (Left i, map (Right . findNum) refs)
                     | (i, refs) <- aval_refs ]

        -- ----------
        -- put it together into one graph

        g =
{-
            trace ("fcalls = " ++ ppReadable numbered_fcalls) $
            trace ("def_edges = " ++ ppReadable def_edges) $
            trace ("fcall_edges = " ++ ppReadable fcall_edges) $
            trace ("fcall_def_edges = " ++ ppReadable fcall_def_edges) $
            trace ("def_fcall_edges = " ++ ppReadable def_fcall_edges) $
-}
            map_insertManyWith union (fcall_edges) $
            map_insertManyWith union (fcall_def_edges) $
            map_insertManyWith union (def_fcall_edges) $
            M.fromList def_edges

        -- Convert the graph to the format expected by tsort.
        g_edges = M.toList g

        -- ----------
        -- convert a graph node back into a def/action
        -- and then to a SimCCFnStmt

        convertNode (Left i) = Left (getDef i)
        convertNode (Right n) = Right (getFCall n)

    in
        -- tsort returns Left if there is a loop, Right if sorted.
        case (tsort g_edges) of
            Right is -> map convertNode is
            Left (scc:_) ->
                let path = extractOneCycle_map g scc
                in  internalError ("tsortForeignCallsAndDefs: cyclic " ++
                                   ppReadable (map convertNode path))
            Left [] -> internalError ("tsortForeignCallsAndDefs: cyclic []")


getAVDependDefs :: (M.Map AId [AId]) -> [AForeignCall] -> [AId]
getAVDependDefs rev_dep_map fcalls =
    let avalues = concatMap afc_writes fcalls
        all_ids = closeOverMap rev_dep_map avalues
    in  -- don't include the avalues themselves
        all_ids \\ avalues
        -- for efficiency, we could exploit knowledge that the avalues
        -- are at the end of the list and do this:
        --rDrop (length avalues) all_ids

getFCallDependDefs :: (M.Map AId [AId]) -> [AForeignCall] -> [AId]
getFCallDependDefs dep_map fcalls =
    let -- XXX we presumably don't need to include the reset exprs?
        is = aVars (concatMap afc_args fcalls)
    in  closeOverMap dep_map is

closeOverMap :: (M.Map AId [AId]) -> [AId] -> [AId]
closeOverMap dmap is = S.toList $ closeOverMap' dmap (S.fromList is) S.empty is

closeOverMap' :: (M.Map AId [AId]) -> S.Set AId -> S.Set AId -> [AId] -> S.Set AId
closeOverMap' dmap considered consider_next [] =
    if (S.null consider_next)
    then considered
    else let consider_next' = S.difference consider_next considered
             considered' = S.union considered consider_next'
         in  closeOverMap' dmap considered' S.empty (S.toList consider_next')
closeOverMap' dmap considered consider_next (i:is) =
    case (M.lookup i dmap) of
        (Just dep_is) -> let consider_next' = set_insertMany dep_is consider_next
                         in  closeOverMap' dmap considered consider_next' is
        Nothing       -> closeOverMap' dmap considered consider_next is

-- ==============================

isAFunCallWithRetAsArg :: VConvtOpts -> ForeignFuncMap -> AExpr -> Bool
isAFunCallWithRetAsArg vco ffmap fn@(AFunCall { ae_isC = True }) =
  case M.lookup (ae_funname fn) ffmap of
    (Just ff) -> isPoly (ff_ret ff) || ((vco_use_dpi vco) && isWide (ff_ret ff))
    Nothing   -> False
isAFunCallWithRetAsArg _ _ _ = False


vDefMpd :: VConvtOpts -> ADef -> ForeignFuncMap
              -> [VMItem]
-- special case for two input mux, for readability
{-
vDefMpd _ (ADef i t (APrim _ _ PrimPriMux [ce,te,_,ee])) =
        [ VMDecl $ VVDecl VDWire (vSize t) [VVar (vId i)],
          VMAssign (VLId (vId i)) (VEIf (vExpr vco ce) (vExpr vco te) (vExpr vco ee)) ]
-}
vDefMpd vco (ADef i t (APrim _ _ PrimPriMux []) _) _ = internalError("vDefMpd 11" )

vDefMpd vco (ADef i t (APrim _ _ PrimPriMux [e]) _) _ = internalError("vDefMpd 12" )

vDefMpd vco  def@(ADef i t (APrim _ _ PrimPriMux es) _) _ =
    if (not (vco_readableMux vco)) then
        [ VMDecl $ VVDecl VDWire (vSize t) [VVar (vId i)],
          muxInst vco True (aSize t) (vPrimInstId "priorityMux_" i) (VEVar (vId i) : map (vExpr vco) es) ]
    else
        [ VMDecl $ VVDecl VDReg (vSize t) [VVar vi],
          VMStmt { vi_translate_off = False,
                   vi_body =
                       Valways $ VAt ev $
                       Vcase { vs_case_expr = one,
                               vs_case_arms = arms (makePairs es),
                               vs_parallel = False,
                               vs_full = False
                             }
                 }
        ]
  where vi = vId i
        one = VEWConst (mkVId "1") 1 2 1
        arms [] = []  -- shouldn't happen
        arms [(c,e)] = [VDefault (VAssign (VLId vi) (vExpr vco e))]
        arms ((c,e) : ces) =
            (VCaseArm [vExpr vco c] (VAssign (VLId vi) (vExpr vco e)) : arms ces)
        sensitivityList = nub (concatMap aIds es)
        ev = if (null sensitivityList)
             then (internalError("AVerilogUtil:: null sensitivity list for PrimPriMux" ++ ppReadable def))
             else foldr1 VEEOr (map (VEE . VEVar) sensitivityList)

vDefMpd vco def@(ADef i t (APrim _ _ PrimMux es) _) _ =
    if (not (vco_readableMux vco)) then
        [ VMDecl $ VVDecl VDWire (vSize t) [VVar (vId i)],
          muxInst vco False (aSize t) (vPrimInstId "mux_" i) (VEVar (vId i) : map (vExpr vco) es) ]
    else
        [ VMDecl $ VVDecl VDReg (vSize t) [VVar vi],
          VMStmt { vi_translate_off = False,
                   vi_body =
                       Valways $ VAt ev $
                       VSeq [ -- VAssign (VLId vi) (VEConst 0), -- no need to put default assignment
                              Vcase { vs_case_expr = one,
                                      vs_case_arms = map arm (init armpairs) ++ defaultArm (last armpairs),
                                      vs_parallel = True,
                                      vs_full = False
                                    }
                            ]
                 }
        ]
  where vi = vId i
        one = VEWConst (mkVId "1") 1 2 1
        armpairs = makePairs es
        arm (c,e) = VCaseArm [vExpr vco c] (VAssign (VLId vi) (vExpr vco e))
        defaultArm (c,e) = [VDefault (VAssign (VLId vi) (vExpr vco e))]
        sensitivityList = nub (concatMap aIds es)
        ev = if (null sensitivityList)
             then (internalError("AVerilogUtil:: null sensitivity list for PrimMux"  ++ ppReadable def))
             else foldr1 VEEOr (map (VEE . VEVar) sensitivityList)

vDefMpd vco (ADef i t
               (ANoInlineFunCall _ _
                  (ANoInlineFun n is (ips, ops) (Just inst_name)) es) _) _ =
        let ops' = ops -- filter (\(x,y) -> y >= 0 ) $ traces ("ops " ++ show ops) ops
                   -- Size information all appears to be 0
            (ips',es')  = unzip $ filter (isNotZeroSized  . ae_type . snd) (zip ips es)
            oname = VEVar (vId i) -- a concat of the outputs
            oports = case ops' of
                     [(o, _)] -> [(mkVId o, Just oname)]
                     ons -> let ns = tailOrErr "vDefMpd.oports" (scanr (+) 0 (map snd ons))
                            in  zipWith (\ (o, s) l ->
                                        (mkVId o,
                                         Just (veSelect
                                                 oname
                                                 (VEConst (l+s-1))
                                                 (VEConst l))))
                                                 ons
                                                 ns
        in
        [ VMDecl $ VVDecl VDWire (vSize t) [VVar (vId i)],
          VMInst {
                  vi_module_name = mkVId n,
                  vi_inst_name   = VId inst_name i Nothing,
                  -- these are size params, so default width of 32 is fine
                  vi_inst_params = Left (map (\x -> (Nothing,VEConst x)) is),
                  vi_inst_ports  = (zip
                                    (map (mkVId . fst) ips')
                                    (map (Just . (vExpr vco)) es')
                                    ++ oports)
                 }
            ]

vDefMpd vco defin@(ADef i t (APrim _ _ PrimCase es@(x:defarm:ces_t)) _) _ =
        [ VMDecl $ VVDecl VDReg (vSize t) [VVar vi],
          VMStmt { vi_translate_off = False,
                   vi_body =
                       Valways $ VAt ev $
                       VSeq [Vcase { vs_case_expr = vExpr vco x,
                               vs_case_arms = arms (makePairs ces_t) ++ def,
                               vs_parallel = False,
                               vs_full = False
                             }]
                 }
        ]
  where vi = vId i
        arms [] = []
        arms ((c,e) : ces) =
                let (cs, ces') = partition ((== e) . snd) ces
                in  VCaseArm (map (vExpr vco) (c:map fst cs)) (VAssign (VLId vi) (vExpr vco e)) : arms ces'
        sensitivityList = nub (concatMap aIds es)
        ev = if (null sensitivityList)
             then (internalError("AVerilogUtil:: null sensitivity list for case" ++ ppReadable defin))
             else foldr1 VEEOr (map (VEE . VEVar) sensitivityList)
        n = aSize x
        fullcase = (2^n * 2) == (length ces_t)
        def = if fullcase then [] else [VDefault (VAssign (VLId vi) (vExpr vco defarm))]

vDefMpd vco (ADef i_t t_t@(ATBit _) (ATaskValue {}) _) _ =
    [VMDecl $ VVDecl VDReg (vSize t_t) [VVar (vId i_t)]]

vDefMpd vco (ADef i_t t_t@(ATBit _) fn@(AFunCall {}) _) ffmap
  | isAFunCallWithRetAsArg vco ffmap fn =
    [ VMDecl $ VVDecl VDReg (vSize t_t) [VVar (vId i_t)]
    , VMStmt { vi_translate_off = True, vi_body = body }
    ]
  where name = vCommentTaskName vco (vNameToTask (vco_use_dpi vco) (ae_funname fn))
        vtaskid = VId name (ae_objid fn) Nothing
        sensitivityList = nub (concatMap aIds (ae_args fn))
        ev = foldr1 VEEOr (map (VEE . VEVar) sensitivityList)
        arg_list = (ASDef t_t i_t) : ae_args fn
        args = map (vExpr vco) arg_list
        body = if (null sensitivityList)
               then Vinitial $ VSeq [VTask vtaskid args]
               else Valways $ VAt ev $ VSeq [VTask vtaskid args]

vDefMpd vco (ADef i_t t_t@(ATBit _) e_t _) _ =
    let
        -- XXX AMethCall/AMethValue shouldn't exist
        -- vExprMpd (AMethCall t i m []) = VEVar (vMethId i m 1 MethodResult)
        -- vExprMpd (AMethCall t i m _) = internalError "AVerilog.vExprMpd: AMethCall with args"
        -- vExprMpd (AMethValue t i m) = VEVar (vMethId i m 1 MethodResult)
        vExprMpd e = vExpr vco e
    in
        [VMDecl $ VVDWire (vSize t_t) (VVar (vId i_t)) (vExprMpd e_t)]
vDefMpd vco adef@(ADef i_t t_t@(ATAbstract aid _) e_t _) _ | aid==idInout_ =
    [VMDecl $ VVDWire (vSize t_t) (VVar (vId i_t)) (vExpr vco e_t)]
vDefMpd vco adef@(ADef i_t t_t@(ATString _) e_t _) _ =
    [VMDecl $ VVDWire (vSize t_t) (VVar (vId i_t)) (vExpr vco e_t)]

vDefMpd vco adef@(ADef _ _ _ _) _ = internalError( "unexpected pattern in AVerilog::vDefMpd: " ++ ppReadable adef ) ;


-- ------------------------------

veSelect :: VExpr -> VExpr -> VExpr -> VExpr
veSelect e h l = if h == l then VESelect1 e l else VESelect e h l


-- ==============================

vId :: Id -> VId
vId i = VId (getIdString i) i Nothing

vInstId :: Id -> VId
vInstId i =
    let string = (verilogInstancePrefix ++ getIdString i)
    in VId string (setIdBaseString ( unQualId i ) string ) Nothing

-- We need a prefix for prims which must not be "" (because verilog complains about
-- collisions between instance names and net names.)
vPrimInstId :: String -> Id -> VId
vPrimInstId name i = VId (name ++ getIdString i) i Nothing

-- ------------------------------

suff :: VId -> String -> VId
suff (VId is i m) s = VId (is ++ s) i m

pref :: String -> VId -> VId
pref p (VId is i m) = VId (p ++ is) i m


-- ==============================
-- main conversion for AExpr to VExpr
vExpr :: VConvtOpts -> AExpr -> VExpr
vExpr vco e@(APrim _ _ PrimCase _) = internalError ("vExpr vco CASE " ++ ppReadable e)
vExpr vco e@(APrim _ _ PrimMux es) = internalError ("vExpr vco MUX " ++ ppReadable e)
vExpr vco e@(APrim _ _ PrimPriMux es) = internalError ("vExpr vco MUX " ++ ppReadable e)
vExpr vco (APrim _ _ PrimResetUnassertedVal []) = mkNotReset
vExpr vco (APrim _ _ PrimConcat es@(e:_)) | allSame es = VERepeat (VEConst (genericLength es)) (vExpr vco e)
vExpr vco (APrim _ _ PrimConcat es) = VEConcat (map (vExpr vco) es)
-- Avoid repetition syntax for strings
vExpr vco (APrim _ _ PrimStringConcat es) = VEConcat (map (vExpr vco) es)
vExpr vco (APrim _ _ PrimExtract [e1, e2, e3]) | e2 == e3 = VESelect1 (vExpr vco e1) (vExprC vco e2)
vExpr vco (APrim _ _ PrimExtract [e1, e2, e3]) | isConst e2 && isConst e3 = VESelect (vExpr vco e1) (vExprC vco e2) (vExprC vco e3)
vExpr vco (APrim _ _ PrimIf [e1, e2, e3]) = VEIf (vExpr vco e1) (vExpr vco e2) (vExpr vco e3)
vExpr vco (APrim _ _ PrimBNot [e]) = vNot (vExpr vco e)
vExpr vco (APrim _ _ PrimRange [_,_,e]) = vExpr vco e
vExpr vco (APrim _ t PrimZeroExt [e]) =
            VEConcat [VEWConst
                        (mkVId "0")
                        (aSize t - aSize e)
                        10
                        0,
                    vExpr vco e]
vExpr vco (APrim _ t PrimSignExt [e]) | aSize e == 1 && aSize t > 0 = VERepeat (VEConst (aSize t)) (vExpr vco e)
vExpr vco e0@(APrim _ t PrimSignExt [e]) = VEConcat [vERepeat fill (VESelect1 vexp vhi), vexp]
    where fill = if (j >= i) then
                   internalError("AVerilogUtil.broken SignExtend: " ++ ppReadable e0)
                 else i-j
          vhi = VEConst (j-1)
          vexp = vExpr vco e
          i = aSize t
          j = aSize e
          vERepeat 1 x = x
          vERepeat n x = VERepeat (VEConst n) x
vExpr vco (APrim aid t p [e1, e2]) | isSignedCmp p = VEOp (idToVId aid) (flip_t (vExpr vco e1)) (unsOp p) (flip_t (vExpr vco e2))
  where flip_t e = vXor e (VEWConst (mkVId (show ((2 :: Integer)^(s-1)))) s 16 (2^(s-1)))
        s = aSize (aType e1)
vExpr vco (APrim aid _ p [e]) = VEUnOp (idToVId aid) (toVOp p) (vExpr vco e)
vExpr vco (APrim aid _ p [e1,e2]) | p == PrimSL || p == PrimSRL = VEOp (idToVId aid) (vExpr vco e1) (toVOp p) (vExprC vco e2)
vExpr vco (APrim aid _ p [e1,e2]) = VEOp (idToVId aid) (vExpr vco e1) (toVOp p) (vExpr vco e2)
vExpr vco (APrim aid t p es) = VEOp (idToVId aid) (vExpr vco (APrim aid t p (init es))) (toVOp p) (vExpr vco (last es))
-- XXX AMethCall/AMethValue shouldn't exist
-- vExpr vco (AMethCall t i m []) = VEVar (vMethId i m 1 MethodResult M.Empty)
-- vExpr vco (AMethCall t i m _) = internalError "AVerilog.vExpr: AMethCall with args"
-- vExpr vco (AMethValue t i m) = VEVar (vMethId i m 1 MethodResult M.Empty)
vExpr vco (AFunCall _ _ n isC es) =
  let name = vCommentTaskName vco (if isC then vNameToTask (vco_use_dpi vco) n else n)
  in VEFctCall (mkVId name) (map (vExpr vco) es)
vExpr vco (ASInt idt (ATBit w) (IntLit _ b i))  = VEWConst (idToVId idt) w b i
vExpr vco (ASReal _ _ r)                        = VEReal r
vExpr vco (ASStr _ _ s)                         = VEString s
vExpr vco (ASDef _ i)                           = VEVar (vId i)
vExpr vco (ASPort _ i)                          = VEVar (vId i)
vExpr vco (ASParam _ i)                         = VEVar (vId i)
vExpr vco (ASAny (ATBit w) _)                   = VEUnknown w (vco_unspec vco)

vExpr vco e = internalError ("vExpr vco " ++ ppReadable e)

vXor :: VExpr -> VExpr -> VExpr
vXor (VEWConst id_t s b i1) (VEWConst _ _ _ i2) = VEWConst id_t s b (integerXor i1 i2)
vXor e1 e2 = mkVEOp e1 VXor e2

-- need to understand what vExprC is used for
-- emitting VEConst seems dangerous in some cases
vExprC :: VConvtOpts -> AExpr -> VExpr
vExprC vco e@(ASInt _ (ATBit _) (IntLit _ _ i)) = -- trace ("vExprC: " ++ (ppReadable e)) $
  VEConst i
vExprC vco e = -- trace ("vExprC: " ++ (ppReadable e)) $
  dropLeadingZeroes (vExpr vco e)

vNot :: VExpr -> VExpr
vNot (VEOp vid e1 VULT e2) = VEOp vid e1 VUGE e2
vNot (VEOp vid e1 VULE e2) = VEOp vid e1 VUGT e2
vNot (VEOp vid e1 VEQ  e2) = VEOp vid e1 VNE  e2
vNot (VEOp vid e1 VEQ3 e2) = VEOp vid e1 VNE3 e2
vNot e                     = mkVEUnOp VNot e

toVOp :: PrimOp -> VOp
toVOp PrimBNot = VNot
toVOp PrimInv  = VInv
toVOp PrimNeg  = VNeg
toVOp PrimMul  = VMul
toVOp PrimQuot = VQuot
toVOp PrimRem  = VRem
toVOp PrimAdd  = VAdd
toVOp PrimSub  = VSub
toVOp PrimSL   = VShL
toVOp PrimSRL  = VShR
-- should no longer be needed after quirks fix
-- toVOp PrimSRA = VShRA
toVOp PrimULT  = VULT
toVOp PrimULE  = VULE
toVOp PrimEQ   = VEQ
toVOp PrimEQ3  = VEQ3
toVOp PrimAnd  = VAnd
toVOp PrimXor  = VXor
toVOp PrimOr   = VOr
toVOp PrimBAnd = VLAnd
toVOp PrimBOr  = VLOr
toVOp p        = internalError ("toVOp " ++ show p)

isSignedCmp :: PrimOp -> Bool
isSignedCmp PrimSLT = True
isSignedCmp PrimSLE = True
isSignedCmp _       = False

unsOp :: PrimOp -> VOp
unsOp PrimSLT = VULT
unsOp PrimSLE = VULE
unsOp _ = internalError ("AVerilog::unsOp")

dropLeadingZeroes :: VExpr -> VExpr
dropLeadingZeroes e_t =
    case dropLeadingZeroes' e_t of
    VEConcat [e] -> e
    e -> e
dropLeadingZeroes' :: VExpr -> VExpr
dropLeadingZeroes' (VEConcat (VEWConst _ _ _ 0 : es@(_:_))) = dropLeadingZeroes (VEConcat es)
dropLeadingZeroes' e = e

-- ------------------------------

muxInst :: VConvtOpts -> Bool -> Integer -> VId -> [VExpr] -> VMItem
muxInst vco pri s i es =
    VMInst {
            vi_module_name  = mkVId ((if pri then "Pri" else "")
                                     ++ "Mux_"
                                     ++ itos (length es `div` 2)),
            vi_inst_name    = i,
            vi_inst_params  = if ( vco_v95 vco )
                              then Left [(Just $ getVIdString viWidth ,VEConst s)]
                              else Right [(viWidth, Just (VEConst s))],
            vi_inst_ports   = zip muxInputs (map Just es)
           }

-- an infinite list of Ids;
muxInputs :: [VId]
muxInputs = mkVId "out" : fxx  0
  where
  fxx :: Integer -> [VId]
  fxx n = mkVId ("s_" ++ itos n) : mkVId ("in_" ++ itos n)  : fxx (n+1)


-- ==============================

-- pairs of the Verilog module port/param name and the expression
-- connected to it in the VMInst (expressions for params and port args,
-- but Ids in all other cases, because wires are declared)
type InstInfo = ([(VId, VExpr)],  -- parameter exprs
                 [(VId, VExpr)],  -- non-method port exprs (clocks, resets, inouts)
                 [(VId, VId)],    -- special ifc outputs (clocks, resets, inouts)
                 [(VId, VId)],    -- method input port signals
                 [(VId, VId)])    -- method output port signals

-- an instance is "wired" to the outside world
-- if it connects *any* sort of port
-- (method input or output, dynamic argument, inout, clock, reset)
-- modules that connect no wires (probably because of zero-width ports)
-- will be thrown out (see use in AVerilog.hs)
wiredInstance :: VMItem -> Bool
wiredInstance inst@(VMInst {}) = (not . null) (vi_inst_ports inst)
wiredInstance item = internalError ("wiredInstance - not instance: " ++ ppReadable item)

-- this also takes a "rewiring" map for those special wires
-- that need to be redirected (currently only inouts)
-- given an AVInst, this produces
--  * the instance name
--  * the Verilog instantiation (VMInst)
--  * instantiation information:
--    * a list of instantiation parameter expressions,
--    * a list of non-method instantiation port expressions (clocks, resets),
--    * a list of special outputs (clocks, resets),
--    * a list of method input port signals, and
--    * a list of method output port signals
-- XXX this function is too big
vState :: Flags -> M.Map AId AId -> AVInst -> (AId, VMItem, InstInfo)
vState  flags rewire_map avinst =
    let vco = flagsToVco flags
        v_inst_name = avi_vname avinst
        mts = avi_meth_types avinst
        vi = avi_vmi avinst
        es = avi_iargs avinst
        --
        -- the port multiplicity usage (how many copies are used)
        -- ns = avi_iarray avinst

        -- get the number of copies of a method which are used
        -- getMethodMultUse m =
        --    case (lookup m ns) of
        --        Just mult -> mult
        --        Nothing -> internalError ("vState getMethodMultUse: " ++
        --
        --                          "ns list not consistent with vfi")

        --
        -- a map from ATS names for method names and args
        -- to the corresponding signals in verilog
        -- e.g., "r$write" -> "r$EN", "r$write_1" -> "r->$D_IN"
        port_rename_table =
            M.fromList (createVerilogNameMapForAVInst flags avinst)

        rewire_inout (ASPort t i) | isInoutType t,
                                    Just i' <- M.lookup i rewire_map = ASPort t i'
        rewire_inout e = e

        -- list of (parameter or port name, assigned expression)
        -- e.g., (port (CLK, [clock]),    CLK)
        --       (param width;,           32'd32)
        -- make sure to filter-out 0-width ports and parameters
        -- we also rewire inout ports that might have been renamed
        -- because of a connection
        arges = [(vai, vExpr vco e') | (vai, e) <- zip (vArgs vi) es,
                                       let e' = rewire_inout e,
                                       isNotZeroSized (aType e) ]

        -- Below, we construct info on the method:
        --   arguments, return values, and enables

        mkArgId :: Id -> Integer -> Maybe Integer -> VId
        mkArgId m k m_port = vMethId v_inst_name m m_port (MethodArg k) port_rename_table

        mkEnId m m_port = vMethId v_inst_name m m_port MethodEnable port_rename_table

        mkResId m k m_port = vMethId v_inst_name m m_port (MethodResult k) port_rename_table

        -- add the multiplicity to Verilog port names
        -- (if there are not multiple ports, no uniquifier is added)
        portid :: String -> Maybe Integer -> String
        portid s Nothing  = s
        portid s (Just n) = s ++ "_" ++ itos (n+1) -- ports start numbering at 1 not 0

        -- check that an instantiated module doesn't reuse an input port
        check_inps [i] = i
        check_inps ((port, _, _):_) =
            -- XXX should this be a user error?
            internalError("attempt to instantiate module " ++
                          (ppReadable v_inst_name) ++
                          " with duplicated port " ++ (ppReadable port))
        check_inps [] = internalError( "AVerilog::mkinput" )

        -- for each method argument: the Verilog port name with muliplicity,
        -- the Id in method syntax (<inst>$<meth>_[<portnum>_]<argnum>), and possibly
        -- the size if it is not 1-bit
        inps :: [(VId, VId, Maybe VRange)]
        inps =  [ (mkVId (portid s ino),
                   mkArgId m k ino,
                   vSize argType)
                  | (meth@(Method m _ _ mult ps outs me),
                     (argTypes,_,_))
                        <- zip (vFields vi) mts,
                        -- (VName s, vps)
                    -- let multu = getMethodMultUse m,
                    ino <- if mult > 1 then map Just [0..mult-1] else [Nothing],
                    (VName s, argType, k) <- zip3 (map fst ps) argTypes [1..],
                    isNotZeroSized argType
                ]

        -- check for duplicates
        inputs :: [(VId, VId, Maybe VRange)]
        inputs = map check_inps
                     (sortGroup (\ (x,_,_) (y,_,_) -> x <= y) inps)

        -- for each method with an action: the method name, the enable
        -- Verilog port name, the enable name in method syntax
        -- (<inst>$EN_<meth>), whether the method must be always enabled
        meth_enables =
                [ (m,
                   mkVId (portid s ino),
                   mkEnId m ino,
                   inhigh )
                  | (Method m _ _ mult ss outs me@(Just (VName s,vps)))
                        <- vFields vi,
                    let inhigh = VPinhigh `elem` vps,
                    -- let multu = getMethodMultUse m,
                    ino <- if mult > 1 then map Just [0..mult-1] else [Nothing]
                ]

        -- for each method with a result: the result Verilog port name,
        -- the result name in method syntax (<inst>$<meth>)
        -- (nub, because several methods might have their return value
        --  come from the same output port)
        meth_return_vals =
            nub
                [ (mkVId (portid s ino),
                   mkResId m k ino)
                  | ((Method m _ _ mult ss outs me), (_,_,retTypes))
                        <- zip (vFields vi) mts,
                     ((VName s, vps), retType, k) <- zip3 outs retTypes [1..],
                     isNotZeroSized retType,
                     -- let multu = getMethodMultUse m,
                     ino <- if mult > 1 then map Just [0..mult-1] else [Nothing]
                ]

        -- clock and reset outputs
        -- no nub because getSpecialPorts takes care of it
        -- include a flag that tells us if the wire needs to be declared or not
        special_wire_blobs =
            [ (vIdV wvname, vId wid', wid' == wid)
                | (wid, wtype, (wvname, wvprops)) <- getSpecialOutputs avinst,
                  -- redirect wires that need special wiring (currently inouts)
                  let wid' = fromMaybe wid (M.lookup wid rewire_map),
                  isNotZeroSized wtype
            ]

        -- the only special wires that are true outputs are the ones
        -- that need to be declared
        -- i.e. are not directly wired somewhere else
        special_wire_outputs = [ (port, wid) | (port, wid, keep) <- special_wire_blobs, keep ]

        -- but we need to connect all the special wires
        special_wire_connections = map fst2of3 special_wire_blobs

        -- drop output ports repeated between "special" signals and
        -- method return values
        -- XXX we should error if these ports are used at varying widths
        -- XXX or varying names after rewiring
        output_wire_connections = nubByFst (meth_return_vals ++ special_wire_connections)

        -- instantiation parameters
        paramExprs =
            -- Lennart added the dropping of sizes in r364, but this leads
            -- to bugs if the uses of the param in the submod rely on the
            -- size of the parameter.  All our parameters are sized
            -- (Integer becomes 32-bit), so there's no reason to drop,
            -- except maybe for readability (where we could drop the 32 if
            -- it's size 32, but only if the value isn't so large that we
            -- want to display it in hex).
            [ (vIdV vn, {-vDropSize-} ve) | (Param vn, ve) <- arges ]

        -- dynamic module arguments
        port_ps = [ (vIdV vn, ve) | (Port (vn,_) _ _, ve) <- arges ]

        -- the wires (ins, outs and inouts) to connect to the module ports
        args :: [(VId, Maybe VExpr)]
        args =
            -- dynamic arguments
            [ (p, Just e) | (p, e) <- port_ps ] ++
            -- method inputs
            [ (p, Just (VEVar w)) | (p, w, rng) <- inputs, nonZero rng ] ++
            -- method enables (those which are not always enabled)
            [ (p, Just (VEVar w)) | (_, p, w, False) <- meth_enables ] ++
            -- wire outputs - method return values and "special" (e.g. clock and reset)
            [ (p, Just (VEVar w)) | (p, w) <- output_wire_connections ]

        ifc_position = (getIfcIdPosition vi)

        vminst = VMInst {
                         vi_module_name  = vIdV (vName vi),
                         vi_inst_name    = vInstId v_inst_name,
                         vi_inst_params  = if ( vco_v95 vco )
                                           then Left (mapFst (Just . getVIdString)  paramExprs)
                                           else Right (mapSnd Just paramExprs),
                         vi_inst_ports   = map (updateArgPosition ifc_position . tildeHack) args
                        }

        inst_info =
            (-- param exprs
             paramExprs,
             -- non-meth input port exprs
             port_ps,
             -- special wire output names
             special_wire_outputs,
             -- method input names
             [ (p, w) | (p, w, rng) <- inputs, nonZero rng ] ++
             [ (p, w) | (_, p, w, False) <- meth_enables],
             -- method output names
             meth_return_vals
            )


        -- debug_inputs = traces ("\n\nDBG vState:\n" ++ ppReadable avinst ++ "\n\n")
        -- debug_arges = traces ("\n\nDBG arges:\n" ++ ppReadable arges ++ "\n")
        -- debug_tymap = traces ("\n\nDBG tyMap:\n" ++ ppReadable tyMap ++ "\n")
        -- debug_vminst = traces ("\n\nDBG vState vminst=\n" ++ ppReadable vminst ++ "\n\n")

    in
        -- debug_inputs $ debug_arges $ debug_vminst $
        if (length (vArgs vi)) /= (length es)
        then internalError "AVerilog.vState: # args differs from expected"
        else (v_inst_name,
              vminst,
              inst_info)

-- ------------------------------
updateArgPosition :: Position -> (VId,Maybe VExpr) -> (VId,Maybe VExpr)
updateArgPosition pos ((VId s id0 m), (Just (VEUnOp (VId s2 id2 m2) vop vexpr))) =
    ((VId s (setIdPosition pos id0) m), (Just (VEUnOp (VId s2 (setIdPosition pos id2) m2) vop vexpr)))
updateArgPosition pos ((VId s id0 m), (Just (VEVar (VId s2 id2 m2)))) =
     ((VId s (setIdPosition pos id0) m), (Just (VEVar (VId s2 (setIdPosition pos id2) m2))))
updateArgPosition pos arg = arg




isNotZeroSized :: AType -> Bool
isNotZeroSized atb@(ATBit {}) = 0 /= atb_size atb
isNotZeroSized atb@(ATAbstract { ata_sizes = [n]}) = 0 /= n
isNotZeroSized _                  = True

vSize :: AType -> Maybe VRange
vSize (ATBit 1) = Nothing
vSize (ATBit n) = Just (VEConst (n-1), VEConst 0)
vSize (ATAbstract i [1]) | i==idInout_ = Nothing
vSize (ATAbstract i [n]) | i==idInout_ = Just (VEConst (n-1), VEConst 0)
vSize t@(ATString (Just _)) = Just (VEConst ((aSize t)-1::Integer), VEConst 0)
vSize (ATString Nothing)  = Just (VEConst (dummy_string_size - 1::Integer), VEConst 0)
vSize t = internalError("Attempt to get size of non-Bit type: " ++ ppReadable t)

-- Looks at VRange to determine if Verilog expression is 0 size [-1:0]  yuck.
nonZero :: Maybe (VExpr,VExpr) -> Bool
nonZero (Just (VEConst (-1), VEConst 0)) = False
nonZero _ = True

tildeHack :: (VId,Maybe VExpr) -> (VId ,Maybe VExpr)
tildeHack (VId ('~':fs) _ m, e) = (mkVId fs, fmap (mkVEUnOp VInv) e)
tildeHack p = p

vIdV :: VName -> VId
vIdV (VName s) = mkVId s

vMethId :: Id -> Id -> Maybe Integer -> MethodPart -> M.Map FString FString -> VId
vMethId i m m_port mp fsmap =
    let fstring =
            xLateFStringUsingFStringMap fsmap (mkMethStr i m m_port mp)
    in VId (getFString fstring) (setIdBase ( unQualId i) fstring ) Nothing

{-
-- unsized constants are only guaranteed 32 bits
-- and we want to force hex printing for constants > 1000
vDropSize :: VExpr -> VExpr
vDropSize (VEWConst _ w _ i) | w <= 32 && i <= 1000 = VEConst i
vDropSize e = e
-}


-- ==============================

aIds :: AExpr -> [VId]
aIds (APrim _ _ _ es)     = concatMap aIds es
-- XXX AMethCall/AMethValue shouldn't exist
-- aIds (AMethCall _ i m []) = [(vMethId i m 1 MethodResult M.Empty)]
-- aIds (AMethCall _ _ _ es) = concatMap aIds es
-- aIds (AMethValue _ i m)   = [(vMethId i m 1 MethodResult M.Empty)]
aIds (ANoInlineFunCall _ _ _ es)  = concatMap aIds es
aIds (AFunCall _ _ _ _ es) = concatMap aIds es
aIds (ASPort _ i)         = [vId i]
aIds (ASParam _ i)        = [vId i]
aIds (ASDef _ i)          = [vId i]
aIds (ASInt _ _ _)        = []
aIds (ASStr _ _ _)        = []
aIds (ASAny _ _)          = []
aIds _                    = internalError("Unexpected pattern in AVerilog::aIds" ) ;


-- ==============================

-- replace non v95 task with their name enclosed in a comment
vCommentTaskName :: VConvtOpts -> String -> String
vCommentTaskName vco s | vco_v95 vco && elem s (vco_v95_tasks vco) = " /*" ++ s ++ "*/ "
                       | otherwise = s

-- create a Verilog DPI/VPI task name from a foreign function name
-- XXX When using DPI, if any types are poly, use the wrapper name
vNameToTask :: Bool -> String -> String
vNameToTask True  s = s
vNameToTask False s = "$imported_" ++ s


-- ==============================
