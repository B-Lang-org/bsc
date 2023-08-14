module SimBlocksToC ( simBlocksToC
                    , SBMap
                    , mkSchedName
                    ) where

import Data.List(nub, (\\), find, genericLength, sortBy, groupBy)
import Data.List.Split(wordsBy)
import Data.Maybe(catMaybes, isJust, fromJust)
import Data.Function(on)
import Control.Monad.State(runState)
import System.Time -- XXX: in old-time package
import qualified Data.Map as M

import ErrorUtil(internalError)
import Flags
import Id(getIdString, getIdQual, getIdQualString, unQualId)
import SimCCBlock
import ASyntax
import ASyntaxUtil(exprForeignCalls,actionForeignCalls)
import ForeignFunctions
import FileNameUtil(mkCxxName, mkHName)
import FStringCompat(mkFString)
import CCSyntax
import Wires(ClockDomain)
import VModInfo(vName_to_id)
import PPrint(ppReadable) -- hiding (int, char)
import Util(concatMapM, mapFst, mapSnd)
import SimFileUtils(codeGenOptionDescr)
import TopUtils(TimeInfo(..))
import Version(versionname)
import BuildVersion(buildVersion)

-- import Debug.Trace

-- Create many .cxx and .h files from the entire list of SimCCBlocks
-- and SimCCScheds.  The blocks are grouped by module, the schedules
-- cut across all modules.
simBlocksToC :: Flags -> TimeInfo -> SBId ->
                (Maybe String) -> (Maybe String) ->
                SBMap -> ForeignFuncMap ->
                [String] -> [SimCCBlock] -> [SimCCSched] ->
                [SimCCClockGroup] -> SimCCGateInfo ->
                (String -> String -> IO String) -> IO [String]
simBlocksToC flags time top_block def_clk def_rst
             sb_map ff_map reused mod_blocks scheds
             clk_groups gate_info writeFileC = do
    let sub_ids = [ i | sb <- M.elems sb_map, (i, _, _) <- sb_state sb ]
        top_mod_id = find (not . isPrimBlock) ((M.keys sb_map) \\ sub_ids)
        -- Build up a structure to map a module block id and the signal name
        -- within that block to the clock domain on which that signal is written.
        -- Since the Ids can be both in the port and def namespace, they are encoded as a pair
        -- "Bool,Id").
        matchesInst i1 = \(i2,_) -> q1' == getIdQual i2
          where q1  = getIdQualString i1
                q1' = mkFString $ if q1 == "top" then "" else drop 4 q1
        lookupDom (c,i) clk_groups =
            do (SimCCClockGroup _ ds) <- find (\g -> aclock_osc (grp_canonical g) == c) clk_groups
               (_,d) <- find (matchesInst i) ds
               return d
        maps = [ M.singleton sbid [(fromJust d, nub (mapSnd unQualId ids_in_instance))]
               | (SimCCSched clk _ fn _) <- scheds
               -- all Ids written in this schedule function
               , let ids_written = concatMap defs_written (sf_body fn)
               -- sorted and grouped based on their instance qualifier
               , let sorted_ids = sortBy (compare `on` (getIdQual . snd)) ids_written
               , ids_in_instance <- groupBy ((==) `on` (getIdQual . snd)) sorted_ids
               -- find the Id of the module block for this instance
               , let inst_name = getIdQualString $ snd (head ids_in_instance)
               , let sbid = lookupInstance sb_map top_mod_id inst_name
               -- lookup the clock domain for this clock in this instance
               , let i = snd (head ids_in_instance)
               , let d = lookupDom (clk,i) clk_groups
               , isJust d
               ]
        -- put the maps together into a single map pairing:
        -- module Id with a map from signal Id to its clock
        clk_list = [ (fromJust m, M.fromList (map (\i->(i,d)) ids))
                   | (m, xs) <- M.toList $ M.unionsWith (++) maps
                   , isJust m
                   , (d, ids) <- xs
                   ]
        clk_map = M.fromListWith (M.union) clk_list
        wdef_mod_map =
            M.fromList
            [ (sb_id sb, wide_defs) |
                  sb <- mod_blocks,
                  let defs = sb_publicDefs sb ++ sb_privateDefs sb,
                  let ports = [ (t,vName_to_id vn) | (t,_,vn) <- sb_methodPorts sb ],
                  let wide_defs = map snd $ filter isWideDef (defs ++ ports) ]
        wdef_inst_map =
            M.fromList
            [ (inst, wide_defs) |
                  (inst, mod) <- mkInstanceMap sb_map top_block,
                  let wide_defs = M.findWithDefault [] mod wdef_mod_map ]

    let cvtModBlock = convertModuleBlock flags sb_map ff_map clk_map wdef_mod_map reused top_block
    module_names <- concatMapM (cvtModBlock writeFileC) mod_blocks
    schedule_names <- convertSchedules flags time top_block def_clk def_rst sb_map ff_map
                                       wdef_inst_map scheds clk_groups gate_info writeFileC
    return $ module_names ++ schedule_names

lookupInstance :: SBMap -> Maybe SBId -> String -> Maybe SBId
lookupInstance _ Nothing _ = Nothing
lookupInstance sb_map (Just top_id) s =
  let path = wordsBy (=='.') s
  in case path of
       ("top":rest) -> helper rest top_id
       otherwise    -> Nothing
  where helper []     i = Just i
        helper (p:ps) i =
          case M.lookup i sb_map of
            (Just sb) -> case find (\(_,x,_) -> getIdString x == p) (sb_state sb) of
                           (Just (i',_,_)) -> helper ps i'
                           Nothing         -> Nothing
            Nothing   -> Nothing

-- Given a top block Id, it makes a list of pairs of (inst,mod)
-- qualified with "top"
mkInstanceMap :: SBMap -> SBId -> [(String, SBId)]
mkInstanceMap sb_map i =
  let addInstQual i "" = i
      addInstQual i s  = i ++ "." ++ s
      mkMap :: SBId -> [(String, SBId)]
      mkMap i =
          case (M.lookup i sb_map) of
              Nothing -> [("",i)]
              Just sb ->
                  let mkSubs (mod, inst, _) =
                          mapFst (addInstQual (getIdString inst)) (mkMap mod)
                  in  [("",i)] ++ concatMap mkSubs (sb_state sb)
  in  mapFst (addInstQual "top") (mkMap i)

-- Test if a SimCCBlock or SimCCFn calls a foreign function
fnCallsForeignFn :: SimCCFn -> Bool
fnCallsForeignFn fn = (any makesForeignCall (sf_body fn))
  where makesForeignCall (SFSDef _ _ Nothing)      = False
        makesForeignCall (SFSDef _ _ (Just expr))  =
          not (null (exprForeignCalls expr))
        makesForeignCall (SFSAssign _ _ expr)    =
          not (null (exprForeignCalls expr))
        makesForeignCall (SFSAction act)         =
          not (null (actionForeignCalls act))
        makesForeignCall (SFSAssignAction _ _ act _) =
          not (null (actionForeignCalls act))
        makesForeignCall (SFSRuleExec _)         = False
        makesForeignCall (SFSCond expr ts fs)    =
          (not (null (exprForeignCalls expr))) ||
          (any makesForeignCall (ts ++ fs))
        makesForeignCall (SFSMethodCall _ _ args)  =
          not (null (concatMap exprForeignCalls args))
        makesForeignCall (SFSFunctionCall _ _ args) =
          not (null (concatMap exprForeignCalls args))
        makesForeignCall (SFSResets stmts)       =
          (any makesForeignCall stmts)
        makesForeignCall (SFSReturn Nothing)     = False
        makesForeignCall (SFSReturn (Just expr)) =
          not (null (exprForeignCalls expr))
        makesForeignCall (SFSOutputReset _ expr) =
          not (null (exprForeignCalls expr))

blockCallsForeignFn :: SimCCBlock -> Bool
blockCallsForeignFn block =
    (any fnCallsForeignFn (get_rule_fns block))   ||
    (any fnCallsForeignFn (get_method_fns block)) ||
    (any fnCallsForeignFn (sb_resets block))

modName :: SimCCBlock -> String
modName sb = fst (sb_naming_fn sb [])

schedCallsForeignFn :: SimCCSched -> Bool
schedCallsForeignFn sched = fnCallsForeignFn (sched_fn sched)

-- Convert the block for a module into .cxx and .h files
convertModuleBlock :: Flags -> SBMap -> ForeignFuncMap ->
                       M.Map SBId (M.Map (Bool,AId) ClockDomain) ->
                       M.Map SBId [AId] -> [String] -> SBId ->
                       (String -> String -> IO String)-> SimCCBlock ->
                       IO [String]
convertModuleBlock flags sb_map ff_map clk_map wdef_mod_map reused top_blk writeFileC sb = do
    let name = sb_name sb
        dom_map = M.findWithDefault M.empty (sb_id sb) clk_map
        wide_defs = M.findWithDefault [] (sb_id sb) wdef_mod_map
        wdef_inst_map = M.fromList [("", wide_defs)]
        uses_foreign_fn = blockCallsForeignFn sb
        is_top = (sb_id sb) == top_blk

        -- list of subblocks that need to be included
        include_ids = nub (map (\(id,_,_)->id) (sb_state sb))

        -- class declaration (for the H file)
        class_decl = simCCBlockToClassDeclaration sb_map sb

        -- method definitions (for the CXX file)
        (method_defs, state) =
            runState (simCCBlockToClassDefinition sb_map dom_map sb)
                     (initialState ff_map wdef_inst_map (unSpecTo flags))
        lit_defs = mkLiteralDecls (nub (literals state))
        str_defs = mkStringDecls (M.toList (str_map state))
        class_defs = lit_defs ++ str_defs ++ method_defs
    if (name `elem` reused)
    then return [] -- don't generate any files for reused blocks
    else mkCxxAndH flags sb_map name uses_foreign_fn is_top
                   ( include_ids
                   , [class_decl]
                   , class_defs
                   )
                   writeFileC

-- Convert the schedule and reset functions into .cxx and .h files
convertSchedules :: Flags -> TimeInfo -> SBId ->
                    (Maybe String) -> (Maybe String) ->
                    SBMap -> ForeignFuncMap -> M.Map String [AId] ->
                    [SimCCSched] -> [SimCCClockGroup] -> SimCCGateInfo ->
                    (String -> String -> IO String) -> IO [String]
convertSchedules flags creation_time top_id def_clk def_rst sb_map ff_map
                 wdef_map scheds clk_groups gate_info writeFileC = do
    let ids      = []
        top_blk  = lookupSB sb_map top_id
        top_inst = (modName top_blk) ++ "_instance"

        model_includes = [ cpp_include "bs_model.h"
                         , cpp_include $ (modName top_blk) ++ ".h" ]

        -- declaration of the model class, named for the top module
        model_name = pfxModel ++ (modName top_blk)
        inst = mkVar ((modName top_blk) ++ "_instance")
        inst_decl = [ comment "Top-level module instance" $
                      private $
                      [ decl $ ptr . (moduleType top_blk []) $ inst ] ]
        sim_hdl_decl = [ comment "Handle to the simulation kernel" $
                         private $
                         [ decl $ userType "tSimStateHdl" $ mkVar "sim_hdl" ] ]
        ctor_decl = [ comment "Constructor" $
                      public $
                      [ decl $ ctor (mkVar model_name) [] ] ]
        kernel_fns_decl =
            [ comment "Functions required by the kernel" $
              public $
              [ decl $ function void (mkVar "create_model")
                           [ (userType "tSimStateHdl") (mkVar "simHdl")
                           , bool (mkVar "master") ]
              , decl $ function void (mkVar "destroy_model") []
              , decl $ function void (mkVar "reset_model")
                           [ bool (mkVar "asserted") ]
              , decl $ function void (mkVar "get_version")
                           [ (ptr . ptr . constant . char) (mkVar "name")
                           , (ptr . ptr . constant . char) (mkVar "build") ]
              , decl $ function (userType "time_t") (mkVar "get_creation_time") []
              , decl $ function (ptr . void) (mkVar "get_instance") []
              , decl $ function void (mkVar "dump_state") []
              , decl $ function void (mkVar "dump_VCD_defs") []
              , decl $ function void (mkVar "dump_VCD")
                           [ (userType "tVCDDumpType") (mkVar "dt") ]
              ]
            ]
        class_decl =
            [ comment ("Class declaration for a model of " ++
                       modName top_blk) $
              c_class model_name (Just "Model") $
                      concat [ inst_decl
                             , sim_hdl_decl
                             , ctor_decl
                             , kernel_fns_decl
                             ]
            ]

        -- abstract the model constructor
        new_fn_proto =
            function (ptr . void) (mkVar ("new_" ++ model_name)) []
        new_fn_decl =
            [ comment "Function for creating a new model" $
              externC [decl $ new_fn_proto]
            ]

        new_fn_def =
            [ comment "Function for creating a new model" $
              define new_fn_proto
                (block
                 [ decl $ (ptr . userType model_name) $
                            (mkVar "model") `assign`
                                (new (classType model_name) (Just []))
                 , ret $ Just (cCast (ptrType voidType) (var "model")) ]
                 )
            ]

        -- model constructor
        mkScopedVar s = mkVar (model_name ++ "::" ++ s)
        ctor_def = [ comment "Constructor" $
                     define (ctor (mkScopedVar model_name) [])
                            (block $ [ inst `assign` mkNULL ])
                   ]

        -- definitions of the schedule functions
        (sch_fn_lists,state) =
            runState (mapM (simCCScheduleToFunctionDefinition top_blk) scheds)
                     (initialState ff_map wdef_map (unSpecTo flags))
        sched_fns = [comment "Schedule functions" (blankLines 1)] ++
                    concat sch_fn_lists

        -- wide literals used in the methods
        meth_lits = mkLiteralDecls (nub (literals state))

        str_lits = mkStringDecls (M.toList (str_map state))

        -- include files needed for kernel callbacks, etc.
        uses_foreign = any schedCallsForeignFn scheds
        kernel_includes =
                  [ cpp_system_include "cstdlib"
                  , cpp_system_include "time.h"
                  , cpp_include "bluesim_kernel_api.h"
                  , cpp_include "bs_vcd.h"
                  , cpp_include "bs_reset.h"
                  , blankLines 1 ]

        -- calls for declaring clocks
        declare_clk_name grp =
          let name = mkClkName (aclock_osc (grp_canonical grp))
          in  stmt $ (var "bk_get_or_define_clock") `cCall` [ var "sim_hdl", mkStr name ]

        -- calls for setting up clock waveforms
        set_waveform clk_name init_val has_init first_edge hi lo =
          let val_enum = if (init_val /= (0 :: Integer))
                         then var "CLK_HIGH"
                         else var "CLK_LOW"
          in stmt $ (var "bk_alter_clock") `cCall`
                      [ var "sim_hdl"
                      , (var "bk_get_clock_by_name") `cCall` [ var "sim_hdl", mkStr clk_name ]
                      , val_enum
                      , mkBool has_init
                      , mkUInt64 first_edge
                      , mkUInt64 lo
                      , mkUInt64 hi
                      ]

        -- calls for setting up initial reset
        setup_reset = stmt $ (var "bk_use_default_reset") `cCall` [ var "sim_hdl" ]

        -- calls for setting clock names
        set_clk_name grp =
          let name = mkClkName (aclock_osc (grp_canonical grp))
          in map (helper name) (grp_instances grp)
          where helper nm (aid,dom) =
                  let fn   = mkSetClkFnName dom
                      -- given an Id which has an empty base and possibly an
                      -- instance for the qualifier, make the instance name
                      s = concatMap (++".") (fst (adjustInstQuals aid))
                      meth = if (null s) then fn else s ++ fn
                  in stmt $ (var top_inst) `cArrow` meth `cCall` [ mkStr nm ]

        -- calls for registering clock schedules
        -- Note: the argument list must match the
        -- declaration in sim/bluesim_kernel_api.h and
        -- implementation in sim/kernel.cxx
        register_clk sched =
          let clk        = sched_clock sched
              clk_name   = mkClkName clk
              is_posedge = sched_posedge sched
              dir_enum   = if is_posedge
                           then var "POSEDGE"
                           else var "NEGEDGE"
              after_edge_sched =
                  case (sched_after_fn sched) of
                    Nothing -> mkNULL
                    (Just f) -> var (mkSchedName (clk, is_posedge, True))
          in stmt $ (var "bk_set_clock_event_fn") `cCall`
                      [ var "sim_hdl"
                      , (var "bk_get_clock_by_name") `cCall` [ var "sim_hdl", mkStr clk_name ]
                      , (var (mkSchedName (clk, is_posedge, False)))
                      , after_edge_sched
                      , (classType "tEdgeDirection") `cCast` dir_enum
                      ]

        -- calls for setting clock gate pointers
        set_gate_ptr (inst, ginfo) =
            map (uncurry (mkGateAssign top_inst inst)) ginfo

        gate_lits =
            let any_true = any (any ((== (Left True)) . snd) . snd) gate_info
                any_false = any (any ((== (Left False)) . snd) . snd) gate_info
            in
                if (any_true || any_false)
                then [ comment "Constant gate declarations" (blankLines 0)]
                     ++ (if any_true then [mkGateConst True] else [])
                     ++ (if any_false then [mkGateConst False] else [])
                else []

        -- functions for creating, destroying and resetting the model
        create_model_decl  = function void (mkScopedVar "create_model")
                                 [ (userType "tSimStateHdl") (mkVar "simHdl")
                                 , bool (mkVar "master") ]
        destroy_model_decl = function void (mkScopedVar "destroy_model") []
        reset_model_decl   = function void (mkScopedVar "reset_model")
                                 [ bool $ mkVar "asserted" ]
        get_instance_decl  = function (ptr . void) (mkScopedVar "get_instance") []

        newInst sb   = let inst = mkVar ((modName sb) ++ "_instance")
                           new_expr = new (classType (pfxMod ++ (modName sb)))
                                          (Just [var "sim_hdl", mkStr "top", mkNULL])
                       in inst `assign` new_expr
        deleteInst sb = let nm = (modName sb) ++ "_instance"
                        in [ stmt $ delete (var nm)
                           , (mkVar nm) `assign` mkNULL
                           ]
        resetInst sb = let nm = (modName sb) ++ "_instance"
                           arg = cTernary (var "asserted") (mkBit 0) (mkBit 1)
                       in [ stmt $ ((var nm) `cArrow` meth) `cCall` [arg]
                          | rst <- sb_inputResets sb
                          , let meth = mkResetFnName rst
                          ]

        setup_clk_and_rst = (case def_clk of
                               (Just name) -> [ set_waveform name
                                                             0
                                                             False
                                                             0
                                                             5
                                                             5
                                              ]
                               Nothing     -> []) ++
                            (case def_rst of
                               (Just _) -> [ setup_reset ]
                               Nothing  -> [])
        create_model_def =
          define create_model_decl
                 (block $ -- record the sim state handle
                          [ (mkVar "sim_hdl") `assign` (var "simHdl") ] ++
                          -- clear reset counters
                          [ stmt $ (var "init_reset_request_counters") `cCall`
                                     [ var "sim_hdl" ] ] ++
                          -- allocate top module instance
                          [ newInst top_blk ] ++
                          -- declare clock names (which creates handles)
                          (map declare_clk_name clk_groups) ++
                          -- if master, setup default clock and reset
                          [ if_cond (var "master")
                                    (block setup_clk_and_rst)
                                    Nothing ] ++
                          -- register schedule callbacks
                          (map register_clk scheds) ++
                          -- tell mods what their clocks are
                          (concatMap set_clk_name clk_groups) ++
                          -- tell mods what their clock gates are
                          concatMap set_gate_ptr gate_info
                 )

        destroy_model_def =
          define destroy_model_decl
                 (block $ -- delete top module instance
                          (deleteInst top_blk)
                 )

        reset_model_def =
          define reset_model_decl
                 (block $ -- call reset functions for top module instance
                          (resetInst top_blk)
                 )

        get_instance_def =
          let inst_name = (modName top_blk) ++ "_instance"
          in define get_instance_decl
                    (block $ -- return pointer to model instance
                             [ret (Just (var inst_name))]
                    )

        model_methods = [comment "Model creation/destruction functions" (blankLines 1)] ++
                        [ create_model_def
                        , destroy_model_def
                        , reset_model_def
                        , get_instance_def
                        ]


        -- functions for getting the version information and creation time
        get_version = function void
                               (mkScopedVar "get_version")
                               [ ptr . ptr . constant . char $ (mkVar "name")
                               , ptr . ptr . constant . char $ (mkVar "build")
                               ]
        mk_version_str s = let vs = if showVersion flags then s else ""
                           in  if vs == "" then mkNULL else mkStr vs
        model_version_name  = mk_version_str versionname
        model_version_build = mk_version_str buildVersion
        gv_def =
          define get_version
                 (block [ stmt (cDeref (var "name"))  `assign` model_version_name
                        , stmt (cDeref (var "build")) `assign` model_version_build
                        ])

        get_creation_time = function (userType "time_t")
                                     (mkScopedVar "get_creation_time")
                                     []
        (TimeInfo _ clock_time@(TOD t _)) = if (timeStamps flags)
                                            then creation_time
                                            else TimeInfo 0 (TOD 0 0)
        time_str = calendarTimeToString (toUTCTime clock_time)
        gct_def = define get_creation_time
                         (comment time_str (ret (Just (mkUInt64 t))))
        version_methods = [ comment "Fill in version numbers" gv_def
                          , comment "Get the model creation time" gct_def
                          ]

        -- functions for dumping state values and rule firings
        state_dump    = function void (mkScopedVar "dump_state") []
        mkDumpCall sb fn_name args =
          let inst = var ((modName sb) ++ "_instance")
          in stmt $ ((inst `cArrow` fn_name) `cCall` args)
        state_dump_def = define state_dump
                                (block [mkDumpCall top_blk "dump_state" [mkUInt32 0]])
        dump_methods  = [ comment "State dumping function" state_dump_def ]

        -- function for dumping VCDs
        top_backing    = [mkBacking top_blk]
        dump_type      = (userType "tVCDDumpType") (mkVar "dt")
        vcd_depth      = (var "vcd_depth") `cCall` [ var "sim_hdl" ]
        vcd_hdr_proto  = function void (mkScopedVar "dump_VCD_defs") []
        vcd_hdr_def    = define vcd_hdr_proto
                                (block [ mkDumpCall top_blk "dump_VCD_defs"
                                                    [ vcd_depth ]])
        backing_fn sb  = (var ((sb_name sb) ++ "_backing")) `cCall` [ var "sim_hdl" ]
        vcd_proto      = function void (mkScopedVar "dump_VCD") [ dump_type ]
        vcd_def        = define vcd_proto
                                (block [ mkDumpCall top_blk "dump_VCD"
                                                    [ var "dt"
                                                    , vcd_depth
                                                    , backing_fn top_blk
                                                    ]
                                       ])
        vcd_methods = [ comment "VCD dumping functions" (blankLines 0) ] ++
                      top_backing ++ [ vcd_hdr_def, vcd_def ]

        fname = "model_" ++ (modName top_blk)

    mkCxxAndH flags sb_map fname uses_foreign False
              ( ids
              , (model_includes ++ class_decl ++ new_fn_decl)
              , (kernel_includes ++
                 meth_lits ++
                 str_lits ++
                 gate_lits ++
                 ctor_def ++
                 new_fn_def ++
                 sched_fns ++
                 model_methods ++
                 version_methods ++
                 dump_methods ++
                 vcd_methods
                )
              )
              writeFileC

-- Some literals cannot be written inline in the generated C, so they are
-- declared as separate variables at the beginning of the file.
mkLiteralDecls :: [(ASize,Integer)] -> [CCFragment]
mkLiteralDecls [] = [blankLines 0]
mkLiteralDecls lits = [comment "Literal declarations" (blankLines 0)]
                      ++ (concatMap mkLitDecl lits)
                      ++ [blankLines 1]
  where mkLitDecl (sz,val) =
           let name = mkLiteralName sz val
               arr_name = name ++ "_arr";
               arr_words = [ mkUInt32 ((val `div` (2^n))
                                            `mod` (2^(32::Integer)))
                           | n <- [0,32..(sz-1)] ]
               initializer = mkInitBraces arr_words
               arr_decl = constant . array . unsigned . int $
                            (mkVar arr_name) `assign` initializer
               lit_var = constant $
                            (mkVar name) `ofType` (bitsType 65 CTunsigned)
               lit = construct lit_var [mkUInt32 sz, var arr_name]
           in [static $ arr_decl, static $ lit]


-- String literals may have embedded null characters, so we must
-- construct std::strings for them based on their known size.
mkStringDecls :: [(String,Integer)] -> [CCFragment]
mkStringDecls [] = [blankLines 0]
mkStringDecls lits = [comment "String declarations" (blankLines 0)]
                      ++ (map mkStrDecl lits)
                      ++ [blankLines 1]
  where mkStrDecl (s,n) =
           let name = mkStringLiteralName n
               str_var = constant $
                           (mkVar name) `ofType` (classType "std::string")
           in static $ construct str_var [ mkStr s, mkUInt32 (genericLength s) ]

-- Make a function implementing "construct-on-first-use", but
-- specialized for th VCD backing structures
mkBacking :: SimCCBlock -> CCFragment
mkBacking sb =
  let mod_type = moduleType sb []
      fn_name  = (sb_name sb) ++ "_backing"
      fn_proto = function (reference . mod_type) (mkVar fn_name)
                     [ (userType "tSimStateHdl") (mkVar "simHdl") ]
      new_expr = new (classType (pfxMod ++ (modName sb)))
                     (Just [var "simHdl", mkStr "top", mkNULL])
      backing_fn = (var "vcd_set_backing_instance")
      fn_body  = [ static . ptr . mod_type $
                         (mkVar "instance") `assign` mkNULL
                 , if_cond ((var "instance") `cEq` mkNULL)
                           (block [ stmt $ backing_fn `cCall` [ var "simHdl", mkBool True ]
                                  , (mkVar "instance") `assign` new_expr
                                  , stmt $ backing_fn `cCall` [ var "simHdl", mkBool False ]
                                  ]
                           )
                           Nothing
                 , ret (Just (cDeref (var "instance")))
                 ]
  in define fn_proto (block fn_body)

-- Create one .cxx and one .h file, given a list of
-- referenced blocks, class declarations and method definitions.
mkCxxAndH :: Flags -> SBMap -> String -> Bool -> Bool ->
             ([SBId],[CCFragment],[CCFragment]) ->
             (String -> String -> IO String) -> IO [String]
mkCxxAndH flags sb_map name include_foreign is_top (ids,decls,meths) writeFileC = do
  let c_file_name = mkCxxName Nothing "" name
      h_file_name = mkHName Nothing "" name
      c_includes  = [ cpp_include "bluesim_primitives.h"
                    , cpp_include h_file_name ]
      foreign_includes = if include_foreign
                         then [cpp_include "imported_BDPI_functions.h"]
                         else []
      state_files = (catMaybes (nub (map (idToHFile sb_map) ids)))
      h_includes  = [ cpp_include "bluesim_types.h"
                    , cpp_include "bs_module.h"
                    , cpp_include "bluesim_primitives.h"
                    , cpp_include "bs_vcd.h"
                    ] ++
                    (map cpp_include state_files)
      c_fragments = c_includes ++ foreign_includes ++ [blankLines 1] ++ meths
      h_fragments = h_includes ++ [blankLines 1] ++ decls
      c_file_contents = ppReadable $ program c_fragments
      code_gen_option_comment = literal_comment [codeGenOptionDescr flags is_top]
      h_file_contents = ppReadable $ program [ code_gen_option_comment
                                             , protect_header name h_fragments
                                             ]
  h_name_rel <- writeFileC h_file_name h_file_contents
  c_name_rel <- writeFileC c_file_name c_file_contents
  return [ h_name_rel, c_name_rel ]
  where idToHFile sb_map id =
          if isPrimBlock id
          then Nothing
          else Just (sb_name (lookupSB sb_map id) ++ ".h")

-- Extract the name from an expression naming a clock port
mkClkName :: AExpr -> String
mkClkName expr = case expr of
                   ASPort _ i -> getIdString i
                   _ -> internalError ("mkClkName: " ++ ppReadable expr)

-- Make a name for a schedule function given the clock expression,
-- edge direction and whether this is for the edge or after it
mkSchedName :: (AExpr,Bool,Bool) -> String
mkSchedName (expr, is_posedge, after_edge) =
  let dir = (if after_edge then "_after" else "") ++
            (if is_posedge then "_posedge_" else "_negedge_")
      clk_name  = escapeClkName (mkClkName expr)
  in "schedule" ++ dir ++ clk_name

-- remove chars which can't be in a C Id, like '.'
escapeClkName :: String -> String
escapeClkName "" = ""
escapeClkName ('.':cs) = ('_' : escapeClkName cs)
escapeClkName (c:cs)   = (c   : escapeClkName cs)

-- ----------------
