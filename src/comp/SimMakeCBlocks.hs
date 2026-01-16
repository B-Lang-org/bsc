module SimMakeCBlocks ( simMakeCBlocks ) where

import Flags
import PPrint
import ErrorUtil(internalError)
import SimPackage
import SimCCBlock
import SimDomainInfo
import SimBlocksToC(mkSchedName)
import ASyntax
import ASyntaxUtil
import Wires(ResetId, wpClockDomain, wpResets)
import VModInfo
import Pragma
import Prim
import SimPrimitiveModules
import Id
import Position(noPosition)
import FStringCompat(mkFString, concatFString)
import PreStrings(fsUnderscore, fsEmpty)
import SCC(tsort)
import Util

import Data.Maybe(mapMaybe, isJust, fromJust, fromMaybe, maybeToList)
import Data.List(partition, nub, union, find, sortBy, (\\))
import qualified Data.Map as M
import qualified Data.Set as S

-- import Debug.Trace

-- A set of Ids (used in place of lists, for efficiency)
type IdSet = S.Set AId

-- This is a map from SimBlock names to SBId
type NameMap = M.Map String SBId

-- map from module name to its def map
type ModDefMap = M.Map String DefMap

-- map from method names to method port info
type MethMap = M.Map AId ( Maybe VName            -- enable
                         , [(AType, AId, VName)]  -- args
                         , [(AType, VName)]       -- return
                         , Bool                   -- is action
                         , [AId]                  -- rule Ids
                         )

-- map from module name to its method map
type ModMethMap = M.Map String MethMap

-- map from module names to rule method calls
type CallMap = M.Map String [(ARuleId, [AId])]

findModDef :: ModDefMap -> String -> DefMap
findModDef mdmap inst =
    case M.lookup inst mdmap of
        Just def_map -> def_map
        Nothing -> internalError ("SimMakeCBlocks.findModDef: cannot find " ++
                                  ppReadable inst ++ ppReadable mdmap)

findModMeth :: ModMethMap -> String -> MethMap
findModMeth mmmap inst =
    case M.lookup inst mmmap of
        Just meth_map -> meth_map
        Nothing -> internalError ("SimMakeCBlocks.findModMeth: cannot find " ++
                                  ppReadable inst ++ ppReadable mmmap)

-- Used several places to name the top-level instance
top_blk_name :: String
top_blk_name = "top"

-- Create SimCCBlocks and SimCCScheds from a SimSystem.
-- The result will include one SimCCSched for each clock edge
-- with any associated action, and one SimCCBlock for each module.
simMakeCBlocks :: Flags -> SimSystem ->
                  ([SimCCBlock], [SimCCSched], [SimCCClockGroup], SimCCGateInfo, SBId)
simMakeCBlocks flags sim_system =
  let pkg_map  = ssys_packages sim_system
      pkgs     = M.elems pkg_map
      scheds   = ssys_schedules sim_system
      inst_map = ssys_instmap sim_system

      -- map module names to numeric ids (these become the SBIds)
      first_id  = (maximum (map sb_id primBlocks)) + 1
      names = (zip (map getModuleName pkgs) [first_id..]) ++
              (map (\p -> (sb_name p, sb_id p)) primBlocks)
      name_map  = M.fromList names

      -- make a map from module name (as String) to the map for the defs
      -- in that module, so that the scheduler has access to all defs
      full_dmap =
          let mkPair sp = (getIdString (sp_name sp), sp_local_defs sp)
          in  M.fromList (map mkPair pkgs)

      -- make a map from module name (as String) to the map for all methods
      -- in that module, so that the scheduler has access to all methods
      full_mmap =
          let mkPair sp = (getIdString (sp_name sp),
                           M.fromList (mapMaybe (getPortInfo (sp_pps sp)) (sp_interface sp)))
          in  M.fromList (map mkPair pkgs)

      -- ----------
      -- build blocks

      -- build the top package separately
      top_pkg       = fromJust (M.lookup (ssys_top sim_system) pkg_map)
      top_block    = onePackageToBlock flags name_map full_mmap sim_system top_pkg
      top_block_id = sb_id top_block

      -- build the rest
      other_blocks  = [ onePackageToBlock flags name_map full_mmap sim_system pkg
                      | pkg <- pkgs
                      , pkg /= top_pkg
                      ]

      -- ----------
      -- build schedules

      -- methods on the top-level module
      top_methods   = sp_interface top_pkg
      (top_ameths, top_vmeths) = partition aIfaceHasAction top_methods
      top_vmeth_set = S.fromList $ concatMap aIfaceResIds top_vmeths
      top_ameth_set = S.fromList $ map aRuleName $ concatMap aIfaceRules top_ameths

      -- input clocks to the top-level module
      top_gates = [ gate | (AAI_Clock _ (Just gate)) <- sp_inputs top_pkg ]

      -- action methods called in each rule
      method_map = M.fromList $
                   [ ((p_name,m_name), sub_names)
                   | p <- pkgs
                   , let p_name = getModuleName p
                   , let ms = sp_interface p
                   , m <- ms
                   , let m_name = aif_name m
                   , let m_rules = aIfaceRules m
                   , let sub_actions = concatMap arule_actions m_rules
                   , let sub_names = [ (o,m) | (ACall o m _) <- sub_actions ]
                   ]
      getCalls :: String -> AMethodId -> [(AId,AMethodId)]
      getCalls pkg_name mid =
        M.findWithDefault [] (pkg_name, unQualId mid) method_map
      getAllCalls :: SimPackage -> (AId,AMethodId) -> [AId]
      getAllCalls root (mod,mid) =
        case (findSubPkg sim_system root mod) of
          (Just root') -> let p_name = getModuleName root'
                              cs     = getCalls p_name mid
                              locals = [ setIdQualString m (getIdString o) | (o,m) <- cs ]
                              subs   = [ map (addToQual (getIdString o)) (getAllCalls root' (o,m))
                                       | (o,m) <- cs ]
                          in  nub $ locals ++ (concat subs)
          Nothing      -> []
      actionCalls :: SimPackage -> ARule -> [AId]
      actionCalls root r =
        let actions = [ (o,m) | (ACall o m _) <- arule_actions r ]
            locals  = [ setIdQualString m (getIdString o) | (o,m) <- actions ]
            subs    = [ map (addToQual (getIdString o)) (getAllCalls root (o,m))
                      | (o,m) <- actions
                      ]
        in  nub $ locals ++ (concat subs)
      rule_calls = [ (p_name, calls)
                   | p <- pkgs
                   , let p_name = getModuleName p
                   , let calls = [ (arule_id r, actionCalls p r)
                                 | r <- sp_rules p
                                 ] ++
                                 (if (p == top_pkg)
                                  then [ (arule_id r, actionCalls p r)
                                       | r <- concatMap aIfaceRules top_ameths
                                       ]
                                  else [])
                   ]
      call_map = M.fromList rule_calls

      -- get and combine stmt lists for each clock edge
      stmt_infos =
        map (mkScheduleStmts flags
                 top_methods top_vmeth_set top_ameth_set top_gates
                 inst_map full_dmap full_mmap call_map)
            scheds
      stmt_map = M.unionsWith combineStmtGroups stmt_infos

      -- make the SimCCScheds from the stmt pairs in the map
      schedules = mapMaybe mkOneSchedule (M.toList stmt_map)

      -- make the SimCCClockGroups from the schedules
      clock_groups = map mkClockGroup scheds

      -- make the clk gate info
      gate_info = mkGateInfo pkg_map top_gates inst_map scheds

  in ((top_block:other_blocks), schedules, clock_groups, gate_info, top_block_id)

-- Get all of the AIds used by AActions, as well as
-- the AIds used by the defs of those AIds, etc.
getIds :: DefMap -> IdSet -> [AAction] -> IdSet
getIds def_map known [] = known
getIds def_map known (act:acts) =
  let known' = getExprIds False def_map known (aact_args act)
  in getIds def_map known' acts

-- Accumulate AIds used by an expression and its sub-expressions.
-- Recurse into (and count) WILL_FIRE signals if we are in the scheduler
-- Skip them (and don't count them) if we're not
getExprIds :: Bool -> DefMap -> IdSet -> [AExpr] -> IdSet
getExprIds _ _ known [] = known
getExprIds in_sched def_map known ((APrim _ _ _ args):es) =
  getExprIds in_sched def_map known (args ++ es)
getExprIds in_sched def_map known ((AMethCall _ _ _ args):es) =
  getExprIds in_sched def_map known (args ++ es)
getExprIds in_sched def_map known ((ATuple _ elems):es) =
  getExprIds in_sched def_map known (elems ++ es)
getExprIds in_sched def_map known ((ATupleSel _ e _):es) =
  getExprIds in_sched def_map known (e:es)
getExprIds in_sched def_map known ((ANoInlineFunCall _ _ _ args):es) =
  getExprIds in_sched def_map known (args ++ es)
getExprIds in_sched def_map known ((AFunCall _ _ _ _ args):es) =
  getExprIds in_sched def_map known (args ++ es)
-- don't recurse into enable or will fire signals
-- note that we mask the Id property when building the scheduler
-- because we need the will fire definitions there
getExprIds in_sched def_map known ((ASDef _ id):es) =
  if id `S.member` known ||
     isIdWillFire id && not (in_sched)
  then getExprIds in_sched def_map known es
  else let known' = id `S.insert` known
       in case M.lookup id def_map of
         (Just def) -> getExprIds in_sched def_map known' ((adef_expr def):es)
         Nothing    -> getExprIds in_sched def_map known' es
getExprIds in_sched def_map known (_:es) = getExprIds in_sched def_map known es

-- Create the SimCCBlock for a SimPackage
onePackageToBlock :: Flags -> NameMap -> ModMethMap -> SimSystem -> SimPackage -> SimCCBlock
onePackageToBlock flags name_map full_meth_map ss pkg =
  let
      -- ----------
      -- package fields

      class_name       = getModuleName pkg
      modId            = sp_name pkg
      rules            = sp_rules pkg
      iface            = sp_interface pkg
      def_map          = sp_local_defs pkg
      avinst_map       = sp_state_instances pkg
      noinline_insts   = sp_noinline_instances pkg
      method_order_map = sp_method_order_map pkg
      reset_list       = sp_reset_list pkg
      gate_map         = sp_gate_map pkg

      raw_defs   = M.elems def_map
      -- alphabetize the avis, by inst Id
      raw_avis   = let -- Ord on Id is broken, so use cmpIdByName
                       cmpFn a b = fst a `cmpIdByName` fst b
                   in  map snd $ sortBy cmpFn $ M.toList avinst_map

      -- ----------
      -- the SimCCBlock state info

      state      = map (mkState name_map) raw_avis ++
                   map (mkNoInlineState name_map) noinline_insts

      -- ----------
      -- public and private class defs (public defs are all defs needed
      -- to compute CAN_FIRE and WILL_FIRE signals.
      all_defs = map cvtADef raw_defs
      cf_wf_ex = [ ASDef t i
                 | (t,i) <- all_defs
                 , (isFire i)
                 ]
      pub_ids  = getExprIds True def_map S.empty cf_wf_ex
      (pub_defs, pri_defs) = partition ((`S.member` pub_ids).snd) all_defs

      task_defs  = [ aid | d@(ADef aid _ (ATaskValue {}) _) <- raw_defs ]

      -- ----------
      -- instantiation parameters (module arguments)
      arg_defs   =
          let ains = [ (ai, name, isPort vainfo)
                     | (ai, vainfo) <- getSimPackageInputs pkg
                     , not (isClock vainfo || isReset vainfo)
                     , let name = getVArgInfoName vainfo
                     ]
              getType (AAI_Port (_,t)) = t
              getType ai = internalError ("onePackageToBlock: " ++
                                          "unexpected abs input: " ++
                                          ppReadable ai)
          in  [ (getType ai,n,ip) | (ai,n,ip) <- ains ]

      -- ----------
      -- gather all method ports
      meth_map  = findModMeth full_meth_map class_name
      meth_ens  = [ (aTBool, vName_to_id vn, vn)
                  | ((Just vn),_,_,_,_) <- M.elems meth_map
                  ]
      meth_args = concat [ ins | (_,ins,_,_,_) <- M.elems meth_map ]
      meth_rets = [ (rt, n, vn)
                  | (n, (_,_,rts,_,_)) <- M.toList meth_map
                  , (rt,vn) <- rts
                  ]
      ports = meth_ens ++ meth_args ++ meth_rets

      -- ----------
      -- clock domains
      findClkDom aid [] = internalError $ "No domain for clock input: " ++ (ppReadable aid)
      findClkDom aid ((dom,aclks):rest) =
          if aid `elem` [i | (AClock (ASPort _ i) _) <- aclks]
          then dom
          else findClkDom aid rest
      domains = map fst (sp_clock_domains pkg)
      input_clks = [ (osc,dom)
                   | (AAI_Clock osc _) <- sp_inputs pkg
                   , let dom = findClkDom osc (sp_clock_domains pkg)
                   ]

      -- ----------
      -- rule functions

      drs = [ M.singleton clk [(aid,r')]
            | r <- rules
            , let clk = wpClockDomain (arule_wprops r)
            , let aid = aRuleName r
            , let r'  = cvtARule modId def_map method_order_map reset_list r
            ]
      rule_fns = M.toList (M.unionsWith (++) drs)

      -- ----------
      -- method functions

      dms = [ M.singleton clk [(aid, fromJust m')]
            | m <- iface
            , let aid = aif_name m
            , let m' = cvtIFace modId (sp_pps pkg)
                           def_map meth_map method_order_map reset_list m
            , isJust m'
            , let clk = wpClockDomain (aif_props m)
            ]
      method_fns = M.toList (M.unionsWith (++) dms)

      -- ----------
      -- output resets

      -- list of output resets and the AReset they are assigned
      output_resets = [ (rstId, arst) | (AIReset rstId arst _) <- iface ]

      -- find the output resets for a particulart AReset
      findOutputRsts arst = [ rstId | (rstId, arst') <- output_resets,
                                      arst' == arst ]

      -- ----------
      -- reset defs and functions

      rst_defs =  [ (aTBool, ae_objid (areset_wire port))
                  | (_,port) <- reset_list
                  ]

      rst_map :: M.Map AReset [(AId, AId)]
      rst_map =
          let edges = [ (rst, [(modId, portId)])
                          | avi <- raw_avis,
                            (ResetArg rstId, ASReset _ rst) <- getInstArgs avi,
                            -- confirm that the port is connected,
                            -- and get the port name
                            (rstId2, (Just portName, _))
                                <- input_resets (vRst (avi_vmi avi)),
                            rstId2 == rstId,
                            let modId = avi_vname avi,
                            -- XXX we only need the String part of the Id
                            let portId = vName_to_id portName
                      ]
          in  M.fromListWith (++) edges

      findRstMods rst_port = M.findWithDefault [] rst_port rst_map

      -- tuples of:
      --  * the numeric resetId
      --  * the wire name
      --  * the submodules which are reset by this wire
      --  * the output resets which are defined as this wire
      reset_instances =
          [ (rst_id, areset_wire port, findRstMods port, findOutputRsts port)
                | (rst_id, port) <- reset_list ]

      reset_fns = map cvtReset reset_instances

      -- map from reset wire to the source module and output reset Id
      reset_out_ports =
          [ (wire, (mod_id, rst_id))
                | avi <- raw_avis,
                  let mod_id = avi_vname avi,
                  (rst_id, (wire, _, _)) <- getOutputResetPorts avi ]

      -- in case some resets are unused, filter the used resets
      reset_srcs =
          let used_rsts = map snd rst_defs
              isUsed (i, _) = i `elem` used_rsts
          in  filter isUsed reset_out_ports

      -- ----------
      -- names of input resets

      in_resets =
          -- is it overkill to check for ResetArg?
          -- we could just look for AAI_Reset in "sp_inputs pkg"
          [ port_id
              | (AAI_Reset port_id, ResetArg _) <- getSimPackageInputs pkg ]

      -- ----------
      -- Put it all together
      sim_block  = SimCCBlock (M.findWithDefault 0 class_name name_map)
                              class_name
                              (\ args -> (class_name, args))
                              domains
                              state
                              arg_defs
                              rst_defs
                              ports
                              pub_defs
                              pri_defs
                              rule_fns
                              method_fns
                              reset_fns
                              task_defs
                              reset_srcs
                              in_resets
                              (map fst output_resets)
                              input_clks
                              gate_map
  in sim_block

-- Get the name of the SimPackage's module as a String
getModuleName :: SimPackage -> String
getModuleName pkg = getIdBaseString (sp_name pkg)

-- Get the SimCCBlock Id corresponding to a module name
modNameToSBId :: NameMap -> String -> SBId
modNameToSBId map name =
  case M.lookup name map of
     (Just sbid) -> sbid
     Nothing     -> internalError ("unknown block name: " ++ name)

-- Extract the values needed for SimCCBlock state from an AVInst
mkState :: NameMap -> AVInst -> (SBId,AId,[AExpr])
mkState name_map avinst =
  let inst_name = avi_vname avinst
      mod_info  = avi_vmi avinst
      sbid      = modNameToSBId name_map (getVNameString (vName mod_info))
      -- get the instantiation argument exprs
      iarg_pairs = getInstArgs avinst
      -- the only clk/rst, if any, are the defaults.
      -- drop them and only consider the other arguments
      iarg_pairs_no_clk =
          filter (\ (i,e) -> not (isClock i || isReset i) ) iarg_pairs
      -- just the exprs
      iarg_exprs_no_clk = map snd iarg_pairs_no_clk
      -- we do not check whether these exprs are static, because that was
      -- already checked both when generating .ba and when reading back in
  in  (sbid, inst_name, iarg_exprs_no_clk)

mkNoInlineState :: NameMap -> (String, String) -> (SBId, AId, [AExpr])
mkNoInlineState name_map (inst, mod) =
  let -- no position is ok, because we only use this as a lookup into
      -- the sb_map
      inst_name = mkId noPosition (mkFString inst)
      sbid = modNameToSBId name_map mod
      inst_args = []
  in  (sbid, inst_name, inst_args)


-- Convert an ADef into an (AType,AId) pair that is used by SimCCBlock
cvtADef :: ADef -> (AType,AId)
cvtADef (ADef aid ty expr _) = (ty,aid)

-- Convert a list of AActions into a list of SimCCFnStmts,
-- where the list also includes assignments for all
-- definitions used by the actions, and definitions used
-- by those definitions, etc.
-- (Takes a list of additional Ids whose defs should be sorted
-- along with the defs needed for any other values, say for an ActionValue,
-- which is unioned with the defs for the action part.)
cvtActions :: Id -> Id ->
              DefMap -> MethodOrderMap -> IdSet -> [AAction] -> [AId] ->
              [SimCCFnStmt]
cvtActions modId rId def_map method_order_map other_defs acts reset_ids =
  let
      -- get all ids for defs used in the actions
      action_ids = getIds def_map S.empty acts
      -- merge in the other defs (needed for, say, an ActionValue)
      ids = other_defs `S.union` action_ids

      -- get their defs
      defs = map (findDef def_map) (S.toList ids)

      -- order the defs and actions, and convert to statements
      -- XXX is it more efficient to pass in the whole def map,
      -- XXX than have this func make its own map of just the defs used?
      ordered_stmts =
          tsortActionsAndDefs modId rId method_order_map defs acts reset_ids
  in ordered_stmts

-- Convert a rule body into a SimCCFn
cvtARule :: Id -> DefMap -> MethodOrderMap -> [(ResetId, AReset)] ->
            ARule -> SimCCFn
cvtARule modId def_map method_order_map reset_list
         (ARule rId _ _ wp _ acts _ _) =
  let name = getIdBaseString rId
      args = []
      reset_ids = map (ae_objid . areset_wire)
                      (mapMaybe (\n -> lookup n reset_list) (wpResets wp))
      body = cvtActions modId rId
                 def_map method_order_map S.empty acts reset_ids
  in SimCCFn name args Nothing body

-- Convert an interface method body into a SimCCFn
-- Some AIFace variants return Nothing, others
-- build a SimCCFn with the correct name, return type,
-- arguments and body.  As for a rule, the body includes
-- assignments for defs used by the method.
-- The method ports are handled specially, since they exist
-- in the ports sub-structure and may also appear as
-- arguments to the method.
cvtIFace :: Id -> [PProp] ->
            DefMap -> MethMap -> MethodOrderMap -> [(ResetId, AReset)] ->
            AIFace -> Maybe SimCCFn
cvtIFace modId pps def_map meth_map method_order_map reset_list m =
  do let name    = aif_name m
         inputs  = aIfaceArgs m
         args    = [ (t,i) | (i,t) <- inputs ]
         -- always_enabled methods need to forcibly check their ready signal
         -- for situations like gated clocks because we've disabled
         -- all errors when the user lies
         check_rdy ss =
             if ((isAlwaysEn pps name) && (aIfaceHasAction m))
             then -- we have to find the name of the port associated
                  -- with the RDY method
                  let rdy_id = mkRdyId (aif_name m)
                      mport = do (_,_,[(_,vn)],_,_) <- M.lookup rdy_id meth_map
                                 return $ ASPort aTBool (vName_to_id vn)
                 in case mport of
                      (Just prt) -> [SFSCond prt ss []]
                      Nothing    -> internalError ("cvtIFace: failed to locate RDY port "
                                                   ++ "for method " ++
                                                   (ppReadable rdy_id))
             else ss
         body = concatMap arule_actions (aIfaceRules m)
         -- is it enough to look at the method's wire props, not each rule's?
         -- it should be because the evaluator should ensure the entire method
         -- is in a single clock domain
         wp      = aIfaceProps m
         rst_ids = map (ae_objid . areset_wire)
                       (mapMaybe (\n -> lookup n reset_list) (wpResets wp))
     (men, ins, rs, _, ifcrules) <- M.lookup name meth_map
     let prt vn     = vName_to_id vn
         rt         =
              case rs of
                 [(t,_)] -> Just t
                 []      -> Nothing
                 _      -> internalError ("cvtIFace: multiple return values "
                                      ++ "not supported in method "
                                      ++ ppReadable name)
         en_stmts   = maybe [] (\vn -> [SFSAssign True (prt vn) aTrue]) men
         wf_stmts   = map (\i -> SFSAssign False (mkIdWillFire i) aTrue) ifcrules
         in_stmts   = map (\(t,i,vn) -> SFSAssign True (prt vn) (ASPort t i)) ins
         body_stmts =
           case rs of
             [(t,vn)] ->
               -- account for the possible return of an actionvalue result
               let -- the return def
                   ret_def  = aif_value m
                   ret_id   = adef_objid ret_def
                   ret_type = adef_type ret_def
                   -- the port name
                   port_id  = prt vn
                   -- find all the defs needed to compute the return value
                   def_map' = M.insert ret_id ret_def def_map
                   ret_expr = ASDef ret_type ret_id
                   val_ids = getExprIds False def_map' S.empty [ret_expr]
                   -- convert the body to SimCCFnStmts
                   ss = cvtActions modId name
                            def_map' method_order_map val_ids body rst_ids
                   -- find assignments to ret_def and replace with port_id
                   replaceRetDef (SFSAssign _ i e) | (i == ret_id) =
                     (SFSAssign True port_id e)
                   replaceRetDef (SFSAssignAction _ i a t) | (i == ret_id) =
                     (SFSAssignAction True port_id a t)
                   -- the assignment might be guarded by a reset
                   replaceRetDef (SFSCond c ts fs) =
                     (SFSCond c (map replaceRetDef ts) (map replaceRetDef fs))
                   replaceRetDef s = s
                   ss' = map replaceRetDef ss
                   -- at the end of the method, return the port value
                   ret_stmts = [ SFSReturn (Just (ASPort t port_id)) ]
               in
                   -- XXX This returns the stale port value in the case when
                   -- and always-enabled ActionValue method is called and its
                   -- ready is off (the user lied about it being always_en'd),
                   -- but, at that point, all bets are off anyway
                   check_rdy ss' ++ ret_stmts
             [] -> check_rdy $
                        cvtActions modId name
                            def_map method_order_map S.empty body rst_ids
             -- TODO: Support methods with multiple return values
             _ -> internalError ("cvtIFace: multiple return values "
                                  ++ "not supported in method "
                                  ++ ppReadable name)
         all_stmts  = concat [en_stmts, wf_stmts, in_stmts, body_stmts]
     return $ SimCCFn (getIdBaseString name) args rt all_stmts

cvtReset :: (ResetId, AExpr, [(AId,AId)], [AId]) -> SimCCFn
cvtReset (rst_num, port, inst_ports, output_resets) =
  let rstval_id  = mk_homeless_id "rst_in"
      rstval_ref = ASPort aTBool rstval_id
      body    = [ SFSAssign True (ae_objid port) rstval_ref ] ++
                [ SFSFunctionCall inst (mkResetFnName rst) [rstval_ref]
                      | (inst, rst) <- inst_ports ] ++
                [ SFSOutputReset outRstId rstval_ref
                      | outRstId <- output_resets ]
  in  SimCCFn (mkResetFnName (ae_objid port))
              [(aTBool, rstval_id)] Nothing body

-- Create the assignment for a def
mkDefAssign :: ADef -> SimCCFnStmt
mkDefAssign (ADef id _ expr _) = SFSAssign False id expr

buildEnWFZeroStmts :: [(Maybe AId,[AId])] -> [SimCCFnStmt]
buildEnWFZeroStmts xs =
    concat [ en_stmts ++ wf_stmts
           | (men,wfs) <- xs
           , let en_stmts = map (assign True) (maybeToList men)
           , let wf_stmts = map (assign False) wfs
           ]
  where assign is_port i= addScope top_blk_name (SFSAssign is_port i aFalse)

doTickCall :: Bool -> InstModMap -> (AId, (AId,AClock)) ->
              Maybe (AClock, [(AId,AId,[AExpr])])
doTickCall is_posedge inst_map (inst_id, (port, clk)) =
  let inst_name = getIdString inst_id
      port_name = getIdBaseString port
      prim_type = case M.lookup inst_name inst_map of
                    (Just t) -> t
                    Nothing  -> internalError $ "unknown instance: " ++ inst_name
      prim_entry = find (\(n,_,_,_) -> (n == prim_type)) primMap
      tick_list =
        case prim_entry of
          (Just (_,_,_,l)) -> if is_posedge
                              then filter tickIsPos l
                              else filter tickIsNeg l
          Nothing  -> internalError $ "unknown primitive: " ++ prim_type
      port_tick = find (\t -> (tickElem t) == port_name) tick_list
  in case port_tick of
       (Just (Both _)) -> Just (clk, [(inst_id, port, [aSBool is_posedge])])
       (Just (Pos _))  -> Just (clk, [(inst_id, port, [aTrue])])
       (Just (Neg _))  -> Just (clk, [(inst_id, port, [aFalse])])
       Nothing         -> Nothing

buildTickStmts :: Bool -> InstModMap -> [(AId, (AId,AClock))] -> [SimCCFnStmt]
buildTickStmts is_posedge inst_map prims =
  let ticks = mapMaybe (doTickCall is_posedge inst_map) prims
      sorted_ticks = sortTickCalls ticks
  in  concatMap mkTickStmt sorted_ticks

sortTickCalls :: [(AClock, [(AId,AId,[AExpr])])] ->
                 [(AClock, [(AId,AId,[AExpr])])]
sortTickCalls ticks =
  let
      -- join ticks for the same clock
      grouped_ticks_map = M.fromListWith (++) ticks

      findCalls clk =
          case (M.lookup clk grouped_ticks_map) of
              Just calls -> (clk, calls)
              Nothing -> internalError ("sortTickCalls: missing from map: " ++
                                        ppReadable clk)

      clocks = M.keys grouped_ticks_map
      -- map from a gate to its clock
      clock_map =
          let mkEdge clk = case (aclock_gate clk) of
                               (AMGate _ modId _) -> Just (modId, [clk])
                               (ASPort _ objId)   -> Just (mk_homeless_id (getIdQualString objId), [clk])
                               _ -> Nothing
              es = mapMaybe mkEdge clocks
          in  M.fromListWith (++) es

      -- for a set of ticks, find the Ids of the submods that are ticked
      getModIds calls = map fst3 calls

      -- make the tsort edges
      mkEdge (clk, calls) =
          let mods = getModIds calls
              clocks = concat (mapMaybe (\i -> M.lookup i clock_map) mods)
          in  (clk, clocks)
      edges = map mkEdge (M.toList grouped_ticks_map)
  in  case (tsort edges) of
        Left is -> internalError ("sortTickCalls: cyclic " ++ ppReadable is)
        Right is -> map findCalls (reverse is)

-- map from an edge of a clock expression to schedule stmts, tick calls, etc.
data SchedStmtGroup = SchedFns { sched_stmts :: [SimCCFnStmt]
                               , sched_ticks :: [SimCCFnStmt]
                               , sched_after :: [SimCCFnStmt]
                               }
type SchedStmtMap = M.Map (TickDirection AExpr) SchedStmtGroup

combineStmtGroups :: SchedStmtGroup -> SchedStmtGroup -> SchedStmtGroup
combineStmtGroups (SchedFns a1 b1 c1) (SchedFns a2 b2 c2) =
    SchedFns (a1 ++ a2) (b1 ++ b2) (c1 ++ c2)

-- Convert a SimSchedule into a map from clock edges to pairs of
-- schedule statements and tick statements.
mkScheduleStmts :: Flags -> [AIFace] -> S.Set AId -> S.Set AId -> [AId] ->
                   InstModMap -> ModDefMap -> ModMethMap -> CallMap ->
                   SimSchedule -> SchedStmtMap
mkScheduleStmts flags top_ifc top_vmeth_set top_ameth_set top_gates
                inst_map full_def_map full_meth_map call_map sim_sched =
  let sched_order = ss_sched_order sim_sched
      disjoint_map = ss_disjoint_rules_db sim_sched
      -- This should be a list of one element
      domain_infos = M.toList (ss_domain_info_map sim_sched)

      clk_expr = aclock_osc (ss_clock sim_sched)

      rules = concatMap (di_rules . snd) domain_infos
      lookupMethods r = do mod   <- M.lookup (getIdQualString r) inst_map
                           calls <- M.lookup mod call_map
                           lookup (unQualId r) calls
      calls_by_rule = M.fromList $
                      [ (r, maybe [] id (lookupMethods r))
                      | r <- (rules ++ (S.toList top_ameth_set)) -- XXX unnecessary conversion
                      ]
      isNotPrimitive q m =
        let inst = if (null q)
                   then getIdQualString m
                   else q ++ "." ++ (getIdQualString m)
        in  case M.lookup inst inst_map of
              (Just x) -> not (isPrimitiveModule x)
              Nothing  -> internalError $ "bad instance: " ++ (ppReadable m)
      non_prim_calls = M.mapWithKey
                        (\r -> (filter (isNotPrimitive (getIdQualString r))))
                        calls_by_rule

      -- partition sched_order into early_sched_order and edge_sched_order
      isEarlyNode (Exec rid)  = rid `elem` (ss_early_rules sim_sched)
      isEarlyNode (Sched rid) = rid `elem` (ss_early_rules sim_sched)
      (early_sched_order, edge_sched_order) = partition isEarlyNode sched_order

      -- build the schedule statements
      sched_ME_inhibits =
          mkMERuleInhibits top_vmeth_set sched_order disjoint_map
      sched_conflicts =
          case (ss_schedule sim_sched) of
            (ASchedule [ASchedEsposito cs] _) -> cs
            (ASchedule as _) ->
                internalError ("mkScheduleStmts: as = " ++ ppReadable as)
      gate_substs = mkGateSubstMap top_gates $
                        concatMap (di_clock_substs . snd) domain_infos
      mkStmt = mkSchedStmts top_ifc top_vmeth_set top_ameth_set
                            inst_map full_def_map non_prim_calls
                            gate_substs sched_conflicts sched_ME_inhibits
      (pos_rule_stmts, neg_rule_stmts) =
          if (ss_posedge sim_sched)
          then (stableOrdNub (concatMap mkStmt edge_sched_order), [])
          else ([], stableOrdNub (concatMap mkStmt edge_sched_order))
      (after_posedge_stmts, after_negedge_stmts) =
          if (ss_posedge sim_sched)
          then (stableOrdNub (concatMap mkStmt early_sched_order), [])
          else ([], stableOrdNub (concatMap mkStmt early_sched_order))

      -- determine all ids used in the schedule
      used_ids = S.fromList $ (concatMap defs_read
                                         (pos_rule_stmts ++ neg_rule_stmts ++
                                          after_posedge_stmts ++ after_negedge_stmts))
      isUsedId i = (i `inlineIdFrom` top_blk_name) `S.member` used_ids

      -- build the enable-zeroing statements
      schedule_rules = [ i | (Exec i) <- edge_sched_order ]
      getMeths r = do ms <- M.lookup r non_prim_calls
                      let inst = getIdQualString r
                          qms = [ addToQual inst m | m <- ms ]
                      return qms
      schedule_methods = stableOrdNub $ concat $ mapMaybe getMeths schedule_rules
      getEnWFPort m =
        do let inst = getIdQualString m
           mod <- M.lookup inst inst_map
           let meth_map = findModMeth full_meth_map mod
           (e,_,_,_,rs) <- M.lookup (unQualId m) meth_map
           let en = do v <- e
                       return $ (vName_to_id v) `inlineIdFrom` inst
               wfs = [ (mkIdWillFire i) `inlineIdFrom` inst | i <- rs ]
               init_port = (keepFires flags) || (any isUsedId ((maybeToList en) ++ wfs))
           if init_port then return (en,wfs) else Nothing

      schedule_enables = mapMaybe getEnWFPort schedule_methods

      (pos_enable_stmts, neg_enable_stmts) =
          if (ss_posedge sim_sched)
          then (buildEnWFZeroStmts schedule_enables, [])
          else ([], buildEnWFZeroStmts schedule_enables)

      -- build the tick statements
      prims = concatMap (di_prims . snd) domain_infos
      pos_tick_stmts = buildTickStmts True inst_map prims
      neg_tick_stmts = buildTickStmts False inst_map prims

      -- build the conditional reset tick stmts
      inst_clk_map = M.fromList [((i,c), ac) | (i,(c,ac)) <- prims]
      addGateInfo (inst,clk) =
          let gate = case M.lookup (inst,clk) inst_clk_map of
                       Just ac ->
                           -- if this is a top-level input, replace with True
                           case (aclock_gate ac) of
                             -- XXX might be cheaper to test that the Id
                             -- XXX qualifier is empty?
                             (ASPort _ portId) | portId `elem` top_gates
                               -> aTrue
                             g -> g
                       Nothing -> internalError $ "mkScheduleStmts: no primitive info for " ++ (ppReadable inst) ++ " with clock " ++ (ppReadable clk)
          in (inst,clk,gate)
      prims_with_reset = concatMap (di_prim_resets . snd) domain_infos
      reset_info = map addGateInfo prims_with_reset
      reset_tick_stmt = mkResetTickStmt reset_info

      -- combine the statements for each edge direction
      pos_stmt_group =
          SchedFns { sched_stmts = pos_enable_stmts ++ pos_rule_stmts
                   , sched_ticks = pos_tick_stmts ++ [reset_tick_stmt]
                   , sched_after = after_posedge_stmts
                   }
      neg_stmt_group =
          SchedFns { sched_stmts = neg_enable_stmts ++ neg_rule_stmts
                   , sched_ticks = neg_tick_stmts
                   , sched_after = after_negedge_stmts
                   }
      edge_stmt_list = [ (Pos clk_expr, pos_stmt_group)
                       , (Neg clk_expr, neg_stmt_group)
                       ]
  in M.fromList edge_stmt_list

-- build a SimCCSched from an edge and sched and tick statement lists
mkOneSchedule :: ((TickDirection AExpr), SchedStmtGroup) -> Maybe SimCCSched
mkOneSchedule (clk, ssg) =
  let clk_expr      = tickElem clk
      is_posedge    = ((Pos clk_expr) == clk)
      fn_name       = mkSchedName (clk_expr, is_posedge, False)
      after_fn_name = mkSchedName (clk_expr, is_posedge, True)
      edge_stmts    = (sched_stmts ssg) ++ (sched_ticks ssg)
      edge_fn       = SimCCFn fn_name [] Nothing edge_stmts
      after_fn      = case (sched_after ssg) of
                        [] -> Nothing
                        xs -> Just $ SimCCFn after_fn_name [] Nothing xs
  in if (null edge_stmts)
     then Nothing
     else Just (SimCCSched { sched_clock    = clk_expr
                           , sched_posedge  = is_posedge
                           , sched_fn       = edge_fn
                           , sched_after_fn = after_fn
                           })

-- build a SimSchedule based on the clocks and instances in a SimSchedule
mkClockGroup :: SimSchedule -> SimCCClockGroup
mkClockGroup ss = let aclk  = ss_clock ss
                      insts = concatMap di_domains (M.elems (ss_domain_info_map ss))
                  in SimCCClockGroup aclk insts

mkGateInfo :: PackageMap -> [AId] -> InstModMap -> [SimSchedule] ->
              SimCCGateInfo
mkGateInfo pkg_map top_gates inst_map scheds =
  let
      -- --------------------
      -- The SimSchedule contains a substitution mapping from gates in the
      -- modules (with fully qualified hierarchy) to the real source of the
      -- gate (a primitive, also with fully qualified hierarchy)

      getDomainGateSubsts sched =
          let
              -- This should be a list of one element
              domain_infos = M.toList (ss_domain_info_map sched)
          in
              mkGateSubstMap top_gates $
                  concatMap (di_clock_substs . snd) domain_infos

      -- the full substitution map for the system
      gateSubsts = M.unions (map getDomainGateSubsts scheds)

      -- --------------------
      -- The individual SimBlocks will not have fully qualified hierarchical
      -- names, so we the following functions to add that hierarchy

      qualifyId :: String -> AId -> AId
      qualifyId inst i =
          let q_str = getIdQualString i
              q_str' = if (q_str == "")
                       then inst
                       else inst ++ "." ++ q_str
          in  setIdQualString i q_str'

      qualifyGate :: String -> AExpr -> AExpr
      qualifyGate inst (AMGate t oid cid) =
          (AMGate t (qualifyId inst oid) cid)
      qualifyGate inst (ASPort t g) = (ASPort t (qualifyId inst g))
      qualifyGate inst e | isTrue e = e
      qualifyGate inst e =
          internalError ("qualifyGate: unexpected expr " ++ ppReadable e)

      -- --------------------

      mkOneGateInfo :: String -> (Int, AExpr) -> (Int, Either Bool AId)
      mkOneGateInfo inst (num, gate) =
          let qual_gate = qualifyGate inst gate
          in  case (M.lookup qual_gate gateSubsts) of
                Just (ASPort _ portId) -> (num, Right portId)
                Just gate_expr | isTrue gate_expr -> (num, Left True)
                Just gate_expr | isFalse gate_expr -> (num, Left False)
                Just gate_expr -> internalError
                                      ("mkOneGateInfo: unexpected src: " ++
                                       show gate_expr)
                Nothing ->
                    --internalError ("mkOneGateInfo: " ++ ppReadable qual_gate)
                    -- This occurs if the clock is instantiated with noClock
                    -- XXX Consider eliminating this by having mergeSched
                    -- XXX include info for the noClock domain?
                    (num, Left False) -- XXX True?

      mkGateInfo :: (String, String) ->
                    Maybe (String, [(Int, Either Bool AId)])
      mkGateInfo (inst, mod) =
          let modId = mk_homeless_id mod
          in  case (M.lookup modId pkg_map) of
                Just pkg ->
                    let gate_map = zip [0..] (sp_gate_map pkg)
                    in  Just (inst, map (mkOneGateInfo inst) gate_map)
                _ | isPrimitiveModule mod -> Nothing
                _ -> internalError ("mkGateInfo: " ++ mod ++ "\n" ++
                                    ppReadable (M.keys pkg_map))
  in
      mapMaybe mkGateInfo (M.toList inst_map)

-- apply a binary primitive to a list to reduce it to a singleton
reduce :: PrimOp -> [AExpr] -> [AExpr]
reduce prim []      = []
reduce prim [e]     = [e]
reduce prim [e1,e2] = [APrim dummy_id (ae_type e1) prim [e1,e2]]
reduce prim es      = reduce prim (concatMap (reduce prim) (pairs es))
  where pairs []         = []
        pairs [x]        = [[x]]
        pairs (x:y:rest) = [[x,y]] ++ (pairs rest)

-- functions for adding instance scope to Id qualifiers when inlining
inlineIdFrom :: Id -> String -> Id
inlineIdFrom aid scope = addToQual scope aid

inlineExprFrom :: AExpr -> String -> AExpr
inlineExprFrom expr scope = mapExprIds (`inlineIdFrom` scope) expr

mapExprIds :: (AId -> AId) -> AExpr -> AExpr
mapExprIds fn expr = mapAExprs (aIdFnToAExprFn fn) expr

mapActionIds :: (AId -> AId) -> AAction -> AAction
mapActionIds fn act = mapAActions (aIdFnToAActionFn fn) act

addScope :: String -> SimCCFnStmt -> SimCCFnStmt
-- if the scope is empty, do nothing
addScope "" x = x
addScope scope (SFSDef p (ty,aid) (Just v)) =
  let aid' = aid `inlineIdFrom` scope
      v'   = v `inlineExprFrom` scope
  in SFSDef p (ty, aid') (Just v')
addScope scope (SFSDef p (ty,aid) Nothing) =
  let aid' = aid `inlineIdFrom` scope
  in SFSDef p (ty, aid') Nothing
addScope scope (SFSAssign p aid v) =
  let aid' = aid `inlineIdFrom` scope
      v'   = v `inlineExprFrom` scope
  in SFSAssign p aid' v'
addScope scope (SFSAction action) =
  SFSAction (mapActionIds (`inlineIdFrom` scope) action)
addScope scope (SFSAssignAction p aid action ty) =
  let aid' = aid `inlineIdFrom` scope
      action' = mapActionIds (`inlineIdFrom` scope) action
  in SFSAssignAction p aid' action' ty
addScope scope (SFSRuleExec rid) =
  let rid'  = rid `inlineIdFrom` scope
  in SFSRuleExec rid'
addScope scope (SFSCond cond ts fs) =
  let cond' = cond `inlineExprFrom` scope
      ts' = map (addScope scope) ts
      fs' = map (addScope scope) fs
  in SFSCond cond' ts' fs'
addScope scope (SFSMethodCall obj meth args) =
  let obj' = obj `inlineIdFrom` scope
      args' = map (`inlineExprFrom` scope) args
  in SFSMethodCall obj' meth args'
addScope scope (SFSFunctionCall obj func args) =
  let obj' = obj `inlineIdFrom` scope
      args' = map (`inlineExprFrom` scope) args
  in SFSFunctionCall obj' func args'
addScope scope (SFSResets stmts) =
  let stmts' = map (addScope scope) stmts
  in SFSResets stmts'
addScope scope (SFSReturn Nothing) = SFSReturn Nothing
addScope scope (SFSReturn (Just v)) =
  let v'  = v `inlineExprFrom` scope
  in SFSReturn (Just v')
-- It is unlikely that scope will be added to an OutputReset, but here it is
addScope scope (SFSOutputReset rstId val) =
  let rstId' = rstId `inlineIdFrom` scope
      val'   = val `inlineExprFrom` scope
  in  SFSOutputReset rstId' val'


-- Create the SimCCFnStmts that correspond to a schedule node
mkSchedStmts :: [AIFace] -> S.Set AId -> S.Set AId -> InstModMap -> ModDefMap ->
                M.Map ARuleId [AId] -> GateSubstMap ->
                [(AId, [AId])] -> M.Map AId [AId] -> SchedNode -> [SimCCFnStmt]
mkSchedStmts top_ifc top_vmeth_set top_ameth_set inst_map full_dmap
             calls_by_rule gate_substs sched_conflicts sched_me_inhibits
             (Sched qual_rid) =
  let method_calls = fromMaybe [] (M.lookup qual_rid calls_by_rule)
  in if (qual_rid `S.member` top_vmeth_set)
     then mkValueMethodSchedStmts top_ifc top_vmeth_set top_ameth_set
                                  inst_map full_dmap
                                  gate_substs sched_conflicts sched_me_inhibits
                                  qual_rid
     else if (qual_rid `S.member` top_ameth_set)
          then mkActionMethodSchedStmts top_ifc top_vmeth_set top_ameth_set
                                        inst_map full_dmap method_calls
                                        gate_substs sched_conflicts
                                        sched_me_inhibits qual_rid
          else mkRuleSchedStmts inst_map full_dmap method_calls
                                gate_substs sched_conflicts sched_me_inhibits
                                qual_rid
mkSchedStmts top_ifc top_vmeth_set top_ameth_set inst_map full_dmap
             calls_by_rule gate_substs sched_conflicts sched_me_inhibits
             (Exec rid) =
  if (rid `S.member` top_vmeth_set)
  then mkValueMethodExecStmts top_ifc top_vmeth_set top_ameth_set
                              inst_map full_dmap
                              gate_substs sched_conflicts sched_me_inhibits
                              rid
  else if (rid `S.member` top_ameth_set)
       then mkActionMethodExecStmts top_ifc top_vmeth_set top_ameth_set
                                    inst_map
                                    full_dmap gate_substs sched_conflicts
                                    sched_me_inhibits rid
       else mkRuleExecStmts top_ifc top_vmeth_set top_ameth_set
                            inst_map full_dmap
                            gate_substs sched_conflicts sched_me_inhibits
                            rid

-- Make statements for determining if a value method is ready
mkValueMethodSchedStmts :: [AIFace] -> S.Set AId -> S.Set AId ->
                           InstModMap -> ModDefMap -> GateSubstMap ->
                           [(AId, [AId])] -> M.Map AId [AId] ->
                           AId -> [SimCCFnStmt]
mkValueMethodSchedStmts top_ifc top_vmeth_set top_ameth_set inst_map full_dmap
                        gate_substs sched_conflicts sched_me_inhibits
                        qual_rid =
  []

-- Make statements for determining if an action method should fire
mkActionMethodSchedStmts :: [AIFace] -> S.Set AId -> S.Set AId ->
                            InstModMap -> ModDefMap -> [AId] -> GateSubstMap ->
                            [(AId, [AId])] -> M.Map AId [AId] ->
                            AId -> [SimCCFnStmt]
mkActionMethodSchedStmts top_ifc top_vmeth_set top_ameth_set inst_map
                         full_dmap method_calls gate_substs
                         sched_conflicts sched_me_inhibits qual_rid =
  let bit_type  = ATBit 1
      wf        = mkIdWillFire qual_rid
      unqual_wf = unQualId wf

      -- The qualifier tells us which submodule instance this rule is in.
      -- Remove the qualifier and use it to get the def_map for the defs
      -- in that module.  Then process the rule unqualified, using that map.
      inst = getIdQualString qual_rid
      modtype = findInstMod inst_map inst
      def_map = findModDef full_dmap modtype

      -- ----------
      -- Get all the defs needed for the WF expr
      ids = S.toList $ getExprIds True def_map S.empty [ASDef bit_type unqual_wf]
      defs = tsortADefs $ map (findDef def_map) ids

      -- ----------
      -- Call the RDY method for top-level methods, since they may check their
      -- RDY port in the method body.
      call_rdy_method = [ SFSMethodCall (setIdBase emptyId (getIdQual qual_rid))
                                        (mkRdyId (unQualId qual_rid))
                                        []
                        ]

      -- ----------
      -- The sub-methods this method calls may need to check their RDY ports
      -- if they are always_ready, so we need to call the RDY method for
      -- any methods which might be called but are not in the WF expr.
      wf_rdys = [ (setIdQualString emptyId (getIdBaseString inst), unQualId rm)
                | (inst,rm) <-
                    -- "aMethCalls" can return duplicates, but that's OK
                    concatMap (aMethCalls . adef_expr) defs
                ]
      meth_rdys = [ (setIdBase m fsEmpty, unQualId (mkRdyId m))
                  | m <- method_calls
                  ]
      rdy_calls = [ addScope inst (SFSMethodCall obj rdy [])
                  | (obj,rdy) <- (nub meth_rdys) \\ wf_rdys
                  ]

      -- ----------
      -- Make the statements
      stmts = (map mkDefAssign defs) ++ call_rdy_method ++ rdy_calls
  in map (addScope top_blk_name) stmts

-- Make statements for determining if a rule should fire
mkRuleSchedStmts :: InstModMap -> ModDefMap -> [AId] ->
                    GateSubstMap -> [(AId, [AId])] -> M.Map AId [AId] ->
                    AId -> [SimCCFnStmt]
mkRuleSchedStmts inst_map full_dmap method_calls
                 gate_substs sched_conflicts sched_me_inhibits
                 qual_rid =
  let bit_type  = ATBit 1
      cf        = mkIdCanFire qual_rid
      wf        = mkIdWillFire qual_rid
      unqual_wf = unQualId wf

      -- The qualifier tells us which submodule instance this rule is in.
      -- Remove the qualifier and use it to get the def_map for the defs
      -- in that module.  Then process the rule unqualified, using that map.
      inst = getIdQualString qual_rid
      modtype = findInstMod inst_map inst
      def_map = findModDef full_dmap modtype

      -- ----------
      -- Get all the defs needed for the WF expr
      ids = S.toList $ getExprIds True def_map S.empty [ASDef bit_type unqual_wf]
      defs = tsortADefs $ map (findDef def_map) ids

      -- ----------
      -- Make the statements
      stmts = map mkDefAssign defs

      -- reintroduce the instance hierarchy to the WF and its defs,
      -- so that the variables referenced are from the proper scope.
      qual_stmts0 = map (addScope inst) stmts

      -- ----------
      -- replace any gate references with the substitute value
      -- (the substs have the full scope, so this step requires that the
      -- defs have had the scope added, as was just done above)
      qual_stmts1 = substGateReferences gate_substs qual_stmts0

      -- ----------
      -- Mutual exclusion inhibitors to be added to the CF
      -- The purpose of this is to deal with the way that Bluesim
      -- performs updates directly.  This can cause 2 rules with
      -- mutually exclusive conditions to be fired together erroneously
      -- if the first rule is schedule and executed, and its execution
      -- makes the predicate of the second rule true.  The "solution"
      -- used here is to explicitly add logic to prevent this case.

      me_inhibitors =
          -- XXX we could take advantage of the fact that the inhibits are
          -- XXX in order, so the lookup should be the top of the list
          case (M.lookup qual_rid sched_me_inhibits) of
              Nothing -> []
              Just is -> is
      inhibit_ids = map mkIdCanFire me_inhibitors
      inhibit_expr = reduce PrimBOr (map (ASDef bit_type) inhibit_ids)
      addInhibitExpr base_expr =
          case inhibit_expr of
              [] -> base_expr
              [cfl] -> let not_inhibit = APrim dummy_id bit_type
                                               PrimBNot [cfl]
                       in  APrim dummy_id bit_type
                                 PrimBAnd [base_expr, not_inhibit]
              _ -> internalError "reduce produced a list of length > 1"

      -- ----------
      -- Update the CF with the inhibitor

      updateCFStmt (SFSAssign p i e) | (i == cf) =
          SFSAssign p i (addInhibitExpr e)
      updateCFStmt d = d
      qual_stmts2 = map updateCFStmt qual_stmts1

      -- ----------
      -- Methods in the rule which are always_ready may need to check
      -- their RDY ports, so we need to call the RDY method for any methods
      -- which might be called but are not in the WF expr.
      wf_rdys = [ (setIdQualString emptyId (getIdBaseString inst), unQualId rm)
                | (inst,rm) <-
                    -- "aMethCalls" can return duplicates, but that's OK
                    concatMap (aMethCalls . adef_expr) defs
                ]
      rl_rdys = [ (setIdBase m fsEmpty, unQualId (mkRdyId m))
                | m <- method_calls
                ]
      rdy_calls = [ addScope inst (SFSMethodCall obj rdy [])
                  | (obj,rdy) <- (nub rl_rdys) \\ wf_rdys
                  ]
  in  -- in addition to the submodule instance hierarchy,
      -- we add the top module instance to all identifiers
      map (addScope top_blk_name) (rdy_calls ++ qual_stmts2)

-- Make statements for computing value method outputs
mkValueMethodExecStmts :: [AIFace] -> S.Set AId -> S.Set AId ->
                          InstModMap -> ModDefMap -> GateSubstMap ->
                          [(AId, [AId])] -> M.Map AId [AId] ->
                          AId -> [SimCCFnStmt]
mkValueMethodExecStmts top_ifc top_vmeth_set top_ameth_set inst_map full_dmap
                       gate_substs sched_conflicts sched_me_inhibits rid =
  []

-- Make statements for executing an action method
mkActionMethodExecStmts :: [AIFace] -> S.Set AId -> S.Set AId ->
                           InstModMap -> ModDefMap -> GateSubstMap ->
                           [(AId, [AId])] -> M.Map AId [AId] ->
                           AId -> [SimCCFnStmt]
mkActionMethodExecStmts top_ifc top_vmeth_set top_ameth_set inst_map full_dmap
                        gate_substs sched_conflicts sched_me_inhibits mid =
  let blk_id = mk_homeless_id top_blk_name
      wf = (mkIdWillFire mid) `inlineIdFrom` top_blk_name
      method = headOrErr ("method not in interface: " ++ (ppReadable mid))
                         [ m | m <- top_ifc, aif_name m == mid ]
      args = [ ASPort t (i `inlineIdFrom` top_blk_name)
             | (i,t) <- aif_inputs method ]
      cond_stmt = SFSCond (ASDef (ATBit 1) wf)
                          [SFSMethodCall blk_id mid args]
                          []
  in [cond_stmt]

-- Make statements for executing a rule
mkRuleExecStmts :: [AIFace] -> S.Set AId -> S.Set AId ->
                   InstModMap -> ModDefMap -> GateSubstMap ->
                   [(AId, [AId])] -> M.Map AId [AId] ->
                   AId -> [SimCCFnStmt]
mkRuleExecStmts top_ifc top_vmeth_set top_ameth_set inst_map full_dmap
                gate_substs sched_conflicts sched_me_inhibits rid =
  let wf = mkIdWillFire rid
      cond_stmt = SFSCond (ASDef (ATBit 1) wf) [SFSRuleExec rid] []
  in map (addScope top_blk_name) [cond_stmt]

-- Create the SimCCFnStmt that corresponds to a group of tick calls
-- for a clock.
mkTickStmt :: (AClock, [(AId,AId,[AExpr])]) -> [SimCCFnStmt]
mkTickStmt (clk, ticks) =
  let gate = aclock_gate clk
      calls = [ SFSFunctionCall obj (getIdBaseString mid) (args ++ [gate])
              | (obj,mid,args) <- ticks
              ]
  in map (addScope top_blk_name) calls

-- Create the SimCCFnStmt that corresponds to a group of reset tick
-- calls for the primitives clocked by a clock.
mkResetTickStmt :: [(AId,AId,AExpr)] -> SimCCFnStmt
mkResetTickStmt prims =
  let mname clk_id  = "rst_tick_" ++ getIdBaseString clk_id
      calls = [ SFSFunctionCall obj (mname clk) [gate]
              | (obj,clk,gate) <- prims
              ]
  in addScope top_blk_name (SFSResets calls)

-- ===============

tsortActionsAndDefs ::
    Id -> Id -> MethodOrderMap -> [ADef] -> [AAction] -> [AId] ->
    [SimCCFnStmt]
tsortActionsAndDefs modId rId mmap ds acts reset_ids =
    let
        -- we will create a graph where the edges are:
        -- * "Left AId" to represent a def (by it's name)
        -- * "Right Integer" to represent an action (by it's position in acts)

        -- The use of Left and Right was chosen to make Defs lower in
        -- the Ord order than Actions.  This way, tsort puts them first.

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

        -- ----------
        -- Actions

        -- give the actions a unique number and make a mapping
        -- (this is necessary because the same action can be repeated
        -- more than once ... for instance, $display on the same arguments)

        -- (numbering in order also helps the Ord order, for tsort)
        numbered_acts = zip [1..] acts
        act_map = M.fromList numbered_acts
        getAct n = case (M.lookup n act_map) of
                       Just d -> d
                       Nothing -> internalError "tsortActionsAndDefs: getAct"

        -- separate the sorts of actions
        -- * method calls we will re-order, respecting sequential composability
        -- * foreign task/function calls we will keep in order, but allow
        --   other things to come between them (because tasks can return
        --   values)

        isACall (_, ACall {}) = True
        isACall _ = False

        isATaskAction (_, ATaskAction {}) = True
        isATaskAction _ = False

        (method_calls, foreign_calls) = partition isACall numbered_acts
        task_calls = filter isATaskAction foreign_calls

        -- ----------
        -- foreign-to-foreign edges
        -- (to maintain the user-specified order of system/foreign-func calls)

        -- (are these still needed now that we use Ord to bias tsort?)
        foreign_edges =
            if (length foreign_calls > 1)
            then let mkEdge (n1,_) (n2,_) = (Right n2, [Right n1])
                 in  zipWith mkEdge (init foreign_calls) (tail foreign_calls)
            else []

        -- ----------
        -- Action to def edges

        -- any defs used by an action have to be computed before the
        -- action is called

        act_def_edges = [ (Right n, map Left uses)
                              | (n,a) <- numbered_acts,
                                let uses = filter (`S.member` s) (aVars a) ]

        -- ----------
        -- Action method to Action method edges

        -- function to create order edges
        --    m1 `isBefore` m2 == True
        --       when (m1 SB m2) is in the VModInfo for the submodule
        isBefore (ACall obj1 meth1 _) (ACall obj2 meth2 _) =
            -- do they act on the same object?
            if (obj1 /= obj2)
            then False
            else let mset = findMethodOrderSet mmap obj1
                 in  (unQualId meth1, unQualId meth2) `S.member` mset
        isBefore _ _ = False

        -- order the method calls
        --   The edges must be of the form (a, as) s.t. all actions in "as"
        --   have to execute before "a".
        meth_edges = [ (Right n1, ns)
                          | (n1,a1) <- method_calls,
                            let ns = [ Right n2 | (n2,a2) <- numbered_acts,
                                                 a2 /= a1,
                                                 a2 `isBefore` a1 ] ]

        -- ----------
        -- ActionValue method edges

        (av_meth_edges, av_meth_set, av_meth_local_vars) =
            mkAVMethEdges ds method_calls

        -- ----------
        -- ActionValue task edges

        -- Make edges from the task to the def that it sets
        -- (ATaskValue is always a top-level def, and the Id is stored
        -- in the ATaskAction by the ATaskSplice stage.)
        -- (Rather than remove the def for the ATaskValue and make edges from
        --  the users of that def to the ATaskAction, we leave the def in
        --  the graph and just generate nothing for it when we make statements
        --  from the flattened graph.)
        av_task_edges =
            [ (Left tmp_id, [Right n]) |
               (n, ATaskAction { ataskact_temp=(Just tmp_id) }) <- task_calls ]

        -- ----------
        -- Action / Value method call edges

        -- like isBefore, but for Action vs Value method
        isVMethSB v_obj v_meth (ACall a_obj a_meth _) =
            -- do they act on the same object?
            if (v_obj /= a_obj)
            then False
            else let mset = findMethodOrderSet mmap v_obj
                 in  (unQualId v_meth, unQualId a_meth) `S.member` mset
        isVMethSB _ _ _ = False

        isAMethSB v_obj v_meth (ACall a_obj a_meth _) =
            -- do they act on the same object?
            if (v_obj /= a_obj)
            then False
            else let mset = findMethodOrderSet mmap v_obj
                 in  (unQualId a_meth, unQualId v_meth) `S.member` mset
        isAMethSB _ _ _ = False

        -- value method calls which are SB with action methods
        -- need to be properly ordered
        --   Edges must be of the form (m1, m2) where the method "m2"
        --   has to be executed before "m1".
        mdef_edges =
            [ edge | ADef i _ e _ <- ds,
                     -- "aMethCalls" can return duplicates, but that's OK
                     (obj,meth) <- aMethCalls e,
                     edge <-
                           -- def SB act
                           [ (Right n, [Left i])
                               | (n,a) <- method_calls,
                                 isVMethSB obj meth a ] ++
                           -- act SB def (XXX can this happen?)
                           [ (Left i, map Right ns)
                               | let ns = map fst $
                                          filter ((isAMethSB obj meth) . snd)
                                              method_calls,
                                 not (null ns) ]
            ]

        -- ----------
        -- put it together into one graph

        g =
{-
            trace ("acts = " ++ ppReadable numbered_acts) $
            trace ("foreign_edges = " ++ ppReadable (foreign_edges :: [Edge])) $
            trace ("av_task_edges = " ++ ppReadable av_task_edges) $
            trace ("av_meth_edges = " ++ ppReadable av_meth_edges) $
            trace ("meth_edges = " ++ ppReadable (meth_edges :: [Edge])) $
            trace ("mdef_edges = " ++ ppReadable mdef_edges) $
            trace ("act_def_edges = " ++ ppReadable (act_def_edges :: [Edge])) $
-}
            M.fromListWith union $ concat [ foreign_edges
                                          , av_task_edges
                                          , av_meth_edges
                                          , meth_edges
                                          , mdef_edges
                                          , act_def_edges
                                          , def_edges
                                          ]

        -- Convert the graph to the format expected by tsort.
        g_edges = M.toList g

        -- ----------
        -- convert a graph node back into a def/action
        -- and then to a SimCCFnStmt

        -- map def ids back to their exprs
        -- (remember to substitute away AMethValue references)
        defmap = M.fromList [ (i,d) | d@(ADef i _ _ _) <- ds ]
        getDef i = case (M.lookup i defmap) of
                       Just d -> (mapAExprs substAV d)
                       Nothing -> internalError "tsortActionsAndDefs: getDef"

        -- function to substitute ASDef for AMethValue
        substAV (AMethValue ty obj meth) = ASDef ty (mkAVMethTmpId obj meth)
        substAV (ATuple ts es) = ATuple ts (map substAV es)
        substAV (ATupleSel t e i) = ATupleSel t (substAV e) i
        substAV (APrim i t o es) = (APrim i t o (map substAV es))
        substAV (AMethCall t o m es) = (AMethCall t o m (map substAV es))
        substAV (AFunCall t o f isC es) = (AFunCall t o f isC (map substAV es))
        substAV e = e

        -- allow statements to be conditional on the rule not being reset
        reset_cond = reduce PrimBOr
                            [ APrim dummy_id aTBool PrimEQ [ASPort aTBool rst_id, aFalse]
                            | rst_id <- reset_ids
                            ]
        addRstCond s =
          case reset_cond of
              []  -> s
              [c] -> [ SFSCond (aNot c) s [] ]
              _   -> internalError "reduce produced a list of length > 1"

        -- defs are SFSAssigns, actions are actions,
        -- actionvalue are assignactions
        -- filter out the ATaskValue defs (see av_task_edges)
        convertNode (Left (ADef _ _ (ATaskValue {}) _)) = Nothing
        convertNode (Left d) = Just [mkDefAssign d]
        convertNode (Right (False,acts)) = Just (map cvt_action acts)
        convertNode (Right (True,acts))  = Just (addRstCond (map cvt_action acts))
        cvt_action a@(ACall obj meth _) =
            case (M.lookup (obj,meth) av_meth_set) of
              Just ty -> SFSAssignAction False (mkAVMethTmpId obj meth) a ty
              Nothing -> SFSAction a
        cvt_action a@(ATaskAction { aact_objid = f_id
                                  , ataskact_temp = maybe_tmp_id
                                  , ataskact_value_type = ty
                                  }) =
            case (maybe_tmp_id) of
              Just tmp_id -> SFSAssignAction False tmp_id a ty
              Nothing     -> SFSAction a
        cvt_action a@(AFCall {}) = SFSAction a

        -- g++ sometimes has a hard time with sequences of conditionals,
        -- so we try to group system tasks, etc. with the same reset
        -- condition into one if block.
        -- It's OK to leave stale values for these when in reset,
        -- since Verilog does as well.
        hasRst (Left _)           = False
        hasRst (Right (ACall {})) = False
        hasRst (Right _)          = True
        groupRsts [] = []
        groupRsts ((Left d):rest) = (Left d):(groupRsts rest)
        groupRsts l@(x@(Right _):_) =
            let rst = hasRst x
                sameRight (Left _) = False
                sameRight r        = hasRst r == rst
                (group,rest) = span sameRight l
            in (Right (rst,[act | (Right act) <- group])):(groupRsts rest)
    in  -- tsort returns Left if there is a loop, Right if sorted.
        -- (In the absence of restrictive edges, tsort uses Ord to put
        -- the lower valued nodes first.  Thus, we have chosen the node
        -- representation to put Defs first, followed by Actions in the
        -- order that they were give by the user.)
        case (tsort g_edges) of
            Left iss ->
                let -- lookup def and action nodes
                    lookupFn = either (Left . getDef) (Right . getAct)
                    xss = map (map lookupFn) iss
                in  internalError ("tsortActionsAndDefs: cyclic: " ++
                                   ppReadable (modId, rId) ++
                                   ppReadable xss)
            Right is ->
                let -- lookup def and action nodes
                    xs = map (either (Left . getDef) (Right . getAct)) is
                    -- group by reset conditions
                    grouped = groupRsts xs
                in -- declare the local temporaries
                   av_meth_local_vars ++
                   -- convert the sorted and grouped nodes
                   concat (mapMaybe convertNode grouped)


-- ----------

type Node = Either AId Integer
type Edge = (Node, [Node])

-- ----------

-- Given the defs and a list of only the action method calls (ACall),
-- returns:
-- * a list of edges between the defs using the value and any
--   ActionValue ACall which is producing the value
-- * a set of the ACall which are action value (mapped to their types)
-- * a list of declarations for the new defs (holding the values)
mkAVMethEdges :: [ADef] -> [(Integer, AAction)] ->
                 ([Edge], M.Map (AId,AId) AType, [SimCCFnStmt])
mkAVMethEdges ds method_calls =
    let
        -- check whether an AMethValue is from a particular action
        isMethValueOf v_obj v_meth (ACall a_obj a_meth _) =
            (v_obj == a_obj) && (v_meth == a_meth)
        isMethValueOf _ _ _ = False

        -- find the AMethValue references
        av_meth_refs = [ (i, refs) | ADef i _ e _ <- ds,
                                     -- "aMethValues" can return duplicates
                                     let refs = nub $ aMethValues e,
                                     not (null refs) ]

        -- the value reference from an ActionValue needs to come after
        -- the action method call.
        --   Edges must be of the form (i, as) where all actions in "as"
        --   have to execute before "i" is computed.
        av_meth_edges = [ (Left i, map Right ns)
                            | (i, refs) <- av_meth_refs,
                              (obj,meth,_) <- refs,
                              let ns = map fst $
                                       filter ((isMethValueOf obj meth) . snd)
                                           method_calls,
                              not (null ns) ]

        mkAVMethDecl (obj,meth,ty) =
            let id = mkAVMethTmpId obj meth
            in  SFSDef False (ty, id) Nothing

        av_meths = unions (map snd av_meth_refs)
        av_meth_local_vars = map mkAVMethDecl av_meths

        av_meth_set = M.fromList (map (\ (o,m,t) -> ((o,m),t)) av_meths)

    in
        (av_meth_edges, av_meth_set, av_meth_local_vars)


-- We'll need to declare local variables for the actionvalues,
-- and replace AMethValue with (bogus) ASDef reference for the new
-- temporary (prior to being converted to CC)
mkAVMethTmpId :: Id -> Id -> Id
mkAVMethTmpId obj meth =
    -- XXX make sure this Id is unique?
    mkId noPosition (concatFString [mkFString "AVMeth_",
                                    getIdBase obj,
                                    fsUnderscore,
                                    getIdBase meth])


-- ===============

type GateSubstMap = M.Map AExpr AExpr

mkGateSubstMap :: [AId] -> [(AClock, AClock)] -> GateSubstMap
mkGateSubstMap top_gates es =
    let
        -- For now, replace top-level input gates with True
        mkTopSubst gateId = (ASPort (ATBit 1) gateId, aTrue)
        top_subst = M.fromList $ map mkTopSubst top_gates

        -- And update the existing substitutions
        substTop (orig, new) = (orig, M.findWithDefault new new top_subst)

        -- Convert a clock substitution into a gate substitution
        convEdge (orig_aclk, new_aclk) =
            (aclock_gate orig_aclk, aclock_gate new_aclk)

        es_subst = M.fromList $ map (substTop . convEdge) es
    in
        -- more efficient when the bigset is first
        es_subst `M.union` top_subst

-- This should only be called on a list of converted defs
-- (so the stmt list should only contain SFSAssign stmts)
substGateReferences :: GateSubstMap -> [SimCCFnStmt] -> [SimCCFnStmt]
substGateReferences smap stmts =
    let
        -- replace a gate if found in the map
        substInAExpr e@(AMGate {}) = M.findWithDefault e e smap
        substInAExpr e@(ASPort {}) = M.findWithDefault e e smap
        -- otherwise, follow exprs
        substInAExpr e@(APrim { ae_args = es }) =
            e { ae_args = map substInAExpr es }
        substInAExpr e@(AMethCall { ae_args = es }) =
            e { ae_args = map substInAExpr es }
        substInAExpr e@(ATuple { ae_elems = es }) =
            e { ae_elems = map substInAExpr es }
        substInAExpr e@(ATupleSel { ae_exp = e1 }) =
            e { ae_exp = substInAExpr e1 }
        substInAExpr e@(ANoInlineFunCall { ae_args = es }) =
            e { ae_args = map substInAExpr es }
        substInAExpr e@(AFunCall { ae_args = es }) =
            e { ae_args = map substInAExpr es }
        substInAExpr e = e

        substInStmt (SFSAssign p i e) = (SFSAssign p i (substInAExpr e))
        substInStmt s = internalError ("substGateReferences: non-assign: " ++
                                       ppReadable s)
    in
        map substInStmt stmts


-- ===============
-- Inserting mutual exclusion inhibitors

mkMERuleInhibits :: S.Set AId -> [SchedNode] -> DisjointRulesDB -> M.Map AId [AId]
mkMERuleInhibits top_vmeth_set sched_order disjoint_map =
    let
        -- value methods can't change state, so they don't need to inhibit

        foldfunc :: (IdSet, [(AId,[AId])]) -> SchedNode ->
                    (IdSet, [(AId,[AId])])
        foldfunc (seen_exec_nodes, res) (Exec r) =
            if (S.member r top_vmeth_set)
            then (seen_exec_nodes, res)
            else (S.insert r seen_exec_nodes, res)
        foldfunc (seen_exec_nodes, res) (Sched r) =
            case (M.lookup r disjoint_map) of
                Nothing -> (seen_exec_nodes, res)
                Just dset ->
                    let inhibit_set = S.intersection dset seen_exec_nodes
                        new_res = (r, S.toList inhibit_set)
                    in  (seen_exec_nodes, new_res:res)
    in
        M.fromList $ reverse $ snd $ foldl foldfunc (S.empty, []) sched_order


-- ===============
