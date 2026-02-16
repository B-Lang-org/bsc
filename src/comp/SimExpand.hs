{-# LANGUAGE CPP #-}
module SimExpand ( simExpand, simExpandSched, simCheckPackage ) where

import Data.Maybe (isNothing, isJust, catMaybes, mapMaybe, maybeToList)
import Data.List (partition, union, nub, sort, sortBy, delete)
import Control.Monad (when, guard, msum {-, mapM_ -})
import Debug.Trace
import qualified Data.Map as M
import qualified Data.Set as S

import IOUtil(progArgs)
import Error (internalError, EMsg, ErrMsg(..), ErrorHandle, bsError,
              convExceptTToIO)
import Position (noPosition, getPosition)
import PPrint
import Flags
import FStringCompat(mkFString)
import Backend

import PreStrings (sSigned, sUnsigned)
import PreIds (idDefaultClock, idDefaultReset)
import Id (mkId,
           setSignedId, getIdString, unQualId, isRdyId,
           getIdBaseString, getIdQualString, setIdQualString, emptyId,
           mkIdTempReturn)
import VModInfo
import Wires(WireProps(..), ClockDomain)
import Pragma(PProp(..), isAlwaysEn, isEnWhenRdy, RulePragma(..))
import ASyntax
import ASyntaxUtil(aSubst, findAExprs, exprFold)
import AScheduleInfo
import AUses(MethodId(..))
import Params(isConstAExpr)
import SimPackage
import SimPrimitiveModules(getPrimDomainInfo, checkBluesimPrimitives)
import SimCCBlock(SimCCBlock(..), primBlocks)
import SchedInfo (methodConflictInfo, sSB)
import ABin (ABin(..), ABinModInfo(..))
import ABinUtil(HierMap, getABIHierarchy, assertNoSchedErr)
import SimDomainInfo

import SCC (tsort)

import Util (headOrErr, map_insertManyWith, allPairs, stableOrdNub, mapFst, mapSnd)
import GraphUtil(extractOneCycle_map, reverseMap)

-- ===============
-- Traces

trace_mergesched, trace_bs_mcd :: Bool
trace_mergesched = "-trace-mergesched" `elem` progArgs
trace_bs_mcd = "-trace-bs-mcd" `elem` progArgs


-- ===============

-- topname: the top module of the design
-- fabis: the name of each .ba file paired with its contents
--        (file + abi = fabi)
--        the filename is kept for reporting errors to the user
simExpand :: ErrorHandle -> Flags -> String -> [(String, ABin)] -> IO SimSystem
simExpand errh flags topname fabis = do
    -- get the names of the primitives
    -- (to put in the list of mods we don't need .ba for)
    let prim_names = map sb_name primBlocks

    (topmodId, hiermap, instmap, ffuncmap, filemap, _, emodinfos_used_by_name)
        <- convExceptTToIO errh $
           getABIHierarchy errh (verbose flags) (ifcPath flags) (Just Bluesim)
                           prim_names topname fabis

    modinfos_used_by_name <- convExceptTToIO errh $
                             assertNoSchedErr emodinfos_used_by_name

    -- reject top-level modules with always_enabled ifc, if generating
    -- a Bluesim executable
    let topModInfo =
           case (lookup (getIdString topmodId) modinfos_used_by_name) of
               Just (mi,_) -> mi
               Nothing     -> internalError ("simExpand: topmodId not found")
    when ((not (genSysC flags)) && (hasEnabledMethod topModInfo)) $
        bsError errh [(noPosition, EBSimEnablePragma)]

    -- reject top-level modules with arguments or params in Bluesim or SystemC
    let (top_args, top_params) = getArgsAndParams topModInfo
    if (genSysC flags)
     then when ((not (null top_args)) || (not (null top_params))) $
               bsError errh [(noPosition, EBSimTopLevelArgOrParam True (top_args ++ top_params))]
     else when ((not (null top_args)) || (not (null top_params))) $
               bsError errh [(noPosition, EBSimTopLevelArgOrParam False (top_args ++ top_params))]

    simpkgs <- mapM (simExpandABin errh flags) (map snd modinfos_used_by_name)
    let pkg_map = M.fromList (map (\p -> (sp_name p,p)) simpkgs)

    -- record default clock and reset for top module
    let def_clk = msum $ [ lookup idDefaultClock xs
                         | (PPclock_osc xs) <- (abmi_pps topModInfo)
                         ] ++
                         [Just "CLK"]
        top_clk = do x <- def_clk
                     guard (not (null x))
                     return x
        def_rst = msum $ [ lookup idDefaultReset xs
                         | (PPreset_port xs) <- (abmi_pps topModInfo)
                         ] ++
                         [Just "RSTN"]
        top_rst = do x <- def_rst
                     guard (not (null x))
                     return x

    simscheds <- simExpandSched modinfos_used_by_name hiermap instmap topname

    return $ SimSystem { ssys_packages    = pkg_map
                       , ssys_schedules   = simscheds
                       , ssys_top         = topmodId
                       , ssys_instmap     = instmap
                       , ssys_ffuncmap    = ffuncmap
                       , ssys_filemap     = filemap
                       , ssys_default_clk = top_clk
                       , ssys_default_rst = top_rst
                       }

-- ===============

simExpandABin :: ErrorHandle -> Flags -> (ABinModInfo,String) -> IO SimPackage
simExpandABin errh flags (abi,ver) = do
    let
        -- we will update the apkg, so name this as the initial value
        apkg0 = abmi_apkg abi

    when (trace_bs_mcd) $ do
        traceM ("domains = " ++ ppReadable (apkg_clock_domains apkg0))
        traceM ("resets = " ++ ppReadable (apkg_reset_list apkg0))
        let inst_tuples =
                [ (avi_vname avi, getInstArgs avi)
                    | avi <- apkg_state_instances apkg0 ]
        traceM ("insts = " ++ ppReadable inst_tuples)
        let rule_tuples =
                [ (arule_id r, arule_wprops r) | r <- apkg_rules apkg0 ]
        traceM ("rules = " ++ ppReadable rule_tuples)

    -- ----------
    -- Check the package for features not supported by Bluesim
    -- and do any necessary changes (such as inlining module arg exprs)

    -- We already did this prior to generating .ba, but we do it again
    -- here to be sure.

    -- Checks include:

    -- - Inout is not allowed in the ifc or as arguments

    -- - unsupported primitives (MCD, for example)

    -- - module arg exprs
    --
    -- Bluesim can only handle module instantiation arguments which
    -- are static.  VArgInfo distinguishes between Param and Port,
    -- but Bluesim has to treat everything as a Param.
    -- Check here that the values to Port are also constant expressions.
    --
    -- However, isConstAExpr expects all defs to be inlined.
    -- During elaboration, iParams only inlines for Param exprs.
    -- Bluesim needs this inlining to be done for Port too.

    apkg1 <- simCheckPackage errh True apkg0

    -- ----------
    -- Make sure that all ActionValue method return values use a
    -- temporary def.  This is required for the sorting which
    -- ensures that method calls occur in schedule order within an
    -- ActionValue method (see SimMakeCBlocks.hs::tsortActionsAndDefs).
    -- We also lift any method return of a foreign function result,
    -- because that is required for handling of imported function calls.
    let apkg = makeMethodTemps apkg1

    let
        -- ----------
        -- package fields

        -- these we will update, so name indicates they are the initial values
        defs0  = apkg_local_defs apkg

        -- ----------
        -- Remove $signed and $unsigned calls
        -- Sign information is preserved in IdP_signed prop on the ADef's Id
        removeSignCasts def@(ADef id ty (AFunCall _ _ name _ [arg]) props) =
            if (name == sSigned) || (name == sUnsigned)
            then ADef (setSignedId id) ty arg props
            else def
        removeSignCasts def = def

        defs1 = map removeSignCasts defs0

    -- ----------
    -- convert noinline function calls to method calls
    -- and create instantiations for the modules they are calls on

    -- XXX technically, we don't need to convert to method calls,
    -- XXX if we handle ANoInlineFun in aExprToCExpr ?

    let (defs, noinline_instances) = getNoInlineInfo defs1

    -- ----------
    -- identify the gates used in the module (not just connected between mods)
    -- and assign unique numbers (to be the names for those gates in codegen)

    -- XXX Is it worth only keeping around the gates which are used as exprs
    -- XXX (or do we eventually want to dump VCDs for all gates, for example?)
    -- XXX Because maybe it's better to just walk the args and the submods
    -- XXX to get the full list, than to walk all AExprs of the module?
    -- XXX Note that some gates used directly in the ARule won't be included.
    let
        gates = findGates (apkg_inputs apkg) (apkg_interface apkg) defs

    -- ----------
    -- create the SimPackage

    let insts = apkg_state_instances apkg

    let simpkg = SimPackage {
                     sp_name = apkg_name apkg,
                     sp_is_wrapped = apkg_is_wrapped apkg,
                     sp_version = ver,
                     sp_pps = abmi_pps abi,
                     sp_size_params = apkg_size_params apkg,
                     sp_inputs = apkg_inputs apkg,
                     sp_clock_domains = apkg_clock_domains apkg,
                     sp_external_wires = apkg_external_wires apkg,
                     sp_reset_list = apkg_reset_list apkg,
                     sp_state_instances = mkAVInstMap insts,
                     sp_noinline_instances = noinline_instances,
                     sp_method_order_map = mkMethodOrderMap insts,
                     sp_local_defs = mkDefMap defs,
                     sp_rules = apkg_rules apkg,
                     sp_interface = apkg_interface apkg,
                     sp_schedule = abmi_aschedinfo abi,
                     sp_pathinfo = abmi_pathinfo abi,
                     sp_gate_map = gates,
                     sp_schedule_pragmas = apkg_schedule_pragmas apkg
                 }

    return simpkg


-- ===============

simExpandSched :: [(String, (ABinModInfo,String))] -> HierMap -> InstModMap ->
                  String -> IO [SimSchedule]
simExpandSched abis0 hiermap instmap topmod = do

    let abis = [ (n,mi) | (n,(mi,_)) <- abis0 ]

    -- ----------
    -- merge the schedules

    combscheds_by_domain -- :: [(AClock, CombSchedInfo)]
        <- mergeSchedules abis hiermap instmap topmod

    -- ----------
    -- create the SimSchedule

    let
        mkPosSched (aclk, csi) =
            let (sched_graph, sched_order) = flattenCombSchedGraph csi

                (sched_nodes, exec_nodes) = partition isSchedNode sched_order
                urgency_order = map getSchedNodeId sched_nodes
                earliness_order = map getSchedNodeId exec_nodes
                find_conflicts i =
                    M.findWithDefault [] i (csi_conflicts csi)
                conflict_pairs =
                    map (\i -> (i,find_conflicts i)) urgency_order
                asched = ASchedule [ASchedEsposito conflict_pairs]
                                   (reverse earliness_order)
                di = headOrErr "simExpandSched"
                               (M.elems (csi_domain_info_map csi))
                early_rules = di_clock_crossing_rules di
                before_early_rules =
                    concat [ filter (\x -> (getSchedNodeId x) /= r) ns
                           | (n,ns) <- sched_graph
                           , let r = getSchedNodeId n
                           , r `elem` early_rules
                           ]
            in if (null before_early_rules)
               then SimSchedule { ss_clock = aclk
                                , ss_posedge = True
                                , ss_schedule = asched
                                , ss_disjoint_rules_db = csi_drdb csi
                                , ss_sched_graph = sched_graph
                                , ss_sched_order = sched_order
                                , ss_domain_info_map = csi_domain_info_map csi
                                , ss_early_rules = early_rules
                                }
               else internalError $ "unexpected nodes before clock-crossing rule: " ++
                                    (show before_early_rules)

        pos_scheds = map mkPosSched combscheds_by_domain

    let showSchedOrder ss =
            traceM ("sched order: " ++ ppReadable (ss_sched_order ss))
    when trace_mergesched $
        mapM_ showSchedOrder pos_scheds

    -- ----------
    -- return all the schedules

    let simscheds = pos_scheds

    return simscheds

-- ---------------

flattenCombSchedGraph :: CombSchedInfo ->
                         ([(SchedNode, [SchedNode])], [SchedNode])
flattenCombSchedGraph csi =
  let
      sched_map = csi_sched_map csi
      rrmap = csi_rule_rel_map csi

      sched_graph = M.toList sched_map

      -- Sort the SchedNodes initially so we respect the stable ordering
      -- from the Ord instance, but still have fast comparisons for tsort.
      sorted_nodes = sort $ M.keys sched_map
      nodesToInt :: M.Map FastSchedNode Int
      nodesToInt = M.fromList $ zip (map FSN sorted_nodes) [0..]
      getInt n = M.findWithDefault (internalError "flattenCombSchedGraph.getInt")
                                   (FSN n)
                                   nodesToInt
      intToNodes :: M.Map Int SchedNode
      intToNodes = M.fromList $ zip [0..] sorted_nodes
      getNode i  = M.findWithDefault (internalError "flattenCombSchedGraph.getNode")
                                     i
                                     intToNodes
      sched_graph_int = M.toList $ M.mapKeys getInt $ M.map (map getInt) sched_map

      -- whether the ordering of two nodes is only because of
      -- foreign func uses (and therefore the edge can be dropped)
      isFFuncEdge (Exec r1, Exec r2) =
          case (M.lookup (r1,r2) rrmap) of
            Just (RuleRelationInfo
                      Nothing Nothing Nothing Nothing Nothing
                      (Just CFFuncArbitraryChoice)) -> True
            _ -> False
      isFFuncEdge _ = False

      findFFuncEdges scc =
          let -- XXX we could go through the trouble of finding
              -- XXX just the edges on the cycles, and even of finding
              -- XXX some minimal set of edges to break the cycles,
              -- XXX but it didn't seem worth the effort.
              pairs = allPairs $ map getNode scc
          in  filter isFFuncEdge pairs
  in
      case (tsort sched_graph_int) of
        Right order -> (sched_graph, map getNode order)
        Left sccs ->
          let
              edges_to_remove = concatMap findFFuncEdges sccs
              new_sched_map =
                  let updateFn n priors = case (delete n priors) of
                                             [] -> Nothing
                                             rest -> Just rest
                      -- (n1, n2) means delete n1 from n2's priors
                      foldFn (n1, n2) = M.update (updateFn n1) n2
                  in  foldr foldFn sched_map edges_to_remove
              new_sched_graph = M.toList new_sched_map
              new_sched_graph_int = M.toList $ M.mapKeys getInt $ M.map (map getInt) $ new_sched_map
          in
              -- try once more, with the bias edges removed
              case (tsort new_sched_graph_int) of
                Right order -> (new_sched_graph, map getNode order)
                Left [] -> internalError "empty scc"
                Left (scc:_) ->
                    let one_cycle = extractOneCycle_map new_sched_map (map getNode scc)
                    in  internalError ("cycle in combsched: " ++
                                       ppReadable one_cycle)


-- ===============
-- Merging schedules

-- This the intermediate data which is carried around while combining
-- AScheduleInfos.  After merging is done, this info is processed to
-- create the final SimSchedule.
data CombSchedInfo = CombSchedInfo
    {
      -- this is used to reconstruct the ASchedule
      csi_conflicts :: ConflictMap,
      csi_drdb :: DisjointRulesDB,
      -- from this we can get the sched_graph and
      -- (by flattening) the sched_order
      csi_sched_map :: SchedMap,
      csi_rule_rel_map :: RuleRelationMap,
      -- clock domain info (rules, clocked submods, resets)
      csi_domain_info_map :: DomainInfoMap
    }
  deriving (Eq, Show)

-- Just the conflict info from the RuleRelationDB
-- (the disjoint info cannot be accumulated across method calls)
type RuleRelationMap = M.Map (AId, AId) RuleRelationInfo

-- The schedule graphs will be converted from list to map for better access
type SchedMap = M.Map SchedNode [SchedNode]

-- The Esposito scheduler is a list of rules/methods paired with the
-- more urgent rules/methods that block it.  This pairing we will store
-- as a map, for better update and access.
type ConflictMap = M.Map AId [AId]

-- ------

-- A map from module name to the result of merging all the schedules
-- from submodules into this parent module.  This is the map we will
-- be building up from the leaves of the design, from an empty map.
type CSIMap = M.Map String CombSchedInfo


-- ----------

reverseSchedMap :: SchedMap -> SchedMap
reverseSchedMap smap = M.mapKeys unFSN $ M.map (map unFSN) $ reverseMap smap'
  where smap' = M.mapKeys FSN $ M.map (map FSN) smap

reverseConflictMap :: ConflictMap -> ConflictMap
reverseConflictMap cmap = reverseMap cmap

-- ----------

makeDomainMaps :: [AClockDomain] -> [ARule] -> [AVInst] -> [AIFace] ->
                  (DomainIdMap, DomainInfoMap)
makeDomainMaps cds rs insts iface =
    let
        -- convert a domain to its DomainId
        domainToDomainId cd = (emptyId, cd)

        -- empty info, for building up from
        emptyDomainInfo = DomainInfo {
                              di_clocks = [],
                              di_domains = [],
                              di_rules = [],
                              di_clock_crossing_rules = [],
                              di_prims = [],
                              di_prim_resets = [],
                              di_output_clocks = [],
                              di_clock_substs = []
                          }

      -- ----------
      -- domain Id map

        -- make a map from clocks visible in this module to their DomainId
        domain_id_map =
            makeDomainIdMap
                [ (aclk, domainToDomainId cd)
                      | (cd, aclks) <- cds,
                        aclk <- aclks ]

      -- ----------
      -- start the domain info map with just the domain info

        dinfoFromClks dom_id aclks = emptyDomainInfo { di_clocks = aclks,
                                                       di_domains = [dom_id] }

        dmap_with_clks =
            M.fromList [ (dom_id, dinfoFromClks dom_id aclks)
                       | (cd, aclks) <- cds
                       , let dom_id = domainToDomainId cd
                       ]

      -- ----------
      -- accumulate rule info

        singleRule r False = emptyDomainInfo { di_rules = [r] }
        singleRule r True  = emptyDomainInfo { di_rules = [r]
                                             , di_clock_crossing_rules = [r] }

        -- assumes no duplicates

        accumRule :: ARule -> DomainInfoMap -> DomainInfoMap
        accumRule r map_so_far =
            let rid = arule_id r
                cd = getWPropDomain rid (arule_wprops r)
                clock_crossing = RPclockCrossingRule `elem` (arule_pragmas r)
                new_dom = domainToDomainId cd
                new_rl = singleRule rid clock_crossing
            in
                M.insertWith joinDomainInfo new_dom new_rl map_so_far

        -- add the rules to the map
        dmap_with_clks_rules = foldr accumRule dmap_with_clks rs

      -- ----------
      -- accumulate primitive info

        singlePrim p@(pid, (arg_id, _)) True =
            emptyDomainInfo { di_prims = [p]
                            , di_prim_resets = [(pid, arg_id)]
                            }
        singlePrim p False =
            emptyDomainInfo { di_prims = [p] }

        -- primtives
        prim_names = map sb_name primBlocks

        accumPrim :: AVInst -> DomainInfoMap -> DomainInfoMap
        accumPrim p map_so_far
          | (getVNameString (vName (avi_vmi p)) `notElem` prim_names) = map_so_far
        accumPrim p map_so_far =
            let pid = avi_vname p
                -- all the clock arguments to the module
                clk_infos = [ (aclk, arg_id)
                                | (ClockArg arg_id, clk_expr) <- getInstArgs p,
                                  let aclk = getClkFromAExpr clk_expr,
                                  -- don't count the ones with no clock
                                  not (isNoClock aclk)
                                  ]
                -- (input) clocks associated with input resets
                rst_clks =
                    nub $ [ c | (r, (mp, (Just c)))
                                    <- input_resets (vRst (avi_vmi p)),
                                -- ignore resets which don't have a port
                                isJust mp ]
                -- convert it to the DomainInfo form
                infoToEntry :: (AClock, AId) -> (DomainId, DomainInfo)
                infoToEntry (aclk, arg_id) =
                  let has_reset = arg_id `elem` rst_clks
                  in (findDomainId domain_id_map aclk,
                      singlePrim (pid, (arg_id, aclk)) has_reset)
                new_entries = map infoToEntry clk_infos
                new_map = M.fromListWith joinDomainInfo new_entries
            in
                M.unionWith joinDomainInfo new_map map_so_far

        dmap_with_clks_rules_prims =
            foldr accumPrim dmap_with_clks_rules insts

      -- ----------
      -- add the output clocks

        singleOutClk c = emptyDomainInfo { di_output_clocks = [c] }

        outclks = [ (findDomainId domain_id_map aclk,
                     singleOutClk (clk_id, aclk))
                        | (AIClock clk_id aclk _) <- iface,
                          -- noClock has no domain
                          not (isNoClock aclk) ]

        dmap_with_clks_rules_prims_outclks =
            let outclk_map = M.fromListWith joinDomainInfo outclks
            in M.unionWith joinDomainInfo outclk_map dmap_with_clks_rules_prims

      -- ----------
      -- return the result

    in
        (domain_id_map, dmap_with_clks_rules_prims_outclks)


-- This assumes no duplicates (uses ++ instead of `union`)
joinDomainInfo :: DomainInfo -> DomainInfo -> DomainInfo
joinDomainInfo di1 di2 =
    DomainInfo {
        di_clocks = (di_clocks di1) ++ (di_clocks di2),
        di_domains = (di_domains di1) ++ (di_domains di2),
        di_rules = (di_rules di1) ++ (di_rules di2),
        di_clock_crossing_rules = (di_clock_crossing_rules di1) ++ (di_clock_crossing_rules di2),
        di_prims = (di_prims di1) ++ (di_prims di2),
        di_prim_resets = (di_prim_resets di1) ++ (di_prim_resets di2),
        di_output_clocks = (di_output_clocks di1) ++ (di_output_clocks di2),
        di_clock_substs = (di_clock_substs di1) ++ (di_clock_substs di2)
    }

-- ----------

substInputClockInDomainInfo :: AClock -> AClock -> DomainInfo -> DomainInfo
substInputClockInDomainInfo child_clk parent_clk child_dom_info =
    let
        clocks      = di_clocks               child_dom_info
        domains     = di_domains              child_dom_info
        rules       = di_rules                child_dom_info
        cross_rules = di_clock_crossing_rules child_dom_info
        prims       = di_prims                child_dom_info
        prim_resets = di_prim_resets          child_dom_info
        output_clks = di_output_clocks        child_dom_info
        clk_substs  = di_clock_substs         child_dom_info

        -- ----------
        -- clocks are unchanged

        clocks'  = clocks
        domains' = domains

        -- ----------
        -- the set of rules remains the same

        rules'       = rules
        cross_rules' = cross_rules

        -- ----------
        -- Replace the child clock with the parent clock in primitives
        -- (this will include any gate from the parent)

        substPrim (inst, (arg_id, clk)) | clk == child_clk
            = (inst, (arg_id, parent_clk))
        substPrim p = p

        prims' = map substPrim prims

        -- reset ids are unchanged
        prim_resets' = prim_resets

        -- ----------
        -- Output clocks which come from input clocks should be substituted

        substOutputClk (clk_id, aclk) | aclk == child_clk
                         = (clk_id, parent_clk)
        substOutputClk c = c

        output_clks' = map substOutputClk output_clks

        -- ----------
        -- Substitute in the clock substitutions and add this substitution

        substClockSubst (orig_clk, new_clk) | new_clk == child_clk
                          = (orig_clk, parent_clk)
        substClockSubst s = s

        clk_substs' = [(child_clk, parent_clk)] ++
                      (map substClockSubst clk_substs)

        -- ----------
    in
        DomainInfo {
            di_clocks               = clocks',
            di_domains              = domains',
            di_rules                = rules',
            di_clock_crossing_rules = cross_rules',
            di_prims                = prims',
            di_prim_resets          = prim_resets',
            di_output_clocks        = output_clks',
            di_clock_substs         = clk_substs'
        }

-- ----------

substOutputClockInDomainInfo :: AClock -> AClock -> DomainInfo -> DomainInfo
substOutputClockInDomainInfo parent_clk child_clk parent_dom_info =
    let
        clocks      = di_clocks               parent_dom_info
        domains     = di_domains              parent_dom_info
        rules       = di_rules                parent_dom_info
        cross_rules = di_clock_crossing_rules parent_dom_info
        prims       = di_prims                parent_dom_info
        prim_resets = di_prim_resets          parent_dom_info
        output_clks = di_output_clocks        parent_dom_info
        clk_substs  = di_clock_substs         parent_dom_info

        -- ----------
        -- clocks are unchanged
        -- (the child clock will be added when we join the domain infos)

        clocks'  = clocks
        domains' = domains

        -- ----------
        -- the set of rules remains the same

        rules'       = rules
        cross_rules' = cross_rules

        -- ----------
        -- Replace the parent clock with the child clock in primitives

        substPrim (inst, (arg_id, clk)) | clk == parent_clk
            = (inst, (arg_id, child_clk))
        substPrim p = p

        prims' = map substPrim prims

        -- reset ids are unchanged
        prim_resets' = prim_resets

        -- ----------
        -- Output clocks

        substOutputClk (clk_id, aclk) | aclk == parent_clk
                         = (clk_id, child_clk)
        substOutputClk c = c

        output_clks' = map substOutputClk output_clks

        -- ----------
        -- Substitute in the clock substitutions and add this substitution

        substClockSubst (orig_clk, new_clk) | new_clk == parent_clk
                          = (orig_clk, child_clk)
        substClockSubst s = s

        clk_substs' = [(parent_clk, child_clk)] ++
                      (map substClockSubst clk_substs)

        -- ----------
    in
        DomainInfo {
            di_clocks               = clocks',
            di_domains              = domains',
            di_rules                = rules',
            di_clock_crossing_rules = cross_rules',
            di_prims                = prims',
            di_prim_resets          = prim_resets',
            di_output_clocks        = output_clks',
            di_clock_substs         = clk_substs'
        }

-- ----------

mergeSchedules :: [(String, ABinModInfo)] -> HierMap -> InstModMap ->
                  String -> IO [(AClock, CombSchedInfo)]
mergeSchedules abis hiermap instmap topmod = do
    -- ----------
    -- trace

    let showSched abi =
            traceM ("sched (" ++
                    ppReadable (apkg_name (abmi_apkg abi)) ++ "): " ++
                    ppReadable (asi_sched_graph (abmi_aschedinfo abi)))
    when trace_mergesched $
        mapM_ showSched (map snd abis)

    -- ----------

    let pu_map = mkParentUseModMap abis
        smap = combineSchedInfos abis hiermap instmap pu_map topmod M.empty
        combschedinfo = case (M.lookup topmod smap) of
                            Just x -> x
                            Nothing -> internalError "combschedinfo"

    -- ----------
    -- trace of the result

    when trace_mergesched $ do
        traceM ("comb sched_map = " ++
                ppReadable (csi_sched_map combschedinfo))
        traceM ("comb conflicts = " ++
                ppReadable (csi_conflicts combschedinfo))

    -- ----------
    -- return the result

    -- XXX combineSchedInfos could have been splitting the CSIs by domain
    -- XXX as it was building up from the leaves.  Here, we have built one
    -- XXX graph and kept rule domain info alongside, so that we can split
    -- XXX the graph at the end.

    -- since the domain info hasn't been built with methods, we'll need to
    -- pass them in, to add them.  (we didn't build with them, because for
    -- each submodule, we throw the method info away, so it's wasted work)
    let res = let topabi = getABI topmod abis
                  topifc = apkg_interface (abmi_apkg topabi)
              in  splitCSIByClock topifc combschedinfo

    when trace_bs_mcd $ do
        let getSchedIds es =
                nub $ concat $
                [ [getSchedNodeId n1] ++ map getSchedNodeId n2s
                    | (n1, n2s) <- es ]
            domain_tuples =
                [ (cd, rs) | (cd, csi) <- res,
                              let rs = getSchedIds
                                           (M.toList (csi_sched_map csi)) ]
        traceM ("merged domains = " ++ ppReadable domain_tuples)

    return res

-- ----

splitCSIByClock :: [AIFace] -> CombSchedInfo -> [(AClock, CombSchedInfo)]
splitCSIByClock topifc csi =
    let
        confls = csi_conflicts csi -- ConflictMap
        drdb = csi_drdb csi -- DisjointRulesDB
        smap = csi_sched_map csi -- SchedMap
        dmap = csi_domain_info_map csi -- DomainInfoMap
        rrmap = csi_rule_rel_map csi -- RuleRelationMap

        -- make a map from domain to the top-level methods in that domain
        ifc_dmap =
            let accumMeth (AIClock {}) map_so_far = map_so_far
                accumMeth (AIReset {}) map_so_far = map_so_far
                accumMeth m map_so_far =
                    let mid = aif_name m
                        cd = getWPropDomain mid (aif_props m)
                    in  M.insertWith (++) cd [mid] map_so_far
            in  foldr accumMeth M.empty topifc

        getDomainMeths cd = case (M.lookup (snd cd) ifc_dmap) of
                                Nothing -> []
                                Just ms -> ms

        -- from all the clocks in a domain, choose the best
        countChars :: Char -> String -> Int
        countChars _ []     = 0
        countChars t (c:cs) = (if (c == t) then 1 else 0) + (countChars t cs)
        numLevels :: Char -> AExpr -> Int
        numLevels d e@(ASPort _ i)     = 1 + ((countChars d) . getIdString) i
        numLevels d e@(AMGate _ i1 i2) = 1 + ((countChars d) . getIdString) i1 + ((countChars d) . getIdString) i2
        numLevels _ _                  = 0
        cmp_clk :: AClock -> AClock -> Ordering
        cmp_clk (AClock o1 g1) (AClock o2 g2)
          | (numLevels '.' g1) < (numLevels '.' g2) = LT
          | (numLevels '.' g1) > (numLevels '.' g2) = GT
          | (numLevels '.' o1) < (numLevels '.' o2) = LT
          | (numLevels '.' o1) > (numLevels '.' o2) = GT
          | otherwise = (numLevels '$' o1) `compare` (numLevels '$' o2)
        findBestClock :: [AClock] -> AClock
        findBestClock aclks =
           let sorted_clks = sortBy cmp_clk aclks
           in  headOrErr "splitCSIByClock: no clocks found" sorted_clks

        domains :: [(DomainId, DomainInfo)]
        --domains = filter clocks_something $ M.toList dmap
        domains = M.toList dmap

        -- for each domain, extract the CSI for that domain
        extractCSI (cd, dinfo) =
            let aclk = findBestClock (di_clocks dinfo)
                cd_rules = di_rules dinfo
                cd_methods = getDomainMeths cd
                cd_rules_and_meths = cd_rules ++ cd_methods
                csi = CombSchedInfo {
                         csi_conflicts = extractConflicts cd_rules_and_meths,
                         csi_drdb = extractDRDB cd_rules_and_meths,
                         csi_sched_map = extractSchedMap cd_rules_and_meths,
                         csi_domain_info_map = M.singleton cd dinfo,
                         csi_rule_rel_map = extractRuleRelMap cd_rules_and_meths
                      }
            in (aclk, csi)

        -- XXX leave them as the full info for now
        extractConflicts _ = confls
        extractDRDB _ = drdb
        extractRuleRelMap _ = rrmap

        extractSchedMap :: [ARuleId] -> SchedMap
        extractSchedMap cd_rs =
            let cd_rs_set = S.fromList cd_rs
                -- func to see if a SchedNode is in the domain
                inDomain :: SchedNode -> Bool
                inDomain sn = (getSchedNodeId sn) `S.member` cd_rs_set

                -- flatten to a list
                es = M.toList smap
                -- remove the nodes which aren't in the list
                es' = filter (inDomain . fst) es
                -- if there are any outgoing edges not in the cd_rs, error
                checkKeys (r,vs) =
                    let err_rs = filter (not . inDomain) vs
                    in  if (null err_rs)
                        then (r,vs)
                        else internalError ("schedMap not disjoint: " ++
                                            ppReadable (r, err_rs))
            in
                M.fromList (map checkKeys es')
    in
        map extractCSI domains


-- ----------

{-
-- Example sched_graph from mkGCD
-- Note that the Sched nodes will eventually become RDY value methods,
-- but at this point those separate "methods" don't exist.
sched (mkGCD): [(Sched start, []),
 (Exec start, [Sched start, Exec result]),
 (Sched result, []),
 (Exec result, [Sched result]),
 (Sched RL_sub, [Sched start]),
 (Exec RL_sub, [Sched RL_sub]),
 (Sched RL_flip, [Sched start]),
 (Exec RL_flip, [Sched RL_flip])]
-}

-- Recursive function which merges the AScheduleInfos from
-- all the ABinModInfos in the design, according to the hierarchy,
-- to produce a CSIMap for all the module types in the design
-- (from which we'll just take the CSI associated with the top
-- module type, but the others are in the map for merging along
-- the way).
combineSchedInfos :: [(String, ABinModInfo)] ->
                     HierMap -> InstModMap -> ParentUseModMap ->
                     String -> CSIMap -> CSIMap
combineSchedInfos abis hiermap instmap pu_map curmod smap =
    let
        -- the map for this module
        use_map = findParentUseMap pu_map curmod

        curmod_abi = getABI curmod abis

        -- this returns the Id map separately
        -- (no need for it to be stored an accumulated in the CSI;
        --  it's like the parent use map)
        (dom_id_map, curmod_csi) = makeCSIForModule curmod_abi

        -- map from inst name as String to its AVInst
        avi_map =
            let curmod_avis = apkg_state_instances (abmi_apkg curmod_abi)
            in  M.fromList $
                    map (\i -> (getIdString (avi_vname i), i)) curmod_avis
        -- function to lookup an AVInst
        getAVInst s =
            case (M.lookup s avi_map) of
                Just avi -> avi
                Nothing -> internalError ("SimExpand.getAVInst: " ++
                                          "cannot find " ++ s)

        -- don't follow prim modules
        prim_names = map sb_name primBlocks
    in
        case (M.lookup curmod smap) of
          Just cschedinfo -> smap
          Nothing ->
            case (M.lookup curmod hiermap) of
              Nothing -> internalError ("combineSchedInfos: " ++ curmod)
              -- the noinline instances don't have schedule info,
              -- so it's okay to ignore them
              Just ([],_) -> M.insert curmod curmod_csi smap
              Just (insts, _) ->
                let
                    foldfunc :: (String, String) ->
                                (ABinModInfo, CombSchedInfo, CSIMap) ->
                                (ABinModInfo, CombSchedInfo, CSIMap)
                    foldfunc (inst, mod) (p_abi, p_csi, smap) =
                      let s_abi = getABI mod abis
                          smap' = combineSchedInfos
                                      abis hiermap instmap pu_map mod smap
                          s_csi = case (M.lookup mod smap') of
                                      Just x -> x
                                      Nothing ->
                                          internalError ("s_csi: " ++ mod)
                      in
                        if (mod `elem` prim_names)
                        then
                          let csi' = combinePrimClocks dom_id_map p_csi
                                                       inst (getAVInst inst)
                                                       mod
                          in (p_abi, csi', smap)
                        else
                          let csi' = combineCombSchedInfo use_map dom_id_map
                                                          p_abi p_csi
                                                          inst (getAVInst inst)
                                                          s_abi s_csi
                          in (p_abi, csi', smap')
                    (_, combined_csi, new_smap) =
                        foldr foldfunc (curmod_abi, curmod_csi, smap) insts
                in
                    M.insert curmod combined_csi new_smap


-- Given a module ABI, construct the initial CSI for the module,
-- from its schedule and package.
makeCSIForModule :: ABinModInfo -> (DomainIdMap, CombSchedInfo)
makeCSIForModule curmod_abi =
    let
        curmod_aschedinfo = abmi_aschedinfo curmod_abi

        curmod_graph = asi_sched_graph curmod_aschedinfo
        curmod_sched_map = M.fromList curmod_graph

        curmod_conflicts =
            case (asi_schedule curmod_aschedinfo) of
                (ASchedule [ASchedEsposito cs] _) -> M.fromList cs
                x -> internalError ("curmod_conflicts: " ++ ppReadable x)

        curmod_drdb = exclRulesDBToDisjRulesDB $
                          asi_exclusive_rules_db curmod_aschedinfo

        (RuleRelationDB _ curmod_rule_rel_map)
            = asi_rule_relation_db curmod_aschedinfo

        curmod_apkg    = abmi_apkg            curmod_abi
        curmod_domains = apkg_clock_domains   curmod_apkg
        curmod_rules   = apkg_rules           curmod_apkg
        curmod_insts   = apkg_state_instances curmod_apkg
        curmod_iface   = apkg_interface       curmod_apkg
        (curmod_dom_id_map, curmod_dmap) =
            makeDomainMaps curmod_domains curmod_rules
                curmod_insts curmod_iface

        csi = CombSchedInfo {
                  csi_conflicts = curmod_conflicts,
                  csi_drdb = curmod_drdb,
                  csi_sched_map = curmod_sched_map,
                  csi_rule_rel_map = curmod_rule_rel_map,
                  csi_domain_info_map = curmod_dmap
              }
    in
        -- return the domain Id map separately
        --     we *could* store the Id map in the CSI,
        --     but right now we don't ever need the info from the children
        --     (it's like the parent use info)
        --     so it's not really something we accumulate and need at the end.
        --     conceivable, though, we *could* accumulate it, by qualifying
        --     the clocks ... in case someday we want the info?
        (curmod_dom_id_map, csi)


-- ----------

-- Function to merge one submodule's CombSchedInfo into its parent's info.
-- This will be folded across all the submodule instances in a parent mod.
combineCombSchedInfo :: ParentUseMap -> DomainIdMap ->
                        ABinModInfo -> CombSchedInfo ->
                        String -> AVInst ->
                        ABinModInfo -> CombSchedInfo ->
                        CombSchedInfo
combineCombSchedInfo use_map domain_id_map parent_abi parent_csi
                     inst avinst child_abi child_csi =
    -- for each node of parent that references a method of the submod,
    -- add an edge from the parent node to all places pointed to from
    -- the Sched node for calls to RDY methods and Exec node for calls
    -- the actual non-RDY methods.
    let
        parent_nodes = M.keys (csi_sched_map parent_csi)

        -- mapping from Rdy Id back to its method Id
        -- XXX store this in the info for a module?
        rdy_map = mkRdyMap child_abi

        -- for each node in the parent schedule, find its uses in the child
        makeParentNodeUses node = (node, findUses use_map rdy_map inst node)

        parent_uses = map makeParentNodeUses parent_nodes

        -- once we join the child methods to the parent rules which use
        -- them, we need to remove all the methods from the child's
        -- schedule graph and conflicts (even the methods not used by
        -- any parent rules), so we need to know which are the method Ids
        child_apkg = abmi_apkg child_abi
        child_meth_set = S.fromList $ map aif_name (apkg_interface child_apkg)

        -- combine each part of the CSI
        comb_sched_map = combineSchedMap inst parent_uses
                             child_meth_set
                             (csi_sched_map parent_csi)
                             (csi_sched_map child_csi)
        comb_conflicts = combineSchedConflicts inst parent_uses
                             child_meth_set
                             (csi_conflicts parent_csi)
                             (csi_conflicts child_csi)
        comb_drdb = combineSchedDRDB inst parent_uses
                        child_meth_set
                        (csi_drdb parent_csi)
                        (csi_drdb child_csi)
        comb_rule_rel_db = combineSchedRuleRelDB inst parent_uses
                               child_meth_set
                               (csi_rule_rel_map parent_csi)
                               (csi_rule_rel_map child_csi)
        comb_domain_info_map =
            combineDomainInfoMap inst avinst
                                 domain_id_map
                                 (csi_domain_info_map parent_csi)
                                 (csi_domain_info_map child_csi)
    in
        CombSchedInfo {
            csi_conflicts = comb_conflicts,
            csi_drdb = comb_drdb,
            csi_sched_map = comb_sched_map,
            csi_rule_rel_map = comb_rule_rel_db,
            csi_domain_info_map = comb_domain_info_map
        }


-- Function to merge one submodule's CombSchedInfo into its parent's info.
-- This will be folded across all the submodule instances in a parent mod.
combinePrimClocks :: DomainIdMap -> CombSchedInfo -> String -> AVInst ->
                     String -> CombSchedInfo
combinePrimClocks domain_id_map parent_csi inst avinst mod =
    let
        -- combine the domain info for the primitive
        comb_domain_info_map =
          case (getPrimDomainInfo avinst mod) of
            (Just (new_avinst, prim_domains, prim_output_clks)) ->
              combineDomainInfoMap inst new_avinst
                                   domain_id_map
                                   (csi_domain_info_map parent_csi)
                                   (snd (makeDomainMaps prim_domains
                                                        [] -- no rules
                                                        [] -- no subinstances
                                                        prim_output_clks))

            Nothing ->  -- nothing to add, so pass parent through
              csi_domain_info_map parent_csi
    in parent_csi { csi_domain_info_map = comb_domain_info_map }

-- ----------

-- Functions to merge the individual fields of the CombSchedInfo for
-- a submodule into its parent module's CombSchedInfo.


combineDomainInfoMap :: String -> AVInst ->
                        DomainIdMap -> DomainInfoMap -> DomainInfoMap ->
                        DomainInfoMap
combineDomainInfoMap inst avinst
                     parent_id_map parent_info_map child_info_map =
    let
        -- - remove the nodes for methods
        --   (calling rules in parent module will have the appropriate domain)
        -- - qualify rule names in the child module
        -- - substitute the child's domain names for their names from the
        --   parent module (for clocks coming from the parent)
        -- - XXX substitute parent's domain names for names from the child
        --   XXX module (for clocks coming from the child)

        child_edges = M.toList child_info_map
        -- there are no methods in the domain info (we only added rules)
        child_rule_edges = child_edges

        -- qualify the domain info
        qual_child_edges =
            let qualifyEdge (d, di) = (qualifyChildDomainId inst d,
                                       qualifyChildDomainInfo inst di)
            in  map qualifyEdge child_rule_edges

        -- Make a map from the input clocks of the child module
        -- to the domain it is connected to in the parent module
        -- (and the gate of the particular clock in that domain).
        -- The value is Nothing if the input is noClock, and the
        -- child domain should therefore be removed.
        input_clock_substs :: [(AClock, Maybe (DomainId, AClock))]
        input_clock_substs =
            let vmi = avi_vmi avinst
                mkInputAClock osc mgate =
                    let osc_expr = ASPort aTBool (vName_to_id osc)
                        gate_expr =
                            case (mgate) of
                                Nothing -> aTrue
                                Just gate -> ASPort aTBool (vName_to_id gate)
                    in  AClock osc_expr gate_expr
                -- substitute the input argument with substs so far
                substArgClk dom_id aclk =
                    let dinfo = findDomainInfo parent_info_map dom_id
                    in  applyClockSubst (di_clock_substs dinfo) aclk
            in
            [ (qual_child_aclk, maybe_domain)
                | (ClockArg child_clk_id, clk_expr) <- getInstArgs avinst,
                  -- this filters out clocks which aren't connected
                  (osc, mgate) <- maybeToList $
                                      lookupInputClockWires child_clk_id vmi,
                  let qual_child_aclk = qualifyChildAClock inst $
                                            mkInputAClock osc mgate,
                  let aclk = getClkFromAExpr clk_expr,
                  let maybe_domain =
                          if (isNoClock aclk)
                          then Nothing
                          else let dom_id = findDomainId parent_id_map aclk
                                   aclk' = substArgClk dom_id aclk
                               in  Just (dom_id, aclk')
            ]

        -- pairs domains in the parent module with child output clocks
        output_clock_substs :: [(DomainId, (AId, AClock))]
        output_clock_substs =
            let
                child_id = avi_vname avinst
                out_clocks = getOutputClockWires avinst
                mkAClock clk_id osc_wire Nothing =
                    AClock (ASPort (ATBit 1) osc_wire)
                           (aSBool True)
                mkAClock clk_id osc_wire (Just gate_wire) =
                    AClock (ASPort (ATBit 1) osc_wire)
                           (AMGate (ATBit 1) child_id clk_id)
                pairWithParentDomain (clk_id, clk_info, maybe_gate_info) =
                    let aclk = mkAClock clk_id clk_info maybe_gate_info
                    in  case (findMaybeDomainId parent_id_map aclk) of
                            Nothing -> Nothing
                            Just dom_id -> Just (dom_id, (clk_id, aclk))
            in
                mapMaybe pairWithParentDomain out_clocks

        -- pair a child output clock name with the parent domain and
        -- the aclk as seen by the parent
        --   if an output clock couldn't be found in the parent domain,
        --   then it will not be in this list (but that's OK, because it
        --   either means that the output is unused or that it is defined
        --   from an input clock which is noClock)
        parent_outclk_map :: [(AId, (DomainId, AClock))]
        parent_outclk_map =
            [ (clk_id, (dom_id, aclk))
                | (dom_id, (clk_id, aclk)) <- output_clock_substs ]

        -- ----------

        -- Now we do two things:
        -- For each child domain,
        --   * if the domain has an input clock, then change the domain Id
        --     to the parent Id, and subst the parent clock/gate in the info
        --   * else if the domain has an output clock, then change the
        --     domain Id to the parent Id (if it's both an input and output,
        --     then the first case will handle it)
        --   * otherwise, do nothing
        -- For each parent domain,
        --   * if the domain includes an output clock, then substitute any
        --     references to the clock/gate in the info with the clock used
        --     in the child to define the output clock
        --     (do this for each output clock in the domain)
        --     (if the expression is noClock ... subst appropriately?)
        --     * output clocks which are input clocks need to be properly
        --       handled in the parent domain:  the substitution in the
        --       parent should use the value connected to the input and
        --       if the input is noClock, then ... such uses should be
        --       removed?  or the domain won't exist anyway in the parent?
        --   * otherwise, do nothing

        -- Then the new child edges are added to the updated parent map
        -- (any child edges which have been renamed to have parent domain
        -- names will have their info merged with the existing parent info).

        -- ----------

        -- find if a child AClock is an input clock
        -- and return the parent domain (Nothing if the argument was noClock)
        findInputClockInfo :: AClock ->
                              Maybe (AClock, Maybe (DomainId, AClock))
        findInputClockInfo aclk =
            lookup aclk input_clock_substs >>=
            \v -> Just (aclk, v)

        -- find if a child AClock is an output clock
        -- and return the parent domain
        findOutputClockInfo :: AId -> Maybe (DomainId, AClock)
        findOutputClockInfo clk_id = lookup clk_id parent_outclk_map

        -- function to see if any clocks in the given child domain are
        -- input clocks and, if so, what parent domain they belong to
        findInputParentDomain :: DomainInfo ->
                                 [(AClock, Maybe (DomainId, AClock))]
        findInputParentDomain child_dom_info =
            let child_clks = di_clocks child_dom_info
            in mapMaybe findInputClockInfo child_clks

        -- function to see if any clocks in the given child domain are
        -- output clocks and, if so, what parent domain they belong to
        findOutputParentDomain :: DomainInfo -> Maybe DomainId
        findOutputParentDomain child_dom_info =
            let child_outclks = map fst $ di_output_clocks child_dom_info
                parent_domains :: [DomainId]
                parent_domains =
                    nub $ map fst $ mapMaybe findOutputClockInfo child_outclks
            in  case (parent_domains) of
                  -- no output clock in this domain
                  [] -> Nothing
                  -- one output domain
                  [d] -> Just d
                  -- multiple output domains should not be possible?
                  ds -> internalError
                            ("combineDomainInfoMap: " ++
                             "output clocks in same domain in the child " ++
                             "but different domains in the parent")

        -- substitute for clocks coming from the parent
        -- (domains which are connected to noClock are removed)
        subst_qual_child_edges =
            let
                -- for child domains which contains clocks coming from the
                -- parent, replace the child domain id with the parent's
                -- domain id (so that this DomainInfo is added to the
                -- existing entry for that domain)
                substDomain :: (DomainId, DomainInfo) ->
                               Maybe (DomainId, DomainInfo)
                substDomain edge@(child_dom_id, child_dom_info) =
                    case (findInputParentDomain child_dom_info) of
                        [] ->
                            case (findOutputParentDomain child_dom_info) of
                                Nothing ->
                                    -- no change
                                    Just edge
                                Just parent_dom_id ->
                                    -- same info, but add to the parent domain
                                    Just (parent_dom_id, child_dom_info)
                        ds | any (\(_,md) -> isNothing md) ds ->
                            -- remove this clock
                            Nothing
                        ds ->
                            -- substitute each (child,parent) clock pair
                            -- to create the new domain info
                            let parent_dom_id =
                                  case ds of
                                     ((_, Just (i,_)):_) -> i
                                     _ -> internalError "combineDomainInfoMap substDomain"
                                ps = [ (c,p) | (c, Just(_,p)) <- ds ]
                                sub dom_info (child_clk,parent_clk) =
                                    substInputClockInDomainInfo child_clk
                                                                parent_clk
                                                                dom_info
                                new_dom_info = foldl sub child_dom_info ps
                            in Just (parent_dom_id, new_dom_info)
            in
                catMaybes $ map substDomain qual_child_edges

        -- pair a child output clock name with the aclk as seen by the child
        -- (uses the substituted child edges, to account for input clocks
        -- which are used by output clocks; if the input clock was noClock,
        -- then the clk_id won't be found in this map, so assume noClock
        -- if not found)
        child_outclk_map :: [(AId, AClock)]
        child_outclk_map =
            concatMap (di_output_clocks . snd) subst_qual_child_edges

        -- update the parent map, with any output clocks
        subst_parent_info_map =
            let
                -- returns Nothing if the info is not to be changed
                -- and otherwise returns Just the updated info
                substDomain :: (DomainId, DomainInfo) ->
                               Maybe (DomainId, DomainInfo)
                substDomain edge@(parent_dom_id, parent_dom_info) =
                    case (lookup parent_dom_id output_clock_substs) of
                        Nothing -> Nothing
                        Just (clk_id, aclk_in_parent) ->
                          case (lookup clk_id child_outclk_map) of
                            Just aclk_in_child ->
                              Just $
                               (parent_dom_id,
                                substOutputClockInDomainInfo
                                  aclk_in_parent aclk_in_child parent_dom_info)
                            Nothing ->
                              -- the domain is empty, so substitute noClock
                              Just $
                               (parent_dom_id,
                                substOutputClockInDomainInfo
                                  aclk_in_parent noClock parent_dom_info)

                -- get the changed edges
                changed_edges =
                    catMaybes $ map substDomain (M.toList parent_info_map)
            in
                -- update the parent map
                -- (taking advantage of the fact that "add" overwrites)
                (M.fromList changed_edges) `M.union` parent_info_map

        -- ----------

        -- remove output clocks from the child edges before joining
        -- to the parent, since they are not outputs of the parent
        subst_qual_child_edges_no_outclks =
            let rmOutClks dinfo = dinfo { di_output_clocks = [] }
            in  mapSnd rmOutClks subst_qual_child_edges

        subst_child_info_map = M.fromListWith joinDomainInfo subst_qual_child_edges_no_outclks
        combinedInfo = M.unionWith joinDomainInfo subst_child_info_map subst_parent_info_map
    in  combinedInfo


combineSchedDRDB :: String -> [(SchedNode,[SchedNode])] -> S.Set AId ->
                    DisjointRulesDB -> DisjointRulesDB ->
                    DisjointRulesDB
combineSchedDRDB inst parent_use_map child_meth_set parent_map child_map =
    let
        -- start by adding all nodes in the child map to the parent map,
        -- which requires qualifying all the nodes of the child
        -- (but don't include methods)
        isMethId i = i `S.member` child_meth_set
        child_edges = mapSnd S.toList (M.toList child_map)
        child_rule_edges =
            let -- first remove edges from method Ids
                edges' = filter (not . isMethId . fst) child_edges
            in  -- then remove edges to method Ids
                map (\ (n,ns) -> (n, filter (not . isMethId) ns)) edges'
        -- qualify the remaining edges
        qual_child_edges = mapSnd (S.fromList) $
                               qualifyChildDRDBGraph inst child_rule_edges
        start_comb_map = (M.fromList qual_child_edges) `M.union` parent_map

        -- the disjoint map should be the same in both directions,
        -- so no need to reverse it!

        -- but combine sched and exec nodes of parent rules and
        -- remove uses of sched node (RDY signals) and flatten to just AId
        flat_use_map =
            let convEdge (snode, ns) =
                    (getSchedNodeId snode,
                     map getSchedNodeId (filter (not . isSchedNode) ns))
                flat_edges = map convEdge parent_use_map
            in  foldr (uncurry (M.insertWith union)) M.empty flat_edges

        -- but we do need to reverse the use map
        rev_flat_use_map = reverseMap flat_use_map

        findDisjointChildRules :: AId -> [AId]
        findDisjointChildRules methId =
            case (M.lookup methId child_map) of
                Nothing -> []
                Just nset -> filter (not . isMethId) (S.toList nset)

        findDisjointParentRules :: AId -> [AId]
        findDisjointParentRules methId =
            case (M.lookup methId child_map) of
                Nothing -> []
                Just nset ->
                    let meths = filter isMethId (S.toList nset)
                        lookupMeth m =
                            case (M.lookup m rev_flat_use_map) of
                                Nothing -> []
                                Just parent_ns -> parent_ns
                    in  foldr union [] (map lookupMeth meths)

        handleParentNode :: (AId, [AId]) -> DisjointRulesDB ->
                            DisjointRulesDB
        handleParentNode (parentId, uses) dmap =
            let handleUse :: AId -> DisjointRulesDB -> DisjointRulesDB
                handleUse useId dmap =
                    let child_disjoints = map (qualifyChildId inst)
                                              (findDisjointChildRules useId)
                        parent_disjoints = findDisjointParentRules useId
                        disjoints = child_disjoints ++ parent_disjoints
                        edges = [(parentId, S.fromList disjoints)] ++
                                [(d, S.singleton parentId) | d <- disjoints]
                    in  M.unionWith S.union (M.fromListWith S.union edges) dmap
            in  foldr handleUse dmap uses
    in
        foldr handleParentNode start_comb_map (M.toList flat_use_map)


combineSchedRuleRelDB :: String -> [(SchedNode,[SchedNode])] -> S.Set AId ->
                         RuleRelationMap -> RuleRelationMap ->
                         RuleRelationMap
combineSchedRuleRelDB inst parent_use_map child_meth_set parent_map child_map =
    let
        isMethId i = i `S.member` child_meth_set

        -- combine sched and exec nodes of parent rules and
        -- remove uses of sched node (RDY signals) and flatten to just AId
        flat_use_map =
            let convEdge (snode, ns) =
                    (getSchedNodeId snode,
                     map getSchedNodeId (filter (not . isSchedNode) ns))
                flat_edges = map convEdge parent_use_map
            in  foldr (uncurry (M.insertWith union)) M.empty flat_edges

        -- reverse to make it a map from child Id to parent uses
        rev_flat_use_map = reverseMap flat_use_map

        -- make a new set of edges (with possible duplicates) by qualifying
        -- children IDs and replacing methods with parent rules that call them

        expandMeth i =
            if (isMethId i)
            then case (M.lookup i rev_flat_use_map) of
                   Nothing -> []
                   Just parent_ns -> parent_ns
            else [qualifyChildId inst i]

        makePairs i1s i2s = [ (i1, i2) | i1 <- i1s, i2 <- i2s ]

        new_map_pairs =
            let
                expandFn ((i1, i2), rri) =
                    let qual_rri = qualifyChildRuleRelationInfo inst rri
                        ks = makePairs (expandMeth i1) (expandMeth i2)
                    in  [ (k, qual_rri) | k <- ks ]
            in
                concatMap expandFn (M.toList child_map)

    in
        map_insertManyWith unionRuleRelationInfo new_map_pairs parent_map


combineSchedConflicts :: String -> [(SchedNode,[SchedNode])] -> S.Set AId ->
                         ConflictMap -> ConflictMap -> ConflictMap
combineSchedConflicts inst parent_uses child_meth_set parent_cs child_cs =
    let
        -- start by adding all conflicts in the child list to the parent list,
        -- which requires qualifying all the conflicts of the child
        -- (but don't add conflicts from or to methods!)
        isMethId i = i `S.member` child_meth_set
        child_edges = M.toList child_cs
        child_rule_edges =
            let -- first remove edges from method nodes
                edges' = filter (not . isMethId . fst) child_edges
            in  -- then remove any ingoing nodes
                map (\ (n,ns) -> (n, filter (not . isMethId) ns)) edges'
        -- qualify the remaining edges
        qual_child_edges = qualifyChildConflictGraph inst child_rule_edges
        -- add them to the parent
        start_comb_cs = M.union (M.fromList qual_child_edges) parent_cs

        -- for finding incoming edges, reverse the child list
        -- XXX are we constructing this more than once, if we instantiate
        -- XXX the same module multiple times?
        rev_child_cmap = reverseConflictMap child_cs

        -- XXX until rules can block methods, this is empty
        findBlockers :: AId -> [AId]
        findBlockers methId = []

        findBlockees :: AId -> [AId]
        findBlockees methId =
            case (M.lookup methId rev_child_cmap) of
                Nothing -> []
                    -- value methods will not be found, so don't error
                    --internalError ("findBlockees: " ++ ppReadable methId)
                Just ns -> ns
                    -- don't reintroduce edges to methods
                    -- XXX can't happen because method conflicts are
                    -- XXX annotated and not in the conflicts list
                    --filter (not . isMethId) ns

        -- for each use of a given node in the parent schedule,
        -- we do two things:
        --   * If there are any conflicts which block the used method
        --     (not possible until rules can be more urgent), we add those
        --     blockers to the parent rule's list.
        --   * If there are any rules which are blocked by the method,
        --     they now have to be blocked by all the parent rules which
        --     use the method.
        -- XXX does it matter if the parent node is a sched or exec node?
        -- XXX Can ignore uses in sched nodes, since they are only value
        -- XXX methods, and so any blocker would show up in the RDY
        -- XXX (that is, for now value methods don't have a CF/WF, and
        -- XXX don't appear in the conflicts in the schedule).

        handleParentNode :: (SchedNode, [SchedNode]) -> ConflictMap ->
                            ConflictMap
        -- XXX ignore sched nodes as described above
        handleParentNode (Sched _, _) cmap = cmap
        handleParentNode (Exec parentId, uses) cmap =
            let
                handleUse :: SchedNode -> ConflictMap -> ConflictMap
                -- XXX ignore sched node as described above
                handleUse (Sched _) cmap = cmap
                handleUse (Exec useId) cmap =
                    let outs = findBlockers useId
                        q_outs = map (qualifyChildId inst) outs
                        ins = findBlockees useId
                        q_ins = map (qualifyChildId inst) ins
                        edges = [(parentId, q_outs)] ++
                                [(q_in, [parentId]) | q_in <- q_ins]
                        trace_dump =
                            if (trace_mergesched)
                            then trace("combine conflicts: (pnode,use) = " ++
                                       ppReadable (parentId,useId)) $
                                 trace("  ins: " ++ ppReadable ins) $
                                 trace("  outs: " ++ ppReadable outs)
                            else id
                    in
                        trace_dump $
                        M.unionWith (++) (M.fromListWith (++) edges) cmap
            in  foldr handleUse cmap uses
    in
        foldr handleParentNode start_comb_cs parent_uses


combineSchedMap :: String -> [(SchedNode,[SchedNode])] -> S.Set AId ->
                   SchedMap -> SchedMap -> SchedMap
combineSchedMap inst parent_uses child_meth_set parent_smap child_smap =
    let
        -- start by adding all nodes in the child to the parent,
        -- which requires qualifying all the nodes of the child
        -- (but don't add edges from or to methods!)
        isMethSN sn = (getSchedNodeId sn) `S.member` child_meth_set
        child_edges = M.toList child_smap
        child_rule_edges =
            let -- first remove edges from method nodes
                edges' = filter (not . isMethSN . fst) child_edges
            in  -- then remove any ingoing nodes
                map (\ (n,ns) -> (n, filter (not . isMethSN) ns)) edges'
        -- qualify the remaining edges
        qual_child_edges = qualifyChildSchedGraph inst child_rule_edges
        start_comb_smap = M.union (M.fromList qual_child_edges) parent_smap

        -- for finding incoming edges, reverse the child map
        -- XXX are we constructing this more than once, if we instantiate
        -- XXX the same module multiple times?
        rev_child_smap = reverseSchedMap child_smap

        -- XXX maybe the best thing to do here is to first add all
        -- XXX edges from parent rules to methods they use.
        -- XXX *then* remove all methods, one at a time, by reconnecting
        -- XXX ingoing and outgoing nodes.
        -- XXX this allows for two rules to get an edge because two methods
        -- XXX had an edge, etc.

        -- find outgoing edges
        findOutEdges use_node =
            case (M.lookup use_node child_smap) of
                Nothing -> internalError ("findOutEdges")
                Just [] -> []
                Just ns ->
                    -- don't reintroduce edges to methods
                    filter (not . isMethSN) ns

        -- find ingoing edges
        findInEdges use_node =
            case (M.lookup use_node rev_child_smap) of
                Nothing -> internalError ("findInEdges: " ++ ppReadable (use_node, M.toList rev_child_smap))
                Just [] -> []
                Just ns ->
                    -- don't reintroduce edges to methods
                    filter (not . isMethSN) ns

        -- for each use of a given node in the parent schedule,
        -- figure out whether to use Sched or Exec node
        -- and lookup the outgoing edges and add them to the parent schedule
        handleParentNode :: (SchedNode, [SchedNode]) -> SchedMap -> SchedMap
        handleParentNode (pnode, uses) sched_map =
            let
                handleUse :: SchedNode -> SchedMap -> SchedMap
                handleUse use_node sched_map =
                    let outs = findOutEdges use_node
                        q_outs = map (qualifyChildSchedNode inst) outs
                        ins = findInEdges use_node
                        q_ins = map (qualifyChildSchedNode inst) ins
                        edges = [(pnode, q_outs)] ++
                                [(q_in, [pnode]) | q_in <- q_ins]
                        trace_dump =
                            if (trace_mergesched)
                            then trace("pnode: " ++ ppReadable pnode) $
                                 trace("  uses: " ++ ppReadable use_node) $
                                 trace("  ins: " ++ ppReadable ins) $
                                 trace("  outs: " ++ ppReadable outs) $
                                 trace("  edges: " ++ ppReadable edges)
                            else id
                    in
                        trace_dump $
                        M.unionWith (++) (M.fromListWith (++) edges) sched_map
            in  foldr handleUse sched_map uses
    in
        foldr handleParentNode start_comb_smap parent_uses


-- from the submodule whose edges should be merged with this SchedNode.
-- (Note that we merge an Exec node of a parent rule with the Sched and
-- Exec for the methods that the rule calls, not just the Exec.  This is
-- to account for the possibility that the method is called conditionally
-- inside the rule, and so the rule body must execute to compute whether
-- the method is scheduled -- so the rule must execute before anything
-- which depends on the scheduling of the method, such as the scheduling
-- of a less-urgent conflicting rule.)
findUses :: ParentUseMap -> RdyMap -> String -> SchedNode -> [SchedNode]
findUses use_map rdy_map inst snode =
    let rId = getSchedNodeId snode
        (pred_uses, body_uses) = findParentUses use_map (rId, inst)
        convertUseToNode mId = if (isRdyId mId)
                               then [Sched (findRdyMeth rdy_map mId)]
                               else [Sched mId, Exec mId] -- see comment
        uses = if (isSchedNode snode)
               then pred_uses
               else body_uses
    in  concatMap convertUseToNode uses


-- ===============
-- Rather than hardcode the remove of fs_rdy to get the the Id for which
-- a ready method is associated, we can create an authoritative map by
-- looking at the def references of the individual methods.

type RdyMap = M.Map AId AId

mkRdyMap :: ABinModInfo -> RdyMap
mkRdyMap abi =
    let apkg = abmi_apkg abi
        ifcs = apkg_interface apkg
        -- clocks and resets don't have Rdy methods
        mkPair (AIClock {}) = []
        mkPair (AIReset {}) = []
        mkPair ifc =
            let name = aif_name ifc
                pred_e = aIfacePred ifc
            in  if (isRdyId name)
                then [] -- Rdy methods don't have Rdy methods
                else case (pred_e) of
                         (ASDef _ pred_i) -> [(pred_i, name)]
                         (ASInt {})       -> []
                         _ -> internalError
                                ("mkRdyMap: pred is not a def or const: " ++
                                 ppReadable (name, pred_e))
    in  M.fromList $ concatMap mkPair ifcs

-- This takes a Rdy Id and returns the Id of the method for which it
-- is the Rdy.
findRdyMeth :: RdyMap -> AId -> AId
findRdyMeth rdy_map rdyId =
    case M.lookup rdyId rdy_map of
        Just mId -> mId
        Nothing -> internalError ("SimExpand.findRdyMeth: cannot find " ++
                                  ppReadable rdyId ++
                                  ppReadable (M.toList rdy_map))


-- ===============
-- Functions for qualifying Ids in data from a submodule with its instance
-- so that it will not clash when added into the parent module's data.

-- Qualify an Id by using the qualifier field of the Id,
-- leaving the base identifier unchanged.
-- This allows us to extract the base Id and manipulate it, independent
-- of the qualifier (like adding "CAN_FIRE_" to a rule Id).

-- Hierarchy is indicated with "." between the instance names,
-- so if there is already a qualifier, add the instance in front with dot.
-- XXX what happens if there's a dot in an escaped name? "\foo.bar"

qualifyChildId :: String -> AId -> AId
qualifyChildId inst i =
    let q_str = getIdQualString i
        q_str' = if (q_str == "")
                 then inst
                 else inst ++ "." ++ q_str
    in  setIdQualString i q_str'



-- Functions to qualify Ids in CombSchedInfo data

qualifyChildSchedNode :: String -> SchedNode -> SchedNode
qualifyChildSchedNode inst (Sched i) = (Sched (qualifyChildId inst i))
qualifyChildSchedNode inst (Exec i) = (Exec (qualifyChildId inst i))

qualifyChildSchedGraph :: String -> [(SchedNode,[SchedNode])] ->
                          [(SchedNode,[SchedNode])]
qualifyChildSchedGraph inst edges =
    let qualifyEdge (n, ns) = (qualifyChildSchedNode inst n,
                               map (qualifyChildSchedNode inst) ns)
    in  map qualifyEdge edges

qualifyChildConflictGraph :: String -> [(AId,[AId])] -> [(AId,[AId])]
qualifyChildConflictGraph inst edges =
    let qualifyEdge (i, is) = (qualifyChildId inst i,
                               map (qualifyChildId inst) is)
    in  map qualifyEdge edges

qualifyChildDRDBGraph :: String -> [(AId,[AId])] -> [(AId,[AId])]
qualifyChildDRDBGraph inst edges =
    let qualifyEdge (r, rs) = (qualifyChildId inst r,
                               map (qualifyChildId inst) rs)
    in  map qualifyEdge edges

qualifyChildDomainId :: String -> DomainId -> DomainId
qualifyChildDomainId inst (i,d) = (qualifyChildId inst i, d)

qualifyChildDomainInfo :: String -> DomainInfo -> DomainInfo
qualifyChildDomainInfo inst dinfo =
    let qualifyClocks = map (qualifyChildAClock inst)
        qualifyDomains = map (qualifyChildDomainId inst)
        qualifyRules =
            let qualifyRule rule_id = qualifyChildId inst rule_id
            in  map qualifyRule
        qualifyPrims =
            let qualifyPrim (prim_id, (clk_arg, aclk)) =
                    (qualifyChildId inst prim_id,
                     (clk_arg, qualifyChildAClock inst aclk))
            in  map qualifyPrim
        qualifyResets = mapFst (qualifyChildId inst)
        qualifyOutputClks = mapSnd (qualifyChildAClock inst)
        qualifyClkSubsts =
            let qualSubst (a,b) = (qualifyChildAClock inst a,
                                   qualifyChildAClock inst b)
            in  map qualSubst
    in  DomainInfo {
            di_clocks               = qualifyClocks (di_clocks dinfo),
            di_domains              = qualifyDomains (di_domains dinfo),
            di_rules                = qualifyRules (di_rules dinfo),
            di_clock_crossing_rules = qualifyRules (di_clock_crossing_rules dinfo),
            di_prims                = qualifyPrims (di_prims dinfo),
            di_prim_resets          = qualifyResets (di_prim_resets dinfo),
            di_output_clocks        = qualifyOutputClks (di_output_clocks dinfo),
            di_clock_substs         = qualifyClkSubsts (di_clock_substs dinfo)
        }

-- XXX alternatively, we can declare QualifiedAClock,
-- XXX to be a qualifier plus the underlying AClock ?
qualifyChildAClock :: String -> AClock -> AClock
-- This is called on substitution pairs where the value might be "noClock"
-- instead of a port, so don't call "qualifyChildOsc" in that situation.
qualifyChildAClock inst aclk | isNoClock aclk = aclk
qualifyChildAClock inst (AClock osc gate) =
    AClock (qualifyChildOsc inst osc) (qualifyChildGate inst gate)

qualifyChildOsc :: String -> AExpr -> AExpr
qualifyChildOsc inst (ASPort t pid) =
    (ASPort t (qualifyChildId inst pid))
qualifyChildOsc inst e =
    internalError ("qualifyChildOsc: unexpected expr " ++
                   ppReadable e)

qualifyChildGate :: String -> AExpr -> AExpr
qualifyChildGate inst (AMGate t oid cid) =
    (AMGate t (qualifyChildId inst oid) cid)
qualifyChildGate inst (ASPort t g) = (ASPort t (qualifyChildId inst g))
qualifyChildGate inst e | isTrue e = e
qualifyChildGate inst e =
    internalError ("qualifyChildGate: unexpected expr " ++
                   ppReadable e)


qualifyChildRuleRelationInfo :: String -> RuleRelationInfo -> RuleRelationInfo
qualifyChildRuleRelationInfo inst rri =
    RuleRelationInfo {
        mCF     = fmap (qualifyChildConflicts inst) (mCF rri),
        mSC     = fmap (qualifyChildConflicts inst) (mSC rri),
        mRes    = fmap (qualifyChildConflicts inst) (mRes rri),
        mCycle  = fmap (qualifyChildConflicts inst) (mCycle rri),
        mPragma = fmap (qualifyChildConflicts inst) (mPragma rri),
        mArb    = fmap (qualifyChildConflicts inst) (mArb rri)
    }

qualifyChildConflicts :: String -> Conflicts -> Conflicts
qualifyChildConflicts inst (CUse mpairs) =
    let mapFn (m1, m2) = (qualifyChildMethodId inst m1,
                          qualifyChildMethodId inst m2)
    in  CUse (map mapFn mpairs)
qualifyChildConflicts inst (CCycle rIds) =
    CCycle (map (qualifyChildId inst) rIds)
qualifyChildConflicts inst c@(CResource mId) =
    CResource (qualifyChildMethodId inst mId)
qualifyChildConflicts inst c@(CMethodsBeforeRules) = c
qualifyChildConflicts inst c@(CUserEarliness _) = c
qualifyChildConflicts inst c@(CUserAttribute _) = c
qualifyChildConflicts inst c@(CUserPreempt _) = c
qualifyChildConflicts inst c@(CArbitraryChoice) = c
qualifyChildConflicts inst c@(CFFuncArbitraryChoice) = c

qualifyChildMethodId :: String -> MethodId -> MethodId
qualifyChildMethodId inst (MethodId objId methId) =
    MethodId (qualifyChildId inst objId) methId


-- ===============
-- Functions for creating the maps in SimPackage

mkDefMap :: [ADef] -> DefMap
mkDefMap ds = M.fromList $ map (\d -> (adef_objid d,d)) ds

mkAVInstMap :: [AVInst] -> AVInstMap
mkAVInstMap avis = M.fromList $ map (\inst -> (avi_vname inst, inst)) avis

mkMethodOrderMap :: [AVInst] -> MethodOrderMap
mkMethodOrderMap avis =
    let mkMethodOrderSet avi =
            S.fromList $ sSB (methodConflictInfo (vSched (avi_vmi avi)))
    in  M.fromList $ map (\avi -> (avi_vname avi, mkMethodOrderSet avi)) avis


-- ===============
-- Data and functions for creating method use maps

-- the code for creating the map is similar to AUses.aRuleUseMap,
-- but this creates the data structure that's better here,
-- and we choose to re-compute the info to both be sure that it's
-- up-to-date and to not have to write the info the .ba file

-- ---------------

-- map from a submod instance name to a map from each rule/method in
-- the parent module to uses in the child module (pred uses, body uses)
type ParentUseModMap = M.Map String ParentUseMap
-- given (ruleId, instId), return the (sched uses, exec uses)
-- of that rule/method on that submodule instance
type ParentUseMap = M.Map (AId, String) Uses
-- The uses by a rule/method are (sched uses, exec uses)
type Uses = ([AId], [AId])

findParentUseMap :: ParentUseModMap -> String -> ParentUseMap
findParentUseMap pumod_map mod =
    case M.lookup mod pumod_map of
        Just pumap -> pumap
        Nothing -> internalError ("SimExpand.findParentUseMap: cannot find " ++
                                  mod)

findParentUses :: ParentUseMap -> (AId, String) -> Uses
findParentUses use_map idx =
    case M.lookup idx use_map of
        Just uses -> uses
        Nothing -> -- no entry means there are no uses of that rule with
                   -- that module, so return empty uses
                   -- XXX if we wanted some sanity checking, we could have
                   -- XXX put in empty entries; but it would also slow down
                   -- XXX lookup
                   ([], [])
{-
             internalError ("SimExpand.findParentUses: cannot find " ++
                                  ppReadable idx ++
                                  ppReadable (M.toList use_map))
-}

-- ---------------

mkParentUseModMap :: [(String, ABinModInfo)] -> ParentUseModMap
mkParentUseModMap abis =
    let edges = [ (mod, mkParentUseMap abi) | (mod, abi) <- abis ]
    in  M.fromList edges

mkParentUseMap :: ABinModInfo -> ParentUseMap
mkParentUseMap parent_abi =
    let apkg = abmi_apkg parent_abi
        local_defs = apkg_local_defs apkg
        ifcs = apkg_interface apkg
        rs = apkg_rules apkg

        -- definitions of the value methods in the interface
        ifc_defs = [d | (AIDef { aif_value = d }) <- ifcs] ++
                   [d | (AIActionValue { aif_value = d }) <- ifcs]
        defs = ifc_defs ++ local_defs
        defUseMap = M.fromList [(d, eDomain defUseMap e) | ADef d _ e _<- defs]

        use_infos = (concatMap cvtIfc ifcs) ++ (map cvtARule rs)

        -- This is a map from ruleId to uses on all submodules
        raw_use_pairs = [ (rId, raw_uses)
                            | uinfo <- use_infos,
                              let rId = user_name uinfo,
                              let raw_uses = rUses defUseMap uinfo ]

        -- convert a list of raw uses into a map for pairs (rId,inst)
        cvtRawUses (rId, (pred_raw_uses, body_raw_uses)) map_so_far =
            let
                -- function for adding uses to an existing list
                -- (the 2nd pair will be shorted, so start with it)
                comb (as1, bs1) (as2, bs2) = ((as2 ++ as1), (bs2 ++ bs1))

                cvtOnePredRawUse (inst,meth) m =
                    M.insertWith comb (rId, getIdString inst) ([meth],[]) m
                cvtOneBodyRawUse (inst,meth) m =
                    M.insertWith comb (rId, getIdString inst) ([],[meth]) m

                map_with_pred_uses =
                    foldr cvtOnePredRawUse map_so_far pred_raw_uses
                map_with_all_uses =
                    foldr cvtOneBodyRawUse map_with_pred_uses body_raw_uses
            in
                map_with_all_uses

        rUseMap = foldr cvtRawUses M.empty raw_use_pairs
    in
        rUseMap


-- ---------------

-- Returns the (pred uses, body uses) for a given rule/method useinfo.
-- A use is a method Id on a particular instance (instId, methId).
rUses :: M.Map AId [(AId,AId)] -> UseInfo -> ([(AId,AId)], [(AId,AId)])
rUses m (UseInfo _ pred_reads body_reads body_writes) =
    let
        body_action_uses = mergeUses $ map (aUses m) body_writes
        body_read_uses = mergeUses $ map (eDomain m) body_reads
        pred_read_uses = mergeUses $ map (eDomain m) pred_reads
    in
        (pred_read_uses, body_action_uses `union` body_read_uses)

mergeUses :: [[(AId, AId)]] -> [(AId, AId)]
mergeUses = stableOrdNub . concat

-- Returns the method uses in an action.
-- A use is a method Id on a particular instance (instId, methId)
aUses :: M.Map AId [(AId,AId)] -> AAction -> [(AId,AId)]
aUses m a@(ACall i mi es) =
    [(i, unQualId mi)] ++ mergeUses (map (eDomain m) es)
aUses m a@(AFCall i _ _ es isAssump) =
    if isAssump then [] else mergeUses $ map (eDomain m) es
aUses m a@(ATaskAction i _ _ _ es _ _ isAssump) =
    if isAssump then [] else mergeUses $ map (eDomain m) es

-- Returns the method uses in an expression.
-- A use is a method Id on a particular instance (instId, methId)
eDomain :: M.Map AId [(AId,AId)] -> AExpr -> [(AId,AId)]
eDomain m (APrim _ _ _ es) = mergeUses $ map (eDomain m) es
eDomain m e@(AMethCall _ i mi es) =
    mergeUses ([(i, unQualId mi)] : map (eDomain m) es)
-- don't count the return value uses of actionvalue, only the action part
eDomain m (AMethValue _ _ _) = []
eDomain m (ATupleSel _ e _) = eDomain m e
eDomain m (ATuple _ es) = mergeUses $ map (eDomain m) es
eDomain m (ANoInlineFunCall _ _ _ es) = mergeUses $ map (eDomain m) es
eDomain m (AFunCall _ _ _ _ es) = mergeUses $ map (eDomain m) es
eDomain _ e@(ASPort _ i) = []
eDomain _ e@(ASParam _ i) = []
eDomain m (ASDef _ d) = M.findWithDefault err d m
    where err = internalError $
                "SimExpand.eDomain: no definition for " ++ ppReadable d ++
                    ppReadable (M.toList m)
eDomain _ (ASInt _ _ _) = []
eDomain _ (ASReal _ _ _) = []
eDomain _ (ASStr _ _ _) = []
eDomain _ (ASAny _ _) = []
-- the uses are counted on the action side
eDomain _ (ATaskValue { }) = []
eDomain _ e@(ASClock { }) =
    internalError ("SimExpand.eDomain unexpected clock" ++ ppReadable e)
eDomain _ e@(ASReset { }) =
    internalError ("SimExpand.eDomain unexpected reset" ++ ppReadable e)
eDomain _ e@(ASInout { }) =
    internalError ("SimExpand.eDomain unexpected inout" ++ ppReadable e)
eDomain _ (AMGate { }) = []

-- ---------------

-- extract from a rule or method:
--  (predicate reads, body reads, body actions)

data UseInfo = UseInfo { user_name :: AId
                       , pred_reads :: [AExpr]
                       , body_reads :: [AExpr]
                       , body_actions :: [AAction]
                       }

cvtARule :: ARule -> UseInfo
cvtARule (ARule rId _ _ _ rPred rActs _ rOrig) = UseInfo
    { user_name = rId
    , pred_reads = [rPred]
    , body_reads = []
    , body_actions = rActs
    }

cvtIfc :: AIFace -> [UseInfo]
cvtIfc (AIAction _ _ ifPred ifId ifRs _) =
    -- note that if we had used cvtIfc from AUses, we wouldn't
    -- have been able to distinguish pred reads from non-pred reads
    [(UseInfo rId [ifPred, rPred] [] rActs)
        | (ARule rId _ _ _ rPred rActs _ _) <- ifRs]
cvtIfc (AIActionValue _ _ ifPred ifId ifRs (ADef dId t _ _) _) =
    -- similar to converting an action, but include the return value
    -- in the body value uses of each split rule
    -- (note that, if the method body is not split into multiple
    -- rule, dId and rId will be the same)
    [(UseInfo rId [ifPred, rPred] [dExpr] rActs)
        | (ARule rId _ _ _ rPred rActs _ _) <- ifRs]
        where dExpr = ASDef t dId
cvtIfc (AIDef _ _ _ ifPred (ADef dId t _ _) _ _)
    | isRdyId dId = []
    | otherwise   = [(UseInfo dId [ifPred] [dExpr] [])]
        where dExpr = ASDef t dId
cvtIfc (AIClock {}) = []
cvtIfc (AIReset {}) = []
cvtIfc (AIInout {}) = []


-- ===============

getABI :: String -> [(String, ABinModInfo)] -> ABinModInfo
getABI mod abis =
    case (lookup mod abis) of
        Nothing -> internalError ("getABI: " ++ mod ++ "\n" ++
                                  ppReadable (map fst abis))
        Just x -> x

-- ===============

-- If the backend is Bluesim,
-- check that the package does not contain any features not supported
-- by the Bluesim backend:
-- - Inout not supported in the provided interface
-- - Inout not supported as a module argument
-- - Dynamic expressions for ports on submodule instantiations
--   (for this, we also inline the
-- Returns the package, possibly with submod port expressions inlined.
-- When compiling for Verilog, we just return the package, unchanged.
-- XXX Note that when the backend is not Bluesim, but the .ba file is not
-- XXX marked Verilog-only, then the following Bluesim-only checks
-- XXX could still be done, but would taint the .ba file to be
-- XXX Verilog-only and we would issue a warning.
-- The first argument is whether the backend is Bluesim
simCheckPackage :: ErrorHandle -> Bool -> APackage -> IO APackage
simCheckPackage errh False apkg = return apkg
simCheckPackage errh True apkg = do
    -- check for unsupported primitives (such as MCD)
    checkBluesimPrimitives errh apkg

    -- check for Inout in the ifc and the arguments
    checkInout errh apkg

    -- check for split methods
    checkSplitMethods errh apkg

    -- check for dynamic ports (and also inline submodule port/param exprs)
    apkg' <- simExpandParams errh apkg

    return apkg'

-- ----------

checkInout :: ErrorHandle -> APackage -> IO ()
checkInout errh apkg = do
    let pos = getPosition (apkg_name apkg)

    -- check for Inout in the ifc
    let inout_ifcs = [ i | (AIInout i _ _) <- apkg_interface apkg ]
        ifc_errs =
            if (null inout_ifcs)
            then []
            else [(pos, EBSimInoutIfc (map getIdString inout_ifcs))]

    -- check for Inout arguments
    let inout_args = [ i | (AAI_Inout i _) <- apkg_inputs apkg ]
        arg_errs =
            if (null inout_args)
            then []
            else [(pos, EBSimInoutArg Nothing (map getIdString inout_args))]

    -- report all the Inout errors together (rather than stop at the first)
    let errs = ifc_errs ++ arg_errs
    when (not (null errs)) $
        bsError errh errs

-- ----------

checkSplitMethods :: ErrorHandle -> APackage -> IO ()
checkSplitMethods errh apkg = do
    let pos = getPosition (apkg_name apkg)
        ifcs = apkg_interface apkg

    let split_methods =
            [ i | (AIAction { aif_name = i, aif_body = rs }) <- ifcs,
                  length rs > 1 ] ++
            [ i | (AIActionValue { aif_name = i, aif_body = rs }) <- ifcs,
                  length rs > 1 ]
    when (not (null split_methods)) $
        bsError errh
            [(pos, EBSimSplitMethods (map getIdString split_methods))]

-- ----------

simExpandParams :: ErrorHandle -> APackage -> IO APackage
simExpandParams errh apkg =
    let
        defs = apkg_local_defs apkg
        dmap = M.fromList [ (i, aSubst dmap e) | ADef i _ e _ <- defs ]
        port_ids = [ i | AAI_Port (i,_) <- apkg_inputs apkg ]

        inlineArg (Param {}, expr) = aSubst dmap expr
        inlineArg (Port {},  expr) = aSubst dmap expr
        inlineArg (_,        expr) = expr

        inlineArgs avi =
            let varginfo = vArgs (avi_vmi avi)
                es = avi_iargs avi
                es' = map inlineArg (zip varginfo es)
            in  avi { avi_iargs = es' }

        insts = apkg_state_instances apkg
        insts' = map inlineArgs insts
        apkg' = apkg { apkg_state_instances = insts' }

        emsgs = concatMap (checkInstArgs port_ids) insts'
    in        if (null emsgs)
        then return apkg'
        else bsError errh emsgs


-- The first argument is a list of ports to the parent module
-- (we will check later that they are constant, so we can assume
-- that they are constant here)
-- We also go ahead and do a (redundant) check that none of the submodule
-- arguments are Inout.
checkInstArgs :: [AId] -> AVInst -> [EMsg]
checkInstArgs port_ids avi =
    let
        inst_name = avi_vname avi
        iarg_pairs = getInstArgs avi
        -- the only clk/rst, if any, are the defaults.
        -- drop them and only consider the other arguments
        iarg_pairs_no_clk =
            filter (\ (i,e) -> not (isClock i || isReset i) ) iarg_pairs
        -- separate Inout from normal ports/params
        (iarg_pairs_inout, iarg_pairs_port_or_param) =
            partition (\ (i,e) -> isInout i ) iarg_pairs_no_clk

        getIArgNames ia_pairs =
            map (getIdString . getVArgInfoName . fst) ia_pairs

        -- Bluesim does not support Inout, so create errors
        inout_iarg_names = getIArgNames iarg_pairs_inout
        inout_iarg_errs =
            if (null iarg_pairs_inout)
            then []
            else [(getPosition inst_name,
                   EBSimInoutArg (Just (getIdString inst_name)) inout_iarg_names)]

        -- Bluesim does not support dynamic ports, so create errors
        dynamic_iarg_pairs =
            filter (not . isConstAExpr port_ids . snd) iarg_pairs_port_or_param
        -- the names of any ports with dynamic exprs
        dynamic_iarg_names = getIArgNames dynamic_iarg_pairs
        dynamic_iarg_errs =
            if (null dynamic_iarg_pairs)
            then []
            else [(getPosition inst_name,
                   EBSimDynamicArg (getIdString inst_name) dynamic_iarg_names)]

    in
        -- report as many at once
        inout_iarg_errs ++ dynamic_iarg_errs

-- ===============

-- Lift AIActionValue return values which are method calls
-- and any method return value which is a foreign call to
-- local defs.

makeMethodTemps :: APackage -> APackage
makeMethodTemps apkg =
  let (defs', iface') = cvt 1 (apkg_local_defs apkg) [] (apkg_interface apkg)
  in apkg { apkg_local_defs = defs', apkg_interface = iface' }
  where cvt _     defs iface [] = (defs, reverse iface)
        cvt seqNo defs iface (aif:aifs) =
          let (is_def, is_av) = case aif of
                                  (AIDef {})         -> (True,False)
                                  (AIActionValue {}) -> (False,True)
                                  otherwise          -> (False,False)
              v = aif_value aif
          in if is_def || is_av
             then case process is_av v (aif_name aif) seqNo of
                    (Just t@(ADef tid ty e props)) ->
                       let aid = adef_objid v
                           -- unclear if propagating the props is correct
                           new_def = (ADef aid ty (ASDef ty tid) props)
                           aif' = aif { aif_value = new_def }
                           in cvt (seqNo + 1) (t:defs) (aif':iface) aifs
                    Nothing -> cvt seqNo defs (aif:iface) aifs
             else cvt seqNo defs (aif:iface) aifs
        process is_av (ADef aid ty e@(AMethCall {}) props) name seqNo =
          if is_av
          then let tid = mkIdTempReturn is_av name seqNo
               in (Just (ADef tid ty e props))
          else Nothing
        process is_av (ADef aid ty e@(AFunCall {}) props) name seqNo =
          if (ae_isC e)
          then let tid = mkIdTempReturn is_av name seqNo
               in (Just (ADef tid ty e props))
          else Nothing
        process _ _ _ _ = Nothing


-- ===============
-- Convert noinline function uses into method calls on module instances

-- Assumes that noinline funcs are all top-level defs,
-- which aNoInline ensures.

-- Returns new defs (that call methods, not noinline functions)
-- and pairs of info for each instance (inst name, mod name)

getNoInlineInfo :: [ADef] -> ( [ADef], [(String, String)] )
getNoInlineInfo defs =
    let
        -- extract the output port name
        getOutPortName (_,[(oname,_)]) = oname
        getOutPortName _ = internalError "getNoInlineInfo: invalid ports"

        cvtDef (ADef di dt
                  (ANoInlineFunCall ft fi
                    (ANoInlineFun mod_name _ ports (Just inst_name))
                    es) props) =
            let
                pos = getPosition fi
                -- XXX because noinline "foreign" Id is escaped with an "_",
                -- XXX we can't get the method name from "fi"
                --methId = fi
                methId = mkId pos (mkFString (getOutPortName ports))
                instId = mkId pos (mkFString inst_name)
                new_def = ADef di dt (AMethCall ft instId methId es) props
            in
                (new_def, Just (inst_name, mod_name))
        cvtDef def = (def, Nothing)

        (new_defs, maybe_inst_infos) = unzip (map cvtDef defs)

        noinline_instances = catMaybes maybe_inst_infos
    in
        (new_defs, noinline_instances)


-- ===============

-- Extract the clock from a clock arg instantiation expr
getClkFromAExpr :: AExpr -> AClock
getClkFromAExpr (ASClock _ aclk) = aclk
getClkFromAExpr e = internalError ("SimExpand: getClkFromAExpr: " ++
                                   "not clock expr: " ++ ppReadable e)

isNoClock :: AClock -> Bool
isNoClock aclk = isFalse (aclock_osc aclk)

noClock :: AClock
noClock = AClock aFalse aFalse

{-
-- Given the expr for a clk, gate, or reset,
-- extract the port that the expr refers to
getPortId :: AExpr -> AId
getPortId (ASPort _ i) = i
getPortId e = internalError ("SimExpand getPortId: not a port: " ++ show e)

-- Alias for extracting an oscillator (in case the representation changes)
getOscId :: AExpr -> AId
getOscId = getPortId

-- Or get the oscillator Id in String form
getOscStr :: AExpr -> String
getOscStr = getIdString . getOscId

-- Alias for extracting a gate
getGateId :: AExpr -> AId
getGateId = getPortId

-- Or get the gate Id in String form
getGateStr :: AExpr -> String
getGateStr = getIdString . getGateId
-}

-- ===============

getWPropDomain :: AId -> WireProps -> ClockDomain
getWPropDomain i wprops =
    case (wpClockDomain wprops) of
        Just x -> x
        Nothing -> internalError ("getWPropDomain: " ++
                                  "rule/method with no clock: " ++
                                  ppReadable i)

-- ===============
-- check whether a module has a method which is required to be enabled
-- (so that Bluesim can reject simulating a design with always_enabled or
-- enabled_when_ready methods at the top-level)

hasEnabledMethod :: ABinModInfo -> Bool
hasEnabledMethod modInfo =
    let
        pps = abmi_pps modInfo
        apkg = abmi_apkg modInfo
        ifcs = apkg_interface apkg

        -- get just the methods with Action component
        getActionIfcs (AIAction { aif_name = i }) = [i]
        getActionIfcs (AIActionValue { aif_name = i }) = [i]
        getActionIfcs _ = []
        action_ifcs = concatMap getActionIfcs ifcs

        -- get just the pps for method enables
        isEnPragma (PPalwaysEnabled {}) = True
        isEnPragma (PPenabledWhenReady {}) = True
        isEnPragma _ = False
        en_pps = filter isEnPragma pps

        isEn i = (isAlwaysEn en_pps i) || (isEnWhenRdy en_pps i)
    in
        -- are any action methods required to be enabled
        (not (null en_pps)) && (any isEn action_ifcs)

-- ===============
-- Get the module arguments and parameters, so that Bluesim can reject
-- designs with top-level args.

getArgsAndParams :: ABinModInfo -> ([String],[String])
getArgsAndParams modInfo =
    let inputs = getAPackageInputs (abmi_apkg modInfo)
        params = filter (isParam . snd) inputs
        ports  = filter (isPort . snd) inputs
        params' = [ getIdBaseString i | (AAI_Port (i,_),_) <- params ]
        ports'  = [ getIdBaseString i | (AAI_Port (i,_),_) <- ports ]
    in (ports',params')

-- ===============

findGates :: [AAbstractInput] -> [AIFace] -> [ADef]  -> [AExpr]
findGates is fs ds =
    let
        in_gate_map = S.fromList [ g | (AAI_Clock _ (Just g)) <- is ]

        findGate e@(AMGate {}) gs                             = (e:gs)
        findGate e@(ASPort t i) gs | (S.member i in_gate_map) = (e:gs)
        findGate e gs                                         = gs

        def_gate_uses = findAExprs (exprFold findGate []) ds
        ifc_gate_uses = findAExprs (exprFold findGate []) fs
    in
        -- combine and remove duplicates
        S.toList $ S.union (S.fromList def_gate_uses) (S.fromList ifc_gate_uses)

-- ===============
