module APaths(
              PathGraphInfo,
              PathUrgencyPairs, PathNode,
              aPathsPreSched, aPathsPostSched
             ) where

-- ========================================================================
-- APaths
--
-- Defines two aPath stages of the compiler.
--
-- The first stage takes an APackage prior to scheduling and produces:
--   1) a graph of the paths through the package,
-- This is used to produce two others pieces of information, which
-- are used in the scheduling pass:
--   2) urgency restrictions due to paths from WF(r1) to CF(r2),
--   3) execution order restrictions due to values from r1 being
--      combinationally passed to expressions in r2.
-- If there are any cycles in the graph so far (sans scheduling),
-- this stage reports an error.
--
-- The second stage takes in the graph from the first stage and the
-- scheduler produced by the scheduling stage, and checks whether
-- there are any cycles in the graph with scheduling edges added.
-- If there is, the stage reports an error.  (There shouldn't be any
-- new cycles, if scheduling has done its job.  Urgency and execution
-- order cycles should be handled in the scheduling stage.)
-- This stage also computes the path information from module inputs
-- to module outputs, which will be added to the vModInfo for this module.
--
-- ==========
--
-- The nodes of the graph are:
--   * All identifiers in the ADefT
--
--   * All arguments to methods of submodules
--   * All return values of methods of submodules
--   * All enable signals of methods of submodules
--   * (There are no separate ready signals -- they are return values)
--   * All instantiation arguments to modules (those that become ports,
--     not parameters), except clocks (and their gates) and resets
--     (though there is some infrastructure for tracking this, if we want,
--     but it is not finished, because it will change with MCD support)
--   * A control mux for all methods of submodules with arguments
--     (the arguments to a single resource is potentially muxed, based on
--     the enable signal of the rules which provide the inputs)
--
--   * All CAN_FIRE signals for the rules and method-rules
--   * All WILL_FIRE signals for the rules and methods-rules
--
--   * All arguments to methods of the current module
--   * All return values of methods of the current module
--   * All enable signals of methods of the current module
--   * (There are no separate ready signals -- they are return values)
--   * All instantiation arguments of the current module
--     (These are include clock and reset, except for "noinline" functions
--      which do not have clock and reset.  And they include arguments to
--      the module which become ports -- we do not generate Verilog
--      parameters.)
--   * CLK and RST for the current module
--     (These are needed since they can appear in instantiation expressions
--     to arguments of submodules, e.g. the change_clock module in ClockConv.)
--
-- We assume that we can ignore paths through foreign action functions
-- and system tasks.
--
-- ==========
--
-- Urgency restrictions are found by:
--   1) Add an edge from each of the method RDY to the method EN
--      (because there is an assumption that the outside will consider
--       the EN based on the RDY signal)
--   2) For any path from WF(r1) to CF(r2), assert that r1 is more
--      urgent than r2.
--
-- Execution order restrictions are found by:
--   XXX ...
--
-- Path information for the module is computed by finding paths in the
-- graph from module inputs:
--   * method arguments for the current module
--   * method enable signals for the current module
--   * parameters for the current module
-- to module outputs:
--   * method return values for the current module
--     (this includes method ready signals, currently)
--
-- ==========
--
-- For now, we do not distinguish between cycles which are stable and
-- those which are unstable.  In the future, we may want to assign a
-- boolean expression to each edge of the path graph, which is the
-- condition under which that link is active or affects the value of
-- the receiving node.  If the compiler can prove that all of the
-- boolean conditions of a cycle cannot be satisfied at the same time,
-- then the cycle is at least stable.  We can include this information
-- in the warning, in case the user wants to allow stable cycles and
-- only disallow unstable cycles.
--
-- But given our current compilation scheme, cycles between rules
-- breaks TRS semantics.  Stable cycles are only okay inside a single
-- rule.
--
-- ========================================================================

import ErrorMonad(ErrorMonad(..), convErrorMonadToIO)
import PFPrint
import Flags(Flags)
import ASyntax
import Error(internalError, EMsg, ErrMsg(..), ErrorHandle)
import VModInfo(vPath, vFields, vArgs,
                VPathInfo(..), VName(..), VFieldInfo(..),
                VArgInfo(..), VWireInfo(..),
                getInputClockPorts, getInputResetPorts,
                isClock, isReset, isPort, isParam, id_to_vName,mkNamedEnable)
import Pragma
import Control.Monad(when)
import Data.Maybe(isJust, isNothing, fromJust)
import Data.List(partition)
import Id(unQualId, getIdBaseString)
import Eval
import Position(getPosition)
import qualified Data.Map as M
import qualified Data.Set as S

import GraphWrapper

import Util(itos, snd3, concatUnzip, concatUnzip3)
import Debug.Trace(traceM)
import IOUtil(progArgs)

-- ====================================
-- Tracing
--

trace_apaths :: Bool
trace_apaths = "-trace-apaths" `elem` progArgs

-- ====================================
-- Data Types
--


type PathEnv = M.Map AId PathNode

-- The information that is passed between the pre and post scheduler stages
data PathGraphInfo = PathGraphInfo
                         { pgi_graph :: Graph PathNode,
                           pgi_inputs :: [PathNode],
                           pgi_outputs :: [PathNode] }

instance PPrint PathGraphInfo where
    pPrint d p pgi =
        text "PathGraphInfo" <+> text "{" $+$
        nest 2 (text "graph" <+> text "=" <+>
                pPrint d p (pgi_graph pgi) <+> text "," $+$
                text "inputs" <+> text "=" <+>
                pPrint d p (pgi_inputs pgi) <+> text "," $+$
                text "outputs" <+> text "=" <+>
                pPrint d p (pgi_outputs pgi)) $+$
        text "}"

instance NFData PathGraphInfo where
    rnf x = rnf3 (pgi_graph x) (pgi_inputs x) (pgi_outputs x)

type PathUrgencyPairs = [(ARuleId, ARuleId, [PathNode])]

data PathNode =
    -- ID in the ADefT
    PNDef AId  |
    -- arguments to methods of submodules (Ids: instance, method, arg #)
    PNStateMethodArg AId AId Integer  |
    -- return values of methods of submodules (Ids: instance, method)
    PNStateMethodRes AId AId  |
    -- enable signal of action methods of submodules (Ids: instance, method)
    PNStateMethodEnable AId AId  |
    -- imported state has no ready signal
    --PNStateMethodReady AId AId  |
    -- arguments of submodules (Ids: instance, arg VName, position in arg list)
    -- Note that arguments are Verilog ports, and are not parameters.
    -- The position is included because args in the source are only
    -- known to the user by position (the VName is compiler generated).
    PNStateArgument AId VName Integer |
    -- control mux for arguments to methods of submodules
    -- (Ids: instance, method)
    PNStateMethodArgMux AId AId |
    -- ready signal of a method or rule
    PNCanFire AId  |
    -- enable signal of a method or rule
    PNWillFire AId  |
    -- arguments to methods of current module (Ids: method, argument)
    PNTopMethodArg AId AId  |
    -- return values of methods of current module (Id: method)
    PNTopMethodRes AId  |
    -- this is an internal graph node for the method's ready signal,
    -- the real output port is handled by a separate read method
    -- (Id: method)
    PNTopMethodReady AId  |
    -- enable signal for action method (Id: method)
    PNTopMethodEnable AId  |
    -- instantiation arguments to the module
    -- (typically Verilog ports, but could be parameters)
    -- The position number is included because args in the source might only
    -- be known to the user by position (the VName is compiler generated).
    -- (Though it's generated from the user's name in BSV, isn't it?)
    PNTopArgument AId Integer |
    -- clock wire (input or state element output)
    PNClk AId |
    -- inverted reset wire (input or state element output)
    PNRstN AId |
    -- clock-gating signal (input)
    PNTopClkGate AId |
    -- clock-gating signal (state element output)
    PNStateClkGate AId AId
  deriving (Eq, Ord, Show)

-- The Bool indicates whether to use pPrint or pvPrint
printPathNode :: Bool -> PDetail -> Int -> PathNode -> Doc
printPathNode use_pvprint d p node =
    let pp :: (PVPrint a, PPrint a) => a -> Doc
        pp = if (use_pvprint)
             then pvPrint d p
             else pPrint d p
    in  case (node) of
            (PNDef def_id) ->
                fsep [text "Definition", quotes (pp def_id)]
            (PNStateMethodArg inst_id meth_id port_id) ->
                fsep [text "Argument", pp port_id,
                      s2par "of method", quotes (pp meth_id),
                      s2par "of submodule", quotes (pp inst_id)]
            (PNStateMethodRes inst_id meth_id) ->
                fsep [s2par "Return value",
                      s2par "of method", quotes (pp meth_id),
                      s2par "of submodule", quotes (pp inst_id)]
            (PNStateMethodEnable inst_id meth_id) ->
                fsep [s2par "Enable signal",
                      s2par "of method", quotes (pp meth_id),
                      s2par "of submodule", quotes (pp inst_id)]
--          (PNStateMethodReady inst_id meth_id) -> ...
            (PNStateArgument inst_id arg_id arg_num) ->
--                fsep [s2par "Instantiation argument", pp arg_id]
--              Report the position of the argument, not its mangled name
                fsep [s2par "Instantiation argument", pp arg_num,
                      s2par "of submodule", quotes (pp inst_id)]
            (PNStateMethodArgMux inst_id meth_id) ->
                fsep [s2par "Control mux for arguments ",
                      s2par "of method", quotes (pp meth_id),
                      s2par "of submodule", quotes (pp inst_id)]
            (PNCanFire rule_or_meth_id) ->
                fsep [s2par "CanFire signal of rule/method",
                quotes (pp rule_or_meth_id)]
            (PNWillFire rule_or_meth_id) ->
                fsep [s2par "WillFire signal of rule/method",
                quotes (pp rule_or_meth_id)]
            (PNTopMethodArg meth_id arg_id) ->
                fsep [text "Argument", pp arg_id,
                      s2par "of top-level method", quotes (pp meth_id)]
            (PNTopMethodRes meth_id) ->
                fsep [text "Output",
                      s2par "of top-level method", quotes (pp meth_id)]
            (PNTopMethodReady meth_id) ->
                fsep [s2par "Ready condition",
                      s2par "of top-level method", quotes (pp meth_id)]
            (PNTopMethodEnable meth_id) ->
                fsep [s2par "Enable signal",
                      s2par "of top-level method", quotes (pp meth_id)]
            (PNTopArgument arg_id arg_num) ->
                fsep [s2par "Top-level module argument",
--                      quotes (pp arg_id)]
--              Report the position of the argument, not its mangled name
                      quotes (pp arg_num)]
            (PNClk clk_id) ->
                s2par ("Clock: " ++ (pfpReadable clk_id))
            (PNRstN rstn_id) ->
                s2par ("Reset: " ++ (pfpReadable rstn_id))
            (PNTopClkGate gate_id) ->
                s2par ("Top-level module clock-gating input: " ++
                       pfpReadable gate_id)
            (PNStateClkGate inst_id clk_id) ->
                fsep [s2par "Clock-gating output",
                      s2par "of clock", quotes (pp clk_id),
                      s2par "of submodule", quotes (pp inst_id)]

instance PPrint PathNode where
    pPrint d p = printPathNode False d p

instance PVPrint PathNode where
    pvPrint d p = printPathNode True d p

instance NFData PathNode where
    rnf (PNDef aid) = rnf aid
    rnf (PNStateMethodArg a1 a2 n) = rnf3 a1 a2 n
    rnf (PNStateMethodRes a1 a2) = rnf2 a1 a2
    rnf (PNStateMethodEnable a1 a2) = rnf2 a1 a2
    rnf (PNStateArgument aid vn n) = rnf3 aid vn n
    rnf (PNStateMethodArgMux a1 a2) = rnf2 a1 a2
    rnf (PNCanFire aid) = rnf aid
    rnf (PNWillFire aid) = rnf aid
    rnf (PNTopMethodArg a1 a2) = rnf2 a1 a2
    rnf (PNTopMethodRes aid) = rnf aid
    rnf (PNTopMethodReady aid) = rnf aid
    rnf (PNTopMethodEnable aid) = rnf aid
    rnf (PNTopArgument aid n) = rnf2 aid n
    rnf (PNClk aid) = rnf aid
    rnf (PNRstN aid) = rnf aid
    rnf (PNTopClkGate aid) = rnf aid
    rnf (PNStateClkGate a1 a2) = rnf2 a1 a2

-- When reporting errors, all of the above are in the user's source
-- except the defs, so don't report them.  This function filters them out.
filterPNDefs :: [PathNode] -> [PathNode]
filterPNDefs pns = filter (not . isPNDef) pns
    where isPNDef (PNDef _) = True
          isPNDef _ = False

alwaysRdyNode :: [PProp] -> PathNode -> Bool
alwaysRdyNode pps (PNTopMethodRes m) = isAlwaysRdy pps m
alwaysRdyNode pps _ = False

enWhenRdyNode :: [PProp] -> PathNode -> Bool
enWhenRdyNode pps (PNTopMethodEnable m) = isEnWhenRdy pps m
enWhenRdyNode pps _ = False

-- ====================================
-- aPathsPreSched
--

-- aPathsPreSched
--    This is the first half of path analysis.  We construct all the nodes
--    of the graph (even rules) and add in all edges (except between CanFire
--    and WillFire signals, which we'll add after we have the scheduler).
--
-- Inputs:
--   APackage
--     mi = module ID
--     fmod = is the module wrapped around a non-inlined function
--     size_ps = size parameters (names in Verilog)
--     inputs = module inputs (clock and reset, module arg ports)
--     vs = state elements (Verilog instances)
--     ds = local defs ([ADefT])
--     ors = list of rules (in no specified order)
--     rt = rule tree
--     ifc = interface methods ([AIFaceT])
--
-- Outputs:
--   Graph information used in the next stage of path computation.
--   A list of urgency requirements implied by paths, to be used in
--   scheduling.
--
aPathsPreSched :: ErrorHandle -> Flags -> APackage ->
                  IO (PathGraphInfo, PathUrgencyPairs)
aPathsPreSched errh flags apkg = do

  let mi = apkg_name apkg
      -- fmod = apkg_is_wrapped apkg
      size_ps = apkg_size_params apkg
      inputs = apkg_inputs apkg
      wi = apkg_external_wires apkg
      clks = concatMap snd (apkg_clock_domains apkg)
      rsts = map snd (apkg_reset_list apkg)
      vs = apkg_state_instances apkg
      ds = apkg_local_defs apkg
      ors = apkg_rules apkg
      -- rt = apkg_schedule_pragmas apkg
      ifc = apkg_interface apkg

  -- ====================
  -- Debug

  when trace_apaths $ do
    traceM ("size_ps = " ++ ppReadable size_ps)
    traceM ("inputs = " ++ ppReadable inputs)
    traceM ("vs = " ++ ppReadable vs)
    traceM ("ds = " ++ ppReadable ds)
    traceM ("ifc = " ++ eshowList ifc)

  -- ====================
  -- Internal checks

{- Top-level pragmas can mess with module inputs
  -- Inlined functions (fmod == True) do not have clock and reset,
  -- all other generated modules do
  when ((not fmod) && (length inputs < 2)) $
      internalError ("APath.aPathsPreSched: module has too few parameters")
-}

  -- ====================
  -- Separate out the module inputs for clocks, resets, ports, and params
  -- along with more internal checks for consistency

  -- (The function call returns the inputs paired with their VArgInfo
  -- and does all the sanity checking on the two fields)
  let inputs_with_arginfo = getAPackageInputs apkg

  -- record the order of the arguments, so that we can report args to
  -- the user by their position, and zip with the VArgInfo so we can
  -- identify which are ports, params, etc
  -- XXX top-level arguments should have names, so the numbers aren't
  -- XXX needed now, right?
  let numbered_inputs =
          let pair_to_triple x (y,z) = (x,y,z)
          in  zipWith pair_to_triple [1..] inputs_with_arginfo

  -- the Verilog names of the clocks/resets according to the VWireInfo
  let clk_ports = getInputClockPorts (wClk wi)
  let rst_ports = getInputResetPorts (wRst wi)

  -- checks against the VWireInfo
  let is_clk i = (id_to_vName i) `elem` clk_ports
      is_rst i = (id_to_vName i) `elem` rst_ports
      is_clk_or_rst i = (is_clk i) || (is_rst i)

  -- separate out the input list according to the VArgInfo
  let
      getClkPorts (AAI_Clock osc Nothing) = [osc]
      getClkPorts (AAI_Clock osc (Just gate)) = [osc, gate]
      getClkPorts ai = internalError ("APaths: unexpected clk input: " ++
                                      ppReadable ai)

      getRstPort (AAI_Reset r) = r
      getRstPort ai = internalError ("APaths: unexpected rst input: " ++
                                     ppReadable ai)

      getSimplePort (AAI_Port p) = p
      getSimplePort ai = internalError ("APaths: unexpected port input: " ++
                                        ppReadable ai)

      -- drop the type info on clocks/resets, and the numbering
      clk_inputs = concatMap getClkPorts
                       [ ai | (n, ai, arginfo) <- numbered_inputs,
                              isClock arginfo ]
      rst_inputs = [ getRstPort ai | (n, ai, arginfo) <- numbered_inputs,
                              isReset arginfo ]
      -- keep the numbering and type for ports/params
      port_inputs  = [ (n,p) | (n, ai, arginfo) <- numbered_inputs,
                                isPort arginfo,
                                let p = getSimplePort ai ]
      param_inputs = [ (n,p) | (n, ai, arginfo) <- numbered_inputs,
                                isParam arginfo,
                                let p = getSimplePort ai ]

  -- sanity check the VArgInfo separation with the clks/rsts from VWireInfo
  when (any (not . is_clk) clk_inputs) $
      internalError ("APaths.aPathsPreSched: " ++
                     "clock inputs not in VWireInfo")
  when (any (not . is_rst) rst_inputs) $
      internalError ("APaths.aPathsPreSched: " ++
                     "reset inputs not in VWireInfo")
  when (any (\(n,(i,t)) -> is_clk_or_rst i) (port_inputs ++ param_inputs)) $
      internalError ("APaths.aPathsPreSched: " ++
                     "non-clk/rst inputs found as clk/rst in VWireInfo")

  -- We don't handle size parameters yet
  when (not (null size_ps)) $
      internalError "APath.aPathsPreSched: size parameters not supported"


  -- ====================
  -- Determine the nodes of the graph

  let defs = [(i, PNDef i) | (ADef i _ _ _) <- ds]
      def_nodes = map snd defs

  -- ----------

  let
      -- This produces a list of tuples:
      --  1) Verilog instance name
      --  2) Path info in the form of a list of pairs of VNames
      --  3) Triple for each instantiation argument (no clks or rsts)
      --     1) VName of associated Verilog port
      --     2) Argument position in the arg list (1,2,...)
      --     3) AExpr for the instantiation value
      --  4) A list of tuples for each method:
      --     1) method name
      --     2) input argument list zipped with [1..]
      --     3) (Maybe VName) if method has an enable signal (action method)
      --     4) (Maybe VName) if method has a result (now only value methods)
      --     5) (Maybe Id)    if method has an associated clock
      -- Note: the VPort's are stripped of VeriPortProp to be just VName
      -- XXX is the VeriPortProp info worth keeping?
      state_instances ::
          [ ( AId, [(VName, VName)], [(VName, Integer, AExpr)],
              [(AId, [(VName,Integer)], Maybe VName, Maybe VName, Maybe AId)] ) ]
      state_instances =
          [(inst_id, nns, args, meth_info) |
             avi <- vs,
             let vmi = avi_vmi avi,
             -- instance name
             let inst_id = avi_vname avi,
             let args = getVModInfoArgs avi,
             -- path info pairs
             let (VPathInfo nns) = vPath vmi,

             -- instantiation arguments
             -- (for now, we don't track paths through clk and rst)
             -- let (_,_,_,args) = getVModInfoArgs avi,

             -- method info
             let meth_info =
                   [(meth_id, numbered_args, maybe_EN, maybe_res, maybe_clk) |
                      vfieldinfo@(Method { vf_name = meth_id }) <- vFields vmi,
                      let args = map fst (vf_inputs vfieldinfo),
                      let numbered_args = zip args [1..],
                      let maybe_EN = (vf_enable vfieldinfo) >>= return . fst,
                      let maybe_res = (vf_output vfieldinfo) >>= return . fst,
                      let maybe_clk = vf_clock vfieldinfo
                   ]
          ]

      state_input_nodes =
          [ PNStateMethodArg inst_id meth_id arg_num |
                (inst_id, _, _, methods) <- state_instances,
                (meth_id, numbered_args, maybe_EN, maybe_res, _) <- methods,
                arg_num <- map snd numbered_args
          ]
      state_output_nodes =
          [ PNStateMethodRes inst_id meth_id |
                (inst_id, _, _, methods) <- state_instances,
                (meth_id, _, _, Just res_name, _) <- methods
          ]
      state_enable_nodes =
          [ PNStateMethodEnable inst_id meth_id |
                (inst_id, _, _, methods) <- state_instances,
                (meth_id, _, Just en_name, _, _) <- methods
          ]

      state_arg_nodes =
          [ PNStateArgument inst_id arg_id arg_num |
                (inst_id, _, arg_pairs, _) <- state_instances,
                (arg_id, arg_num, _) <- arg_pairs
          ]

      state_mux_nodes =
          [ PNStateMethodArgMux inst_id meth_id |
                (inst_id, _, _, methods) <- state_instances,
                (meth_id, args, _, _, _) <- methods,
                not (null args) ]

  -- ----------

  -- This creates WF and CF nodes for all rule (and method rule) ids,
  -- even though some may be removed from the scheduler (such as
  -- noAction rules).
  let rule_ids =
          -- methods
          [ r_id | (AIAction { aif_body = rs }) <- ifc,
                   (ARule { arule_id = r_id }) <- rs ] ++
          [ r_id | (AIActionValue { aif_body = rs }) <- ifc,
                   (ARule { arule_id = r_id }) <- rs ] ++
          -- rules
          [ r_id | (ARule { arule_id = r_id }) <- ors ]

  let can_fire_nodes = [ PNCanFire r_id | r_id <- rule_ids ]
  let will_fire_nodes = [ PNWillFire r_id | r_id <- rule_ids ]

  -- ----------

  let method_inputs =
          [(arg, PNTopMethodArg m arg) | (AIDef { aif_inputs = args,
                                                  aif_value = (ADef m _ _ _) }) <- ifc,
                                         (arg,_) <- args] ++
          [(arg, PNTopMethodArg m arg) | (AIAction { aif_inputs = args,
                                                     aif_name = m }) <- ifc,
                                         (arg,_) <- args] ++
          [(arg, PNTopMethodArg m arg) | (AIActionValue { aif_inputs = args,
                                                          aif_name = m }) <- ifc,
                                         (arg,_) <- args]

      method_outputs =
          [(m, PNTopMethodRes m) | (AIDef { aif_value = (ADef m _ _ _) }) <- ifc] ++
          [(m, PNTopMethodRes m) | (AIActionValue { aif_name = m, aif_value = (ADef m' _ _ _) }) <- ifc]

      method_enables =
          -- Name creation is safe, since it is based on VFieldInfo
          [(mkNamedEnable afi, PNTopMethodEnable m) |
               (AIAction { aif_name = m, aif_fieldinfo = afi }) <- ifc ] ++
          [(mkNamedEnable afi, PNTopMethodEnable m) |
               (AIActionValue { aif_name = m, aif_fieldinfo = afi }) <- ifc ]

      -- port and parameter module args which are not clocks or resets
      module_arg_ports =
          [ (arg_id, PNTopArgument arg_id arg_num) |
                (arg_num, (arg_id,_)) <- port_inputs ]
      module_arg_params =
          [ (arg_id, PNTopArgument arg_id arg_num) |
                (arg_num, (arg_id,_)) <- param_inputs ]

      clk_wires  = [ (i, PNClk i)
                         | AClock { aclock_osc = ASPort _ i }  <- clks ]
      input_clk_wires = filter (\(i,n) -> i `elem` clk_inputs) clk_wires

      gate_wires = [ (i, PNTopClkGate i)
                         | AClock { aclock_gate = ASPort _ i } <- clks ]
      input_clk_gate_wires =
          let -- should not be any which is not an elem of clk_inputs
              isInputClk i = elem i clk_inputs
              non_input_clk_gates =
                  filter (not . isInputClk) (map fst gate_wires)
          in  if (null non_input_clk_gates)
              then gate_wires
              else internalError
                      ("Found non-input clock gates referenced as ASPort: " ++
                       ppReadable non_input_clk_gates)

      rstn_wires     = [ (i, PNRstN i)    | AReset { areset_wire = ASPort _ i } <- rsts ]
      input_rstn_wires = filter (\(i,n) -> i `elem` rst_inputs) rstn_wires

      method_input_nodes = map snd method_inputs
      method_output_nodes = map snd method_outputs
      method_enable_nodes = map snd method_enables
      module_arg_port_nodes = map snd module_arg_ports
      module_arg_param_nodes = map snd module_arg_params
      clk_nodes            = map snd clk_wires
      input_clk_nodes      = map snd input_clk_wires
      gate_nodes           = map snd gate_wires
      input_clk_gate_nodes = map snd input_clk_gate_wires
      rstn_nodes           = map snd rstn_wires
      input_rstn_nodes     = map snd input_rstn_wires

      -- These are internal graph nodes, not part of the interface.
      -- There are separate read methods which become the Verilog ports.
      method_ready_nodes = map (PNTopMethodReady . aIfaceName) ifc

  -- ----------

      submod_clk_gate_nodes =
          [ (PNStateClkGate i c)
                | AClock { aclock_gate = AMGate _ i c } <- clks ]

  -- ----------

  -- We assume there are no paths through tasks and foreign functions

  -- ----------

  let pathnodes = def_nodes ++
                  state_input_nodes ++ state_output_nodes ++
                  state_enable_nodes ++ state_arg_nodes ++
                  state_mux_nodes ++
                  can_fire_nodes ++ will_fire_nodes ++
                  method_input_nodes ++ method_output_nodes ++
                  method_enable_nodes ++ method_ready_nodes ++
                  module_arg_port_nodes ++ module_arg_param_nodes ++
                  clk_nodes ++ gate_nodes ++ rstn_nodes ++
                  submod_clk_gate_nodes

  -- ====================
  -- Determine the edges of the graph

  -- XXX could separate the ifc_env into maps for port/param?
  let def_map = M.fromList defs
  let ifc_env = method_inputs ++ method_outputs ++ method_enables ++
                module_arg_ports ++ module_arg_params ++
                clk_wires ++ gate_wires ++ rstn_wires

  -- internalError asserts that there is no name clash between ASDef and
  -- ASPort/ASParam
  -- (laziness ensures it will not be computed unless necessary)
  let overlap_error a b =
          internalError ("APaths.aPaths': ifc or def overlap: " ++
                         ppReadable a ++ ppReadable b)

  -- add ifc_env elements one-by-one,
  -- bailing with an error if we ever need to combine
  let env = foldr (uncurry (M.insertWith overlap_error)) def_map ifc_env

  when trace_apaths $
    traceM ("env = " ++ ppReadable (M.toList env))

  -- --------------------
  -- Module parameter defaults

  -- No paths should be possible for these, so no need to check these exprs

  -- --------------------
  -- Defs (ds)

  let mkDefEdges (ADef i _ e _) = mkEdges (PNDef i) e env
      def_edges = concatMap mkDefEdges ds

  -- --------------------
  -- methods (ifc)

  let mkMethodEdges :: AIFace -> [(PathNode,PathNode)]
      mkMethodEdges (AIDef mid inputs wp rdy (ADef m _ e _) _ _) =
          -- connect the rdy expression (likely just an ASDef reference)
          -- to the internal graph node for the method ready
          (mkEdges (PNTopMethodReady m) rdy env) ++
          -- make faux connections from the rdy to the arguments, so that
          -- dependencies in the other direction are caught as loops
          [(PNTopMethodReady m, PNTopMethodArg m arg) | (arg,_) <- inputs] ++
          -- connect the definition to the method result
          -- (this method has no enable, so it cannot contribute to any
          -- methcall argument muxes, so just use "mkEdges")
          (mkEdges (PNTopMethodRes m) e env)
      mkMethodEdges (AIAction inputs wp rdy m rs fi) =
          let rdy_node = PNTopMethodReady m
              en_node  = PNTopMethodEnable m
              mkMRuleEdges (ARule ri _ _ _ rpred actions _ _) =
                -- Note: rule predicate   -> CanFire
                --       method predicate -> CanFire
                --       CanFire          -> method RDY
                --       method EN        -> WillFire
                --       WillFire         -> rule action enables
                -- Connection from CanFire to WillFire added in sched_edges.
                let cf_node  = PNCanFire ri
                    wf_node  = PNWillFire ri
                in  -- add edges from rule predicate to the CanFire
                    (mkEdges cf_node rpred env) ++
                    -- add edges from method predicate to CanFire
                    (mkEdges cf_node rdy env) ++
                    -- add edge from the CanFire to method RDY
                    [(cf_node, rdy_node)] ++
                    -- add edge from the method EN to the WillFire
                    [(en_node, wf_node)] ++
                    -- add edges from rule WillFire to ENs in each action
                    (concatMap (mkActionEdges env wf_node) actions)
          in
              -- make faux connections from the rdy to the arguments and the
              -- enable, so that dependencies in the other direction are caught
              -- as loops
              [(rdy_node, en_node)] ++
              [(rdy_node, PNTopMethodArg m arg)
                   | (arg,_) <- inputs] ++
              -- connect the rules
              concatMap mkMRuleEdges rs

      mkMethodEdges (AIActionValue inputs wp rdy m rs (ADef m' _ e _) fi) =
          let rdy_node = PNTopMethodReady m
              en_node  = PNTopMethodEnable m
              mkMRuleEdges (ARule ri _ _ _ rpred actions _ _) =
                -- Note: rule predicate   -> CanFire
                --       method predicate -> CanFire
                --       CanFire          -> method RDY
                --       method EN        -> WillFire
                --       WillFire         -> rule action enables
                -- Connection from CanFire to WillFire added in sched_edges.
                let cf_node  = PNCanFire ri
                    wf_node  = PNWillFire ri
                in  -- add edges from rule predicate to the CanFire
                    (mkEdges cf_node rpred env) ++
                    -- add edges from method predicate to CanFire
                    (mkEdges cf_node rdy env) ++
                    -- add edge from the CanFire to method RDY
                    [(cf_node, rdy_node)] ++
                    -- add edge from the method EN to the WillFire
                    [(en_node, wf_node)] ++
                    -- add edges from rule WillFire to ENs in each action
                    (concatMap (mkActionEdges env wf_node) actions)
          in
              -- make faux connections from the rdy to the arguments and the
              -- enable, so that dependencies in the other direction are caught
              -- as loops
              [(rdy_node, en_node)] ++
              [(rdy_node, PNTopMethodArg m arg)
                   | (arg,_) <- inputs] ++
              -- connect the definition to the method result
              -- (this method's Enable could contribute to methcall argument
              -- muxes, so use "mkEdgesWithMux")
              (mkEdgesWithMux en_node (PNTopMethodRes m) e env) ++
               -- connect the rules
              concatMap mkMRuleEdges rs

      mkMethodEdges (AIClock {}) = []
      mkMethodEdges (AIReset {}) = []
      mkMethodEdges (AIInout {}) = []

      method_edges = concatMap mkMethodEdges ifc

  -- --------------------
  -- rules (rt)

  let mkRuleEdges (ARule ri _ _ _ rpred actions _ _) =
          -- Note: Connection from canfire to willfire added in sched_edges.
          -- add edge from pred to can_fire
          (mkEdges (PNCanFire ri) rpred env) ++
          -- add edges from will_fire to ENs of actions
          (concatMap (mkActionEdges env (PNWillFire ri)) actions)

      rule_edges = concatMap mkRuleEdges ors

  -- --------------------
  -- state (connecting paths through instantiated state)

  -- Assumptions:
  --  * There is no path from a module's static parameters, clock, or reset
  --    (but there are paths for instantiation arguments which become ports)

  let findOutputPathNodes inst_id vname methods =
          [ (clk, PNStateMethodRes inst_id meth_id) |
                (meth_id, _, _, Just res, clk) <- methods,
                res == vname
          ]
      findInputPathNodes inst_id vname methods argpairs =
          [ (Nothing, PNStateArgument inst_id arg_id arg_num) |
                (arg_id, arg_num, _) <- argpairs
          ] ++
          [ (clk, PNStateMethodEnable inst_id meth_id) |
                (meth_id, _, Just enable, _, clk) <- methods,
                enable == vname
          ] ++
          [ (clk, PNStateMethodArg inst_id meth_id arg_num) |
                (meth_id, args, _, _, clk) <- methods,
                (arg, arg_num) <- args,
                arg == vname
          ]

  -- Connect module inputs and outputs based on the path annotations
  let state_internal_edges =
          [ (pn1, pn2) |
                (inst_id, pathpairs, argpairs, methods) <- state_instances,
                (vname1, vname2) <- pathpairs,
                (clk1,pn1) <- findInputPathNodes inst_id vname1 methods argpairs,
                (clk2,pn2) <- findOutputPathNodes inst_id vname2 methods,
                (clk1 == clk2) || (isNothing clk1) || (isNothing clk2)
          ]

  -- Connect module instantiation arguments to the expressions provided
  -- at instantiation time for their values.
  let mkStateArgEdge inst_id (arg_id, arg_num, arg_expr) =
          let arg_node = PNStateArgument inst_id arg_id arg_num
          in  mkEdges arg_node arg_expr env

      state_arg_edges =
          [ e | (inst_id, _, arg_pairs, _) <- state_instances,
                arg_pair <- arg_pairs,
                e <- mkStateArgEdge inst_id arg_pair
          ]

  -- Connect the control mux for a method to the arguments of that method
  let state_mux_edges =
         [ (PNStateMethodArgMux inst_id meth_id,
            PNStateMethodArg inst_id meth_id arg_num) |
               (inst_id, _, _, methods) <- state_instances,
               (meth_id, args, _, _, _) <- methods,
               (_, arg_num) <- args ]

  -- Combine all the submodule edges
  let state_edges =
          state_arg_edges ++ state_internal_edges ++ state_mux_edges

  -- --------------------
  -- scheduling edges (part 1)

  -- For all rules (and methods) connect the CAN_FIRE to the WILL_FIRE.
  -- (Except for rules which are dropped, or statically known to never
  -- fire, this has to be true.)
  -- This will let us catch (prior to scheduling) rules whose
  -- pre-condition (CAN_FIRE) depends on the rule's execution (WILL_FIRE).
  -- That kind of dependency is an error.  (The dependency may not matter
  -- if the rule is eventually dropped, but that's no excuse for not
  -- asserting an error.)

  let sched_edges =
          -- for rules
          [ (PNCanFire ri, PNWillFire ri) |
                (ARule { arule_id = ri }) <- ors ] ++
          -- for methods
          [ (PNCanFire ri, PNWillFire ri) |
                (AIAction { aif_body = rs }) <- ifc,
                (ARule { arule_id = ri }) <- rs ] ++
          [ (PNCanFire ri, PNWillFire ri) |
                (AIActionValue { aif_body = rs }) <- ifc,
                (ARule { arule_id = ri }) <- rs ]

  -- --------------------

  when trace_apaths $ do
    traceM ("pathnodes = " ++ ppReadable pathnodes)
    traceM ("def_edges = " ++ ppReadable def_edges)
    traceM ("method_edges = " ++ ppReadable method_edges)
    traceM ("rule_edges = " ++ ppReadable rule_edges)
    traceM ("state_edges = " ++ ppReadable state_edges)
    traceM ("sched_edges = " ++ ppReadable sched_edges)

  let pathedges = def_edges ++ method_edges ++ rule_edges ++ state_edges ++
                  sched_edges

  let pathnodeset = S.fromList pathnodes

  -- assert that all nodes in the edges are actually nodes
  let unknown_nodes =
          [ n | (n1,n2) <- pathedges,
                n <- filter (\x -> not (S.member x pathnodeset)) [n1,n2] ]
  when (not (null unknown_nodes)) $
      internalError ("APath.aPaths': nodes not in graph: " ++
                      show unknown_nodes)

  -- ====================
  -- Construct the graph

  pathgraph <- makeGraph pathnodes pathedges

  -- ====================
  -- Check for cycles

  cycles <- findCycles pathgraph
  when (not (null cycles)) $
      convErrorMonadToIO errh $ errPathCycles mi pathgraph cycles

  -- ====================
  -- Find urgency restrictions
  -- (a path from WF(r1) to CF(r2) implies r1 more urgent than r2)

  -- For urgency to be computed by paths, we must assume a path from
  -- a method's ready signal to its enable signal.
  let rdy_to_en_edges = [(PNTopMethodRes rdy_id, PNTopMethodEnable m_id) |
                             (AIAction { aif_pred = (ASDef _ rdy_id),
                                         aif_name =  m_id, aif_fieldinfo = m_fi }) <- ifc ] ++
                        [(PNTopMethodRes rdy_id, PNTopMethodEnable m_id) |
                             (AIActionValue { aif_pred = (ASDef _ rdy_id),
                                              aif_name =  m_id, aif_fieldinfo = m_fi }) <- ifc ]

  pathgraph' <- addEdgesWithNodes pathgraph rdy_to_en_edges
  let reachables = findReachables pathgraph' will_fire_nodes

  -- pairs of PathNode
  let urgency_pairs =
          -- edges from WF to CF of rule (or action/actionvalue method)
          [ (wf_rule_id, cf_rule_id, filtered_path) |
                (PNWillFire wf_rule_id, rs) <- zip will_fire_nodes reachables,
                cf_node@(PNCanFire cf_rule_id) <- can_fire_nodes,
                let mpath = lookup cf_node rs,
                isJust mpath,
                let filtered_path = reverse (filterPNDefs (fromJust mpath)) ]
          ++
          -- edges from WF to RDY of value method
          [ (wf_rule_id, meth_id, filtered_path) |
                (PNWillFire wf_rule_id, rs) <- zip will_fire_nodes reachables,
                (AIDef { aif_value = (ADef meth_id _ _ _) }) <- ifc,
                let meth_node = (PNTopMethodReady meth_id),
                let mpath = lookup meth_node rs,
                isJust mpath,
                let filtered_path = reverse (filterPNDefs (fromJust mpath)) ]


  when trace_apaths $ do
    traceM ("urgency_pairs = " ++ ppReadable urgency_pairs)

  -- ====================
  -- Return the result

  let
      -- just the port-list inputs
      -- no need to report paths from params to output ports
      -- (thus, module_arg_param_nodes is not included)
      -- (if we did, then we'd want to add edges for the default exprs,
      -- which we don't currently do)
      mod_inputs = method_input_nodes ++ method_enable_nodes ++
                   module_arg_port_nodes ++ input_clk_nodes ++
                   input_clk_gate_nodes ++ input_rstn_nodes
      mod_outputs = method_output_nodes

  let pathGraphInfo = PathGraphInfo { pgi_graph = pathgraph,
                                      pgi_inputs = mod_inputs,
                                      pgi_outputs = mod_outputs }
  return (pathGraphInfo, urgency_pairs)


-- ====================================
-- aPathsPostSched
--

-- aPathsPostSched
--    This is the second half of path analysis, adding scheduling info.
--    We compute the vPathInfo for vModInfo (paths from inputs to outputs
--    for the verilog module).  Any cycle in the graph should have been
--    caught pre-scheduling and scheduling should not have introduced
--    any, so internal error if any cycles found.
--
-- Inputs:
--   apkg = the package (only the ifc VNames are needed)
--   scheds = list of schedulers on conflict-free groups of rules
--   ruleOrd = list of rule IDs in reverse order of execution
--
aPathsPostSched :: Flags -> [PProp] -> APackage ->
                   PathGraphInfo -> ASchedule -> IO (VPathInfo)
aPathsPostSched flags pps apkg pathGraphInfo (ASchedule scheds _) = do

  -- ====================
  -- Extract path graph info

  let pathgraph0    = pgi_graph pathGraphInfo
      mod_inputs    = filter (not . (enWhenRdyNode pps)) (pgi_inputs pathGraphInfo)
      mod_outputs   = filter (not . (alwaysRdyNode pps)) (pgi_outputs pathGraphInfo)
      user_rule_ids = map aRuleName (apkg_rules apkg)
      rule_ids      = user_rule_ids ++
                      (map aRuleName (concatMap aIfaceRules
                                                (apkg_interface apkg)))

  -- ====================
  -- Schedule connections

  let

      -- In Esposito, the scheduler can add the following types of paths:
      --   The WF for a user-generated rule can have paths from the
      --     WF of conflicting more urgent rules
      --   The WF for a user-generated rule can have paths from the
      --     RDY of conflicting more urgent value methods
      --   The RDY of a method can have paths from the WF of
      --     conflicting more urgent rules
      mkSchedEdges (ASchedEsposito ss) =
        let isUserRule i = i `elem` user_rule_ids
            isRule     i = i `elem` rule_ids
            ss'        = [(i, partition isRule cs) | (i,cs) <- ss ]
            (rule_sched, meth_sched) = partition (isUserRule . fst) ss'
            rr_edges = -- WF of conflicting rule -> WF of user-rule
                       [ (PNWillFire r2, PNWillFire r1)
                       | (r1,(rcs,_)) <- rule_sched
                       , r2 <- rcs
                       ]
            mr_edges = -- RDY of conflicting value method -> WF of user-rule
                       [ (PNTopMethodReady vm, PNWillFire r)
                       | (r,(_,vmcs)) <- rule_sched
                       , vm <- vmcs
                       ]
            rm_edges = -- WF of conflicting rule -> RDY of a method
                       [ (PNWillFire r, PNTopMethodReady m)
                       | (m,(rcs,_)) <- meth_sched
                       , r <- rcs
                       ]
        in rr_edges ++ mr_edges ++ rm_edges

  let sched_edges = concatMap mkSchedEdges scheds

  -- --------------------

  when trace_apaths $ do
    traceM ("sched_edges = " ++ ppReadable sched_edges)

  -- --------------------

  -- add the new connections for the scheduler, now that they are known
  -- XXX with nodes may be unnecessary here
  pathgraph <- addEdgesWithNodes pathgraph0 sched_edges

  -- ====================
  -- Check for cycles again?

  cycles <- findCycles pathgraph

  when (not (null cycles)) $
      internalError ("APath: cycles found post scheduling: " ++
                     ppReadable cycles)

  -- ====================
  -- Find paths from inputs to outputs

  let reachables = findReachables pathgraph mod_inputs

  -- pairs of PathNode
  let pathpairs = [ (input, output) |
                        -- we don't need to know the path
                        (input, rs) <- zip mod_inputs reachables,
                        output <- mod_outputs,
                        isJust (lookup output rs) ]

  -- --------------------
  -- Convert the path ids from PathNode to VName

  -- XXX is this conversion from Id to VName legal?
  let aidToVName i = VName (getIdBaseString i)

  -- We don't currently need the argument conversion info, because
  -- the node already contains the converted name (and not the number)
  let meth_info_map = M.fromList $
          [ (meth_id, ({-numbered_args,-} maybe_EN, maybe_res)) |
              meth <- apkg_interface apkg,
              let vfieldinfo = aif_fieldinfo meth,
              let meth_id = vf_name vfieldinfo,
              --let args = map fst (vf_inputs vfieldinfo),
              --let numbered_args = zip args [1..],
              let maybe_EN = (vf_enable vfieldinfo) >>= return . fst,
              let maybe_res = (vf_output vfieldinfo) >>= return . fst
          ]

  let findMethod m =
          case (M.lookup m meth_info_map) of
              Just info -> info
              Nothing -> internalError ("APaths findMethod: " ++ ppReadable m)

  -- the "arg" is already the VName and not a number
  let convertArg m arg = aidToVName arg

  let convertRes m =
          case (findMethod m) of
              (_, Just res) -> res
              _ -> internalError ("APaths convertRes: " ++ ppReadable m)

  let convertEnable m =
          case (findMethod m) of
              (Just enable, _) -> enable
              _ -> internalError ("APaths convertEnable: " ++ ppReadable m)

  -- convert PathNode back to VName
  let pnToVName (PNTopMethodArg m arg)     = convertArg m arg
      pnToVName (PNTopMethodRes m)         = convertRes m
      pnToVName (PNTopMethodEnable m)      = convertEnable m
      pnToVName (PNTopArgument a _)        = aidToVName a
      pnToVName (PNTopClkGate a)           = aidToVName a
      -- XXX clock and reset?
      pnToVName x = internalError ("APaths.pnToVName: " ++ show x)

  -- pairs of VName
  let vname_pathpairs = map (\(a,b) -> (pnToVName a, pnToVName b)) pathpairs

  -- --------------------

  when trace_apaths $ do
    traceM ("inputs: " ++ ppReadable mod_inputs)
    traceM ("outputs: " ++ ppReadable mod_outputs)
    traceM ("reachables: " ++ ppReadable reachables)
    traceM ("paths: " ++ ppReadable pathpairs)

  -- ====================
  -- Return the result

  return (VPathInfo vname_pathpairs)


-- ====================================
-- Traversing expressions to find variable use
--

-- Given an output node and an expression for that node, find all the
-- contributors to that expression and make connections from the
-- contributors to the output node.  Also return any edges internal to
-- the expression (function call inputs to outputs, for example).
-- Inputs:
--   * output node
--   * expression
--   * environment
mkEdges :: PathNode -> AExpr -> PathEnv -> [(PathNode, PathNode)]
mkEdges pn e env =
    let (is, edges, _) = findEdges env e
    in  edges ++ (connectEdge pn is)

-- Same as mkEdges, but used for expressions inside actions,
-- so that method calls with arguments cause the enable of the action
-- to be connected to the mux of the arguments.
-- Inputs:
--   * action enable node
--   * output node
--   * expression
--   * environment
mkEdgesWithMux :: PathNode -> PathNode -> AExpr -> PathEnv ->
                  [(PathNode, PathNode)]
mkEdgesWithMux en pn e env =
    let (is, edges, mux_nodes) = findEdges env e
    in  edges ++ (connectEdge pn is) ++ (connectEdgeR en mux_nodes)

-- Make an edge from all nodes in the list to the input node
connectEdge :: PathNode -> [PathNode] -> [(PathNode, PathNode)]
connectEdge pn pns = map (\x -> (x, pn)) pns

-- Make an edge from the input node to all nodes in the list
connectEdgeR :: PathNode -> [PathNode] -> [(PathNode, PathNode)]
connectEdgeR pn pns = map (\x -> (pn, x)) pns


mkActionEdges :: PathEnv -> PathNode -> AAction ->
                 [(PathNode, PathNode)]
mkActionEdges env en (ACall state_id qual_meth_id (cond:exprs)) =
    let meth_id = unQualId qual_meth_id
        meth_en = PNStateMethodEnable state_id meth_id
        meth_arg_mux = PNStateMethodArgMux state_id meth_id
        meth_args =
            map (PNStateMethodArg state_id meth_id) [1..]
    in
      -- if the method has arguments, connect the enable signal of the
      -- action to the control mux for the arguments
      (if null exprs then [] else [(en, meth_arg_mux)]) ++
      -- connect the enable of the action to the enable of the method
      [(en, meth_en)] ++
      -- connect the arg expressions to the arguments
      concatMap (\(e,pn) -> mkEdgesWithMux en pn e env)
                (zip exprs meth_args) ++
      -- connect non-split condition of the call to the enable of the method
      mkEdgesWithMux en meth_en cond env

mkActionEdges env en (AFCall { aact_args = es@(cond:exprs) }) =
    -- XXX right now, we don't track cycles through function calls
    concatMap (snd3 . findEdges env) es
mkActionEdges env en (ATaskAction { aact_args = es@(cond:exprs) }) =
    -- XXX right now, we don't track cycles through task calls
    concatMap (snd3 . findEdges env) es
mkActionEdges env en action =
    internalError ("APaths.mkActionEdges: " ++ show (en, action))


-- Returns:
--   * a list of nodes contributing to the result of the
--     expression (to be connected to the user of the result)
--   * a list of any connections encountered along the way
--     (function calls in argument expressions, etc)
--   * a list of muxes encountered along the way
--     (to be connected to EN, if this expr is inside an action)
-- Inputs:
--   * environment mapping Ids of local defs and module inputs
--     to their PathNode
--   * expression to be analyzed
--
findEdges :: PathEnv -> AExpr ->
             ([PathNode], [(PathNode, PathNode)], [PathNode])
findEdges env (APrim i t op es) =
    -- make edge between inputs and output
    concatUnzip3 (map (findEdges env) es)
findEdges env (AMethCall t i qmi exprs) =
    -- make edges between exprs and meth input
    -- return the output connection
    let mi = unQualId qmi
        -- like mkEdgesWithMux, but want to return the muxes, not connect them
        f (n,exp) = let (is, edges, muxes) = findEdges env exp
                        pn = PNStateMethodArg i mi n
                        es = edges ++ (connectEdge pn is)
                    in  (es, muxes)
        (edges, ms) = concatUnzip (map f (zip [1..] exprs))
        meth_arg_mux = PNStateMethodArgMux i mi
        muxes = if null exprs then ms else meth_arg_mux:ms
    in  ([PNStateMethodRes i mi], edges, muxes)
findEdges env (AMethValue t i qmi) =
    ([PNStateMethodRes i (unQualId qmi)], [], [])
findEdges env (ANoInlineFunCall { ae_args = es }) =
    -- return the function call inputs
    -- and return any connections found in the argument expressions
    concatUnzip3 (map (findEdges env) es)
findEdges env (AFunCall { ae_args = es }) =
    -- return the function call inputs
    -- and return any connections found in the argument expressions
    concatUnzip3 (map (findEdges env) es)
findEdges env (ATaskValue { }) = ([],[],[])
-- module port reference
findEdges env (ASPort t i) =
    case (M.lookup i env) of
        Nothing -> internalError ("findEdges: unknown ASPort: " ++ ppReadable i)
        Just pn -> ([pn],[],[])
-- module parameter reference
findEdges env (ASParam t i) =
    case (M.lookup i env) of
        Nothing -> internalError ("findEdges: unknown ASParam: " ++ ppReadable i)
        Just pn -> ([pn],[],[])
-- ref to local def
findEdges env (ASDef t i) =
    case (M.lookup i env) of
        Nothing -> internalError ("findEdges: unknown ASDef: " ++ ppReadable i)
        Just pn -> ([pn],[],[])
findEdges env (ASInt _ _ _) = ([],[],[])
findEdges env (ASReal _ _ _) = ([],[],[])
findEdges env (ASStr _ _ _) = ([],[],[])
-- if we know what the ASAny will turn into,
-- the combinational paths will exist in the output hardware
findEdges env (ASAny _ (Just e)) = findEdges env e
findEdges env (ASAny _ Nothing) = ([],[],[])
-- clock and reset edges should be irrelevant
findEdges env (ASClock _ _) = ([],[],[]) -- XXX recurse into the osc and gate?
findEdges env (ASReset _ _) = ([],[],[]) -- XXX recurse into the rst?
findEdges env (ASInout _ _) = ([],[],[])
-- output osc, gate, and reset
findEdges env (AMGate _ i c) = ([PNStateClkGate i c], [], [])

-- ====================================

-- Converts a list of cycles (sets of SCC) into a list of errors.
-- PNDefs in the cycle are dropped, because the names are not in the source.
errPathCycles :: AId -> Graph PathNode -> [[PathNode]] -> ErrorMonad ()
errPathCycles mid g cycles = EMError (concatMap (errPathCycle mid g) cycles)

-- Report the following cycles:
--  * Paths from a method's arguments or enable to its ready
--  * Paths from a rule's WILL_FIRE to its CAN_FIRE
--  * All other cycles report as a SCC
errPathCycle :: AId -> Graph PathNode -> [PathNode] -> [EMsg]
errPathCycle moduleId graph cycle =
    let
        -- display a path (list of PathNode) in user-friendly form
        -- (notice that PNDefs are omitted)
        printPath path = pPrint PDReadable 0 (filterPNDefs path)

        -- ---------------
        -- Functions for reporting the different types of errors

        -- function to make the default error message
        default_err =
            (getPosition moduleId, EPreSchedCycle (printPath cycle))

        -- function to make WF-to-CF error message
        mkWfToCfErr (ruleId, Just path) =
            (getPosition ruleId,
             ESelfUrgency (pfpString ruleId) (printPath path))
        mkWfToCfErr x = internalError
                            ("APaths.errPathCycle: WfToCf: " ++ show x)

        mkArgToRdyErr (methodId, argId, Just path) =
            (getPosition moduleId,
             EPathMethodArgToRdy
                 (pfpString methodId) (pfpString argId) (printPath path))
        mkArgToRdyErr x = internalError
                              ("APaths.errPathCycle: ArgToRdy: " ++ show x)

        mkEnToRdyErr (methodId, Just path) =
            (getPosition moduleId,
             EPathMethodEnToRdy (pfpString methodId) (printPath path))
        mkEnToRdyErr x = internalError
                             ("APaths.errPathCycle: EnToRdy: " ++ show x)

        -- ---------------

        method_arg_errs =
            [ mkArgToRdyErr (m1, argId, findPath graph arg rdy) |
                  arg@(PNTopMethodArg m1 argId) <- cycle,
                  rdy@(PNTopMethodReady m2) <- cycle,
                  m1 == m2 ]

        method_en_errs =
            [ mkEnToRdyErr (m1, findPath graph en rdy) |
                  en@(PNTopMethodEnable m1) <- cycle,
                  rdy@(PNTopMethodReady m2) <- cycle,
                  m1 == m2 ]

        method_errs = method_arg_errs ++ method_en_errs

        rule_errs =
            [ mkWfToCfErr (r1, findPath graph wf cf) |
                  wf@(PNWillFire r1) <- cycle,
                  cf@(PNCanFire r2) <- cycle,
                  r1 == r2 ]

        -- ---------------
    in
        if not (null method_errs)
        then method_errs
        else if not (null rule_errs)
        then rule_errs
        else [default_err]


-- ====================================

eshowList :: (Show a) => [a] -> String
eshowList [] = "[]"
eshowList xs =
  let eshowElem :: (Show a) => (a, Integer) -> Doc
      eshowElem (x,i) = text ((itos i) ++ ":") <+> text (show x)
  in  pretty 70 70
        (text "[" <+> foldr1 ($$) (map eshowElem (zip xs [1..])) <+> text "]")

-- --------------------

-- Get port-based instantiation arguments
getVModInfoArgs :: AVInst -> [(VName, Integer, AExpr)]
getVModInfoArgs avi = [(port, arg_num, e) | (Port (port,_) _ _, arg_num, e) <- zip3 (vArgs (avi_vmi avi)) [1..] (avi_iargs avi)]

-- ========================================================================

-- Return the module arguments (the ones which turn into ports, not
-- parameters), as a triple:
--   * clocks zipped with their instantiation expressions
--   * clock gates zipped with their clock and instantiation expression
--   * resets zipped with their instantiation expressions
--   * non-clocks and non-resets zipped with their argument-list position
--     and AExpr for the instantiation input expression
--
{-
getVModInfoArgs :: AVInst -> ([(VName, AExpr)],
                              [(VName, VName, AExpr)],
                              [(VName, AExpr)],
                              [(VName, Integer, AExpr)])
getVModInfoArgs avi =
    let -- VModInfo
        vmi = avi_vmi avi
        -- number of parameters (to be dropped from the AExpr list)
        num_params = vNParam vmi
        -- AExpr inputs to just the arguments (not the parameters)
        input_exprs = genericDrop num_params (avi_iargs avi)
        -- all port arguments (not parameters)
        input_names = vArgs vmi

        input_pairs = zip input_names input_exprs

        -- figure out which ports are clocks, clock gates, and resets
        clks = map fst (vClk vmi)
        clkgates = [ (gate_name, clk_name) |
                         (clk_name, Just gate_name) <- vClk vmi ]
        rsts = vRst vmi
        isClk i = elem i clks
        isGate i = lookup i clkgates
        isRst i = elem i rsts

        -- filter out clocks and resets
        foldfunc p@(i,e) (cs, gs, rs, as) =
            if (isClk i)
            then ((p:cs), gs, rs, as)
            else case (isGate i) of
                     Just clk_id -> let t = (i, clk_id, e)
                                    in  (cs, (t:gs), rs, as)
                     Nothing -> if (isRst i)
                                then (cs, gs, (p:rs), as)
                                else (cs, gs, rs, (p:as))

        (clk_pairs, gate_triples, rst_pairs, arg_pairs) =
            foldr foldfunc ([],[],[],[]) input_pairs

        mkArgTriple (arg_id, arg_expr) arg_num = (arg_id, arg_num, arg_expr)
        arg_triples = zipWith mkArgTriple arg_pairs [1..]

    in
        (clk_pairs, gate_triples, rst_pairs, arg_triples)
-}
