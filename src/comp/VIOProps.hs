module VIOProps (VIOProps, getIOProps, getIOPropsA) where

import Data.List(intersect, nub, tails, genericLength, sortBy, partition)
import Data.Maybe(catMaybes, isNothing, fromMaybe)
import qualified Data.Map as M
import qualified Data.Set as S
import Util
import Eval(NFData(..), rnf)
import Flags
import PPrint
import ErrorUtil(internalError)
import IntLit(ilValue)
import Id
import PreIds(idPrimAction, idInout_, idPrimUnit)
import Pragma(PProp, isAlwaysRdy, isAlwaysEn)
import VModInfo(VModInfo, vArgs, vFields, vClk, VName(..), VeriPortProp(..),
                VArgInfo(..), VFieldInfo(..), VPort, VWireInfo(..),
                VClockInfo(..),
                getOutputClockPortTable, getOutputResetPortTable,
                lookupInputClockWires, lookupInputResetWire,
                mkNamedEnable, mkNamedOutput, mkNamedInout, vName_to_id)
import Prim
import ASyntax
import ASyntaxUtil( AVars(..), aType )
import AScheduleInfo(AScheduleInfo(..), ExclusiveRulesDB,
                     areRulesExclusive)
import AState(MethBlob, ratToBlobs, genMethodMult)
import BackendNamingConventions(createVerilogNameMapForAVInst,
                                xLateIdUsingFStringMap,
                                isRWire, isRWire0,
                                isBypassWire, isBypassWire0,
                                isClockCrossingBypassWire,
                                rwireSetStr, rwireGetStr, rwireHasStr,
                                rwireGetResId, rwireHasResId,
                                isCRegInst, cregReadStr, cregWriteStr)

-- import Debug.Trace
-- import Util(traces)


-- The VIO properties are best described as the comments which are printed
-- before the verilog module is dumped in the Verilog file..

data IOIO = INPUT | OUTPUT | INOUT deriving (Eq)

instance NFData IOIO where rnf x = seq x ()

--   (name, input(T)/output(F), width, properties)
newtype VIOProps = VIOProps [(AId, IOIO, Integer, [VeriPortProp])]
        deriving (Eq)

instance NFData VIOProps where
    rnf (VIOProps xs) = rnf xs

instance PPrint VIOProps where
    pPrint d p (VIOProps ps) =
                text "Name                         I/O  size props" $+$
                foldr ($+$) (text "") (map pp ps)
        where pp (i, io, sz, ps) =
                let s = getIdString i
                    si = s ++ replicate (29 - length s) ' '
                    n = itos sz
                    sn = replicate (5 - length n) ' ' ++ n
                    iotxt = case (io) of
                              INPUT -> " I"
                              OUTPUT-> " O"
                              INOUT -> "IO"
                in  text si <+> text iotxt <+>
                    text sn <+> sep (map (pPrint d 0) ps)

-- assuming foreign functions do not affect the IO properties
getIOProps :: Flags -> ASPackage -> (VIOProps, [VPort])
getIOProps flags ppp@(ASPackage _ _ _ os is ios vs _ ds io_ds fs _ _ _) =
        -- returns the VIOProps structure
        -- and a mapping of Verilog port names to their port properties
        (VIOProps ais, [(VName (getIdString i), ps) | (i, _, _, ps) <- ais ])
  where
        -- VIOProps for all outputs
        ois = map getOInfo os
        -- VIOProps for all inputs
        iis = map getIInfo is
        -- VIOProps for all inouts
        iois = map getIOInfo ios
        -- VIOProps for all ports (but only nonzero sized)
        ais = filter nonZero (ois ++ iis ++ iois)
                where nonZero (_, _, sz, _) = sz /= 0

        -- construct VIOProps for an output
        getOInfo :: (AId,AType) -> (AId, IOIO, Integer, [VeriPortProp])
        getOInfo (i, t) = (i, OUTPUT, size t, getOProp i)

        -- construct VIOProps for an input
        getIInfo :: (AId,AType) -> (AId, IOIO, Integer, [VeriPortProp])
        getIInfo (i, t) = (i, INPUT, size t, getIProp i)

        -- construct VIOProps for an inout
        getIOInfo :: (AId,AType) -> (AId, IOIO, Integer, [VeriPortProp])
        getIOInfo (i, t) = (i, INOUT, size t, getIOProp i)

        -- lookup the definition for an id
        getDef :: AId -> ADef
        getDef i = M.findWithDefault err i defMap
            where err = internalError ("getIOProps.getDef failed: " ++
                                       ppString (i, defMap))

        -- mapping from ids to their defs
        defMap = M.union (M.fromList [(i, d) | d@(ADef i _ _ _) <- ds ])
                         -- XXX do the two maps ever mix?  can we defined
                         -- XXX getIOProps to only work with the ioDefMap?
                         ioDefMap

        ioDefMap = M.fromList [(i, d) | d@(ADef i _ _ _) <- io_ds ]

        -- ----------
        -- construct the VeriPortProp list for an output

        getOProp i =
            case getDef i of
            ADef _ _ e _ -> let deduced_props = getOEP e
                            in  -- we could add any props known the ifc here
                              -- (such as input clocks/resets)
                              -- for now, we just derive this
                              -- (but it means that "const" outputs don't
                              -- also get props like "reset" or "gate")
                              deduced_props

        -- construct the VeriPortProp list for an expression
        getOEP :: AExpr -> [VeriPortProp]
        -- for concats, find the common properties of the pieces
        getOEP (APrim _ _ PrimConcat es)         = joinOutProps (map getOEP es)
        -- an extraction doesn't change the properties
        getOEP (APrim _ _ PrimExtract [e, _, _]) = getOEP e
        -- either an output port of a submodule or an input to the ASPackage
        -- (so get its properties)
        getOEP (ASPort _ i)                      = getOVProp i
        -- follow defs
        getOEP (ASDef _ i)                       = getOProp i
        -- constant values
        getOEP (ASParam _ i)                     = [VPconst]
        getOEP (ASInt _ _ _)                     = [VPconst]
        getOEP (ASStr _ _ _)                     = [VPconst]
        -- for any other use, we cannot conclude properties
        getOEP _                                 = []

        -- build table of wire properties for the state element outputs
        wireMap_out :: M.Map AId [VeriPortProp]
        wireMap_out =
            let submod_pairs =
                    -- clock and reset outputs
                    [(i, ps) |
                         v <- vs,
                         (i, _, (_, ps)) <- getSpecialOutputs v] ++
                    -- output ports for method return values
                    [(veri_id, pprops) |
                         -- for each instance
                         v <- vs,
                         -- create the method name map
                         let nmap = M.fromList $
                                    createVerilogNameMapForAVInst flags v,
                         -- for each method (not clocks or resets)
                         vfi@(Method {}) <- vFields (avi_vmi v),
                         -- for each method output port
                         (methpart, (vname, pprops))
                             <- zip (map MethodResult (splitPortNums (vf_outputs vfi)))
                                    (vf_outputs vfi),

                         -- for each port copy
                         ino <- if (vf_mult vfi > 1) then
                                  map Just [0 .. vf_mult vfi]
                                else [Nothing],
                         -- construct the method output signal name
                         let meth_id = mkMethId (avi_vname v)
                                                (vf_name vfi)
                                                ino
                                                methpart,
                         -- convert to Verilog signal name
                         let veri_id = xLateIdUsingFStringMap nmap meth_id
                    ]
                -- outputs can also come from top-level inputs;
                -- we use [] for the properties of the input
                -- XXX this should be OK, because the deriving of the
                -- XXX property for the input would give up if it
                -- XXX reached an output, and the props would be []
                input_pairs =
                    [ (i, []) | (i,_) <- is ]
                -- ifc inouts can also come from argument inouts
                inout_pairs =
                    [ (i, [VPinout])
                      | (i,_) <- ios,
                        isNothing (M.lookup i ioDefMap) ]
            in
                M.unions [M.fromList submod_pairs,
                          M.fromList input_pairs,
                          M.fromList inout_pairs]

        getOVProp :: AId -> [VeriPortProp]
        getOVProp i =
            case (M.lookup i wireMap_out) of
                Just ps -> ps
                Nothing ->
                    -- since we added the module inputs to the map,
                    -- this branch should never happen.  alternatively,
                    -- we could not put the inputs in the map and just
                    -- return empty-list here; but the internal check
                    -- is nice to have (if it's not too expensive).
                    internalError ("getOVProp: could not find method " ++
                                   ppString i ++ " in wireMap_out:\n" ++
                                   ppReadable wireMap_out)

        -- ----------
        -- construct the VeriPortProp list for an input

        getIProp :: AId -> [VeriPortProp]
        getIProp i =
            let derived_props = getSignalInProp i
            in  -- we could add any props known from the ifc here
                -- (such as input clocks/resets)
                -- for now, we just derive this (see comment below)
                derived_props

        -- a list the signals which are connected to
        -- submodule input ports (method arguments and enables)
        wireMap_in :: M.Map Id [VeriPortProp]
        wireMap_in =
            let submod_pairs =
                    -- submodule method inputs
                    [(veri_id, pprops) |
                         -- for each instance
                         v <- vs,
                         -- create the method name map
                         let nmap = M.fromList $
                                    createVerilogNameMapForAVInst flags v,
                         -- for each method (not clocks or resets)
                         vfi@(Method {}) <- vFields (avi_vmi v),
                         -- for each method input part (args and enables);
                         -- args carry (source-arg #, port-within-arg #)
                         (methpart, (vname, pprops))
                             <- [ (MethodArg argN portM, port)
                                | (argN, ports) <- zip [1..] (vf_inputs vfi)
                                , (portM, port) <- zip (splitPortNums ports) ports
                                ] ++
                                case (vf_enable vfi) of
                                    Nothing -> []
                                    Just port -> [(MethodEnable, port)],
                         -- for each port copy
                         ino <- if (vf_mult vfi > 1) then
                                  map Just [0 .. vf_mult vfi]
                                else [Nothing],
                         -- construct the method output signal name
                         let meth_id = mkMethId (avi_vname v)
                                                (vf_name vfi)
                                                ino
                                                methpart,
                         -- convert to Verilog signal name
                         let veri_id = xLateIdUsingFStringMap nmap meth_id
                    ] ++
                    -- submodule argument inputs
                    [(d, pprops) |
                         (AVInst { avi_vmi = vi, avi_iargs = es }) <- vs,
                         (a, e) <- zip (vArgs vi) es,
                         -- AState has converted Clock/Reset to Port
                         let pprops =
                                 case a of
                                   (Port (_,pps) _ _) -> pps
                                   (Param _) -> [VPconst] -- XXX?
                                   arg -> internalError
                                              ("VIOProps wireMap_in: " ++
                                               "unexpected arg: " ++
                                               ppReadable arg) ,
                         -- only carry these props to direct refs
                         let ds = aVars e,
                         all (\i -> okUse i e) ds,
                         d <- ds
                    ]
                -- inputs can also feed into outputs;
                -- we use [] for the properties of the output
                -- (since it is a use that we can conclude nothing about,
                --  not "unused")
                -- XXX this should be OK?
                output_pairs =
                    [ (o, []) | (o,_) <- os ]
                -- an argument inout whose net is exposed at an
                -- interface inout is one net at two pins: the argument
                -- pin is live, not unused (the interface-inout defs are
                -- not in the defuse map, so record the use here)
                inout_sink_pairs =
                    [ (i, [VPinout]) |
                          ADef _ _ e _ <- io_ds, i <- aVars e ]
            in
                M.fromList (submod_pairs ++ output_pairs ++
                            inout_sink_pairs)

        -- use a map to limit search over all definition
        -- key is AId data is list of defs where key is used.
        defuseMap :: M.Map AId (S.Set AId)
        defuseMap = getDefUses ds

        -- given a signal, this determines its props
        getSignalInProp :: AId -> [VeriPortProp]
        getSignalInProp i =
            let
                -- there are two sources of port props:
                --   * wireMap_in (submod inputs, top-mod outputs)
                --   * following defs (via defuseMap) to eventually
                --     reach Ids in wireMap_in
                -- For most of the Ids in the wireMap_in, there should be
                -- no uses in the defs to follow.  But some can be followed.
                -- So in order to support that (and reduce the requirements
                -- on defs in ASPackage), we check both sources and merge.

                wiremap_props =
                    case (M.lookup i wireMap_in) of
                        Just ps -> ps
                        Nothing -> [VPunused]

                defuse_props =
                    let user_set = M.findWithDefault (S.empty) i defuseMap
                    in -- is it unused?
                       if (S.null user_set)
                       then [VPunused]
                       else
                         -- determine if the uses are "direct"
                         -- (direct reference, concat, or extract, but no
                         -- other functions on the value)
                         let uses = [ if noUse i user_e
                                      then Just []
                                      else if okUse i user_e
                                           then Just [user]
                                           else Nothing
                                      | user <- S.toList user_set,
                                        let user_e = adef_expr $ getDef user ]
                         in
                             -- if any are not direct uses,
                             -- then we conclude nothing
                             if (any isNothing uses)
                             then []
                             else let users = concat $ catMaybes uses
                                      userprops = map getSignalInProp users
                                  in
                                      -- a prop is only valid if all uses
                                      -- have that prop
                                      joinInProps userprops
            in
                -- merge the props from the two sources
                joinInProps [wiremap_props, defuse_props]

        -- ----------
        -- construct the VeriPortProp list for an inout

        getIOProp :: AId -> [VeriPortProp]
        getIOProp i =
            -- if it's an interface Inout, then treat it like an output;
            -- otherwise, it's an argument Inout, so treat it like an input
            case M.lookup i ioDefMap of
              Just _  -> getOProp i
              Nothing -> getIProp i


-- given the props for multiple signals,
-- compute the props that the concatenation should have
joinOutProps :: [[VeriPortProp]] -> [VeriPortProp]
joinOutProps (x:xs) = foldr intersect x xs
-- empty list only occurs with prims of no args
-- XXX do we have any? if they all give constant return values,
-- XXX then we could return [VPconst] here
joinOutProps [] = []

-- given the deduced props for multiple signals,
-- compute the props that should be deduced for a signal
-- which connects directly to all these signals (and only these)
joinInProps :: [[VeriPortProp]] -> [VeriPortProp]
joinInProps pss =
    let
        -- if a signal is unused, it might as well not exist,
        -- so don't count it
        pss' = filter (VPunused `notElem`) pss
    in
        case pss' of
            [] -> [VPunused]
            (x:xs) ->
                -- otherwise, a prop needs to be on all used signals
                -- for it to be on the source
                foldr intersect x xs


-- This used to return (Map AId (Set ADef)), which meant that the whole def
-- had to be compared, when inserting new elements, which was inefficient
-- for large expressions.  Changed it to be just a set of the AId, which
-- requires that the def needs to be looked up.  If we're willing to trade
-- off memory, we could use (Map AId ADef) instead of (Set AId) to avoid
-- the lookup.  We could also consider memo-izing "getSignalInProp", if
-- recomputation becomes a problem.  But it's likely that the number of
-- defs being followed is small, so this seems like the right trade-off.
--
getDefUses :: [ADef] -> M.Map AId (S.Set AId)
getDefUses defs = foldl addDef M.empty defs
  where
    addDef :: M.Map AId (S.Set AId) -> ADef -> M.Map AId (S.Set AId)
    addDef m0 def@(ADef def_id _ def_e _) = foldl (addUses) m0 used
      where
        used = aVars def_e
        addUses :: M.Map AId (S.Set AId) -> AId -> M.Map AId (S.Set AId)
        addUses m use_id = M.insertWith S.union use_id (S.singleton def_id) m


okUse :: AId -> AExpr -> Bool
okUse i (APrim _ _ PrimConcat es)         = and (map (okUse i) es)
okUse i (APrim _ _ PrimExtract [e, _, _]) = okUse i e
okUse i (APrim _ _ _ es)                  = and (map (noUse i) es)
okUse i (ANoInlineFunCall _ _ _ es)       = and (map (noUse i) es)
okUse i (AFunCall _ _ _ _ es)             = and (map (noUse i) es)
okUse i (ASInt _ _ _)                     = True
okUse i (ASStr _ _ _)                     = True
okUse i (ASPort _ _)                      = True
okUse i (ASParam _ _)                     = True
okUse i (ASDef _ _)                       = True
okUse i (ASAny _ _)                       = True
okUse i e                                 = internalError ("getIOProps.okUse " ++ show (i,e))


noUse :: AId -> AExpr -> Bool
noUse i (APrim _ _ _ es)     = and (map (noUse i) es)
noUse i (ANoInlineFunCall _ _ _ es) = and (map (noUse i) es)
noUse i (AFunCall _ _ _ _ es) = and (map (noUse i) es)
noUse i (AMethCall _ _ _ es) = and (map (noUse i) es)
noUse i (ASPort _ i')        = i /= i'
noUse i (ASParam _ i')       = i /= i'
noUse i (ASDef _ i')         = i /= i'
noUse _ _                    = True

-- compute the size of a port
size :: AType -> Integer
size (ATBit n) = n
size (ATAbstract a _) | a == idPrimAction = 1
size (ATAbstract a [n]) | a == idInout_ = n
size (ATAbstract a _) | a == idPrimUnit = 0
size (ATString _ ) = 0
size t = internalError ("getIOProps.size: " ++ show t)


-- ===============================================================
-- getIOPropsA: a version of getIOProps which works on APackage
-- (prior to AState), rather than on the final ASPackage.
--
-- The ports of the eventually-generated module are not explicit in an
-- APackage; they are constructed by AState from the module arguments
-- (apkg_inputs / apkg_external_wires) and the interface (apkg_interface).
-- This function mirrors that construction (see AState.aState') to
-- enumerate the same ports (same names, in the same order), and then
-- assigns properties to them.
--
-- This is an approximation of what getIOProps computes: properties
-- which are structurally known at the APackage level (clock, clock
-- gate, reset, inout, and any properties declared in the VArgInfo or
-- VFieldInfo) are assigned directly, rather than being deduced from
-- the generated netlist.  Since scheduling and state instantiation
-- have not happened yet, properties that getIOProps deduces by
-- following the final wiring (such as "const", "reg", and "unused")
-- are approximated by a similar analysis over the APackage (see
-- getOutPropsA and getInPropsA below).
--
-- The "unused" property describes the hardware: a signal whose only
-- uses are as arguments of foreign function or task calls (which
-- exist only in simulation) is unused, as in getIOProps.
--
-- Note some intentional differences from getIOProps:
--  * Clock, gate, and reset ports are always labeled with their
--    structural properties (clock/clock gate/reset), whereas getIOProps
--    only labels them when the deduction succeeds (for example, an
--    unused input clock is labeled "clock unused" here, but just
--    "unused" by getIOProps).
--  * "unused" propagates backwards through any logic which is itself
--    unused, whereas getIOProps only follows direct (okUse)
--    connections; so a signal whose only sink is a foreign call,
--    reached through arithmetic, is "unused" here but gets no
--    properties from getIOProps (it genuinely drives no hardware).
--  * Properties which require the netlist optimization's boolean
--    simplification can be missed.  The common reductions are
--    performed (see evalConstA and getOutPropsA): the schedule's
--    consequences, recorded in the CAN_FIRE/WILL_FIRE defs by
--    AAddScheduleDefs, are constant-folded; selections with constant
--    conditions or equal branches reduce; 1-bit AND/OR reduce over
--    constant operands; and complementary operands (x and !x) fold,
--    as for the ready of a split method.  When the AScheduleInfo is
--    supplied, the argument muxes of state instance methods are also
--    modeled, with the same port allocation, exclusivity test, and
--    priority (earliness) order that AState uses, so an arm which
--    wins or loses the arbitration outright (because the WILL_FIREs
--    involved are constant) is seen as a direct connection or as
--    dropped.  Not replicated are: common-subexpression elimination
--    and other deeper aOpt rewriting, and the tracing of inout nets
--    through InoutConnect instances.  Such misses only lose
--    properties; they never assert a property that the getIOProps
--    deduction would contradict.
--
-- Wire instances (RWire, RWire0, BypassWire) which InlineWires will
-- inline away after AState are looked through: a value flows from the
-- "wset" argument to the "wget" result as through a plain wire (or
-- through a mux, when there are multiple setters, in which case
-- properties do not flow but use/unused information still does).
-- CReg instances (inlined by InlineCReg, leaving a plain register)
-- are also looked through: port 0's read is the register output
-- ("reg"), and higher ports' reads bypass through selections which
-- reduce when the schedule makes the intervening write enables
-- constant.

getIOPropsA :: Flags -> [PProp] -> Maybe AScheduleInfo -> APackage ->
               (VIOProps, [VPort])
getIOPropsA flags pps mschedinfo apkg =
        -- returns the VIOProps structure
        -- and a mapping of Verilog port names to their port properties
        (VIOProps ais, [(VName (getIdString i), ps) | (i, _, _, ps) <- ais ])
  where
        ifc  = apkg_interface apkg
        fmod = apkg_is_wrapped apkg
        wi   = apkg_external_wires apkg
        vs   = apkg_state_instances apkg
        ds   = apkg_local_defs apkg
        -- all rules, including the bodies of the action methods
        rs   = apkg_rules apkg ++ concatMap aIfaceRules ifc

        -- Whether the schedule allows a rule (by its WILL_FIRE) to
        -- ever fire: a rule whose WILL_FIRE the schedule reduces to
        -- constant 0 contributes nothing to the hardware (all of its
        -- logic is dropped), so its method calls do not count as call
        -- sites, its wire sets do not count as setters, and it makes
        -- no uses.  (This is queried lazily, per rule, because
        -- evaluating one rule's WILL_FIRE can require the setters of a
        -- wire read in its predicate, whose liveness is evaluated in
        -- turn.)
        isLiveWF :: AId -> Bool
        isLiveWF wf = evalDefA wf /= Just 0

        isLiveRule :: ARule -> Bool
        isLiveRule r = isLiveWF (mkIdWillFire (arule_id r))

        -- port name tables for the interface output clocks and resets
        clockPortTable = getOutputClockPortTable (wClk wi)
        resetPortTable = getOutputResetPortTable (wRst wi)

        -- module arguments with their VArgInfo
        args_with_info = getAPackageInputs apkg

        -- merge the structurally known properties with the deduced ones
        mergeProps :: [VeriPortProp] -> [VeriPortProp] -> [VeriPortProp]
        mergeProps sps dps = nub (sps ++ dps)

        -- VIOProps for all ports (but only nonzero sized)
        ais = filter nonZero (ois ++ iis ++ iois)
                where nonZero (_, _, sz, _) = sz /= 0

        -- ----------
        -- outputs
        -- (in the order that AState creates them:
        --  method results, then output clocks, then output resets)

        ois = [ (i, OUTPUT, size t, mergeProps sps (getOutPropsA e)) |
                    (i, t, sps, e) <- meth_outs ++ clk_outs ++ rst_outs ]

        -- method value/actionvalue result ports
        -- (mirrors AState.outputDefToADef and its always_ready filtering)
        isAlwaysReadyMethod m =
            isRdyId (aIfaceName m) && isAlwaysRdy pps (aIfaceName m)
        other_ifc = filter (not . isAlwaysReadyMethod) ifc

        meth_outs :: [(AId, AType, [VeriPortProp], AExpr)]
        meth_outs = concatMap getMethOut other_ifc

        getMethOut :: AIFace -> [(AId, AType, [VeriPortProp], AExpr)]
        getMethOut ai@(AIDef {}) =
            -- a module wrapped around a non-inlined function has no RDY
            if (fmod && isRdyId (aif_name ai))
            then []
            else [(mkNamedOutput fi, adef_type d,
                   declaredOutProps fi, adef_expr d)]
          where fi = aif_fieldinfo ai
                d  = aif_value ai
        getMethOut ai@(AIActionValue {}) =
            [(mkNamedOutput fi, adef_type d,
              declaredOutProps fi, adef_expr d)]
          where fi = aif_fieldinfo ai
                d  = aif_value ai
        getMethOut _ = []

        declaredOutProps :: VFieldInfo -> [VeriPortProp]
        declaredOutProps (Method { vf_output = Just (_, ps) }) = ps
        declaredOutProps _ = []

        -- output clock (and gate) ports (mirrors AState's clk_blob)
        clk_outs :: [(AId, AType, [VeriPortProp], AExpr)]
        clk_outs =
            concat [ (vName_to_id osc_vn, aTBool, [VPclock], osc) :
                     gate_ports |
                        (AIClock { aif_name = n,
                                   aif_clock =
                                       AClock { aclock_osc = osc,
                                                aclock_gate = gate } }) <- ifc,
                        let (osc_vn, mgate_vp) =
                                fromJustOrErr
                                    ("getIOPropsA: unknown output clock " ++
                                     ppReadable n)
                                    (M.lookup n clockPortTable),
                        let gate_ports =
                                case mgate_vp of
                                  Nothing -> []
                                  Just (gate_vn, gate_pps) ->
                                      [(vName_to_id gate_vn, aTBool,
                                        VPclockgate : gate_pps, gate)]
                   ]

        -- output reset ports (mirrors AState's rstn_defs)
        rst_outs :: [(AId, AType, [VeriPortProp], AExpr)]
        rst_outs =
            [ (vName_to_id rstn_vn, aTBool, [VPreset], w) |
                  (AIReset { aif_name = n,
                             aif_reset = AReset { areset_wire = w } }) <- ifc,
                  let rstn_vn =
                          fromJustOrErr
                              ("getIOPropsA: unknown output reset " ++
                               ppReadable n)
                              (M.lookup n resetPortTable)
            ]

        -- ----------
        -- inputs
        -- (in the order that AState creates them:
        --  module arguments, method arguments, method enables)

        -- (enable ports are referenced by the WILL_FIRE definitions
        -- that AAddScheduleDefs created, so they are deduced like any
        -- other input; see ruleWFUses for what uses a WILL_FIRE)
        iis = [ (i, INPUT, size t, mergeProps sps (getInPropsA i)) |
                    (i, t, sps) <- arg_ins ++ meth_arg_ins ++ en_ins ]

        -- module argument ports (clocks, resets, and ordinary ports;
        -- parameters are not ports and inouts are handled below)
        arg_ins :: [(AId, AType, [VeriPortProp])]
        arg_ins = concatMap cvtArg args_with_info

        cvtArg :: (AAbstractInput, VArgInfo) -> [(AId, AType, [VeriPortProp])]
        cvtArg (_, Param {}) = []
        cvtArg (AAI_Port (i, t), Port (_, pps) _ _) = [(i, t, pps)]
        cvtArg (AAI_Clock osc mgate, ClockArg {}) =
            (osc, aTBool, [VPclock]) :
            [ (gate, aTBool, [VPclockgate]) | Just gate <- [mgate] ]
        cvtArg (AAI_Reset r, ResetArg {}) = [(r, aTBool, [VPreset])]
        cvtArg (AAI_Inout {}, InoutArg {}) = []
        cvtArg (ai, argi) =
            internalError ("getIOPropsA.cvtArg: mismatched argument: " ++
                           show (ai, argi))

        -- method argument ports, with any properties declared in the ifc
        meth_arg_ins :: [(AId, AType, [VeriPortProp])]
        meth_arg_ins =
            concat [ zipWith mkArg (aIfaceArgs f)
                                   (argPortProps (aif_fieldinfo f) ++
                                    repeat [])
                   | f <- ifc ]
          where mkArg (i, t) pps = (i, t, pps)
                argPortProps (Method { vf_inputs = ins }) = map snd ins
                argPortProps _ = []

        -- method enable ports (mirrors AState's inputIds)
        en_ins :: [(AId, AType, [VeriPortProp])]
        en_ins =
            [ (mkNamedEnable fi, aTBool, enPortProps fi) |
                  (AIAction { aif_name = i, aif_fieldinfo = fi }) <- ifc,
                  not (isAlwaysEn pps i) ] ++
            [ (mkNamedEnable fi, aTBool, enPortProps fi) |
                  (AIActionValue { aif_name = i, aif_fieldinfo = fi }) <- ifc,
                  not (isAlwaysEn pps i) ]
          where enPortProps (Method { vf_enable = Just (_, ps) }) = ps
                enPortProps _ = []

        -- ----------
        -- inouts
        -- (module argument inouts, then interface inouts,
        --  in the order that AState creates them)

        -- as in getIOProps, an argument inout is used by the module
        -- (like an input) and an interface inout is provided by the
        -- module (like an output)
        iois = [ (i, INOUT, size t, mergeProps sps (getInPropsA i)) |
                     (i, t, sps) <- arg_iots ] ++
               [ (i, INOUT, size t, mergeProps sps (getOutPropsA e)) |
                     (i, t, sps, e) <- ifc_iots ]

        arg_iots :: [(AId, AType, [VeriPortProp])]
        arg_iots = [ (i, ATAbstract idInout_ [n], [VPinout]) |
                         (AAI_Inout i n, InoutArg {}) <- args_with_info ]

        ifc_iots :: [(AId, AType, [VeriPortProp], AExpr)]
        ifc_iots = [ (mkNamedInout fi, aType e, [VPinout], e) |
                         (AIInout _ (AInout e) fi) <- ifc ]

        -- ==========
        -- structures shared by the property deductions below

        -- map from state instance name to its VModInfo
        vmiMap :: M.Map AId VModInfo
        vmiMap = M.fromList [ (avi_vname v, avi_vmi v) | v <- vs ]

        -- find the VFieldInfo for a method of a state instance
        -- (method ids in AMethCall/ACall are qualified; vf_name is not)
        findMethodA :: AId -> AId -> Maybe VFieldInfo
        findMethodA obj meth = do
            vmi <- M.lookup obj vmiMap
            case [ m | m@(Method {}) <- vFields vmi,
                       vf_name m == unQualId meth ] of
              (m:_) -> Just m
              []    -> Nothing

        -- the local defs and the interface value defs, by id
        defMapA :: M.Map AId ADef
        defMapA = M.fromList ([ (i, d) | d@(ADef i _ _ _) <- ds ] ++
                              [ (i, d) | f <- ifc,
                                         d@(ADef i _ _ _) <- ifcValueDef f ])

        ifcValueDef :: AIFace -> [ADef]
        ifcValueDef (AIDef { aif_value = d }) = [d]
        ifcValueDef (AIActionValue { aif_value = d }) = [d]
        ifcValueDef _ = []

        -- ----------
        -- wire instances (RWire, RWire0, BypassWire) will be inlined
        -- away after AState (see InlineWires), so we look through them:
        -- a value flows from the "wset" argument to the "wget" result
        -- as through a plain wire (or through a mux, if there is more
        -- than one setter)

        isInlinedWireA :: AVInst -> Bool
        isInlinedWireA v =
            removeRWire flags &&
            (isRWire v || isRWire0 v || isBypassWire0 v ||
             (isBypassWire v &&
              (not (isClockCrossingBypassWire v) || removeCross flags)))

        wireInstSet :: S.Set AId
        wireInstSet = S.fromList [ avi_vname v | v <- vs, isInlinedWireA v ]

        isWireMeth :: String -> AId -> AId -> Bool
        isWireMeth str obj meth =
            (obj `S.member` wireInstSet) &&
            (getIdBaseString (unQualId meth) == str)

        isWireSet, isWireGet, isWireHas :: AId -> AId -> Bool
        isWireSet = isWireMeth rwireSetStr
        isWireGet = isWireMeth rwireGetStr
        isWireHas = isWireMeth rwireHasStr

        -- the nodes representing the data carried by a wire instance
        -- and its validity (also the names of the signals which carry
        -- them after inlining)
        wireDataId, wireHasId :: AId -> AId
        wireDataId inst = rwireGetResId inst
        wireHasId inst = rwireHasResId inst

        -- flowing into a wire instance: alive only as far as the
        -- wire's data and validity are used
        wireFlowUses :: AId -> [AUse]
        wireFlowUses inst = [AUVia (wireDataId inst), AUVia (wireHasId inst)]

        -- the setters of each wire instance: the WILL_FIRE of the
        -- calling rule, the condition, and the data arguments
        wireSetters :: M.Map AId [(AId, AExpr, [AExpr])]
        wireSetters =
            M.fromListWith (++)
                [ (aact_objid a, [(mkIdWillFire (arule_id r), c, es)]) |
                      r <- rs, a@(ACall {}) <- arule_actions r,
                      isWireSet (aact_objid a) (acall_methid a),
                      -- the first element is the condition
                      (c:es) <- [aact_args a] ]

        -- the setters whose rules can ever fire
        liveWireSetters :: AId -> [(AId, AExpr, [AExpr])]
        liveWireSetters inst =
            [ s | s@(wf, _, _) <- M.findWithDefault [] inst wireSetters,
                  isLiveWF wf ]

        -- the number of live "wset" call sites of a wire instance
        wireSetCount :: AId -> Integer
        wireSetCount = genericLength . liveWireSetters

        -- the properties of a wire's "wget" value
        wireGetProps :: AId -> [VeriPortProp]
        wireGetProps inst =
            case (liveWireSetters inst) of
              -- never set: inlining defines the value as a constant
              []  -> [VPconst]
              -- one setter: the value flows through
              [(_, _, [e])] -> getOutPropsA e
              -- multiple setters: the value comes from a mux
              _   -> []

        -- the properties of a wire's "whas" value
        wireHasProps :: AId -> [VeriPortProp]
        wireHasProps inst =
            case (wireHasVal inst) of
              Just _  -> [VPconst]
              Nothing -> []

        -- the constant value of a wire's "whas", when the schedule
        -- determines it: the OR over the setters of (WILL_FIRE AND
        -- condition)
        wireHasVal :: AId -> Maybe Integer
        wireHasVal inst =
            let conj :: (AId, AExpr, [AExpr]) -> Maybe Integer
                conj (wf, c, _) =
                    case (evalDefA wf, evalConstA c) of
                      (Just 0, _) -> Just 0
                      (_, Just 0) -> Just 0
                      (Just _, Just _) -> Just 1
                      _ -> Nothing
                vals = map conj (M.findWithDefault [] inst wireSetters)
            in  if (null vals) then Just 0
                else if (any (== (Just 1)) vals) then Just 1
                else if (all (== (Just 0)) vals) then Just 0
                else Nothing

        -- the constant value of a wire's "wget", when it can be known
        wireGetVal :: AId -> Maybe Integer
        wireGetVal inst =
            case (liveWireSetters inst) of
              -- never set: the value is tied to constant 0
              []  -> Just 0
              -- one setter: the data is connected without gating
              [(_, _, [e])] -> evalConstA e
              _   -> Nothing

        -- ----------
        -- CReg instances will be inlined after AState (see InlineCReg,
        -- keeping only the underlying register), so we look through
        -- them: port 0's read is the register output, and port N's
        -- read bypasses through selection between the port (N-1) write
        -- data and port (N-1)'s read.  Writes always feed the retained
        -- register, so write arguments are uses without properties.

        cregInstSet :: S.Set AId
        cregInstSet =
            if (removeCReg flags)
            then S.fromList [ avi_vname v | v <- vs, isCRegInst v ]
            else S.empty

        -- the number of ports on the primitive CReg (see InlineCReg)
        cregPorts :: Int
        cregPorts = 5

        -- identify a call to a CReg method: Just (port, is_read)
        cregMeth :: AId -> AId -> Maybe (Int, Bool)
        cregMeth obj meth
            | obj `S.member` cregInstSet =
                let s = getIdBaseString (unQualId meth)
                in  case ([ (n, True) | n <- [0..cregPorts-1],
                                        s == cregReadStr n ] ++
                          [ (n, False) | n <- [0..cregPorts-1],
                                         s == cregWriteStr n ]) of
                      (r:_) -> Just r
                      []    -> Nothing
            | otherwise = Nothing

        -- the writers of each CReg port:
        -- the caller's WILL_FIRE, the condition, and the data argument
        cregWriters :: M.Map (AId, Int) [(AId, AExpr, AExpr)]
        cregWriters =
            M.fromListWith (++)
                [ ((aact_objid a, n),
                   [(mkIdWillFire (arule_id r), c, e)]) |
                      r <- rs, a@(ACall {}) <- arule_actions r,
                      Just (n, False) <-
                          [cregMeth (aact_objid a) (acall_methid a)],
                      (c:e:_) <- [aact_args a] ]

        -- the writers whose rules can ever fire
        liveCregWriters :: AId -> Int -> [(AId, AExpr, AExpr)]
        liveCregWriters inst n =
            [ w | w@(wf, _, _) <- M.findWithDefault [] (inst, n) cregWriters,
                  isLiveWF wf ]

        -- the constant value of a CReg port's write enable, when the
        -- schedule determines it (like wireHasVal)
        cregEnVal :: AId -> Int -> Maybe Integer
        cregEnVal inst n =
            let conj :: (AId, AExpr, AExpr) -> Maybe Integer
                conj (wf, c, _) =
                    case (evalDefA wf, evalConstA c) of
                      (Just 0, _) -> Just 0
                      (_, Just 0) -> Just 0
                      (Just _, Just _) -> Just 1
                      _ -> Nothing
                vals = map conj (M.findWithDefault [] (inst, n) cregWriters)
            in  if (null vals) then Just 0
                else if (any (== (Just 1)) vals) then Just 1
                else if (all (== (Just 0)) vals) then Just 0
                else Nothing

        -- the properties of a CReg port's read value
        cregReadProps :: AId -> Int -> [VeriPortProp]
        cregReadProps _ 0 = [VPreg]   -- the retained register's output
        cregReadProps inst n =
            case (cregEnVal inst (n-1)) of
              -- the bypass is never taken
              Just 0 -> cregReadProps inst (n-1)
              -- the bypass is always taken: a single writer's data
              -- flows through
              Just _ ->
                  case (liveCregWriters inst (n-1)) of
                    [(_, _, e)] -> getOutPropsA e
                    _ -> []
              -- otherwise it is a mux
              Nothing -> []

        -- the constant value of a CReg port's read, when it can be
        -- known (the register itself is never constant)
        cregReadVal :: AId -> Int -> Maybe Integer
        cregReadVal _ 0 = Nothing
        cregReadVal inst n =
            case (cregEnVal inst (n-1)) of
              Just 0 -> cregReadVal inst (n-1)
              Just _ ->
                  case (liveCregWriters inst (n-1)) of
                    [(_, _, e)] -> evalConstA e
                    _ -> Nothing
              Nothing -> Nothing

        -- ----------
        -- Evaluate an expression to a constant value, when the
        -- definitions allow it.  This realizes the consequences of the
        -- schedule, which AAddScheduleDefs recorded in the defs: for
        -- example, the WILL_FIRE of a conflict-free rule with a
        -- constant-True predicate is the constant 1, and the WILL_FIRE
        -- of a rule which can never fire is the constant 0.
        -- Boolean structure is only folded at 1-bit width.

        evalConstA :: AExpr -> Maybe Integer
        evalConstA (ASInt _ _ il) = Just (ilValue il)
        evalConstA (ASDef _ i) = evalDefA i
        evalConstA (APrim _ (ATBit 1) p es) = evalPrimA p es
        evalConstA (AMethCall _ obj meth _)
            | isWireHas obj meth = wireHasVal obj
            | isWireGet obj meth = wireGetVal obj
            | Just (n, True) <- cregMeth obj meth = cregReadVal obj n
        evalConstA _ = Nothing

        -- evaluation of defs, memoized (the map's values are lazy)
        evalDefMemo :: M.Map AId (Maybe Integer)
        evalDefMemo = M.map (evalConstA . adef_expr) defMapA

        evalDefA :: AId -> Maybe Integer
        evalDefA i = fromMaybe Nothing (M.lookup i evalDefMemo)

        evalPrimA :: PrimOp -> [AExpr] -> Maybe Integer
        evalPrimA p [e] | (p == PrimBNot) || (p == PrimInv) =
            fmap (1 -) (evalConstA e)
        evalPrimA p es | (p == PrimBAnd) || (p == PrimAnd) =
            let vs = map evalConstA es
            in  if (any (== (Just 0)) vs) then Just 0
                else if (all (== (Just 1)) vs) then Just 1
                -- a contradiction (x && !x) is 0
                else if (anyComplementaryA es) then Just 0
                else Nothing
        evalPrimA p es | (p == PrimBOr) || (p == PrimOr) =
            let vs = map evalConstA es
            in  if (any (== (Just 1)) vs) then Just 1
                else if (all (== (Just 0)) vs) then Just 0
                -- a tautology (x || !x) is 1
                else if (anyComplementaryA es) then Just 1
                else Nothing
        evalPrimA PrimIf [c, t, e] =
            case (evalConstA c) of
              Just 0 -> evalConstA e
              Just _ -> evalConstA t
              Nothing -> Nothing
        evalPrimA _ _ = Nothing

        -- follow def references to the defining expression
        derefA :: AExpr -> AExpr
        derefA e@(ASDef _ i) =
            maybe e (derefA . adef_expr) (M.lookup i defMapA)
        derefA e = e

        -- whether any two operands are complementary (x and !x),
        -- looking through def references; this recognizes the
        -- tautologies that the netlist optimization would fold, such
        -- as the ready of a split method (an OR of complementary
        -- split conditions)
        anyComplementaryA :: [AExpr] -> Bool
        anyComplementaryA es =
            let es' = map derefA es
                isNotOf (APrim _ _ p [a]) b
                    | (p == PrimBNot) || (p == PrimInv) = derefA a == b
                isNotOf _ _ = False
                compl x y = isNotOf x y || isNotOf y x
            in  or [ compl x y | (x:ys) <- tails es', y <- ys ]

        -- pseudo-defs relating the output clock, reset, and inout port
        -- ids to the expressions which drive them (AState creates real
        -- defs for these; see clk_defs, rstn_defs, and iot_defs there)
        out_wire_defs :: [(AId, AExpr)]
        out_wire_defs =
            [ (i, e) | (i, _, _, e) <- clk_outs ++ rst_outs ++ ifc_iots ]

        -- ----------
        -- deduce the properties of an output from its defining
        -- expression (the analog of getOEP in getIOProps)

        -- table of properties for signals which output definitions can
        -- reference: the special outputs (clocks, resets, inouts) of
        -- the state instances, and the module's own inputs (which, as
        -- in getIOProps' wireMap_out, provide no properties)
        wireMapA_out :: M.Map AId [VeriPortProp]
        wireMapA_out =
            let submod_pairs = [ (i, ps) |
                                     v <- vs,
                                     (i, _, (_, ps)) <- getSpecialOutputs v ]
                input_pairs = [ (i, []) |
                                    (i, _, _) <- arg_ins ++ meth_arg_ins ]
            in  M.union (M.fromList submod_pairs) (M.fromList input_pairs)

        getOutPropsA :: AExpr -> [VeriPortProp]
        -- for concats, find the common properties of the pieces
        getOutPropsA (APrim _ _ PrimConcat es) =
            joinOutProps (map getOutPropsA es)
        -- an extraction doesn't change the properties
        getOutPropsA (APrim _ _ PrimExtract [e, _, _]) = getOutPropsA e
        -- a selection whose condition the schedule makes constant
        -- reduces to one of its branches
        getOutPropsA (APrim _ _ PrimIf [c, t, e])
            | Just v <- evalConstA c =
                if (v == 0) then getOutPropsA e else getOutPropsA t
        -- a selection between equal branches reduces to the branch
        getOutPropsA (APrim _ _ PrimIf [_, t, e])
            | t == e = getOutPropsA t
        -- a 1-bit AND/OR reduces over its constant operands, as the
        -- netlist optimization will: identity operands are dropped, an
        -- annihilating operand makes the result constant, and a single
        -- remaining operand passes its properties through
        getOutPropsA (APrim _ (ATBit 1) p es)
            | (p == PrimBAnd) || (p == PrimAnd) = boolOpPropsA 0 es
            | (p == PrimBOr)  || (p == PrimOr)  = boolOpPropsA 1 es
        -- any other primitive of all-constant arguments is constant
        -- (the netlist optimization will fold it to a constant)
        getOutPropsA (APrim _ _ _ es)
            | not (null es),
              all (\ e -> VPconst `elem` getOutPropsA e) es = [VPconst]
        -- either a special output of a state instance
        -- or an input of this module
        getOutPropsA (ASPort _ i) = M.findWithDefault [] i wireMapA_out
        -- follow defs (memoized)
        getOutPropsA (ASDef _ i) =
            M.findWithDefault [] i outDefPropsMemo
        -- constant values
        getOutPropsA (ASParam _ _) = [VPconst]
        getOutPropsA (ASInt _ _ _) = [VPconst]
        getOutPropsA (ASStr _ _ _) = [VPconst]
        -- look through the methods of inlined wire and CReg instances
        getOutPropsA (AMethCall _ obj meth _)
            | isWireGet obj meth = wireGetProps obj
            | isWireHas obj meth = wireHasProps obj
            | Just (n, True) <- cregMeth obj meth = cregReadProps obj n
        getOutPropsA (AMethValue _ obj meth)
            | isWireGet obj meth = wireGetProps obj
            | isWireHas obj meth = wireHasProps obj
            | Just (n, True) <- cregMeth obj meth = cregReadProps obj n
        -- a value method result is wired to the method's output port
        getOutPropsA (AMethCall _ obj meth _) = methOutPropsA obj meth
        getOutPropsA (AMethValue _ obj meth)  = methOutPropsA obj meth
        -- the gate of an output clock of a state instance
        getOutPropsA (AMGate _ obj clk) = gatePropsA obj clk
        -- clock, reset, and inout values just wrap the underlying wires
        getOutPropsA (ASClock _ (AClock { aclock_osc = o })) = getOutPropsA o
        getOutPropsA (ASReset _ (AReset { areset_wire = w })) = getOutPropsA w
        getOutPropsA (ASInout _ (AInout { ainout_wire = w })) = getOutPropsA w
        -- for any other use, we cannot conclude properties
        getOutPropsA _ = []

        -- reduce a 1-bit AND (annihilator 0) or OR (annihilator 1)
        -- over its constant operands
        boolOpPropsA :: Integer -> [AExpr] -> [VeriPortProp]
        boolOpPropsA annihilator es =
            let vs = [ (evalConstA e, e) | e <- es ]
            in  if (any ((== (Just annihilator)) . fst) vs)
                then [VPconst]
                else case [ e | (Nothing, e) <- vs ] of
                       []  -> [VPconst]   -- all operands are constant
                       [e] -> getOutPropsA e
                       _   -> []

        -- properties of defs, memoized (the map's values are lazy)
        outDefPropsMemo :: M.Map AId [VeriPortProp]
        outDefPropsMemo = M.map (getOutPropsA . adef_expr) defMapA

        -- the declared properties of a method's output port
        methOutPropsA :: AId -> AId -> [VeriPortProp]
        methOutPropsA obj meth =
            case findMethodA obj meth of
              Just (Method { vf_output = Just (_, ps) }) -> ps
              _ -> []

        -- the declared properties of the gate port of an instance's
        -- output clock (mirrors getSpecialOutputs' mkGatePort)
        gatePropsA :: AId -> AId -> [VeriPortProp]
        gatePropsA obj clk =
            case M.lookup obj vmiMap of
              Just vmi ->
                  case lookup clk (output_clocks (vClk vmi)) of
                    Just (Just (_, Just (_, ps))) -> VPclockgate : ps
                    _ -> [VPclockgate]
              Nothing -> [VPclockgate]

        -- ----------
        -- deduce the properties of an input from its uses
        -- (the analog of getSignalInProp in getIOProps)

        -- how many places each state-instance method is called from;
        -- if a method is called from more places than it has port
        -- copies, AState will insert muxes, and the connections to its
        -- input ports will not be direct
        methCallCountA :: M.Map (AId, AId) Integer
        methCallCountA = M.fromListWith (+) [ (om, 1) | om <- all_calls ]

        all_calls :: [(AId, AId)]
        all_calls =
            concatMap exprCalls all_exprs ++
            [ (aact_objid a, unQualId (acall_methid a)) |
                  r <- rs, isLiveRule r, a@(ACall {}) <- arule_actions r ]

        -- all expressions in the package (for counting method calls;
        -- rules which can never fire are dropped and count nothing)
        all_exprs :: [AExpr]
        all_exprs =
            [ e | (ADef _ _ e _) <- ds ] ++
            [ adef_expr d | f <- ifc, d <- ifcValueDef f ] ++
            [ e | (_, e) <- out_wire_defs ] ++
            ifc_preds ++
            [ e | a <- all_assumps,
                  e <- assump_property a :
                       concatMap aact_args (assump_actions a) ] ++
            concat [ arule_pred r :
                     concatMap aact_args (arule_actions r) |
                         r <- rs, isLiveRule r ] ++
            concat [ avi_iargs v | v <- vs ]

        ifc_preds :: [AExpr]
        ifc_preds = concatMap getPred ifc
          where getPred (AIDef { aif_pred = p }) = [p]
                getPred (AIAction { aif_pred = p }) = [p]
                getPred (AIActionValue { aif_pred = p }) = [p]
                getPred _ = []

        all_assumps :: [AAssumption]
        all_assumps = concat ([ arule_assumps r | r <- rs ] ++
                              [ aif_assumps f | f@(AIDef {}) <- ifc ])

        exprCalls :: AExpr -> [(AId, AId)]
        exprCalls (AMethCall _ obj meth es) =
            (obj, unQualId meth) : concatMap exprCalls es
        exprCalls (APrim _ _ _ es) = concatMap exprCalls es
        exprCalls (ANoInlineFunCall _ _ _ es) = concatMap exprCalls es
        exprCalls (AFunCall _ _ _ _ es) = concatMap exprCalls es
        exprCalls (ASClock _ (AClock { aclock_osc = o, aclock_gate = g })) =
            exprCalls o ++ exprCalls g
        exprCalls (ASReset _ (AReset { areset_wire = w })) = exprCalls w
        exprCalls (ASInout _ (AInout { ainout_wire = w })) = exprCalls w
        exprCalls (ASAny _ (Just e)) = exprCalls e
        exprCalls _ = []

        -- all the uses of signals in the package, classified
        useMapA :: M.Map AId [AUse]
        useMapA = M.fromListWith (++) [ (i, [u]) | (i, u) <- all_uses ]

        all_uses :: [(AId, AUse)]
        all_uses =
            -- local defs
            concat [ classifyExpr (AUDef i) e | (ADef i _ e _) <- ds ] ++
            -- interface value defs and output clock/reset/inout wires
            -- (these define the output ports, which are recorded in
            -- outSinkSet, so the deduction terminates there)
            concat [ classifyExpr (AUDef (adef_objid d)) (adef_expr d) |
                         f <- ifc, d <- ifcValueDef f ] ++
            concat [ classifyExpr (AUDef i) e | (i, e) <- out_wire_defs ] ++
            -- method predicates and assumptions become scheduling logic
            concat [ classifyExpr AUOpaque p | p <- ifc_preds ] ++
            concat [ classifyExpr AUOpaque (assump_property a) |
                         a <- all_assumps ] ++
            -- assumption actions are foreign (error-reporting) calls
            concat [ classifyForeignExpr e |
                         a <- all_assumps,
                         e <- concatMap aact_args (assump_actions a) ] ++
            -- rules (including the bodies of action methods)
            concat [ ruleUses r | r <- rs ] ++
            -- state instance arguments
            concat [ instArgUses v | v <- vs ]

        ruleUses :: ARule -> [(AId, AUse)]
        ruleUses r =
            let wf = mkIdWillFire (arule_id r)
            in  -- if the schedule says this rule never fires, then all
                -- of its logic is dropped, so it contributes no uses
                if (not (isLiveRule r))
                then []
                else
                -- the predicate feeds the scheduling logic of this
                -- rule, which is hardware only as far as the rule's
                -- WILL_FIRE is used
                classifyExpr (AUVia wf) (arule_pred r) ++
                concatMap (actionUses (arule_id r)) (arule_actions r) ++
                ruleWFUses wf r

        -- The WILL_FIRE of a rule is used by the hardware which the
        -- rule's actions create: the enables and argument muxes of
        -- calls to state instance methods, the data/validity wires of
        -- sets of inlined wires, and the selectors of argument muxes
        -- for value methods called in any of the rule's expressions.
        -- Foreign calls exist only in simulation and contribute no
        -- hardware use.  (References to WILL_FIREs from the scheduling
        -- logic of conflicting rules are already visible in the defs
        -- and need no special handling here.)
        ruleWFUses :: AId -> ARule -> [(AId, AUse)]
        ruleWFUses wf r =
            [ (wf, u) | a <- arule_actions r,
                        u <- actionWFUses (arule_id r) a ] ++
            [ (wf, AUOpaque) |
                  any hasMuxableCall
                      (arule_pred r :
                       concatMap aact_args (arule_actions r)) ]

        actionWFUses :: AId -> AAction -> [AUse]
        actionWFUses rid (ACall obj meth (c:_))
            | isWireSet obj meth = wireFlowUses obj
            | Just _ <- cregMeth obj meth = [AUOpaque]
            -- a call whose arm the arbitration drops uses nothing
            | Just ArmDropped <- armClass obj meth rid = []
            -- an unconditional call with its own surviving connection
            -- wires the WILL_FIRE directly to the method's enable port
            | Just (Method { vf_enable = Just (_, pps) })
                  <- findMethodA obj meth,
              isEnDirect,
              evalConstA c == Just 1
              = [AUConn pps]
          where isEnDirect =
                    case armClass obj meth rid of
                      Just ArmDirect -> True
                      Just _ -> False
                      Nothing ->
                          case findMethodA obj meth of
                            Just m -> isDirectCallA obj meth m
                            Nothing -> False
        actionWFUses _ (ACall {}) = [AUOpaque]
        actionWFUses _ _ = []   -- foreign calls (AFCall, ATaskAction)

        -- whether an expression contains a call to a state instance
        -- method with arguments (whose muxes select on the WILL_FIRE)
        hasMuxableCall :: AExpr -> Bool
        hasMuxableCall e =
            or [ not (null (vf_inputs m)) |
                     (obj, meth) <- exprCalls e,
                     not (obj `S.member` wireInstSet),
                     Just m@(Method {}) <- [findMethodA obj meth] ]

        actionUses :: AId -> AAction -> [(AId, AUse)]
        -- the condition feeds the enable logic (via the WILL_FIRE),
        -- and so is not a direct connection; the arguments are
        -- connections to the method's input ports
        actionUses rid (ACall obj meth (c:es))
            -- setting an inlined wire flows into the wire's data node:
            -- directly for a single setter, through a mux otherwise;
            -- the condition feeds the validity and the mux select
            | isWireSet obj meth =
                let wire_use =
                        if (wireSetCount obj <= 1)
                        then AUDef (wireDataId obj)
                        else AUVia (wireDataId obj)
                in  concat [ classifyExpr u c | u <- wireFlowUses obj ] ++
                    concatMap (classifyExpr wire_use) es
            -- a CReg write feeds the retained register through the
            -- bypass selection chain: a use, but never a direct
            -- connection to a port
            | Just _ <- cregMeth obj meth =
                concatMap (classifyExpr AUOpaque) (c:es)
            -- otherwise, classify by the arm's fate in the arbitration
            -- when the schedule info is available
            | otherwise =
                case armClass obj meth rid of
                  -- the arm is dropped: its logic uses nothing
                  Just ArmDropped -> []
                  Just ArmDirect ->
                      classifyExpr AUOpaque c ++
                      directMethArgs obj meth es
                  Just ArmMuxed ->
                      classifyExpr AUOpaque c ++
                      concatMap (classifyExpr AUOpaque) es
                  Nothing ->
                      classifyExpr AUOpaque c ++
                      classifyMethArgs obj meth es
        -- foreign function and task calls (AFCall, ATaskAction) exist
        -- only in simulation, so their arguments (and conditions) are
        -- not uses in the hardware
        actionUses _ a = concatMap classifyForeignExpr (aact_args a)

        -- Classify the uses of signals in an argument of a foreign
        -- function or task call.  Such an argument is not part of the
        -- hardware (it only feeds a system task or imported function
        -- in simulation), so signals in it are not "used" -- matching
        -- getIOProps, which does not follow foreign calls when looking
        -- for uses.  However, a method call appearing inside such an
        -- argument does wire up the method's input ports in the
        -- hardware, so its arguments are still classified.
        classifyForeignExpr :: AExpr -> [(AId, AUse)]
        classifyForeignExpr (APrim _ _ _ es) =
            concatMap classifyForeignExpr es
        classifyForeignExpr (ANoInlineFunCall _ _ _ es) =
            concatMap classifyForeignExpr es
        classifyForeignExpr (AFunCall _ _ _ _ es) =
            concatMap classifyForeignExpr es
        classifyForeignExpr (AMethCall _ obj meth es)
            | isWireGet obj meth || isWireHas obj meth = []
            | Just _ <- cregMeth obj meth = []
            | otherwise = classifyMethArgs obj meth es
        classifyForeignExpr (ASClock _ (AClock { aclock_osc = o,
                                                 aclock_gate = g })) =
            classifyForeignExpr o ++ classifyForeignExpr g
        classifyForeignExpr (ASReset _ (AReset { areset_wire = w })) =
            classifyForeignExpr w
        classifyForeignExpr (ASInout _ (AInout { ainout_wire = w })) =
            classifyForeignExpr w
        classifyForeignExpr (ASAny _ (Just e)) = classifyForeignExpr e
        classifyForeignExpr _ = []

        instArgUses :: AVInst -> [(AId, AUse)]
        instArgUses v = concatMap cvt (getInstArgs v)
          where
            vmi = avi_vmi v
            cvt (Port (_, pps) _ _, e) = classifyExpr (AUConn pps) e
            -- parameters must be constant expressions
            cvt (Param {}, e) = classifyExpr (AUConn [VPconst]) e
            -- clock/reset/inout wires connect to the real ports
            -- (mirrors AState's rewireClockResetInout)
            cvt (ClockArg c, ASClock _ (AClock { aclock_osc = osc,
                                                 aclock_gate = gate })) =
                case (lookupInputClockWires c vmi) of
                  -- unconnected clock: AState drops the wires
                  Nothing -> []
                  Just (_, Nothing) -> classifyExpr (AUConn [VPclock]) osc
                  Just (_, Just _)  ->
                      classifyExpr (AUConn [VPclock]) osc ++
                      classifyExpr (AUConn [VPclockgate]) gate
            cvt (ResetArg r, ASReset _ (AReset { areset_wire = w })) =
                case (lookupInputResetWire r vmi) of
                  Nothing -> []
                  Just _  -> classifyExpr (AUConn [VPreset]) w
            cvt (InoutArg {}, ASInout _ (AInout { ainout_wire = w })) =
                classifyExpr (AUConn [VPinout]) w
            cvt (_, e) = classifyExpr AUOpaque e

        -- Classify the uses of signals in an expression: signals which
        -- pass through directly (possibly via concat and extract, as in
        -- okUse) receive the given use; anything else is used by the
        -- surrounding logic, which lives or dies with the destination
        -- of the given use (see opaqueOf).  Arguments of method calls
        -- are connections to the method's input ports and are
        -- classified separately.
        classifyExpr :: AUse -> AExpr -> [(AId, AUse)]
        classifyExpr u (ASPort _ i)  = [(i, u)]
        classifyExpr u (ASParam _ i) = [(i, u)]
        classifyExpr u (ASDef _ i)   = [(i, u)]
        classifyExpr u (APrim _ _ PrimConcat es) =
            concatMap (classifyExpr u) es
        classifyExpr u (APrim _ _ PrimExtract (e:es)) =
            classifyExpr u e ++ concatMap (classifyExpr (opaqueOf u)) es
        classifyExpr u (APrim _ _ _ es) =
            concatMap (classifyExpr (opaqueOf u)) es
        classifyExpr u (ANoInlineFunCall _ _ _ es) =
            concatMap (classifyExpr (opaqueOf u)) es
        classifyExpr u (AFunCall _ _ _ _ es) =
            concatMap (classifyExpr (opaqueOf u)) es
        -- reading an inlined wire is a reference to its data node,
        -- and its validity is a reference to its "whas" node;
        -- reading a CReg uses no signals (the register remains)
        classifyExpr u (AMethCall _ obj meth es)
            | isWireGet obj meth = [(wireDataId obj, u)]
            | isWireHas obj meth = [(wireHasId obj, u)]
            | Just _ <- cregMeth obj meth = []
            | otherwise = classifyMethArgs obj meth es
        classifyExpr u (ASClock _ (AClock { aclock_osc = o,
                                            aclock_gate = g })) =
            classifyExpr (opaqueOf u) o ++ classifyExpr (opaqueOf u) g
        classifyExpr u (ASReset _ (AReset { areset_wire = w })) =
            classifyExpr (opaqueOf u) w
        classifyExpr u (ASInout _ (AInout { ainout_wire = w })) =
            classifyExpr (opaqueOf u) w
        classifyExpr u (ASAny _ (Just e)) = classifyExpr (opaqueOf u) e
        -- AMethValue, AMGate, ATaskValue, and literals use no signals
        classifyExpr _ _ = []

        -- The use for a signal consumed by logic (rather than passing
        -- through directly): no properties flow, but the logic itself
        -- lives or dies with the destination -- logic in a definition
        -- is dropped if the definition is unused, and logic in a
        -- signal reached through a mux is dropped if that signal is
        -- unused.  Connections to ports, and uses we know nothing
        -- about, are simply opaque.
        opaqueOf :: AUse -> AUse
        opaqueOf (AUDef d) = AUVia d
        opaqueOf (AUVia d) = AUVia d
        opaqueOf _         = AUOpaque

        -- Arguments of a call to a method of a state instance are
        -- connections to the method's input ports, as long as AState
        -- will not need to insert muxes (which is the case when the
        -- method has enough port copies for all of its call sites)
        classifyMethArgs :: AId -> AId -> [AExpr] -> [(AId, AUse)]
        classifyMethArgs obj meth es =
            case findMethodA obj meth of
              Just m | isDirectCallA obj meth m -> directMethArgs obj meth es
              _ -> concatMap (classifyExpr AUOpaque) es

        -- classify arguments as direct connections to the method's
        -- input ports
        directMethArgs :: AId -> AId -> [AExpr] -> [(AId, AUse)]
        directMethArgs obj meth es =
            case findMethodA obj meth of
              Just (Method { vf_inputs = ins })
                  | length ins == length es
                  -> concat (zipWith (\ (_, pps) e ->
                                          classifyExpr (AUConn pps) e)
                                     ins es)
              _ -> concatMap (classifyExpr AUOpaque) es

        -- whether the method has enough port copies for all of its
        -- (live) call sites, so that AState will not insert muxes
        isDirectCallA :: AId -> AId -> VFieldInfo -> Bool
        isDirectCallA obj meth m =
            M.findWithDefault 0 (obj, unQualId meth) methCallCountA
                <= max 1 (vf_mult m)

        -- ----------
        -- When the schedule info is available, model the muxes that
        -- AState will create for the arguments of calls to state
        -- instance methods, using the same port allocation
        -- (ratToBlobs), the same exclusivity test (which decides
        -- between a parallel and a priority mux), and the same
        -- priority (earliness) order.  Each call site (arm of the
        -- mux) is classified by what the netlist optimization will
        -- leave of it once the constant selectors are folded: a
        -- direct connection, an input of a surviving mux, or dropped
        -- entirely (so that, for example, the argument of a method
        -- call which always loses the arbitration to a more urgent
        -- always-firing caller is unused).

        armClassMap :: M.Map (AId, AId, AId) ArmClass
        armClassMap =
            case mschedinfo of
              Nothing -> M.empty
              Just si -> mkArmClassMap si

        -- the classification for a call to a method of a state
        -- instance from a given rule (Nothing when no schedule info
        -- is available or the call is not in the allocation)
        armClass :: AId -> AId -> AId -> Maybe ArmClass
        armClass obj meth rid =
            M.lookup (obj, unQualId meth, rid) armClassMap

        mkArmClassMap :: AScheduleInfo -> M.Map (AId, AId, AId) ArmClass
        mkArmClassMap si =
            let multMap = M.fromList (concatMap genMethodMult vs)
                (_, action_blobs) =
                    ratToBlobs (asi_method_uses_map si) multMap
                               (asi_resource_alloc_table si)
                edb = asi_exclusive_rules_db si
                (ASchedule _ rev_exec_order) = asi_schedule si
                omPos :: M.Map AId Integer
                omPos = M.fromList (zip rev_exec_order [0..])
            in  M.fromList (concatMap (blobArms edb omPos) action_blobs)

        blobArms :: ExclusiveRulesDB -> M.Map AId Integer -> MethBlob
                 -> [((AId, AId, AId), ArmClass)]
        blobArms edb omPos (((obj, meth), _), port_blobs) =
            let meth' = unQualId meth
                key r = (obj, meth', r)

                -- the selector value of an arm:
                -- the caller's WILL_FIRE AND the call's condition
                selVal :: AExpr -> AId -> Maybe Integer
                selVal (AMethCall _ _ _ (c:_)) r =
                    case (evalDefA (mkIdWillFire r), evalConstA c) of
                      (Just 0, _) -> Just 0
                      (_, Just 0) -> Just 0
                      (Just _, Just _) -> Just 1
                      _ -> Nothing
                selVal _ _ = Nothing

                portArms :: [(AExpr, Maybe [AId])]
                         -> [((AId, AId, AId), ArmClass)]
                -- a single use is a direct connection (see mkEmux)
                portArms [(_, mrs)] =
                    [ (key r, ArmDirect) | Just rs <- [mrs], r <- rs ]
                portArms uses =
                    let arm_rules = concat [ rs | (_, Just rs) <- uses ]
                        usePri = not (and [ areRulesExclusive edb r r' |
                                                r <- arm_rules,
                                                r' <- arm_rules,
                                                r /= r' ])
                        -- arms split per rule, in priority order,
                        -- as in mkEmux's "order"
                        arms = [ (M.findWithDefault 0 r omPos,
                                  r, selVal e r) |
                                     (e, Just rs) <- uses, r <- rs ]
                        arms' = sortBy (\ (x,_,_) (y,_,_) -> compare x y)
                                    arms
                    in  if usePri
                        then priWalk False arms'
                        else parMux arms'

                -- a priority mux folds from the front: constant-0
                -- arms drop out; a constant-1 arm with no unknown arm
                -- before it wins, and all later arms are dropped
                priWalk _ [] = []
                priWalk sawUnknown ((_, r, v) : rest) =
                    case v of
                      Just 0 -> (key r, ArmDropped) :
                                priWalk sawUnknown rest
                      Just _ | not sawUnknown ->
                          (key r, ArmDirect) : dropAll rest
                      Just _ -> (key r, ArmMuxed) : dropAll rest
                      Nothing -> (key r, ArmMuxed) : priWalk True rest

                dropAll rest = [ (key r, ArmDropped) | (_, r, _) <- rest ]

                -- a parallel mux (exclusive arms): constant-0 arms
                -- drop out; a single remaining arm is direct
                parMux arms =
                    let isZero (_, _, v) = (v == Just 0)
                        (zs, rest) = partition isZero arms
                        dropped = [ (key r, ArmDropped) |
                                        (_, r, _) <- zs ]
                    in  dropped ++
                        case rest of
                          [(_, r, _)] -> [(key r, ArmDirect)]
                          _ -> [ (key r, ArmMuxed) | (_, r, _) <- rest ]
            in  concatMap portArms port_blobs

        -- ids which become output or inout ports: a signal which
        -- drives a port is not unused, but no properties can be
        -- concluded from that use (this mirrors the "output_pairs"
        -- entries in getIOProps' wireMap_in)
        outSinkSet :: S.Set AId
        outSinkSet =
            S.fromList ([ adef_objid d | f <- ifc, d <- ifcValueDef f ] ++
                        [ i | (i, _) <- out_wire_defs ])

        getInPropsA :: AId -> [VeriPortProp]
        getInPropsA i = M.findWithDefault (computeInPropsA i) i inPropsMemo

        -- deduction of input properties, memoized over the ids with
        -- recorded uses (the map's values are lazy)
        inPropsMemo :: M.Map AId [VeriPortProp]
        inPropsMemo = M.mapWithKey (\ i _ -> computeInPropsA i) useMapA

        computeInPropsA :: AId -> [VeriPortProp]
        computeInPropsA i =
            let sink_props = if (i `S.member` outSinkSet) then [[]] else []
                uses = M.findWithDefault [] i useMapA
            in  case (sink_props, uses) of
                  ([], []) -> [VPunused]
                  _ -> joinInProps (sink_props ++ map usePropsA uses)

        usePropsA :: AUse -> [VeriPortProp]
        usePropsA (AUConn ps) = ps
        usePropsA AUOpaque    = []
        usePropsA (AUDef d)   = getInPropsA d
        usePropsA (AUVia d)   =
            -- no properties flow through the selection logic, but if
            -- the destination is unused, this use doesn't count either
            if (VPunused `elem` getInPropsA d) then [VPunused] else []


-- A use of a signal, for deducing the properties of module inputs
-- on an APackage (see getInPropsA above)
data AUse = AUDef AId               -- used to define another signal
          | AUVia AId               -- flows into another signal through
                                    -- selection (mux) logic
          | AUConn [VeriPortProp]   -- connected to a port with these props
          | AUOpaque                -- used in a way we cannot analyze

-- The fate of one call site (arm) in the argument muxes that AState
-- creates for a method of a state instance, once the netlist
-- optimization folds the constant selectors (see armClassMap above)
data ArmClass = ArmDirect    -- a direct connection to the port
              | ArmMuxed     -- an input of a surviving mux
              | ArmDropped   -- dropped by the folding
