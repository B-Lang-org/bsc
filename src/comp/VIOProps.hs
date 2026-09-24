module VIOProps (VIOProps, getIOProps, getIOPropsA) where

import Data.List(intersect, nub, tails, sortBy)
import Data.Maybe(catMaybes, isNothing, fromMaybe, isJust)
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
                mkNamedEnable, mkNamedOutputs, mkNamedInout, vName_to_id)
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
-- getIOPropsA: derive the port properties of the generated module
-- from the APackage (prior to AState) and the schedule.
--
-- Unlike getIOProps, which measures the optimized netlist, this
-- function computes the properties from a definition of what each
-- property MEANS for the hardware described by the design and its
-- schedule.  A property is asserted only when it is entailed by
-- structure, dataflow, and the schedule -- never by which
-- optimizations the backend performs, or by where module boundaries
-- fall among the wiring primitives.  The intent is that the answers
-- are stable: recompiling the same design with different optimization
-- or inlining settings, or with a different backend, yields the same
-- port properties.
--
-- The definitions:
--
--  * "clock", "clock gate", "reset", "inout" (and declared properties
--    such as "inhigh" and "outhigh") are the structural role of the
--    port in the module's interface, from the wire info and field
--    info.  They are facts of the interface, not deductions, so they
--    are always present (even on a port which is also unused).
--
--  * "reg": the port's value is the registered output of a state
--    element, reached through wiring only -- concatenation,
--    extraction, definitions, and the wiring primitives (a wire or
--    CReg is connected to the same things whether or not
--    InlineWires/InlineCReg will inline it away, so the look-through
--    does not depend on the inlining flags).
--
--  * "const": the port's value is entailed to be constant by the
--    design and its schedule.  Source-level constants are folded by
--    the evaluator during elaboration; what this pass adds is the
--    folding of SCHEDULE-time facts, which do not exist until after
--    scheduling: WILL_FIREs which the schedule makes constant (rules
--    which can never fire, or always fire), the validity of wires
--    which are never or always set, selections whose conditions
--    become constant, and mux arms which win or lose the arbitration
--    outright (modeled, when the AScheduleInfo is supplied, with the
--    same port allocation, exclusivity test, and earliness order
--    that AState uses).
--
--  * "unused": the port drives no hardware.  Uses which exist only
--    in simulation (arguments of foreign function and task calls) do
--    not count, and a use by logic which is itself unused, or by a
--    rule which can never fire, or by a mux arm which loses the
--    arbitration, does not count either.  The references which
--    AState itself creates for a caller's WILL_FIRE (a method port's
--    enable, the selectors of its argument muxes) are modeled and
--    folded the same way: an enable absorbed by a constant or
--    complementary conjunct, the selector of a direct connection, of
--    a losing arm, or of a mux's last arm (absorbed into its
--    don't-care default) reference nothing.
--
-- The deduction is conservative: it may fail to assert a property
-- whose truth requires reasoning this pass does not do (known cases:
-- boolean minimization of guards over dynamic values, e.g.
-- (a && b) || (!a && b) == b; value analysis of register contents;
-- and the tracing of inout nets through InoutConnect instances).
-- It never asserts a property which does not hold of the hardware.
--
-- Relation to getIOProps: on default flags the two agree almost
-- everywhere, but they can differ in both directions, because
-- getIOProps reports whatever the optimized netlist happens to show:
-- it loses the structural labels on ports whose connectivity was
-- optimized away (an unused input clock is just "unused" there), it
-- misses "unused" through non-direct connections, it weakens when
-- wiring primitives are not inlined, and it can additionally report
-- properties which are true only because of a particular optimizer
-- rewrite (e.g. a "const" established by common-subexpression
-- elimination), which this pass deliberately does not promise.
--
-- The ports themselves are not explicit in an APackage; they are
-- constructed by AState from the module arguments (apkg_inputs /
-- apkg_external_wires) and the interface (apkg_interface).  This
-- function mirrors that construction (see AState.aState') to
-- enumerate the same ports, with the same names, in the same order.

getIOPropsA :: Flags -> [PProp] -> Maybe AScheduleInfo -> APackage ->
               (VIOProps, [VPort])
getIOPropsA _flags pps mschedinfo apkg =
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
            isRdyId (aif_name m) && isAlwaysRdy pps (aif_name m)
        other_ifc = filter (not . isAlwaysReadyMethod) ifc

        meth_outs :: [(AId, AType, [VeriPortProp], AExpr)]
        meth_outs = concatMap getMethOut other_ifc

        getMethOut :: AIFace -> [(AId, AType, [VeriPortProp], AExpr)]
        getMethOut ai@(AIDef {}) =
            -- a module wrapped around a non-inlined function has no RDY
            if (fmod && isRdyId (aif_name ai))
            then []
            else methOutPorts (aif_fieldinfo ai) (aif_value ai)
        getMethOut ai@(AIActionValue {}) =
            methOutPorts (aif_fieldinfo ai) (aif_value ai)
        getMethOut _ = []

        -- one entry per output port of the method's return value
        -- (mirrors AState's outputADefToADefs: a split method's value
        -- is a tuple whose elements pair with the declared ports)
        methOutPorts :: VFieldInfo -> ADef -> [(AId, AType, [VeriPortProp], AExpr)]
        methOutPorts fi (ADef { adef_type = ATTuple ts, adef_expr = ATuple _ es }) =
            zipWith3 (\ (i, pps) t e -> (i, t, pps, e))
                     (zip (mkNamedOutputs fi) (declaredOutProps fi)) ts es
        methOutPorts fi (ADef { adef_type = ATBit 0 })
            | null (mkNamedOutputs fi) = []
        methOutPorts fi (ADef { adef_type = t, adef_expr = e })
            | ([i], [pps]) <- (mkNamedOutputs fi, declaredOutProps fi)
            = [(i, t, pps, e)]
        methOutPorts fi d =
            internalError ("getIOPropsA.methOutPorts: " ++
                           ppReadable (vf_name fi, d))

        -- the declared properties of each output port
        declaredOutProps :: VFieldInfo -> [[VeriPortProp]]
        declaredOutProps (Method { vf_outputs = outs }) = map snd outs
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
                -- vf_inputs groups the ports of each source argument;
                -- aIfaceArgs is the flattened per-port list, so
                -- flatten the property groups to pair with it
                argPortProps (Method { vf_inputs = ins }) =
                    map snd (concat ins)
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
        -- wire instances (RWire, RWire0, BypassWire) are looked
        -- through: a value flows from the "wset" argument to the
        -- "wget" result as through a plain wire (or through a mux, if
        -- there is more than one setter).  This holds whether or not
        -- InlineWires will inline the instance away (the primitive's
        -- Verilog is just an assignment), so the deduced properties do
        -- not depend on the inlining flags.

        isWireInstance :: AVInst -> Bool
        isWireInstance v =
            isRWire v || isRWire0 v ||
            isBypassWire v || isBypassWire0 v

        wireInstSet :: S.Set AId
        wireInstSet = S.fromList [ avi_vname v | v <- vs, isWireInstance v ]

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

        -- The control flow into a wire instance from one setter (the
        -- setter's WILL_FIRE and condition): it always feeds the
        -- wire's validity node, but it feeds the selection of the
        -- wire's data node only when the setter's arm survives in a
        -- data mux -- with a single setter (or one whose arm wins the
        -- arbitration, or several setters sharing one expression) the
        -- data is a direct alias of the argument, and its selection
        -- references nothing.  Both nodes' uses are AUVia: alive only
        -- as far as the node itself is used.
        wireFlowUses :: AId -> AId -> AId -> [AUse]
        wireFlowUses obj meth rid =
            AUVia (wireHasId obj) :
            if (isJust (wireDataExpr obj))
            then []   -- the data is an alias whatever the selectors do
            else case armClass obj meth rid of
                   Just ArmDirect  -> []
                   Just ArmDropped -> []
                   Just ArmMuxed | selDropped obj meth rid -> []
                   _ -> [AUVia (wireDataId obj)]

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

        -- The data expression carried by a wire, when it is uniquely
        -- determined: a single live setter, or several live setters
        -- which all set the same expression (compared through def and
        -- wire references) -- AState's muxing collapses in that case
        -- too, since equal-expression uses share one mux arm.
        wireDataExpr :: AId -> Maybe AExpr
        wireDataExpr inst =
            case [ map derefA es | (_, _, es) <- liveWireSetters inst ] of
              ([e]:rest) | all (== [e]) rest -> Just e
              _ -> Nothing

        -- the properties of a wire's "wget" value
        wireGetProps :: AId -> [VeriPortProp]
        wireGetProps inst =
            case (liveWireSetters inst) of
              -- never set: inlining defines the value as a constant
              []  -> [VPconst]
              -- a unique data expression flows through;
              -- otherwise the value comes from a mux
              _   -> case (wireDataExpr inst) of
                       Just e  -> getOutPropsA e
                       Nothing -> []

        -- the properties of a wire's "whas" value
        wireHasProps :: AId -> [VeriPortProp]
        wireHasProps inst =
            case (wireHasVal inst) of
              Just _  -> [VPconst]
              Nothing -> []

        -- the constant value of a wire's "whas", when the schedule
        -- determines it: the OR over the setters of (WILL_FIRE AND
        -- condition); complementary WILL_FIREs of unconditional
        -- setters (e.g. rules split over a condition) make it 1
        wireHasVal :: AId -> Maybe Integer
        wireHasVal inst =
            let setters = M.findWithDefault [] inst wireSetters
                conj :: (AId, AExpr, [AExpr]) -> Maybe Integer
                conj (wf, c, _) =
                    case (evalDefA wf, evalConstA c) of
                      (Just 0, _) -> Just 0
                      (_, Just 0) -> Just 0
                      (Just _, Just _) -> Just 1
                      _ -> Nothing
                vals = map conj setters
                -- the WILL_FIREs of the unconditional setters
                uncond_wfs = [ ASDef aTBool wf |
                                   (wf, c, _) <- setters,
                                   evalConstA c == Just 1 ]
            in  if (null vals) then Just 0
                else if (any (== (Just 1)) vals) then Just 1
                else if (all (== (Just 0)) vals) then Just 0
                else if (anyComplementaryA uncond_wfs) then Just 1
                else Nothing

        -- the constant value of a wire's "wget", when it can be known
        wireGetVal :: AId -> Maybe Integer
        wireGetVal inst =
            case (liveWireSetters inst) of
              -- never set: the value is tied to constant 0
              []  -> Just 0
              -- a unique data expression is connected without gating
              _   -> case (wireDataExpr inst) of
                       Just e  -> evalConstA e
                       Nothing -> Nothing

        -- ----------
        -- CReg instances are looked through: port 0's read is the
        -- register output, and port N's read bypasses through
        -- selection between the port (N-1) write data and port
        -- (N-1)'s read.  Writes always feed the register, so write
        -- arguments are uses without properties.  As with the wire
        -- instances, this is the primitive's connectivity whether or
        -- not InlineCReg will inline it, so the deduced properties do
        -- not depend on the inlining flags.

        cregInstSet :: S.Set AId
        cregInstSet = S.fromList [ avi_vname v | v <- vs, isCRegInst v ]

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

        -- the data expression written to a CReg port, when it is
        -- uniquely determined (as wireDataExpr)
        cregWriteExpr :: AId -> Int -> Maybe AExpr
        cregWriteExpr inst n =
            case [ derefA e | (_, _, e) <- liveCregWriters inst n ] of
              (e:es) | all (== e) es -> Just e
              _ -> Nothing

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
              -- the bypass is always taken: a unique write expression
              -- flows through
              Just _ ->
                  case (cregWriteExpr inst (n-1)) of
                    Just e  -> getOutPropsA e
                    Nothing -> []
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
                  case (cregWriteExpr inst (n-1)) of
                    Just e  -> evalConstA e
                    Nothing -> Nothing
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

        -- Follow def references to the defining expression -- and
        -- follow reads of wires (and folded CReg bypasses) with a
        -- single live setter to the setter's data expression, since
        -- the wire carries exactly that expression (a wire is
        -- transparent to this reasoning just as it is to the property
        -- flow); this lets the structural reductions below (equal
        -- branches, complementary operands) see through wires, where
        -- the netlist optimization would see the substituted
        -- expressions after inlining.
        derefA :: AExpr -> AExpr
        derefA e@(ASDef _ i) =
            maybe e (derefA . adef_expr) (M.lookup i defMapA)
        derefA e@(AMethCall _ obj meth _)
            | isWireGet obj meth = fromMaybe e (wireDataExpr obj)
            | Just (n, True) <- cregMeth obj meth = derefCregRead obj n e
        -- a selection whose condition is constant is its taken branch
        derefA (APrim _ _ PrimIf [c, t, e])
            | Just v <- evalConstA c = derefA (if v == 0 then e else t)
        -- a 1-bit AND/OR whose identity operands drop away, leaving a
        -- single operand, is that operand
        derefA e@(APrim _ (ATBit 1) p es)
            | (p == PrimBAnd) || (p == PrimAnd) = derefBoolOpA 0 e es
            | (p == PrimBOr)  || (p == PrimOr)  = derefBoolOpA 1 e es
        derefA e = e

        derefBoolOpA :: Integer -> AExpr -> [AExpr] -> AExpr
        derefBoolOpA annihilator orig es =
            let vs = [ (evalConstA e, e) | e <- es ]
            in  -- with an annihilating operand the expression is
                -- constant, which evalConstA handles; otherwise drop
                -- the identity operands and look for a lone survivor
                if (any ((== (Just annihilator)) . fst) vs)
                then orig
                else case [ e | (Nothing, e) <- vs ] of
                       [e] -> derefA e
                       _   -> orig

        derefCregRead :: AId -> Int -> AExpr -> AExpr
        derefCregRead _ 0 e = e
        derefCregRead inst n e =
            case (cregEnVal inst (n-1)) of
              Just 0 -> derefCregRead inst (n-1) e
              Just _ -> fromMaybe e (cregWriteExpr inst (n-1))
              Nothing -> e

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
        -- any primitive whose value the evaluator can determine is
        -- constant (this covers all-constant operands, and boolean
        -- structure such as complementary operands, through wires)
        getOutPropsA e@(APrim _ _ _ _)
            | isJust (evalConstA e) = [VPconst]
        -- a selection whose condition the schedule makes constant
        -- reduces to one of its branches
        getOutPropsA (APrim _ _ PrimIf [c, t, e])
            | Just v <- evalConstA c =
                if (v == 0) then getOutPropsA e else getOutPropsA t
        -- a selection between equal branches reduces to the branch
        -- (compared through def and wire references)
        getOutPropsA (APrim _ _ PrimIf [_, t, e])
            | derefA t == derefA e = getOutPropsA t
        -- a 1-bit AND/OR whose identity operands drop away, leaving a
        -- single operand, passes that operand's properties through
        -- (constant results were already handled above)
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
        -- a selected result of a split method is wired to that output
        -- port
        getOutPropsA (ATupleSel _ (AMethCall _ obj meth _) n) =
            methOutPortPropsA obj meth n
        getOutPropsA (ATupleSel _ (AMethValue _ obj meth) n) =
            methOutPortPropsA obj meth n
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

        -- the declared properties common to all of a method's output
        -- ports (used when a reference does not select a single port;
        -- for a method with one output port this is that port's props)
        methOutPropsA :: AId -> AId -> [VeriPortProp]
        methOutPropsA obj meth =
            case findMethodA obj meth of
              Just (Method { vf_outputs = outs@(_:_) }) ->
                  foldr1 intersect (map snd outs)
              _ -> []

        -- the declared properties of one output port of a method
        -- (ATupleSel indices are 1-based)
        methOutPortPropsA :: AId -> AId -> Integer -> [VeriPortProp]
        methOutPortPropsA obj meth n =
            case findMethodA obj meth of
              Just (Method { vf_outputs = outs }) ->
                  case drop (fromInteger n - 1) outs of
                    ((_, ps) : _) -> ps
                    [] -> []
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
        exprCalls (ATuple _ es) = concatMap exprCalls es
        exprCalls (ATupleSel _ e _) = exprCalls e
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
            concat [ instArgUses v | v <- vs ] ++
            -- the control signals referenced by the selectors of
            -- surviving value-method argument muxes
            valueSelUses

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
        --
        -- When the schedule info is available, the value-method mux
        -- selector uses are recorded exactly, from the arms of the
        -- surviving muxes (see valueSelUses); this also covers calls
        -- reached through defs, which a scan of the rule's own
        -- expressions would miss.  Without it, conservatively treat
        -- the WILL_FIRE as used whenever the rule's expressions
        -- contain a call which could need a mux.
        ruleWFUses :: AId -> ARule -> [(AId, AUse)]
        ruleWFUses wf r =
            [ (wf, u) | a <- arule_actions r,
                        u <- actionWFUses (arule_id r) a ] ++
            [ (wf, AUOpaque) |
                  isNothing mschedinfo,
                  any hasMuxableCall
                      (arule_pred r :
                       concatMap aact_args (arule_actions r)) ]

        actionWFUses :: AId -> AAction -> [AUse]
        actionWFUses rid (ACall obj meth (c:_))
            | isWireSet obj meth = wireFlowUses obj meth rid
            | Just _ <- cregMeth obj meth = [AUOpaque]
            -- a call whose arm the arbitration drops uses nothing
            | Just ArmDropped <- armClass obj meth rid = []
            -- when the arm is classified, account for the WILL_FIRE's
            -- two destinations separately: the method's enable port
            -- (unless the port's enable folds to a constant), and the
            -- argument-mux selectors (only when the arm is an input
            -- of a surviving mux, and not its selector-less last
            -- priority arm)
            | Just cls <- armClass obj meth rid =
                let en_uses
                      | enFolded obj meth rid = []
                      -- an unconditional call with its own surviving
                      -- connection wires the WILL_FIRE directly to
                      -- the method's enable port
                      | cls == ArmDirect,
                        evalConstA c == Just 1,
                        Just (Method { vf_enable = Just (_, pps) })
                            <- findMethodA obj meth
                        = [AUConn pps]
                      | otherwise = [AUOpaque]
                    sel_uses
                      | cls == ArmMuxed,
                        not (selDropped obj meth rid)
                        = [AUOpaque]
                      | otherwise = []
                in  en_uses ++ sel_uses
            -- no schedule info: an unconditional direct call wires
            -- the WILL_FIRE to the enable port
            | Just m@(Method { vf_enable = Just (_, pps) })
                  <- findMethodA obj meth,
              isDirectCallA obj meth m,
              evalConstA c == Just 1
              = [AUConn pps]
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
                let -- with a unique data expression the wire is a
                    -- direct alias; otherwise the data goes via a
                    -- mux, and this arm's fate in the arbitration
                    -- decides: a winning arm is the alias, a losing
                    -- arm's data reaches nothing
                    arg_uses =
                        case (wireDataExpr obj, armClass obj meth rid) of
                          (Just _, _) -> [AUDef (wireDataId obj)]
                          (_, Just ArmDirect) -> [AUDef (wireDataId obj)]
                          (_, Just ArmDropped) -> []
                          _ -> [AUVia (wireDataId obj)]
                in  concat [ classifyExpr u c |
                                 u <- wireFlowUses obj meth rid ] ++
                    concat [ classifyExpr u e | u <- arg_uses, e <- es ]
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
        classifyForeignExpr e@(AMethCall _ obj meth es)
            | isWireGet obj meth || isWireHas obj meth = []
            | Just _ <- cregMeth obj meth = []
            | otherwise = classifyValueCallArgs e obj meth es
        classifyForeignExpr (ASClock _ (AClock { aclock_osc = o,
                                                 aclock_gate = g })) =
            classifyForeignExpr o ++ classifyForeignExpr g
        classifyForeignExpr (ASReset _ (AReset { areset_wire = w })) =
            classifyForeignExpr w
        classifyForeignExpr (ASInout _ (AInout { ainout_wire = w })) =
            classifyForeignExpr w
        classifyForeignExpr (ASAny _ (Just e)) = classifyForeignExpr e
        classifyForeignExpr (ATuple _ es) = concatMap classifyForeignExpr es
        classifyForeignExpr (ATupleSel _ e _) = classifyForeignExpr e
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
        classifyExpr u e@(AMethCall _ obj meth es)
            | isWireGet obj meth = [(wireDataId obj, u)]
            | isWireHas obj meth = [(wireHasId obj, u)]
            | Just _ <- cregMeth obj meth = []
            | otherwise = classifyValueCallArgs e obj meth es
        classifyExpr u (ASClock _ (AClock { aclock_osc = o,
                                            aclock_gate = g })) =
            classifyExpr (opaqueOf u) o ++ classifyExpr (opaqueOf u) g
        classifyExpr u (ASReset _ (AReset { areset_wire = w })) =
            classifyExpr (opaqueOf u) w
        classifyExpr u (ASInout _ (AInout { ainout_wire = w })) =
            classifyExpr (opaqueOf u) w
        classifyExpr u (ASAny _ (Just e)) = classifyExpr (opaqueOf u) e
        -- a tuple groups the per-port values of a split argument;
        -- the pairing with ports happens in directMethArgs, so a
        -- tuple in any other context is surrounding logic
        classifyExpr u (ATuple _ es) =
            concatMap (classifyExpr (opaqueOf u)) es
        -- selecting one result port of a split method call classifies
        -- like the call itself (the call expression is the arm's
        -- identity); any other selection is surrounding logic
        classifyExpr u (ATupleSel _ e@(AMethCall {}) _) = classifyExpr u e
        classifyExpr u (ATupleSel _ e _) = classifyExpr (opaqueOf u) e
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

        -- Arguments of a call to a value method of a state instance,
        -- classified by the fate of this call's arm in the argument
        -- muxes when the schedule info is available (the whole call
        -- expression is the arm's identity -- see exprBlobArms),
        -- otherwise by the port-multiplicity check
        classifyValueCallArgs :: AExpr -> AId -> AId -> [AExpr]
                              -> [(AId, AUse)]
        classifyValueCallArgs e obj meth es =
            case M.lookup e exprArmClassMap of
              -- the arm is dropped: nothing reaches the port
              Just ArmDropped -> []
              Just ArmDirect -> directMethArgs obj meth es
              Just ArmMuxed -> concatMap (classifyExpr AUOpaque) es
              Nothing -> classifyMethArgs obj meth es

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
                  -> concat (zipWith connArg ins es)
              _ -> concatMap (classifyExpr AUOpaque) es
          where
            -- one source argument: a single-port argument connects
            -- directly; a split argument arrives as a tuple whose
            -- elements pair with the argument's ports
            connArg [(_, pps)] e = classifyExpr (AUConn pps) e
            connArg ports (ATuple _ es')
                | length ports == length es'
                = concat [ classifyExpr (AUConn pps) e |
                               ((_, pps), e) <- zip ports es' ]
            connArg _ e = classifyExpr AUOpaque e

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
        --
        -- Action-method call sites are keyed by (instance, method,
        -- calling rule), since the call appears in the rule itself.
        -- Value-method call sites are keyed by the call expression:
        -- the arbitration works on unique expressions (which may be
        -- shared by several rules, through defs), and the expression
        -- is what the classification sites have in hand.  The
        -- selectors of a surviving value mux reference the control
        -- signals of the arms' users (WILL_FIRE for a rule or action
        -- method, RDY for an interface value method, as in AState's
        -- mkEmux), which is recorded as a use (see valueSelUses).

        armClassMap :: M.Map (AId, AId, AId) ArmClass
        enFoldSet, selDropSet :: S.Set (AId, AId, AId)
        exprArmClassMap :: M.Map AExpr ArmClass
        valueSelUses :: [(AId, AUse)]
        (armClassMap, enFoldSet, selDropSet,
         exprArmClassMap, valueSelUses) =
            case mschedinfo of
              Nothing -> (M.empty, S.empty, S.empty, M.empty, [])
              Just si -> mkArmClassMaps si

        -- the classification for a call to a method of a state
        -- instance from a given rule (Nothing when no schedule info
        -- is available or the call is not in the allocation)
        armClass :: AId -> AId -> AId -> Maybe ArmClass
        armClass obj meth rid =
            M.lookup (obj, unQualId meth, rid) armClassMap

        -- whether the enable of the port this call was allocated to
        -- folds to a constant (some caller's WILL_FIRE AND condition
        -- is constant true, absorbing the OR), so that the enable
        -- references no caller's WILL_FIRE
        enFolded :: AId -> AId -> AId -> Bool
        enFolded obj meth rid =
            (obj, unQualId meth, rid) `S.member` enFoldSet

        -- whether this arm survives in a priority mux as its last
        -- arm: the mux's default is a don't-care, so the last arm's
        -- selector is absorbed and references nothing
        selDropped :: AId -> AId -> AId -> Bool
        selDropped obj meth rid =
            (obj, unQualId meth, rid) `S.member` selDropSet

        mkArmClassMaps :: AScheduleInfo
                       -> (M.Map (AId, AId, AId) ArmClass,
                           S.Set (AId, AId, AId),
                           S.Set (AId, AId, AId),
                           M.Map AExpr ArmClass,
                           [(AId, AUse)])
        mkArmClassMaps si =
            let multMap = M.fromList (concatMap genMethodMult vs)
                (expr_blobs, action_blobs) =
                    ratToBlobs (asi_method_uses_map si) multMap
                               (asi_resource_alloc_table si)
                edb = asi_exclusive_rules_db si
                (ASchedule _ rev_exec_order) = asi_schedule si
                omPos :: M.Map AId Integer
                omPos = M.fromList (zip rev_exec_order [0..])
                (a_cls, a_enf, a_drop) =
                    unzip3 (map (blobArms edb omPos) action_blobs)
                a_map = M.fromList (concat a_cls)
                en_set = S.fromList (concat a_enf)
                drop_set = S.fromList (concat a_drop)
                e_results = map (exprBlobArms edb omPos) expr_blobs
                e_map = M.fromListWith classJoin (concatMap fst e_results)
                sel_uses = concatMap snd e_results
            in  (a_map, en_set, drop_set, e_map, sel_uses)

        blobArms :: ExclusiveRulesDB -> M.Map AId Integer -> MethBlob
                 -> ([((AId, AId, AId), ArmClass)],
                     [(AId, AId, AId)],
                     [(AId, AId, AId)])
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

                -- the port's enable is the OR of every arm's
                -- WILL_FIRE AND condition; it folds to constant true
                -- when some conjunct is constant true, or when the
                -- unconditional arms' WILL_FIREs contain a
                -- complementary pair (as in wireHasVal) -- either
                -- way, no caller's WILL_FIRE is referenced by it
                enFold :: [(AExpr, Maybe [AId])] -> [(AId, AId, AId)]
                enFold uses =
                    let conj_one =
                            or [ selVal e r == Just 1 |
                                     (e, Just rs) <- uses, r <- rs ]
                        uncond_wfs =
                            [ ASDef aTBool (mkIdWillFire r) |
                                  (AMethCall _ _ _ (c:_), Just rs) <- uses,
                                  evalConstA c == Just 1,
                                  r <- rs ]
                    in  [ key r | conj_one || anyComplementaryA uncond_wfs,
                                  (_, Just rs) <- uses, r <- rs ]

                -- the last arm surviving in a mux: the mux's default
                -- is a don't-care, so the last arm's selector is
                -- absorbed into it and references nothing
                lastMuxed :: [((AId, AId, AId), ArmClass)]
                          -> [(AId, AId, AId)]
                lastMuxed cls =
                    take 1 [ k | (k, ArmMuxed) <- reverse cls ]

                -- the selector value of an arm shared by several
                -- rules: the OR of their individual selector values
                orSelVal :: AExpr -> [AId] -> Maybe Integer
                orSelVal e rs =
                    let vs = [ selVal e r | r <- rs ]
                        isOne v = (isJust v) && (v /= Just 0)
                    in  if (any isOne vs) then Just 1
                        else if (all (== (Just 0)) vs) then Just 0
                        else Nothing

                portArms :: [(AExpr, Maybe [AId])]
                         -> ([((AId, AId, AId), ArmClass)],
                             [(AId, AId, AId)],
                             [(AId, AId, AId)])
                -- a single use is a direct connection (see mkEmux)
                portArms uses@[(_, mrs)] =
                    ([ (key r, ArmDirect) | Just rs <- [mrs], r <- rs ],
                     enFold uses, [])
                portArms uses =
                    let arm_rules = concat [ rs | (_, Just rs) <- uses ]
                        usePri = not (and [ areRulesExclusive edb r r' |
                                                r <- arm_rules,
                                                r' <- arm_rules,
                                                r /= r' ])
                    in  if usePri
                        then
                          -- arms split per rule, in priority order,
                          -- as in mkEmux's "order"
                          let arms = [ (M.findWithDefault 0 r omPos,
                                        (key r, selVal e r)) |
                                           (e, Just rs) <- uses, r <- rs ]
                              cls = muxWalk
                                        (map snd
                                            (sortBy (\ (x,_) (y,_) ->
                                                         compare x y)
                                                arms))
                          in  (cls, enFold uses, lastMuxed cls)
                        else
                          -- a parallel mux keeps the arms per use, in
                          -- use order (mkEmux does not reorder them)
                          let arms = [ ((e, rs), orSelVal e rs) |
                                           (e, Just rs) <- uses ]
                              ucls = muxWalk arms
                              cls = [ (key r, c) |
                                          ((_, rs), c) <- ucls, r <- rs ]
                              sel_drops =
                                  concat
                                      (take 1 [ map key rs |
                                                    ((_, rs), ArmMuxed)
                                                        <- reverse ucls ])
                          in  (cls, enFold uses, sel_drops)

                (clss, enfs, drops) = unzip3 (map portArms port_blobs)
            in  (concat clss, concat enfs, concat drops)

        -- Classify the arms of the argument muxes of a value method
        -- (an expr blob), keyed by the call expression, and collect
        -- the control signals (WILL_FIRE/RDY) which the selectors of
        -- the surviving muxes reference.  Under a priority mux the
        -- arms are split per user (as in mkEmux's "order"), so the
        -- fates of an expression's split arms are joined.
        exprBlobArms :: ExclusiveRulesDB -> M.Map AId Integer -> MethBlob
                     -> ([(AExpr, ArmClass)], [(AId, AUse)])
        exprBlobArms edb omPos (_, port_blobs) =
            let results = map portArms port_blobs
            in  (concatMap fst results, concatMap snd results)
          where
            -- the control signal of a user: RDY for an interface
            -- value method, WILL_FIRE for a rule or action method
            -- (as in mkEmux's willfireId)
            userSelId r | r `S.member` valueMethodSet = mkRdyId r
                        | otherwise = mkIdWillFire r

            -- the selector value of an arm: the OR of its users'
            -- control signals (the condition of an expression use is
            -- aTrue -- see mkEmuxssExpr)
            selVal :: [AId] -> Maybe Integer
            selVal rs =
                let vs = [ evalDefA (userSelId r) | r <- rs ]
                    isOne v = isJust v && (v /= Just 0)
                in  if (any isOne vs) then Just 1
                    else if (all (== Just 0) vs) then Just 0
                    else Nothing

            portArms :: [(AExpr, Maybe [AId])]
                     -> ([(AExpr, ArmClass)], [(AId, AUse)])
            -- a single use is a direct connection (see mkEmux);
            -- this includes predicate and instance uses, which the
            -- allocation always gives their own port
            portArms [(e, _)] = ([(e, ArmDirect)], [])
            portArms uses
                -- a multi-use port with a predicate or instance use
                -- is not something AState will mux; leave the port
                -- unclassified (conservative)
                | any (isNothing . snd) uses = ([], [])
                | otherwise =
                    let arm_rules = concat [ rs | (_, Just rs) <- uses ]
                        usePri = not (and [ areRulesExclusive edb r r' |
                                                r <- arm_rules,
                                                r' <- arm_rules,
                                                r /= r' ])
                        -- ordered = the arm order in the mux is
                        -- known, so the last surviving arm can be
                        -- recognized (its selector is absorbed into
                        -- the mux's don't-care default)
                        (arm_classes, ordered)
                          | not usePri =
                              -- a parallel mux keeps the arms per
                              -- use, in use order
                              (muxWalk [ ((e, rs), selVal rs) |
                                             (e, Just rs) <- uses ],
                               True)
                          -- a user without an order position (an
                          -- interface value method) cannot be placed
                          -- in the priority; be conservative
                          | any (`M.notMember` omPos) arm_rules =
                              ([ ((e, rs), ArmMuxed) |
                                     (e, Just rs) <- uses ],
                               False)
                          | otherwise =
                              let arms = [ (M.findWithDefault 0 r omPos,
                                            ((e, [r]), selVal [r])) |
                                               (e, Just rs) <- uses,
                                               r <- rs ]
                              in  (muxWalk
                                       (map snd
                                           (sortBy (\ (x,_) (y,_) ->
                                                        compare x y)
                                               arms)),
                                   True)
                        -- join the fates of an expression's split arms
                        class_map =
                            M.toList
                                (M.fromListWith classJoin
                                    [ (e, c) | ((e, _), c) <- arm_classes ])
                        -- the last surviving arm, whose selector is
                        -- not referenced
                        last_arms =
                            if ordered
                            then take 1 [ ku | (ku, ArmMuxed)
                                                   <- reverse arm_classes ]
                            else []
                        -- the selectors of the other surviving mux
                        -- arms reference their users' control signals
                        -- (a constant control signal is folded into
                        -- the selector and is not a dynamic use)
                        sel_uses =
                            [ (si, AUOpaque) |
                                  (ku@(_, rs), ArmMuxed) <- arm_classes,
                                  not (ku `elem` last_arms),
                                  r <- rs,
                                  let si = userSelId r,
                                  isNothing (evalDefA si) ]
                    in  (class_map, sel_uses)

        -- interface value methods, whose muxes select on the RDY
        -- signal instead of the WILL_FIRE (as in aState)
        valueMethodSet :: S.Set AId
        valueMethodSet =
            S.fromList [ i | (AIDef { aif_value = (ADef i _ _ _) }) <- ifc ]

        -- Classify a mux's arms, given in the mux's arm order.  The
        -- netlist realizes the mux as a selection chain whose first
        -- true selector wins (a priority mux by construction, a
        -- parallel mux because its arms are exclusive so any
        -- realization order is faithful), and the folding follows
        -- that structure from the front: a constant-0 arm drops out;
        -- a constant-1 arm ends the chain, dropping all later arms
        -- (and wins outright when no unknown arm precedes it); a
        -- lone surviving arm is a direct connection (the chain's
        -- default is a don't-care).
        muxWalk :: [(k, Maybe Integer)] -> [(k, ArmClass)]
        muxWalk arms =
            let cls = walk False arms
                live = [ i | (i, (_, c)) <- zip idxs cls,
                             c /= ArmDropped ]
                idxs = [(0 :: Int) ..]
            in  case live of
                  [i] -> [ (k, if (j == i) then ArmDirect else c) |
                               (j, (k, c)) <- zip idxs cls ]
                  _ -> cls
          where
            walk _ [] = []
            walk sawUnknown ((k, v) : rest) =
                case v of
                  Just 0 -> (k, ArmDropped) : walk sawUnknown rest
                  Just _ | not sawUnknown -> (k, ArmDirect) : dropAll rest
                  Just _ -> (k, ArmMuxed) : dropAll rest
                  Nothing -> (k, ArmMuxed) : walk True rest
            dropAll xs = [ (k', ArmDropped) | (k', _) <- xs ]

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
     deriving (Eq)

-- Combine the fates of the split arms of one call expression in a
-- priority mux: the expression is dropped only if all of its arms
-- are dropped; an arm which wins the arbitration outright implies
-- all other arms were dropped (there is at most one direct arm)
classJoin :: ArmClass -> ArmClass -> ArmClass
classJoin ArmDropped c = c
classJoin c ArmDropped = c
classJoin ArmDirect ArmDirect = ArmDirect
classJoin _ _ = ArmMuxed
