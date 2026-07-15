module VIOProps (VIOProps, getIOProps, getIOPropsA) where

import Data.List(intersect, nub)
import Data.Maybe(catMaybes, isNothing)
import qualified Data.Map as M
import qualified Data.Set as S
import Util
import Eval(NFData(..), rnf)
import Flags
import PPrint
import ErrorUtil(internalError)
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
import BackendNamingConventions(createVerilogNameMapForAVInst,
                                xLateIdUsingFStringMap)

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
-- Note some intentional differences from getIOProps:
--  * Clock, gate, and reset ports are always labeled with their
--    structural properties (clock/clock gate/reset), whereas getIOProps
--    only labels them when the deduction succeeds (for example, an
--    unused input clock is labeled "clock unused" here, but just
--    "unused" by getIOProps).
--  * Uses of signals in foreign function calls are treated as uses,
--    whereas getIOProps can consider such signals "unused" (foreign
--    calls are not part of the def chain it follows).
--  * Properties which only become deducible after scheduling and
--    netlist optimization can be missed: for example, an enable
--    input whose method's actions are dropped by later optimization
--    is not labeled "unused", and a ready output which scheduling
--    reduces to a constant is not labeled "const".  Such misses only
--    lose properties; they never assert a property that the
--    getIOProps deduction would contradict.

getIOPropsA :: Flags -> [PProp] -> APackage -> (VIOProps, [VPort])
getIOPropsA _flags pps apkg =
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

        iis = [ (i, INPUT, size t, mergeProps sps (getInPropsA i)) |
                    (i, t, sps) <- arg_ins ++ meth_arg_ins ] ++
              -- the enable wires do not exist in the APackage (AState
              -- creates them, gating the WILL_FIREs of the method's
              -- rules), so no deduction is attempted for them
              [ (i, INPUT, size t, sps) | (i, t, sps) <- en_ins ]

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
        -- either a special output of a state instance
        -- or an input of this module
        getOutPropsA (ASPort _ i) = M.findWithDefault [] i wireMapA_out
        -- follow defs
        getOutPropsA (ASDef _ i) =
            case M.lookup i defMapA of
              Just d  -> getOutPropsA (adef_expr d)
              Nothing -> []
        -- constant values
        getOutPropsA (ASParam _ _) = [VPconst]
        getOutPropsA (ASInt _ _ _) = [VPconst]
        getOutPropsA (ASStr _ _ _) = [VPconst]
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
                  r <- rs, a@(ACall {}) <- arule_actions r ]

        -- all expressions in the package (for counting method calls)
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
                     concatMap aact_args (arule_actions r) | r <- rs ] ++
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
            concat [ classifyExpr AUOpaque e |
                         a <- all_assumps,
                         e <- assump_property a :
                              concatMap aact_args (assump_actions a) ] ++
            -- rules (including the bodies of action methods)
            concat [ ruleUses r | r <- rs ] ++
            -- state instance arguments
            concat [ instArgUses v | v <- vs ]

        ruleUses :: ARule -> [(AId, AUse)]
        ruleUses r = classifyExpr AUOpaque (arule_pred r) ++
                     concatMap actionUses (arule_actions r)

        actionUses :: AAction -> [(AId, AUse)]
        -- the condition feeds the enable logic (via the WILL_FIRE),
        -- and so is not a direct connection; the arguments are
        -- connections to the method's input ports
        actionUses (ACall obj meth (c:es)) =
            classifyExpr AUOpaque c ++ classifyMethArgs obj meth es
        -- foreign function and task calls (AFCall, ATaskAction)
        -- are uses that we can conclude nothing about
        actionUses a = concatMap (classifyExpr AUOpaque) (aact_args a)

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
        -- okUse) receive the given use; anything else is opaque.
        -- Arguments of method calls are connections to the method's
        -- input ports and are classified separately.
        classifyExpr :: AUse -> AExpr -> [(AId, AUse)]
        classifyExpr u (ASPort _ i)  = [(i, u)]
        classifyExpr u (ASParam _ i) = [(i, u)]
        classifyExpr u (ASDef _ i)   = [(i, u)]
        classifyExpr u (APrim _ _ PrimConcat es) =
            concatMap (classifyExpr u) es
        classifyExpr u (APrim _ _ PrimExtract (e:es)) =
            classifyExpr u e ++ concatMap (classifyExpr AUOpaque) es
        classifyExpr _ (APrim _ _ _ es) =
            concatMap (classifyExpr AUOpaque) es
        classifyExpr _ (ANoInlineFunCall _ _ _ es) =
            concatMap (classifyExpr AUOpaque) es
        classifyExpr _ (AFunCall _ _ _ _ es) =
            concatMap (classifyExpr AUOpaque) es
        classifyExpr _ (AMethCall _ obj meth es) =
            classifyMethArgs obj meth es
        classifyExpr _ (ASClock _ (AClock { aclock_osc = o,
                                            aclock_gate = g })) =
            classifyExpr AUOpaque o ++ classifyExpr AUOpaque g
        classifyExpr _ (ASReset _ (AReset { areset_wire = w })) =
            classifyExpr AUOpaque w
        classifyExpr _ (ASInout _ (AInout { ainout_wire = w })) =
            classifyExpr AUOpaque w
        classifyExpr _ (ASAny _ (Just e)) = classifyExpr AUOpaque e
        -- AMethValue, AMGate, ATaskValue, and literals use no signals
        classifyExpr _ _ = []

        -- Arguments of a call to a method of a state instance are
        -- connections to the method's input ports, as long as AState
        -- will not need to insert muxes (which is the case when the
        -- method has enough port copies for all of its call sites)
        classifyMethArgs :: AId -> AId -> [AExpr] -> [(AId, AUse)]
        classifyMethArgs obj meth es =
            case findMethodA obj meth of
              Just m@(Method { vf_inputs = ins })
                  | isDirectCall m && length ins == length es
                  -> concat (zipWith (\ (_, pps) e ->
                                          classifyExpr (AUConn pps) e)
                                     ins es)
              _ -> concatMap (classifyExpr AUOpaque) es
          where isDirectCall m =
                    M.findWithDefault 0 (obj, unQualId meth) methCallCountA
                        <= max 1 (vf_mult m)

        -- ids which become output or inout ports: a signal which
        -- drives a port is not unused, but no properties can be
        -- concluded from that use (this mirrors the "output_pairs"
        -- entries in getIOProps' wireMap_in)
        outSinkSet :: S.Set AId
        outSinkSet =
            S.fromList ([ adef_objid d | f <- ifc, d <- ifcValueDef f ] ++
                        [ i | (i, _) <- out_wire_defs ])

        getInPropsA :: AId -> [VeriPortProp]
        getInPropsA i =
            let sink_props = if (i `S.member` outSinkSet) then [[]] else []
                uses = M.findWithDefault [] i useMapA
            in  case (sink_props, uses) of
                  ([], []) -> [VPunused]
                  _ -> joinInProps (sink_props ++ map usePropsA uses)

        usePropsA :: AUse -> [VeriPortProp]
        usePropsA (AUConn ps) = ps
        usePropsA AUOpaque    = []
        usePropsA (AUDef d)   = getInPropsA d


-- A use of a signal, for deducing the properties of module inputs
-- on an APackage (see getInPropsA above)
data AUse = AUDef AId               -- used to define another signal
          | AUConn [VeriPortProp]   -- connected to a port with these props
          | AUOpaque                -- used in a way we cannot analyze
