
--XXX {-# OPTIONS_GHC -fwarn-name-shadowing -fwarn-missing-signatures #-}

module AState(
              aState,
              ) where

import qualified Data.Map as M
import qualified Data.Set as S

import Data.List(transpose, sortBy, partition,
            unzip4, groupBy, intersect,
            genericLength)

import Util
import FStringCompat
import IntLit

import Error(internalError, ErrMsg(..), ErrorHandle)
import ErrorMonad(ErrorMonad(..), convErrorMonadToIO)
import Flags(Flags, useDPI)
import Position(noPosition)

import PreStrings( fsUnderUnder,
                  fsMux, fsMuxPreSel, fsMuxSel, fsMuxVal)
import Id
import Pragma
import Prim
import PFPrint

import VModInfo
import ASyntax
import ASyntaxUtil
import ASchedule(AScheduleInfo(..), ExclusiveRulesDB(..), areRulesExclusive,
                 MethodUsesMap, MethodUsers, MethodId(..), UniqueUse(..))
import AUses(useDropCond)
import AVerilogUtil(vNameToTask)
import RSchedule(RAT, ratToNestedLists)
import Wires(WireProps(..))
import Data.Maybe (listToMaybe)

--import Debug.Trace
--import Util(traces)


-- ==============================
-- Naming conventions

astOrPref, astAndPref :: String
astOrPref = "_dor"
astAndPref = "_dand"


-- ==============================
-- Data Types
--

-- type ActMap = M.Map (AId, AMethodId) [(ARuleId, [AExpr])]

type OrderMap = M.Map ARuleId Int

type AExprSubst = [(AExpr, AExpr)]

-- ---------------

-- A MethBlob relates a method to all of its uses.
--
-- MethBlob is a tuple of:
--  * method name info (objectname, methodname, multi-ported)
--  * a list of uses for each copy of the method (if the method is not
--    multi-ported, then there's just one elem, else one elem for each port)
--
-- The uses of a single port (MethPortBlob) is a list of pairs:
--  * a unique expression used for the method call
--    (AAction uses have been converted to either AMethCall or AFunCall)
--  * a Maybe list of the rules which used that expression
--    (The Maybe is Nothing if any of the uses are in a rule's
--    condition -- because this implies no muxing -- and "Just rs"
--    otherwise, where "rs" is the rules which use the method inside
--    their actions.)
--
-- XXX This is complicated enough that it really should be a data structure
--

type MethBlob = (((AId, AId), Bool), [MethPortBlob])

type MethPortBlob = [(AExpr, Maybe [ARuleId])]


-- ==============================
-- Function: aState
--

-- aState converts an APackage, a list of module properties, and scheduling
-- info into an ASPackage.
--
--  * Multiplicity of submodule methods is expanded, and EFewPorts is
--    signaled if there are less ports than unique uses. (Is this
--    deprecated, because previous resource handling catches this?)
--  * Muxes for method inputs are generated here
--
-- The APackage input has the following fields:
-- APackage { apkg_name=mi,
--            apkg_is_wrapped=fmod,
--            apkg_backend :: Maybe Backend,
--            apkg_size_params=ps,
--            apkg_inputs=args,
--            apkg_clock_domains :: [AClockDomain],
--            apkg_external_wires= ??? ,
--            apkg_reset_list :: [(ResetId, AReset)],
--            apkg_state_instances=vs,
--            apkg_local_defs=ds,
--            apkg_rules=ors,
--            apkg_schedule_pragmas= ??? ,
--            apkg_interface=ifc,
--            apkg_inst_comments :: [(Id, [String])],
--            apkg_proof_obligations= ??? }
-- Note that external_wires and schedule_pragmas are ignored.
--
-- The ASPackage output has the following fields:
--   mi       = unchanged
--   fmod     = unchanged
--   param_inputs = the module parameters =
--       size parameters (size_ps) plus module arg params (from "args")
--   schedule = unchanged (from the ScheduleInfo)
--   exps = exported wires (the outputs of the ifc) =
--       aState finds the AIDefs in "ifc" and removes the RDYs if alwaysReady.
--       (Note, we don't support arguments which might have output wires,
--       such as a function, which could be implemented as out and in wires.)
--   port_inputs = input wires to the module (the inputs of the ifc) =
--       this includes the non-method module inputs (the "args" of APackage)
--       which are generated to ports,
--       plus any arguments to value and action methods (which are assumed
--       to be all bits inputs and not, say, of function type)
--   defs = this is the original "ds" from the APackage,
--       plus the muxes for values and muxes for actions,
--       plus the enable signals for action methods used on submodules,
--       plus the enable signals for always enabled methods (which are
--       wired to 1, rather than coming in as inputs)
--   vs = the original "vs" from the APackage but expanded for multiplicity
--       (which is currently done wrong because it is handled on the instance
--       and not on the method) and with clock and reset port structures
--       fixed up to use the Verilog wire names (saving later stages from
--       having to do the conversion)
--   svars = outputs coming from the instantiated state =
--       undefined state outputs (those not found in "dvars" -- presumably
--       defined state outputs are those which were annotated as being
--       fixed high or low, for example?),
--       plus special wires (clocks and resets)
--   rfas = for each rule in "rs" which has a foreign function action
--       (AFCall or ATaskAction), the call (of type AAction) is converted
--       to a AForeignCall type (with the rule's WILL_FIRE in the condition)
--

aState :: ErrorHandle -> Flags -> [PProp] -> AScheduleInfo -> APackage ->
          IO (ASPackage)
aState errh flags pps sr m = convErrorMonadToIO errh (aState' flags pps sr m)

-- ---------------
-- XXX this function is WAY TOO BIG
aState' :: Flags -> [PProp] -> AScheduleInfo -> APackage -> ErrorMonad (ASPackage)
aState' flags pps schedule_info apkg = do
    --traceM( "In AState: " ++ ppReadable pps ) ;
    let
        mi = apkg_name apkg
        fmod = apkg_is_wrapped apkg
        size_ps = apkg_size_params apkg
        vs = apkg_state_instances apkg
        ds = apkg_local_defs apkg
        ors = apkg_rules apkg
        ifc = apkg_interface apkg
        wi = apkg_external_wires apkg
        submod_cmap = apkg_inst_comments apkg

        clockPortTable = getOutputClockPortTable (wClk wi)
        resetPortTable = getOutputResetPortTable (wRst wi)
        clockdomain_map = M.fromList (apkg_clock_domains apkg)
        reset_map = M.fromList (apkg_reset_list apkg)

        rerr = internalError "AState.reset_lookup unknown reset"
        reset_lookup k = M.findWithDefault rerr k reset_map

        domainerr = internalError "AState.domain_osc_lookup unknown domain"
        domain_osc_lookup k = map aclock_osc
                                  (M.findWithDefault domainerr k clockdomain_map)

        vmi_map :: VModInfoMap
        vmi_map =
            let mkVMIPair avi = (avi_vname avi, avi_vmi avi)
            in  M.fromList (map mkVMIPair vs)

    let
        (ASchedule _ earliness_order_unfiltered) = asi_schedule schedule_info
        -- alwaysEnabled = (PPalwaysEnabled []) `elem` pps

        -- interface rules
        irs :: [ARule] -- the body of the Action methods into ARule
        irs = concatMap aIfaceRules ifc
        -- all rules (including action methods)
        rs_unsorted = irs ++ ors

        -- all rule names (including action methods)
        rs_ids = map aRuleName rs_unsorted
        -- earliness order minus value methods
        earliness_order =
            filter (`elem` rs_ids) earliness_order_unfiltered

        -- interface outputs
        -- these are the output port names and their assignments
        -- We separate out the RDY defs for always_ready methods from others,
        -- because we want the defs (they feed into enables) but do want the
        -- RDY ports.
        isAlwaysReadyMethod m = (isRdyId (aif_name m)) && (isAlwaysRdy pps (aif_name m))
        (always_rdy_ifc,other_ifc) = partition isAlwaysReadyMethod ifc
        outs :: [ADef]
        outs = concatMap (outputDefToADefs fmod pps) other_ifc
        always_ready_defs :: [ADef]
        always_ready_defs = concatMap (outputDefToADefs fmod pps) always_rdy_ifc

    --traceM( "ifc are: " ++ ppReadable ifc ) ;
    --traceM( "outs are: " ++ ppReadable outs ) ;
    --traceM( "rdys are: " ++ ppReadable rdysToRemove )
    let
        -- rule ordering map
        om = M.fromList (zip earliness_order [0..])
        -- ruleid to rule map
        rmap = M.fromList [(aRuleName r, r) | r <- rs_unsorted]

        -- lookup utility function
        ridToRule :: ARuleId -> ARule
        ridToRule rid =
            M.findWithDefault
                (internalError("AState: rule maps do not match\n" ++
                               (ppReadable (reverse earliness_order)) ++
                               (ppReadable (M.keys rmap))))
                rid rmap
        -- sorted rules
        rs = if (not . null) earliness_order then
                 -- lookup with earliness_order to sort the rules
                 map ridToRule (reverse earliness_order)
              else
                 -- order doesn't matter for -schedule-sequential
                 -- and -schedule-disjoint
                 rs_unsorted

        -- from the module arguments, separate out the param inputs
        (param_args, port_args, inout_args) =
            getAPackageParamsPortsAndInouts apkg

        -- aspkg input parameters (other than size parameters)
        param_inputs =
            -- XXX size parameters are bit-32?
            [ (p, aTNat) | p <- size_ps ] ++
            -- module arguments declared as parameters
            param_args

        -- input wires
        inputIds :: [AInput]
        inputIds =
            port_args ++
            concatMap aIfaceArgs ifc ++
                    [ (mkNamedEnable fi, aTBool) |
                          (AIAction { aif_name = i,
                                      aif_fieldinfo = fi }) <- ifc,
                          not (isAlwaysEn pps i)] ++
                    [ (mkNamedEnable fi, aTBool) |
                          (AIActionValue {aif_name = i,
                                          aif_fieldinfo = fi }) <- ifc,
                          not (isAlwaysEn pps i)]

        -- inout wires
        inoutIds :: [AInput]
        inoutIds =
            inout_args ++
            [ (mkNamedInout fi, aType e) | (AIInout _ (AInout e) fi) <- ifc ]

        -- output wires and types
        outputIds :: [AOutput]
        outputIds  = map (\def -> ((adef_objid def),(adef_type def)))
                         (outs ++ clk_defs ++ rstn_defs)

        -- list of tuples of lists (exported identifiers, definitions)
        clk_blob =
            [(clk_id:gate_id, clk_def:gate_def) |
                (AIClock { aif_name = n,
                           aif_clock = AClock { aclock_osc = osc,
                                                aclock_gate = gate } }) <- ifc,
                let (clk_vname, mgate_vname) =
                        fromJustOrErr ("AState.unknown output clock "
                                       ++ ppReadable n)
                            (M.lookup n clockPortTable),
                let clk_id   = vName_to_id clk_vname,
                let clk_def :: ADef
                    clk_def  = (ADef clk_id (ATBit 1) osc []),
                let gate_id  =
                        case mgate_vname of
                            Nothing -> []
                            Just (gate_vname, _) -> [vName_to_id gate_vname],
                let gate_def :: [ADef]
                    gate_def = map (\i -> ADef i (ATBit 1) gate []) gate_id
            ]

        clk_defs = concatMap snd clk_blob

        (rstn_exps, rstn_defs) = unzip
            [(rstn_id, rstn_def) |
                (AIReset { aif_name = n,
                           aif_reset = AReset { areset_wire = wire } }) <- ifc,
                let rstn_vname =
                        fromJustOrErr ("AState.unknown output reset "
                                       ++ ppReadable n)
                            (M.lookup n resetPortTable),
                let rstn_id = vName_to_id rstn_vname,
                let rstn_def :: ADef
                    rstn_def = (ADef rstn_id (ATBit 1) wire [])
            ]

        (iot_exps, iot_defs) = unzip
            [(iot_id, iot_def) |
                (AIInout { aif_name = n,
                           aif_inout = AInout { ainout_wire = wire },
                           aif_fieldinfo =
                               Inout {vf_inout = iot_vname} }) <- ifc,
                let t = aType wire,
                let iot_id = vName_to_id iot_vname,
                let iot_def = (ADef iot_id t wire [])
            ]

        -- definitions
        defs = ds ++ outs ++ always_ready_defs ++
               mux_defs ++ enas ++
               clk_defs ++ rstn_defs

        -- create dummy defs for ATaskActions which ignore their returns
        processActions new_defs new_as n [] = (new_defs, reverse new_as, n)
        processActions new_defs new_as n (a:rest) =
            case a of
              (ATaskAction { ataskact_temp = Nothing }) ->
                  let nid    = mkIdTempReturn True (mk_homeless_id (ataskact_fun a)) n
                      nact   = a { ataskact_temp = Just nid }
                      fn     = ataskact_fun a
                      is_c   = ataskact_isC a
                      cookie = ataskact_cookie a
                      ty     = ataskact_value_type a
                      ndef :: ADef
                      ndef   = ADef nid ty (ATaskValue ty nid fn is_c cookie) []
                  in if aSize ty == 0
                     then processActions new_defs (a:new_as) n rest
                     else processActions (ndef:new_defs) (nact:new_as) (n+1) rest
              _ -> processActions new_defs (a:new_as) n rest
        forceReturns new_defs new_rs _ [] = (new_defs, reverse new_rs)
        forceReturns new_defs new_rs n (r:rest) =
            let (ds,new_as,n') = processActions [] [] n (arule_actions r)
                r' = r { arule_actions = new_as }
            in forceReturns (ds ++ new_defs) (r':new_rs) n' rest
        (dummy_defs, rs') = forceReturns [] [] 1 rs

        -- when "isC", translate from the call name to the
        -- system task wrapper name
        cvtName False f = f
        cvtName True  f = vNameToTask (useDPI flags) f

        addWF rid (c:es) =
            let wf = aBoolVar (mkIdWillFire rid)
                -- aAnd will optimize the expr if "c" is True
                c' = aAnd wf c
            in  (c':es)
        addWF rid es = internalError("addWF: " ++ ppReadable (rid, es))

        cvtForeign rid resets (AFCall id f isC es _) =
            AForeignCall id (cvtName isC f) (addWF rid es) [] resets
        cvtForeign rid resets a@(ATaskAction id f isC _ es Nothing _ _) =
            AForeignCall id (cvtName isC f) (addWF rid es) [] resets
        cvtForeign rid resets  (ATaskAction id f isC _ es (Just aid) ty _) =
            AForeignCall id (cvtName isC f) (addWF rid es) [aid] resets
        cvtForeign rid resets a@(ACall { }) =
            internalError("AState.cvtForeign - not foreign:" ++ ppReadable a)

        -- (domain, rule foreign actions)
        domain_rfas =
            [ (domain, cvtForeign rid resets a) |
              ARule rid _ _ wp _ as _ _ <- rs',
              let domain = fromJustOrErr "AState.domain_rfas no clock domain"
                               (wpClockDomain wp),
              let resets = map (areset_wire . reset_lookup) (wpResets wp),
              a <- as, isForeign a ]

        -- foreign function actions by clock domain
        -- We cons one action at a time onto the result list to avoid an O(n^2) blowup.
        -- foldr combined with cons preserves the original order, which is required.
        fdomain_map = M.toList $ foldr (\(d,a) m -> case M.lookup d m of
                                                      Just as -> M.insert d (a:as) m
                                                      Nothing -> M.insert d [a] m)
                                       M.empty domain_rfas

        -- the foreign blocks
        fblocks = mapFst domain_osc_lookup fdomain_map

        -- New improved resource allocation
        blobs = ratToBlobs (asi_method_uses_map schedule_info)
                           omMultMap
                           (asi_resource_alloc_table schedule_info)
        (ers, ars) = blobs

        -- Old resource allocation
        --(ers, ars) = getMethCalls sch ds outs rs'

        exclusive_rules_db = asi_exclusive_rules_db schedule_info

        -- XXX redo construction of muxes for args, enables, and outputs:
        -- XXX use the fieldinfo to create the right names (and ARenameIO goes away)
        -- XXX can construct the enables and outputs separately from the args
        -- XXX the fieldinfo will also identify which are value, action, and AV methods

        -- mkEmuxxs needs to know which are the value methods, because
        -- selectors for muxes are RDY for value methods (instead of WILLFIRE)
        value_method_ids = [ i | (AIDef { aif_name = i }) <- ifc ]

        -- muxes for values (definitions)
        (emux_selss, emux_valss, emux_outss, esss) =
            unzip4 (map (mkEmuxssExpr exclusive_rules_db value_method_ids om) ers)

        -- muxes for actions
        -- (we don't need a substitution for actionvalue value calls,
        --  because there is no multiplicity for action/actionvalue methods,
        --  so any value calls can be converted to use of the one port)
        (amux_selss, amux_valss, amux_outss, _) =
            unzip4 (map (mkEmuxssAction exclusive_rules_db value_method_ids om) ars)

        mux_sel_defs = concat emux_selss ++ concat amux_selss
        mux_val_defs = concat emux_valss ++ concat amux_valss
        mux_out_defs = concat emux_outss ++ concat amux_outss
        mux_defsRed = mux_sel_defs ++ mux_val_defs ++ mux_out_defs
        --
        -- filter out the redundant def from the new definitions
        -- leave the mux_val_defs since these may not have good names.
        esubmap = M.fromList $ genAliases (mux_sel_defs)
        mux_defs = map (aSubst esubmap)  mux_defsRed

        enas = concatMap mkEnabless ars

        -- substitution of value method calls to instance outputs
        substs = M.fromList (concat esss)

        -- actionvalue method value references can be unconditionally converted
        subst :: AExpr -> Maybe AExpr
        subst (AMethValue vt modId methId) =
            Just (ASPort vt (mkMethId modId methId Nothing (MethodResult 1)))
        subst (ATupleSel vt (AMethValue _ modId methId) idx) =
            Just (ASPort vt (mkMethId modId methId Nothing (MethodResult idx)))
        -- substitute AMOsc, AMGate, AMReset references with their port
        subst (AMGate gt modId clkId) =
            Just (mkOutputGatePort vmi_map modId clkId)
        -- substitute any value method calls, according to the substitution
        subst e@(AMethCall vt modId methId es) =
            case (M.lookup e substs) of
              Nothing ->
                  let ino = do mult <- M.lookup (modId, methId) omMultMap
                               -- send unused calls of multi-ported methods to port 0
                               toMaybe (mult > 1) 0
                  in Just (ASPort vt (mkMethId modId methId ino (MethodResult 1)))
              me' -> me'
        subst e@(ATupleSel vt (AMethCall _ modId methId es) idx) =
            case (M.lookup e substs) of
              Nothing ->
                  let ino = do mult <- M.lookup (modId, methId) omMultMap
                               -- send unused calls of multi-ported methods to port 0
                               toMaybe (mult > 1) 0
                  in Just (ASPort vt (mkMethId modId methId ino (MethodResult idx)))
              me' -> me'
        -- AMethValue, AMGate and AMethCall should cover it
        subst e = Nothing


        getMult o m = let avi = getVInst o vs
                          vmi = avi_vmi avi
                      in  getMethMult vmi m

        -- instances with the number of used port copies
        -- (up to the max multiplicity)
        vs' = map addMult vs

        -- to ensure correlation, make it a pair of the name to its mult
        addMult avi@(AVInst { avi_vname = i, avi_vmi = vi }) =
            let port_mults = [ (m, getMultUse (i, m)) |
                                   (Method { vf_name = m }) <- vFields vi ]
            in  avi { avi_iarray = port_mults }
        getMultUse om = M.findWithDefault 0 om omnsMap

        -- convert the clock and reset args to Verilog wire port connections
        -- (also convert AMGate etc to the Verilog wire names)
        -- XXX is it more efficient to only subst inside rewireClockResetInout
        -- XXX since we only apply it when we actually introduce a gate?
        vs'' :: [AVInst]
        vs'' = mapAExprs (exprMap subst) $
               map rewireClockResetInout vs'

        fblocks' = mapAExprs (exprMap subst) fblocks

        -- output methods with their number of uses (OutputMethodNumberS)
        -- ers and ars omns list the number of methods used (not the total)
        -- for the total see omMultMap
        omns :: [ ( (AId,AId) ,Integer) ]
        omns = [ (om, genericLength is) | ((om, f), is) <- ers ++ ars ]
        omnsMap = M.fromList omns

        -- map from object-method pairs to method multiplicity
        -- this lets us list all possible output wires
        -- (for use in making allmvars)
        omMultMap = M.fromList (concatMap genMethodMult vs)

        -- defined variables
        dvars = S.fromList [ i | ADef i _ _ _ <- defs' ]

        -- all possible method inputs & outputs
        allmvars :: [(AId, AType, Bool)]
        allmvars = genModVars vs omMultMap

        -- all undefined method inputs and outputs
        mvars :: [(AId, AType, Bool)]
        mvars = [ (ui, t, a) | (ui, t, a) <- allmvars,
                               not (ui `S.member` dvars)]

        -- undefined state outputs
        svars = [ (i, t) | (i, t, False) <- mvars ]

        wvars = map fst2of3 (concatMap getSpecialOutputs vs)

        -- unconnected signals
        edefs = concatMap tieToZero mvars
                -- [ ADef i t aFalse | (i, t, True) <- mvars ]
        -- XXX need to tie unconnected  state inputs to 0 will stop verilog warns.
        defs' :: [ADef]
        defs' = [ d {adef_expr = (exprMap subst) e} | d@(ADef _ _ e _) <- defs ]
        defs'' :: [ADef]
        defs'' = defs' ++ edefs ++ dummy_defs

        --rdysToRemove = filter (isRdyToRemove pps) defs''
    -- traceM("Astate omns : " ++ ppReadable omns )
    -- traceM("Astate mvars : " ++ ppReadable mvars )
    -- traceM("Astate edefs : " ++ ppReadable edefs )
    --traceM("Astate reeadys: " ++ ppReadable rdysToRemove )
    --traceM("Astate pps: " ++ ppReadable pps )
    --traceM( "alwaysEnas are: " ++ ppReadable alwaysEnas )
    -- create the signal Id info for the ASPackage
    let signal_info =
            ASPSignalInfo {
                aspsi_inputs = map fst (param_args ++ port_args ++ inout_args),

                aspsi_output_clks  = map mkSIClockTuple clk_blob,
                aspsi_output_rsts  = rstn_exps,
                aspsi_ifc_iots  = iot_exps,
                aspsi_methods = mkSignalInfoMethod ifc,

                aspsi_inlined_ports = [],

                aspsi_rule_sched =
                    [(i,[mkIdCanFire i, mkIdWillFire i])
                         | (ARule { arule_id=i }) <- rs' ],

                -- mux output Ids are just submodule inputs,
                -- so no need to include them here again
                aspsi_mux_selectors  = map adef_objid mux_sel_defs,
                aspsi_mux_values     = map adef_objid mux_val_defs,
                aspsi_submod_enables = map adef_objid enas
            }

    -- create the comment info for the ASPackage
    let rule_cmap = [(i,cs) | r <- ors,
                              let i   = arule_id r,
                              let rps = arule_pragmas r,
                              let cs  = [ c | (RPdoc c) <- rps ] ]
        comment_info =
            ASPCommentInfo {
                aspci_submod_insts = submod_cmap,
                aspci_rules = rule_cmap
            }

    -- if there are no errors, this is the result to return

    let res =  ASPackage { aspkg_name            = mi,
                           aspkg_is_wrapped      = fmod,
                           aspkg_parameters      = param_inputs,
                           aspkg_outputs         = outputIds,
                           aspkg_inputs          = inputIds,
                           aspkg_inouts          = inoutIds,
                           aspkg_state_instances =  vs'',
                           aspkg_state_outputs   = (svars ++ wvars) ,
                           aspkg_values          = defs'',
                           aspkg_inout_values    = iot_defs,
                           aspkg_foreign_calls   = fblocks' ,
                           aspkg_inlined_ports   = [],
                           aspkg_signal_info     = signal_info,
                           aspkg_comment_info    = comment_info }

    -- does the number of uses (n) exceed the number of available ports (p)?
    let overused_ports = [ (o,m,k,n) | ((o,m),n) <- omns,
                                       let k = getMult o m,
                                       k/=0 && n>k ]

{-
    traceM ("aState\n" ++ ppReadable ({-(ds, outs),-} ers, ars, substs))
    traceM ("aState\n" ++ ppReadable ers ++ "--\n"
                       ++ ppReadable ars ++ "--\n"
                       ++ ppReadable blobs)
    traceM (ppReadable (zip earliness_order [0..]))
    traceM (ppReadable (S.toList dvars))
    traceM (ppReadable mvars)
    traceM (ppReadable ers)
    traceM (ppReadable ars)
    traceM (ppReadable (M.toList mum))
    traceM (ppReadable rat)
    traceM (ppReadable (emuxss, esss))
-}

    -- ---------------
    -- check for name clashes

    let port_ids = map fst outputIds ++
                   map fst inputIds ++
                   map fst param_inputs
        --orig_def_ids = map adef_objid ds
        state_inst_ids = map avi_vname vs

    -- instance names vs port/parameter names (user error)
    let state_port_clashes = intersect port_ids state_inst_ids
        state_port_emsgs = [ (noPosition, ENetInstConflict (getIdString inst))
                                 | inst <- state_port_clashes ]

    -- port names vs defs (internal error?)
    --let port_def_clashes = intersect port_ids orig_def_ids
    --    port_def_emsgs = internalError ...

    -- clashes between the state and defs (including new defs)
    --let state_def_clashes = ...

    -- ---------------

    -- do any always_ready methods have a RDY which is not constant 1?
    case (overused_ports) of
        []            -> if (null state_port_emsgs)
                         then EMResult res
                         else EMError state_port_emsgs
        ((o,m,k,n):_) -> EMError [(getIdPosition o,
                                   EFewPorts (pfpString o) (pfpString m) k n)]


-------------------------
genModVars :: [AVInst] -> M.Map (AId, AId) Integer -> [(AId, AType, Bool)]
genModVars vs omMultMap = allmvars
    where
        getMultUse om = M.findWithDefault 0 om omMultMap
        -- For all ports to submodules, make a 3-tuple:
        --  * port signal name uniquified for multiplicity
        --  * the type of the signal
        --  * whether the signal is  an input to module.
        --
        -- XXX This is WRONG since the uniquifier for multiple methods
        -- XXX is added to the instance name rather than the method name.
        allmvars =
            [(uniqueId, portType, isEnable) |
                -- for all submodules (get the module Id,
                -- the method arg types, and the Verilog port names)
                (AVInst { avi_vname = modId,
                          avi_meth_types = methType,
                          avi_vmi = vmodinfo }) <- vs,
                --
                -- for each method (get the method Id, the arg types,
                -- and whether it's an action method)
                --
                ( m@(Method { vf_name = methId, vf_inputs = argIds, vf_mult = mult }),
                  (argTypes, en_type, val_types) )
                    <- zip (vFields vmodinfo) methType,
                --
                -- for each part of the method, produce a triple of
                -- the method part, the type of the associated port,
                -- and a boolean if it is the enable part (of an action meth)
                --
                (meth_part, portType, isEnable) <-
                    -- argument triples
                    [ (MethodArg n, argType, True) -- EWC mark at true for input
                          | (n, argType) <- zip [1..] argTypes ] ++
                    -- enable triple
                    (case (en_type) of
                         Nothing -> []
                         (Just t) -> [(MethodEnable, t, True)]) ++
                    -- value triple
                    [(MethodResult n, t, False)
                        | (n, t) <- zip [1..] val_types ],
                -- uniquifiers for multiple ports
                -- (if only one copy, then the list just contains 0)
                ino <- map (toMaybe (mult > 1)) [ 0 .. (getMultUse (modId, methId) - 1) `max` 0 ],
                let uniqueId = (mkMethId modId methId ino meth_part)]

tieToZero :: (AId,AType,Bool) -> [ADef]
tieToZero (_,_,False) = []
tieToZero (aid,ty@ATBit{ atb_size= size} ,True) = [ADef{ adef_objid = aid,
                                                         adef_type = ty,
                                                         adef_expr = expr,
                                                         adef_props = []}]
    where expr = ASInt{ ae_objid = aid, ae_type = ty, ae_ival = if (size == 1) then (ilBin 0) else (ilHex 0)}
tieToZero x = internalError( "tieToZero: " ++ ppReadable x)

-- get the count of the method uses  key is Inst, method  data is count
genMethodMult :: AVInst -> [( (AId,AId), Integer)]
genMethodMult avinst = concatMap genMethMult vflds
    where instid = avi_vname avinst
          vmodi  = avi_vmi avinst
          vflds  = vFields vmodi
          --
          genMethMult :: VFieldInfo -> [( (AId,AId), Integer)]
          genMethMult vf@Method{} = [( (instid, vf_name vf) , vf_mult vf )]
          genMethMult _ = []

-- ---------------
isForeign :: AAction -> Bool
isForeign (AFCall { })      = True
isForeign (ATaskAction { }) = True
isForeign _                 = False


-- Create output ADefs from the Interface method
-- consider only value method returns and outputs of ActionValue methods
-- note that expressions are named according to the information on
-- the VFieldInfo
outputDefToADefs :: Bool -> [PProp] -> AIFace -> [ADef]
outputDefToADefs fmod pps (AIDef{aif_name=name, aif_value=def, aif_fieldinfo=fi}) = if convert then newdefs else []
    where resNames= mkNamedOutputs fi
          newdefs = outputADefToADefs def resNames
          convert = not (fmod && isRdyId name)
outputDefToADefs _ pps (AIActionValue{aif_name=name, aif_value=def, aif_fieldinfo=fi}) = newdefs
    where resNames= mkNamedOutputs fi
          newdefs  = outputADefToADefs def resNames
outputDefToADefs _ _ a@(AIAction{})       = []
outputDefToADefs _ _ a@(AIClock{})        = []
outputDefToADefs _ _ a@(AIReset{})        = []
outputDefToADefs _ _ a@(AIInout{})        = []

outputADefToADefs :: ADef -> [Id] -> [ADef]
outputADefToADefs (ADef { adef_type = ATTuple ts, adef_expr = ATuple _ es }) resNames =
    zipWith3 (\t e resName -> ADef { adef_objid = resName,
                                      adef_type  = t,
                                      adef_expr  = e,
                                      adef_props = [] })
            ts es resNames
outputADefToADefs (ADef { adef_type = t, adef_expr = e }) [resName] =
    [ADef { adef_objid = resName,
            adef_type  = t,
            adef_expr  = e,
            adef_props = [] }]
outputADefToADefs (ADef { adef_type = ATBit 0}) [] = []
outputADefToADefs def resNames =
    internalError $ "outputADefToADefs: unexpected ADef resNames: " ++ ppReadable (def, resNames)

getVInst :: AId -> [AVInst] -> AVInst
getVInst i as = head ( [ a | a <- as, i == (avi_vname a) ] ++
                      internalError ("getVInst " ++ ppString i))

getMethMult :: VModInfo -> AId -> Integer
getMethMult vi m = head (
        [ k | (Method { vf_name = m', vf_mult = k}) <- vFields vi,
                m == m' ] ++
          internalError ("getMethMult " ++ ppString (vi,m)))


-- ---------------
-- functions for making the signal info

mkSIClockTuple :: (PPrint a, PPrint b) => ([a], b) -> (a, [a])
mkSIClockTuple (clk:gates, _) = (clk, gates)
mkSIClockTuple x = internalError ("aState mkClockIds: " ++ ppReadable x)

mkSIMethodTuple :: AIFace -> [ASPMethodInfo]
mkSIMethodTuple (AIDef name args _ pred _ vfi _) =
   let  (res, rdy, _) = extractNames vfi
   in
    -- assume that method name is the return value Id
   [ASPMethodInfo{ aspm_name       = name,
                   aspm_type       = "value",
                   aspm_mrdyid     = Just rdy,
                   aspm_menableid  = Nothing,
                   aspm_resultids  = res,
                   aspm_inputs     = map fst args,
                   aspm_assocrules = [] }
   ]
mkSIMethodTuple (AIAction args _ pred name rs vfi) =
   let  (_, rdy, ena) = extractNames vfi
   in
   [ASPMethodInfo{ aspm_name       = name,
                   aspm_type       = "action",
                   aspm_mrdyid     = Just rdy,
                   aspm_menableid  = Just ena,
                   aspm_resultids  = [],
                   aspm_inputs     = map fst args,
                   aspm_assocrules = map aRuleName rs }
   ]
mkSIMethodTuple (AIActionValue args _ pred name rs _ vfi) =
   let  (res, rdy, ena) = extractNames vfi
   in
   [ASPMethodInfo{ aspm_name       = name,
                   aspm_type       = "actionvalue",
                   aspm_mrdyid     = Just rdy,
                   aspm_menableid  = Just ena,
                   aspm_resultids  = res,
                   aspm_inputs     = map fst args,
                   aspm_assocrules = map aRuleName rs }
   ]
mkSIMethodTuple (AIClock {}) = []
mkSIMethodTuple (AIReset {}) = []
mkSIMethodTuple (AIInout {}) = []


-- Most of this function is a hack to clean up the ready signals so they can be
-- grouped with the its real method in the output Verilog
mkSignalInfoMethod :: [AIFace] ->  [ASPMethodInfo]
mkSignalInfoMethod aifaces = merged
    where group = concatMap mkSIMethodTuple aifaces
          sgroup = groupBy eqaspm group
          merged = concatMap  mergePorts sgroup
          --
          --
          eqaspm :: ASPMethodInfo -> ASPMethodInfo -> Bool
          eqaspm a b = (toRdy $ aspm_name a) ==  (toRdy $ aspm_name b)
          --
          toRdy :: AId -> AId
          toRdy idin = if (isRdyId idin) then idin else mkRdyId idin
          --
          -- mergePort cleans up from the separate ready methods.
          mergePorts ::  [ASPMethodInfo] -> [ASPMethodInfo]
          mergePorts [] = []
          mergePorts [a] = [a]
          mergePorts [a, b] = [res]
              where res = case (isRdyId (aspm_name a), isRdyId (aspm_name b)) of
                          (True, False) -> b { aspm_mrdyid = listToMaybe (aspm_resultids a) }
                          (False, True) -> a { aspm_mrdyid = listToMaybe (aspm_resultids b) }
                          _ -> internalError( "mergePorts" ++ ppReadable (a,b) )
          mergePorts x = internalError( "mergePorts2:" ++ ppReadable x )


-- ==============================
-- Function: ratToBlobs
--

-- Produces two lists of MethBlob that will be used in various ways
-- in aState (mkEmuxss, mkEnabless, mkIdGuardss, for example),
-- given a method-use map and a resource allocation table.
--
-- The first list ("es") is expression uses.
-- The second list ("as") is action uses.

ratToBlobs :: MethodUsesMap -> M.Map (AId, AId) Integer -> RAT -> ([MethBlob], [MethBlob])
ratToBlobs mMap omMultMap rat =
  let
      -- True if there are 2 or more uses of the method,
      -- which means we need to do some sort of muxing
      nonTrivial :: MethBlob -> Bool
      nonTrivial (_, (((AMethCall _ _ _ _, _) : _) : _)) = True
      nonTrivial _ = False

      -- Create the MethBlobs and partition into expr and action
      (es, as) = partition fst $ map (mkBlob mMap omMultMap) $ ratToNestedLists rat
  in
      -- filter out the expr uses which don't need muxing
      (filter nonTrivial (map snd es), map snd as)


-- Given the method use map and an element from the RAT, produce a
-- pair (Bool,MethBlob) where the Bool is True if the method use is an
-- expression and False if it is an action
mkBlob :: MethodUsesMap -> M.Map (AId, AId) Integer -> (MethodId, [(UniqueUse, Integer)]) ->
          (Bool, MethBlob)
mkBlob mMap omMultMap (method@(MethodId obj met), usedPorts) =
  let
      -- We will use information for this method from both the
      -- MethodUsesMap and the RAT, so prepare an error in case
      -- the two are inconsistent:
      lookupErr m = internalError ("AState: RAT inconsistent with UseMap " ++
                                   ppReadable m)

      -- is a method mult-ported?
      multFlag =  case M.lookup (obj, met) omMultMap of
                    Nothing -> internalError ("Method without multiplicity " ++
                                              ppReadable (obj,met))
                    Just mult -> mult > 1

      -- ---------------
      -- Prepare the (per-port) info for this method from RAT

      -- List of uses per port.
      -- Create the mapping (port_num, [uses]) -- the inverse of the
      -- mapping "usedPorts" found in RAT, which is a list of pairs
      -- that map uses to ports.  Then strip out just the [uses].
      portUses :: [[UniqueUse]]
      portUses = M.elems $
                     -- use "flip" to preserve the order of uses?
                     M.fromListWith (flip (++))
                               [(port, [uUse]) | (uUse,port) <- usedPorts]

      -- ---------------
      -- Prepare the info for this method from MethodUsesMap

      -- List of unique expressions for calling this method
      -- and the rules which use those expressions
      -- (separated into those using it in the predicate, and those
      -- using it in the action)
      -- XXX calling useDropCond here because we still do
      -- condition insensitive resource allocation
      -- so the RAT has uses without their conditions (see RSchedule.hs)
      methodUses :: [(UniqueUse, MethodUsers)]
      methodUses = case (M.lookup method mMap) of
                       Just mUse -> mapFst useDropCond mUse
                       Nothing -> lookupErr method

      -- ---------------
      -- Convert a UniqueUse into an element of MethPortBlob

      -- Given a use from RAT (from portUses), create a pair of
      -- the use and (Just rs) if it is used only in the action of rules
      -- or Nothing if it is used in the predicate of any rules.
      -- (The UniqueUse in this pair will eventually be converted with
      -- "exp" to create an element of the MethPortBlob list.  We don't
      -- finish the conversion here, because the UU is needed to
      -- to determine the expr/action boolean with "uExp".)
      cvt :: UniqueUse -> (UniqueUse, Maybe [ARuleId])
      cvt use = case (lookup use methodUses) of
                    Just ([],rs,[]) -> (use, Just rs)
                    -- pred uses and inst uses must always be available
                    -- (no muxing)
                    Just (ps,_,is)  -> (use, Nothing)
                    Nothing         -> lookupErr use

      -- Convert a UniqueUse into an AExpr for use in MethPortBlob
      -- (For actions, the first argument is the condition, so remove it)
      exp :: UniqueUse -> AExpr
      exp (UUExpr e _) = e
      exp (UUAction (ACall o m es)) = AMethCall aTAction o m es
      exp (UUAction (AFCall i f isC es isA)) = AFunCall aTAction i f isC es
      -- XXX think this is just used for expression muxing
      exp (UUAction (ATaskAction i f isC n es tid tty isA)) =
          AFunCall aTAction i f isC es

      -- ---------------
      -- Make the MethodBlob

      -- The list of converted uses per port
      -- (This intermediate step is exposed to make "u" available to "uExp".)
      uses = map (map cvt) portUses
      u = case uses of
            (((uu, _):_):_) -> uu
            _ -> internalError "AState.mkBlob: u"

      -- Complete the conversion to make a list of MethPortBlob
      meth_port_blobs :: [MethPortBlob]
      meth_port_blobs = map (mapFst exp) uses

      -- The complete MethBlob structure
      meth_blob = (((obj, met), multFlag), meth_port_blobs)

      -- ---------------
      -- Make the Expr/Action boolean for partitioning

      -- True if the use is an expression, False if it's an action
      -- (used to filter out the expression uses from action uses)
      uExp :: UniqueUse -> Bool
      uExp (UUExpr _ _) = True
      uExp _ = False

  in
      -- return the pair, where the first elem is a boolean for filtering
      -- exprs from actions, and the second elem is the MethBlob for this
      -- method
      (uExp u, meth_blob)

-- ==============================
-- Function: mkEmuxss
--

-- When several rules write to the same register (for example), we
-- have to mux the value.  Because of sequential composition, several
-- rules may be trying to write at the same time, and we emulate
-- sequential composition by allowing the last rule to write its
-- value.  To do this, we can generate a priority mux, but we can do
-- better when some of the rules are known to be mutually exclusive.
-- This function is producing these muxes.
--
-- The functions mkEmuxssExpr and mkEmuxssAction simplify the interface
-- for the user, so that mkEmuxss doesn't need to be called directly.
--
-- Inputs:
--  * rdb = database of rule disjointness (exclusion) information
--  * Two functions for extracting the arguments and execution condition.
--    Remember that for actions, the first element is actually the
--    no-split condition, and the rest are the arguments. Thus:
--      tl = func for getting arg expressions from the expr list
--           (use "tail" for actions and "id" for defs)
--      cnd = func for getting the condition expr from the expr list
--            (use "head" for actions and "const aTrue" for defs")
--            XXX see comment on Bug 37 below
--  * value_method_ids = list of ifc value methods
--    (which mux based on RDY signal instead of the WILL_FIRE)
--  * om = rule ordering map in earliness order
--         (maps a rule Id to its numeric position in the order)
--  * MethBlob ((o,m),emrss) = method blob to create muxes for
--
-- Output:
--  * a list of new selector defs to add to the package
--  * a list of new value defs to add to the package
--  * a list of new mux output defs to add to the package
--  * an expression substitution to replace old expressions with uses
--    of the new definitions

mkEmuxss :: ([AExpr] -> [AExpr]) -> ([AExpr] -> AExpr) ->
            ExclusiveRulesDB -> [AId] -> OrderMap -> MethBlob ->
            ([ADef], [ADef], [ADef], AExprSubst)
mkEmuxss tl cnd rdb value_method_ids om (((o, m), f), emrss) =
    let genfunct = mkEmuxs tl cnd rdb value_method_ids om o m
        (sel_dss, val_dss, out_dss, sss) = unzip4 (zipWith genfunct (map (toMaybe f) [0..]) emrss)
    in  (concat sel_dss, concat val_dss, concat out_dss, concat sss)

-- XXX The "const aTrue" suggests that the use is unconditional.
-- XXX This assumption might change some if we fix Bug 37 with
-- XXX conditional def/use analysis.
mkEmuxssExpr :: ExclusiveRulesDB -> [AId] -> OrderMap -> MethBlob
             -> ([ADef], [ADef], [ADef], AExprSubst)
mkEmuxssExpr = mkEmuxss id (const aTrue)

mkEmuxssAction :: ExclusiveRulesDB -> [AId] -> OrderMap -> MethBlob
               -> ([ADef], [ADef], [ADef], AExprSubst)
mkEmuxssAction = mkEmuxss tail head

-- ---------------

-- This function produces a set of muxes per port
-- (that is, per copy of the method on a single state instance)

mkEmuxs :: ([AExpr] -> [AExpr]) -> ([AExpr] -> AExpr) ->
           ExclusiveRulesDB -> [AId] -> OrderMap ->
           AId -> AId -> Maybe Integer -> MethPortBlob ->
           ([ADef], [ADef], [ADef], AExprSubst)
mkEmuxs tl cnd rdb value_method_ids om o m ino emrs =
    let
        -- Break each MethPortBlob into a list of the expressions for
        -- each argument, and then transpose the entire structure to
        -- make a list of, for each argument, a list of the different
        -- expressions used by the different uses for that argument
        arg_blobs = transpose [ [ (e, (cnd es), rs) | e <- tl es ] |
                                    (AMethCall _ _ _ es, rs) <- emrs]

        -- Call mkEmux once for each argument of the method, giving it
        -- the list of different expressions for that argument, to
        -- separately mux the values for each argument.
        -- The result is new defs for the connections to the mux.
        def_tuples = zipWith (mkEmux rdb value_method_ids om ino o m)
                         [1..] arg_blobs
        (sel_defs, val_defs, out_defs) = concatUnzip3 def_tuples

        mkPortSubsts (e, _) =
            case aType e of
                ATTuple ats ->
                    [ (ATupleSel at e idx,
                       ASPort at $ mkMethId o m ino $ MethodResult idx)
                    | (idx, at) <- zip [1..] ats ]
                at -> [ (e, ASPort at $ mkMethId o m ino $ MethodResult 1) ]

        -- Replace the method call with the output port of the method
        subst = concatMap mkPortSubsts emrs
    in
        -- traces ("mkEmuxs " ++ ppReadable emrs ++ ppReadable xs) $
        (sel_defs, val_defs, out_defs, subst)


-- ---------------

-- This function does the actual work.  It considers the muxing of
-- values for one argument of the method at a time.
-- Inputs:
--  * ino = the number of the port being arbitrated for
--  * o = the instance name
--  * m = the method name
--  * ano = the number of the argument whose values are being muxed
--  * a list of triples for each unique use's value for this argument:
--     * the expression for the value
--     * the condition of the expression argument (for the sel signal)
--     * the rules that that use that expression argument
--  * value_method_ids = list of ifc value methods
--    (which mux based on RDY signal instead of the WILL_FIRE)
-- Output:
--  * A list of new definitions for selector signals into the mux
--  * A list of new definitions for the values to be selected in the mux
--  * The definition for the output of the mux
--
mkEmux :: ExclusiveRulesDB -> [AId] -> OrderMap ->
          Maybe Integer -> AId -> AId -> Integer ->
          [(AExpr, AExpr, Maybe [ARuleId])] -> ([ADef], [ADef], [ADef])
mkEmux exclusive_rules_db value_method_ids om ino o m ano [(e, _, _)] =
    -- Only one input to the mux
    ([], [], [ ADef (argId ino o m ano) (aType e) e [] ])
mkEmux exclusive_rules_db value_method_ids om ino o m ano ers@((e,_,_):_) =
    -- Multiple inputs
    let
        -- ---------------
        -- Determine if we need a PrimMux or PrimPriMux

        -- should we use a PrimPriMux?
        -- Old decision: If any rule Id is not in the order map, then it
        --   must be a read method, and we can assume that the scheduler
        --   has taken care to only enable one unique use at a time, so
        --   PrimMux is sufficient.  For all other cases (rules and
        --   action methods), use PrimPriMux.
        -- New decision: We can do better for rules and action methods by
        --   only using PrimPriMux when some of the rules are not disjoint.
        --   (If exclusive_rules_db says all the rules are disjoint, no pri
        --   mux is needed.)  Note that we even do this check for read
        --   methods (to be safe), even though we could have continued to
        --   use the same assumption as in the "old decision".
        -- In both cases: We assume that predicate uses can be ignored,
        --   by matching "(_,_,Just rs)".  If we ever support multiple
        --   predicate uses (due to urgency) we will need to fix this.
        usePri :: Bool
        --usePri = and [ M.lookup r om /= Nothing |
        --               (_, _, Just rs) <- ers, r <- rs ]
        usePri = let rs  = concat [rs | (_, _, Just rs) <- ers]
                     val = not (and
                                [areRulesExclusive exclusive_rules_db r r'
                                 | r <- rs, r' <- rs , r /= r'])
                 in  val

        -- ---------------
        -- Functions to make selector Ids

        selId s =
            mkIdPre fsMux
                (mkIdPost i (concatFString [fsUnderUnder, fsMuxSel, s]))

        preSelId s =
            mkIdPre fsMux
                (mkIdPost i (concatFString [fsUnderUnder, fsMuxPreSel, s]))

        -- ---------------
        -- Functions to make value Ids

        valId s =
            mkIdPre fsMux
                (mkIdPost i (concatFString [fsUnderUnder, fsMuxVal, s]))

        -- ---------------
        -- Function to make control signal Id
        -- (WILL_FIRE for rule or action method, RDY for read method)

        isReadMethod rId = elem rId value_method_ids

        willfireId rId = if (isReadMethod rId)
                         then aRdyId rId
                         else aWillFireId rId

        -- produce the uniquifier for mux selector Ids
        -- Here we just add _#, but we could include the rules for
        -- the selector in its name, or even just include one name
        -- when it's only one rule.  for brevity, we just use _#
        use2suffix :: Integer -> Maybe [Id] -> FString
        use2suffix n _ = mkFString ("_" ++ itos n)

        -- ---------------
        -- Function to make the arguments to the selector primitive

        -- For each arg blob, two AExprs are created: One of type Bool
        -- which refers to the control signal for the arg, and one
        -- which is the expression for the argument (here, "e").
        -- The control signal is just a references to a definition,
        -- which will be created by mkSel (see below).

        -- return a list of the selector expr and the return expr, and
        -- any new defs (because we want to give the return expr a name)

        mkArg :: (Integer, (AExpr, AExpr, Maybe [ARuleId])) ->
                 ([AExpr], [ADef])
        mkArg (n, (e, _, mrs)) =
            let suffix = use2suffix n mrs
                val_type = ae_type e
                val_id = valId suffix
                props = case mrs of
                  Nothing -> []
                  Just rs -> map DefP_Rule rs
            in
                ([ASDef aTBool (selId suffix),
                  ASDef val_type val_id],
                 [ADef val_id val_type e props])

        -- ---------------
        -- Function to make the definitions for the control signals
        mkSel :: (Integer, (AExpr, AExpr, Maybe [ARuleId])) -> [ADef]
        mkSel (n, (_, c, Just rs)) =
          let suffix = use2suffix n (Just rs)
              props :: [DefProp]
              props = map DefP_Rule rs -- record the source rule
          in
              if isTrue c then
                 [ADef (selId suffix) aTBool (aOrs (map willfireId rs))
                  props
                 ]
               else

                 -- if there is a non-split condition, create a
                 -- pre-selector signal which is the OR of the WFs,
                 -- and the selector will be the presel AND the cond
                 [ADef (preSelId suffix) aTBool (aOrs (map willfireId rs)) props,
                  ADef (selId suffix) aTBool
                           (aAnd (ASDef aTBool (preSelId suffix)) c) props]
        -- only one input to the mux was handled by the first case of mkEmux
        mkSel x = internalError ("mkSel, match failed: " ++ ppReadable x)

        -- ---------------
        -- Function to put the muxed arguments in priority order
        -- (if we make a PrimPriMux, it will expect arguments in pri order)

        -- If an arm is found to be used by multiple rules, then we need
        -- to separate it into different arms, so that each rule's arm
        -- can be put at the appropriate place in the priority.

        order uses = let sep_numbered_uses =
                             [ (num, (val, cond, Just [r]))
                                 | (val, cond, Just rs) <- uses,
                                   r <- rs,
                                   let num = mlookup r om ]
                     in  map snd $
                         sortBy (\ (x, _) (y, _) -> compare x y)
                             sep_numbered_uses

        -- ---------------
        -- Put it all together

        -- The type of the muxed value, for use in creating the new Defs
        t = aType e

        -- The arg blobs, numbered, and in priority order if necessary
        ers' = zip [1..] $ if usePri
                           then order ers
                           else ers

        -- PrimMux takes a list of pairs of the selector ASDef and the
        -- expr that should result
        -- mux_pairs = the pairs, val_defs = the new Id defs for the vals
        (mux_pairs, val_defs) = concatUnzipMap mkArg ers'
        default_pair = mkDefaultPair t mux_pairs
        -- The new Id defs for the mux selector control signals
        sel_defs = concatMap mkSel ers'

        -- The Id of this argument
        i = argId ino o m ano

        -- The new def for the result of the mux
        -- default_pair is an explicit default conditions for the mux ASAny
        out_def :: ADef
        out_def = ADef i t (APrim i t
                               (if usePri then PrimPriMux else PrimMux)
                               (mux_pairs ++ default_pair) ) []

        -- The uses used in predicates (should not be > 1)
        pred_uses = [ v | (v, _, Nothing) <- ers ]

    in  --traces ("mkEmux(1) " ++ ppReadable (ers, ers', t)) $
        --traces ("mkEmux(2) " ++ ppReadable (ers)) $
        --traces ("mkEmux(new_defs) " ++ ppReadable (new_defs)) $
        if (length pred_uses > 1)
        then internalError ("Multiple port use " ++
                            ppReadable (o, m, map fst3 ers))
        else (sel_defs, val_defs, [out_def])

mkEmux _ _ _ _ _ _ _ _ = internalError "mkEMux"

-- create a default expresson for a mux from the conditions
mkDefaultPair :: AType -> [AExpr] -> [AExpr]
mkDefaultPair t aexprs = [APrim  defaultAId (ATBit 1) PrimBNot [orCond] , ASAny t Nothing]
    where (conds,_) = unzip $ makePairs aexprs
          orCond = aOrs conds

-- ==============================
-- Function: mkEnabless
--

mkEnabless :: MethBlob -> [ADef]
mkEnabless (((o, m), f), emrss) = concat (zipWith (mkEnables o m) (map (toMaybe f) [0..]) emrss)

mkEnables :: AId -> AId -> Maybe Integer -> MethPortBlob -> [ADef]
mkEnables o m ino emrs =
        let mi = mkMethId o m ino MethodEnable
            (dss, ess) = unzip (zipWith mkE emrs [1..])
            mkE :: (AExpr, Maybe [ARuleId]) -> Integer -> ([ADef], [AExpr])
            mkE (AMethCall _ _ _ (ASInt _ _ (IntLit _ _ 1) : _), Just is) _ =
                ([], [ aWillFireId i | i <- is ])
            mkE (AMethCall _ _ _ (c : _), Just is) k =
              let ior  = mkIdPre (concatFString [mkFString astOrPref,
                                                 mkNumFString k]) mi
                  iand = mkIdPre (concatFString [mkFString astAndPref,
                                                 mkNumFString k]) mi
                  dor :: [ADef]
                  (dor, aor) =
                        case is of
                        [i] -> ([], aWillFireId i)
                        _ -> ([ADef ior aTBool
                               (aOrs [ aWillFireId i | i <- is ]) []],
                              ASDef aTBool ior)
                  dand :: ADef
                  dand = ADef iand aTBool (aAnd aor c) []
              in
                  (dor ++ [dand], [ASDef aTBool iand])
            mkE _ _ = ([], [])
        in case (concat dss, concat ess) of
            ([ADef i _ e p], [ASDef _ i']) | i == i' -> [ADef mi aTBool e p] -- pass on props?
            (ds, es)                               -> ds ++ [ADef mi aTBool (aOrs es) []]


-- ==============================
-- Function: mkIdGuardss
--

-- aState used to also return a structure called idGuards:
--   This is an ARsrcInfo containing, for each method, a triple of the name
--   of the method, the types of the arguments, and a list of WILL_FIRE_
--   signals which will be used in the muxes to the inputs of the method
--   (or OR'd together as the enable signal in the case of action methods?)
--   Note: This return value is only given to aVerilog, which doesn't use it!
--
--   idGuards = ARsrcInfo (concatMap mkIdGuardss ers ++
--                         concatMap mkIdGuardss ars)

{-
data ARsrcInfo = ARsrcInfo [(AId, [AType], [AId])]

instance PPrint ARsrcInfo where
     pPrint d p (ARsrcInfo info) = text "ARsrcInfo:" <+> pPrint d 0 info

mkIdGuardss :: MethBlob -> [(AId, [AType], [AId])]
mkIdGuardss ((o, m), emrss) = zipWith (mkIdGuards o m) [0..] emrss

mkIdGuards :: AId -> AId -> Integer -> MethPortBlob -> (AId, [AType], [AId])
mkIdGuards o m ino emrs@((AMethCall _ _ _ es,_):_) =
    (mkMethId o m ino MethodResult, map aType es,
     [ mkIdWillFire i | (_, Just is) <- emrs, i <- is ])
mkIdGuards _ _ _ exp = internalError $ "mkIdGuards: " ++ ppReadable exp
-}

-- ==============================
-- Helper functions
--

argId :: Maybe Integer -> Id -> Id -> Integer -> Id
argId ino o m ano = mkMethId o m ino (MethodArg ano)

aWillFireId :: AId -> AExpr
aWillFireId i = ASDef aTBool (mkIdWillFire i)

aRdyId :: AId -> AExpr
aRdyId i = ASDef aTBool (mkRdyId i)

-- ---------------

mlookup :: (Ord k, PPrint k, PPrint a) => k -> M.Map k a -> a
mlookup x m =
    case M.lookup x m of
    Just y -> y
    Nothing -> internalError ("mlookup " ++ ppReadable (x, M.toList m))


-- generate a list of alias which can be substituted out.
genAliases :: [ADef] -> [(AId,AExpr)]
genAliases adefs = [(deadid, ASDef t liveid) | (ADef deadid t (ASDef _ liveid) _) <- adefs ]

-- ==============================

-- ResetInfo lookup matches realResetWires
realResetPorts :: VModInfo -> Id -> [VArgInfo]
realResetPorts vmi rst =
  case (lookupInputResetWire rst vmi) of
     Nothing -> []
     Just rst_n ->
         -- We say that the port has no clock, since the info is not used.
         -- If we really needed it, we could lookup the clock and store it.
         [Port (rst_n, [VPreset]) Nothing Nothing]

-- ResetInfo lookup matches realResetPorts
realResetWires :: VModInfo -> Id -> AExpr -> [AExpr]
realResetWires vmi rst (ASReset _ (AReset { areset_wire = a_rst })) =
  case (lookupInputResetWire rst vmi) of
     Nothing -> []
     Just rst_n -> [a_rst]
realResetWires _ _ _ = internalError "AState.realResetWires: unhandled"

-- ClockInfo lookup matches realClockWires
realClockPorts :: VModInfo -> Id -> [VArgInfo]
realClockPorts vmi clk =
   case (lookupInputClockWires clk vmi) of
     Nothing                     -> []
     Just (osc, Nothing)         -> [Port (osc, [VPclock]) Nothing Nothing]
     Just (osc, Just gate_vname) -> [Port (osc, [VPclock]) Nothing Nothing,
                                     Port (gate_vname, [VPclockgate])
                                                           Nothing Nothing]

-- ClockInfo lookup matches realClockPorts
realClockWires :: VModInfo -> Id -> AExpr -> [AExpr]
realClockWires vmi clk (ASClock _ AClock {aclock_osc = a_osc, aclock_gate = a_gate}) =
   case (lookupInputClockWires clk vmi) of
      Nothing -> []
      Just (osc, Nothing) -> [a_osc]
      Just (osc, Just gate_vname) -> [a_osc, a_gate]
realClockWires _ _ _ = internalError "AState.realClockWires: unhandled"

rewireClockResetInout :: AVInst -> AVInst
rewireClockResetInout avi@(AVInst { avi_vmi = vi, avi_iargs = es }) =
    --traces ("rewire: " ++ show es ++ "\nrewire2: " ++ show es') $
    avi { avi_vmi = vi', avi_iargs = es' }
  where vi' = vi { vArgs = concatMap rewirePorts (vArgs vi) }
        -- XXX distinguish between clock and clock gate?
        rewirePorts :: VArgInfo -> [VArgInfo]
        rewirePorts (ClockArg id) = realClockPorts vi id
        rewirePorts (ResetArg id) = realResetPorts vi id
        rewirePorts (InoutArg vn mclk mrst) = realInoutPorts vn mclk mrst
        rewirePorts x = [x]
        es' = concatMap rewireArgs (zip (vArgs vi) es)
        rewireArgs :: (VArgInfo, AExpr) -> [AExpr]
        rewireArgs ((ClockArg id), e) = realClockWires vi id e
        rewireArgs ((ResetArg id), e) = realResetWires vi id e
        rewireArgs ((InoutArg {}), e) = realInoutWires e
        rewireArgs (_, e)             = [e]

-- InoutInfo lookup matches realInoutWires
realInoutPorts :: VName -> Maybe Id -> Maybe Id -> [VArgInfo]
realInoutPorts vn mclk mrst = [Port (vn, [VPinout]) mclk mrst]

-- InoutInfo lookup matches realInoutPorts
realInoutWires :: AExpr -> [AExpr]
realInoutWires (ASInout _ (AInout { ainout_wire = a_iot })) = [a_iot]
realInoutWires _ = internalError "AState.realInoutWires: unhandled"

-- ==============================

type VModInfoMap = M.Map AId VModInfo

mkOutputGatePort :: VModInfoMap -> AId -> AId -> AExpr
mkOutputGatePort vmi_map modId clkId =
    let lookupErr = internalError ("mkOutputGatePort: vmi not found: " ++
                                   ppReadable modId)
        vmi = M.findWithDefault lookupErr modId vmi_map
    in
        case (lookupOutputClockWires clkId vmi) of
            (i_osc, Nothing) ->
                internalError ("mkOutputGatePort: no gating signal " ++
                               ppReadable (modId, clkId))
            (i_osc, Just i_gate) -> mkOutputWire modId i_gate

-- ==============================
