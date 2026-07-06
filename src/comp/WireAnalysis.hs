-- Tcl-free analysis of an elaborated module's wires: build a
-- module-scope-relative {name, IType} list covering every wire in the
-- APackage we can assign a sensible source-level type to.  This module
-- defines the analysis; consumers (bluetcl's wiretypemap command)
-- convert the result to their own representation, the same division of
-- labor as TypeAnalysis and bluetcl's type commands.
--
-- Categories emitted:
--   * external port wires    (apkg_external_wire_types)
--   * input clock CLKs and gates  (Clock / Bool)
--   * input reset port wires (Reset)
--   * EN_<method> and RDY_<method>           (Bool)
--   * CAN_FIRE_RL_<rule> and WILL_FIRE_RL_<rule>  (Bool)
--   * submodule connection wires (avi_port_types)
--
-- For each submodule wire we emit every candidate name a VCD might use,
-- so a single map serves both Verilog and Bluesim correlation:
--   * inst$port   (Verilog flat, post-renameio)
--   * inst.port   (Bluesim scope-relative; correlator concatenates while
--                  descending into the sub-scope)
--   * inst        (Verilog reg-Q_OUT shortcut, when reg)
-- For CReg instances, the same candidates are also emitted after applying
-- cregToReg's port-name rewrite, so the Reg-converted Verilog names are
-- covered without depending on which flags were active at build time.
--
-- Over-emission is intentional: a correlator building a name -> type
-- dict can index by VCD wire name and match whichever form appears.
module WireAnalysis (getWireTypeMap) where

import Data.List(nub)
import qualified Data.Map as M

import Id(getIdString, mkRdyId, isRdyId, mkIdCanFire, mkIdWillFire)
import ISyntax(IType)
import ISyntaxUtil(itBool, itClock, itReset)
import ASyntax
import VModInfo
import BackendNamingConventions(isRegInst, isCRegInst, cregToReg,
                                qoutPortStr,
                                isRWire, isRWire0,
                                isBypassWire, isBypassWire0)

getWireTypeMap :: APackage -> [(String, IType)]
getWireTypeMap apkg =
    let wires = apkg_external_wires apkg
        ext_entries = [ mkEntry (getVNameString vn) t
                      | (vn, t) <- M.toList (apkg_external_wire_types apkg) ]
        clk_entries     = concatMap inClockEntries  (input_clocks  (wClk wires))
        outClk_entries  = concatMap outClockEntries (output_clocks (wClk wires))
        rst_entries     = concatMap inResetEntries  (input_resets  (wRst wires))
        outRst_entries  = concatMap outResetEntries (output_resets (wRst wires))
        ifc = apkg_interface apkg
        en_rdy_entries = concatMap methodEnRdyEntries ifc
        rule_entries = concatMap ruleFireEntries (apkg_rules apkg)
        sub_entries = concatMap submodEntries (apkg_state_instances apkg)
    in  nub $
        ext_entries
            ++ clk_entries ++ outClk_entries
            ++ rst_entries ++ outRst_entries
            ++ en_rdy_entries ++ rule_entries ++ sub_entries
  where
    mkEntry :: String -> IType -> (String, IType)
    mkEntry name t = (name, t)

    -- Input clock oscillator (Clock) and optional gate wire (Bool)
    inClockEntries (_, Nothing) = []
    inClockEntries (_, Just (osc, mgate)) =
        mkEntry (getVNameString osc) itClock :
        (case mgate of
            Right vn -> [mkEntry (getVNameString vn) itBool]
            Left _   -> [])

    -- Output clock oscillator (Clock) and optional gate VPort (Bool)
    outClockEntries (_, Nothing) = []
    outClockEntries (_, Just (osc, mgate)) =
        mkEntry (getVNameString osc) itClock :
        (case mgate of
            Just (vn, _) -> [mkEntry (getVNameString vn) itBool]
            Nothing      -> [])

    -- Input reset port wire (Reset)
    inResetEntries (_, (Just port, _)) =
        [mkEntry (getVNameString port) itReset]
    inResetEntries _ = []

    -- Output reset port wire (Reset)
    outResetEntries (_, (Just port, _)) =
        [mkEntry (getVNameString port) itReset]
    outResetEntries _ = []

    -- EN_<method> and RDY_<method> (both Bool). Skip AIFaces that are
    -- themselves RDY entries (they appear as separate AIFaces with
    -- names like RDY_foo, and applying mkRdyId to them would produce
    -- RDY_RDY_foo). RDY is always emitted for actual methods by
    -- canonical name, even for always_ready methods -- over-emission
    -- is fine; names that don't show up in any VCD just go unmatched.
    methodEnRdyEntries aif =
        case aif_fieldinfo aif of
            Method { vf_enable = mEn } | not (isRdyId (aif_name aif)) ->
                let nm = aif_name aif
                    en = case mEn of
                           Just (vn, _) -> [mkEntry (getVNameString vn) itBool]
                           Nothing      -> []
                    rdy = mkEntry (getIdString (mkRdyId nm)) itBool
                in  rdy : en
            _ -> []

    -- CAN_FIRE_RL_<rule> and WILL_FIRE_RL_<rule> (Bool). These signals
    -- may be optimized away by aOpt, but over-emission is harmless.
    ruleFireEntries r =
        let ri = arule_id r
        in  [ mkEntry (getIdString (mkIdCanFire ri))  itBool
            , mkEntry (getIdString (mkIdWillFire ri)) itBool ]

    submodEntries avi =
        candidateNames avi ++
        (if isCRegInst avi then candidateNames (cregToReg avi) else []) ++
        cregInlinedCandidates avi ++
        inlinedWireCandidates avi ++
        probeCandidates avi ++
        counterCandidates avi ++
        submodClockResetCandidates avi

    -- For each submodule instance, emit candidate names for the
    -- wires connecting parent's clocks/resets to the submodule's
    -- clock/reset ports. Both Verilog flat (<inst>$<port>) and
    -- Bluesim scope-relative (<inst>.<port>) forms. Covers:
    --   * input clocks  -- oscillator (Clock) and optional gate (Bool)
    --   * output clocks -- oscillator and optional gate (same)
    --   * input resets  -- port wire (Reset)
    --   * output resets -- port wire (Reset)
    -- Without these, a submodule like mkBRAM2 (two clock ports CLKA
    -- and CLKB) or mkSyncFIFO (separate source/dest clocks and resets)
    -- would have its clock/reset connection wires show up as misses
    -- in the correlation, even though we know they're Clock/Reset.
    submodClockResetCandidates avi =
        let inst_str = getIdString (avi_vname avi)
            vmi     = avi_vmi avi
            emit vn t = [ mkEntry (inst_str ++ "$" ++ getVNameString vn) t
                        , mkEntry (inst_str ++ "." ++ getVNameString vn) t ]
            -- input clocks: (Id, Maybe (VOscPort, VInputGatePort))
            inClk (_, Nothing) = []
            inClk (_, Just (osc, mgate)) =
                emit osc itClock ++
                (case mgate of
                    Right vn -> emit vn itBool
                    Left _   -> [])
            -- output clocks: (Id, Maybe (VOscPort, VOutputGatePort))
            outClk (_, Nothing) = []
            outClk (_, Just (osc, mgate)) =
                emit osc itClock ++
                (case mgate of
                    Just (vn, _) -> emit vn itBool
                    Nothing      -> [])
            -- resets: (Id, (Maybe VName, Maybe Id))
            rst (_, (Just vn, _)) = emit vn itReset
            rst _                 = []
        in  concatMap inClk  (input_clocks  (vClk vmi)) ++
            concatMap outClk (output_clocks (vClk vmi)) ++
            concatMap rst    (input_resets  (vRst vmi)) ++
            concatMap rst    (output_resets (vRst vmi))

    candidateNames avi =
        let inst_str = getIdString (avi_vname avi)
            isReg = isRegInst avi
            mkCandidates (vn, t) =
                let port_str = getVNameString vn
                    verilog_flat = mkEntry (inst_str ++ "$" ++ port_str) t
                    bluesim_form = mkEntry (inst_str ++ "." ++ port_str) t
                    reg_shortcut = if isReg && port_str == qoutPortStr
                                   then [mkEntry inst_str t]
                                   else []
                in  [verilog_flat, bluesim_form] ++ reg_shortcut
        in  concatMap mkCandidates (M.toList (avi_port_types avi))

    -- When aInlineWires removes an RWire/BypassWire AVInst, the wires
    -- that remain in the post-renameio Verilog are <inst>$wget (data,
    -- typed) and <inst>$whas (Bool). Emit these as candidates so the
    -- VCD correlator picks them up. Bluesim doesn't inline wires
    -- (simExpand reads APackage directly), so the .wget/.whas forms
    -- are over-emitted there -- harmless.
    inlinedWireCandidates avi
        | isRWire avi || isBypassWire avi
          || isRWire0 avi || isBypassWire0 avi =
            let inst_str = getIdString (avi_vname avi)
                pts = avi_port_types avi
                -- Pull the surviving wires' types directly from the
                -- primitive's port map. WGET (or its WSET arg) holds the
                -- source-level data type; WHAS holds Bool. Variants that
                -- don't have a given port (RWire0 has no wget,
                -- BypassWire has no whas) simply have no entry to find,
                -- so they emit nothing.
                wgetEntries =
                    case M.lookup (VName "WGET") pts of
                        Just t -> [ mkEntry (inst_str ++ "$wget") t
                                  , mkEntry (inst_str ++ ".wget") t ]
                        Nothing -> []
                whasEntries =
                    case M.lookup (VName "WHAS") pts of
                        Just t -> [ mkEntry (inst_str ++ "$whas") t
                                  , mkEntry (inst_str ++ ".whas") t ]
                        Nothing -> []
                -- Bluesim VCDs always label the surviving wire as just
                -- the bare instance name (bs_prim_mod_wire.h emits one
                -- $var named inst_name unconditionally, mirroring the
                -- register Q_OUT shortcut). For RWire/BypassWire the
                -- bare wire carries the data type (WGET); for
                -- RWire0/PulseWire it carries whas (Bool); for
                -- BypassWire0 -- which has neither WGET nor WHAS in
                -- avi_port_types because both are constant -- Bluesim
                -- still dumps a 1-bit "always 1" wire, so we hardcode
                -- itBool for that case. Verilog disallows port/instance
                -- name collisions, so this can't shadow a real port.
                bareEntry =
                    case M.lookup (VName "WGET") pts of
                        Just t -> [ mkEntry inst_str t ]
                        Nothing -> case M.lookup (VName "WHAS") pts of
                            Just t -> [ mkEntry inst_str t ]
                            Nothing -> [ mkEntry inst_str itBool ]
            in  wgetEntries ++ whasEntries ++ bareEntry
        | otherwise = []

    -- aInlineCReg creates intermediate wires for each CReg port:
    --   <inst>$port<n>__read     -- read result, data-typed
    --   <inst>$port<n>__write_1  -- write argument, data-typed
    --   <inst>$EN_port<n>__write -- write enable, Bool
    -- bsc always uses a 5-port CRegN5 primitive even for smaller CRegs,
    -- so emit 5 ports' worth of candidates. With -keep-inlined-boundaries
    -- these survive in the Verilog output and appear in the VCD; without
    -- the flag they may be folded by the optimizer.
    cregInlinedCandidates avi
        | isCRegInst avi =
            let inst_str = getIdString (avi_vname avi)
                -- pull the data type from the converted Reg AVInst
                dataType = M.lookup (VName "Q_OUT")
                                    (avi_port_types (cregToReg avi))
            in  case dataType of
                  Just t ->
                      concatMap (\n ->
                        let p = show n
                        in  [ mkEntry (inst_str ++ "$port" ++ p ++ "__read") t
                            , mkEntry (inst_str ++ "$port" ++ p ++ "__write_1") t
                            , mkEntry (inst_str ++ "$EN_port" ++ p ++ "__write") itBool
                            ]) [(0::Int)..4]
                  Nothing -> []
        | otherwise = []

    -- Counter primitives: Bluesim's dump_VCD_defs emits the bare
    -- instance name at the parent scope (carrying the data value),
    -- mirroring the register Q_OUT shortcut. Inside the counter's
    -- sub-scope it also emits `q_state` as an alias of Q_OUT. The
    -- standard candidateNames path already covers `inst.Q_OUT`,
    -- `inst$Q_OUT`, etc.; we just need the bare-name and q_state
    -- forms here. See bs_prim_mod_counter.h.
    counterCandidates avi
        | vName (avi_vmi avi) == VName "Counter" =
            case M.lookup (VName "Q_OUT") (avi_port_types avi) of
                Just t ->
                    let inst_str = getIdString (avi_vname avi)
                    in  [ mkEntry inst_str t
                        , mkEntry (inst_str ++ ".q_state") t ]
                Nothing -> []
        | otherwise = []

    -- Probe primitives don't generate a real submodule instance --
    -- bsc inlines them as wire pairs in the parent module. Both
    -- backends use the same naming convention at the parent scope:
    --   <inst>$PROBE       -- the probed data value
    --   <inst>$PROBE_VALID -- Bool, asserted when the probe is written
    --                        (Verilog only; Bluesim emits just $PROBE
    --                         and folds validity into the dump policy)
    -- See bs_prim_mod_probe.h for Bluesim, and the inlined wire decls
    -- in the generated Verilog for the Verilog convention. There is
    -- no scope-relative `.PROBE` form -- the `$PROBE` suffix is part
    -- of the wire name, not a scope separator.
    probeCandidates avi
        | vName (avi_vmi avi) == VName "Probe" =
            let inst_str = getIdString (avi_vname avi)
                validEntry = mkEntry (inst_str ++ "$PROBE_VALID") itBool
            in  case M.lookup (VName "IN") (avi_port_types avi) of
                    Just t  -> [ mkEntry (inst_str ++ "$PROBE") t
                               , validEntry ]
                    Nothing -> [ validEntry ]
        | otherwise = []
