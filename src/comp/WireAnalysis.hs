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
module WireAnalysis (getWireTypeMap, getWireTypeCandidates,
                     getFinalWireTypeCandidates) where

import qualified Data.Map as M
import qualified Data.Map.Strict as MS
import qualified Data.Set as S
import Util(stableOrdNub)

import Id(getIdString, unQualId, mkRdyId, isRdyId, mkIdCanFire, mkIdWillFire)
import ISyntax(IType(..))
import ISyntaxUtil(itBool, itClock, itReset, itBit)
import ASyntax
import ASourceTypes(canonicalSourceExpr, namedSourceTypes)
import VModInfo
import BackendNamingConventions(isRegInst, isCRegInst, cregToReg,
                                qoutPortStr,
                                isRWire, isRWire0,
                                isBypassWire, isBypassWire0)

-- Existing consumers expect one interpretation per wire. Keep declared source
-- types, refine a bare Bit type only when the evidence is unambiguous, and add
-- new internal wires only when there is a single observed interpretation.
getWireTypeMap :: APackage -> [(String, IType)]
getWireTypeMap apkg =
    let declared = namedDeclaredWireTypeMap apkg
        known = MS.fromListWith S.union [(n, S.singleton t) | (n,t) <- declared]
        inferred = observedWireTypes apkg
        choices n = S.filter (not . isBitType) $
            M.findWithDefault S.empty n known `S.union`
            M.findWithDefault S.empty n inferred
        refine (n,t) = case S.toList (choices n) of
                         [t'] | isBitType t, M.member n inferred -> (n,t')
                         _ -> (n,t)
        extra = [(n,t) | (n,ts) <- M.toList inferred, M.notMember n known,
                         [t] <- [S.toList ts]]
    in stableOrdNub (map refine declared ++ extra)

-- Unlike wiretypemap, this query represents ambiguity explicitly. A CSE'd
-- expression can be unpacked at several unrelated nominal source types.
getWireTypeCandidates :: APackage -> [(String, [IType])]
getWireTypeCandidates apkg = M.toList $ M.map S.toList $
    MS.unionWith S.union (observedWireTypes apkg)
        (MS.fromListWith S.union [(n,S.singleton t) |
                                 (n,t) <- namedDeclaredWireTypeMap apkg])

isBitType :: IType -> Bool
isBitType (ITAp t _) = t == itBit
isBitType _ = False

-- Index all aliases of an expression once, then join type observations to
-- those names. Only actual definitions and named boundary wires are emitted;
-- metadata expressions do not manufacture wires in the generated netlist.
observedWireTypes :: APackage -> M.Map String (S.Set IType)
observedWireTypes apkg = MS.unionWith S.union boundary mapped
  where
    -- Once the backend has supplied physical candidates, raw observations
    -- are needed only for safe declared boundary aliases (e.g. Bluesim names).
    -- Restrict the join itself so it does not construct discarded internals.
    wanted = case apkg_final_wire_types apkg of
        Just _ -> Just (S.filter safeAlias declaredNames)
        Nothing -> Nothing
    raw = sourceObservedWireTypes wanted apkg
    declaredNames = S.fromList (map fst (declaredWireTypeMap apkg))
    -- Established boundary aliases are useful for both Verilog and Bluesim.
    -- Internal observations require a binding to an emitted signal: retaining
    -- the old name can silently alias a DIFFERENT wire after stable renaming.
    boundary = M.filterWithKey (\n _ -> n `S.member` declaredNames && safeAlias n) raw
    safeAlias = case apkg_final_wire_names apkg of
        Nothing -> const True
        Just names -> let emitted = S.fromList (M.elems names)
                      in case apkg_final_wire_types apkg of
                           Just _ -> (`S.notMember` emitted)
                           Nothing -> \n -> n `S.notMember` emitted || M.lookup n names == Just n
    mapped = case apkg_final_wire_types apkg of
        Just ts -> ts
        Nothing -> case apkg_final_wire_names apkg of
            -- Preserve the upstream pre-codegen/Bluesim query fallback.
            Nothing -> raw
            Just names -> MS.fromListWith S.union
                [(final, ts) | (n, ts) <- M.toList raw,
                               Just final <- [M.lookup n names]]

-- Capture the backend's actual expression aliases after optimization. The
-- emitted-name map both proves liveness and applies final Verilog renaming.
getFinalWireTypeCandidates :: M.Map String String -> ASPackage -> M.Map String (S.Set IType)
getFinalWireTypeCandidates names pkg = MS.fromListWith S.union
    [(final, ts) | (name, ts0) <- M.toList observed,
                   let ts = S.filter (not . isBitType) ts0,
                   not (S.null ts), Just final <- [M.lookup name names]]
  where observed = namedSourceTypes (aspkg_values pkg ++ aspkg_inout_values pkg)
                                   (aspkg_expr_types pkg)

-- Keep the declared map's existing aliases, and add their physical spelling
-- when codegen renamed them (including collision-aware dollar removal).
namedDeclaredWireTypeMap :: APackage -> [(String, IType)]
namedDeclaredWireTypeMap apkg = stableOrdNub (declared ++ renamed)
  where
    declared = declaredWireTypeMap apkg
    renamed = case apkg_final_wire_names apkg of
        Nothing -> []
        Just names -> [(final, t) | (n,t) <- declared,
                                   Just final <- [M.lookup n names], final /= n]

sourceObservedWireTypes :: Maybe (S.Set String) -> APackage -> M.Map String (S.Set IType)
sourceObservedWireTypes (Just wanted) _ | S.null wanted = M.empty
sourceObservedWireTypes wanted apkg = MS.fromListWith S.union
    [(name, ts) | (e,ts) <- M.toList observed,
                  name <- S.toList (names e)]
  where
    -- CSE and retained anchors can observe the same expression through many
    -- aliases. Union those interpretations before expanding its names: doing
    -- that expansion per observation generates a quadratic number of repeated
    -- (name, type-set) pairs when there are many aliases of one value.
    observed = MS.fromListWith S.union
        [(canonical e, ts) | (e,ts0) <- apkg_expr_types apkg,
                             let ts = S.filter (not . isBitType) ts0,
                             not (S.null ts)]
    ifcDefs = [(d, fi) | AIDef { aif_value = d, aif_fieldinfo = fi } <- apkg_interface apkg] ++
              [(d, fi) | AIActionValue { aif_value = d, aif_fieldinfo = fi } <- apkg_interface apkg]
    -- A method result can be split across several physical ports. Match
    -- each element to its own port; the aggregate method is not a wire.
    outputDefs (ADef _ (ATTuple ts) (ATuple _ es) _, fi) =
        zipWith3 (\i t e -> ADef i t e []) (mkNamedOutputs fi) ts es
    outputDefs (ADef _ t e _, fi) =
        [ADef i t e [] | [i] <- [mkNamedOutputs fi]]
    namedDefs = apkg_local_defs apkg ++ concatMap outputDefs ifcDefs
    defs = namedDefs ++ map fst ifcDefs
    canonical = canonicalSourceExpr defs
    nameIndex = MS.fromListWith S.union
        [(canonical (ASDef t i), S.singleton name) |
          ADef i t _ _ <- namedDefs, let name = getIdString i, wantedName name]
    wantedName n = maybe True (S.member n) wanted
    names e = M.findWithDefault S.empty e nameIndex `S.union`
              S.filter wantedName (leafNames e)
    leafNames (ASPort _ i) = S.singleton (getIdString i)
    leafNames (AMethValue _ i m) = methodNames i m Nothing
    leafNames (AMethCall _ i m []) = methodNames i m Nothing
    leafNames (ATupleSel _ (AMethValue _ i m) idx) = methodNames i m (Just idx)
    leafNames (ATupleSel _ (AMethCall _ i m []) idx) = methodNames i m (Just idx)
    leafNames _ = S.empty
    -- A wide interface can have many observed methods. Index the fields once
    -- rather than scanning the whole interface for every observation.
    methodIndex = MS.fromListWith S.union
        [((avi_vname v,m,index), S.fromList $
            [inst ++ "$" ++ port, inst ++ "." ++ port] ++
            [inst | isRegInst v && port == qoutPortStr]) |
          v <- apkg_state_instances apkg,
          Method { vf_name = m, vf_outputs = outs } <- vFields (avi_vmi v),
          (idx, (vn,_)) <- zip [1..] outs,
          index <- Just idx : [Nothing | [_] <- [outs]],
          let inst = getIdString (avi_vname v)
              port = getVNameString vn]
    methodNames i m idx = M.findWithDefault S.empty (i, unQualId m, idx) methodIndex

declaredWireTypeMap :: APackage -> [(String, IType)]
declaredWireTypeMap apkg =
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
        -- Deduplicate whole (name, type) pairs, preserving the first
        -- occurrence and retaining distinct types for the same name.
        -- nub is quadratic in the number of candidate wire names.
    in  stableOrdNub $
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
        submodClockResetCandidates avi ++
        submodEnRdyCandidates avi

    -- For each submodule instance, emit candidates for the wires
    -- connecting the parent to the submodule's method ENable and
    -- ready ports; both are trivially Bool.  The annotations decide
    -- which ports exist, and VModInfo already reflects that:
    --   * an always_ready method has no RDY_* field at all (ready
    --     methods appear in vFields as their own Method entries
    --     only when the port exists), and
    --   * an always_enabled method's EN port is marked inhigh and
    --     has no netlist wire,
    -- so emitting from vFields (minus inhigh enables) produces no
    -- phantom candidates for annotated methods.
    submodEnRdyCandidates avi =
        let inst_str = getIdString (avi_vname avi)
            vmi = avi_vmi avi
            emit vn = [ mkEntry (inst_str ++ "$" ++ getVNameString vn) itBool
                      , mkEntry (inst_str ++ "." ++ getVNameString vn) itBool ]
            enOf (Method { vf_enable = Just (vn, props) })
                | VPinhigh `notElem` props = emit vn
            enOf _ = []
            rdyOf (Method { vf_name = n, vf_outputs = outs })
                | isRdyId n = concatMap (emit . fst) outs
            rdyOf _ = []
        in  concatMap (\f -> enOf f ++ rdyOf f) (vFields vmi)

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
