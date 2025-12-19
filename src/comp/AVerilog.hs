{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, PatternGuards #-}
{-# LANGUAGE FlexibleInstances #-}
module AVerilog (aVerilog) where

import Data.List(nub,
            partition,
            intercalate,
            sort,
            sortBy,
            group,
            union,
            groupBy)

import Data.Char
import Data.Maybe
import System.IO.Unsafe
import qualified Data.Set as S
import qualified Data.Map as M

import ListMap(lookupWithDefault)
import Util
import FileNameUtil(hasSuf)
import PFPrint
import Error(internalError, ErrorHandle)
import Flags(Flags, removeReg, removeCross, removeInoutConnect, removeUnusedMods,
             useDPI, verilogDeclareAllFirst)
import Id
import Pragma(PProp(..))
import ASyntax
import ASyntaxUtil
import Verilog
import VPrims(vPriEnc,vMux,vPriMux,verilogInstancePrefix)
import AVerilogUtil
import InlineReg
import BackendNamingConventions(isRegInst, isClockCrossingRegInst, isInoutConnect)
import ForeignFunctions(ForeignFuncMap, mkDPIDeclarations, getForeignFunctions)
import qualified GraphWrapper as G

--import Debug.Trace
--import Util(traces)


-- ==============================
-- aVerilog

-- Converts the ASPackage into a VProgram, which is the raw Verilog
-- output structure.

-- A VProgram is a list of modules (VModule).  If primitives (such as
-- muxes) are not inlined, then they will appear in the list.  If the
-- main module is bit blasted, both the blasted and unblasted modules
-- will appear in the list.

-- Flags are the compiler flags
-- [PProp] are the Pragmas
-- XXX this function is too big
aVerilog :: ErrorHandle -> Flags -> [PProp] -> ASPackage -> ForeignFuncMap ->
            IO VProgram
aVerilog errh flags pps aspack ffmap =
       return (VProgram mods dpi_decls comments)
  where
        vco = flagsToVco flags
        -- look for pass-through comments, taking care of \n
        -- XXX should these attach to the main module instead of the
        -- XXX entire file (attached to file in case of multiple modules)
        topmod_comments = [line | PPdoc comment <- pps, line <- lines comment]
        comments_list = filter (not . null)
                            [topmod_comments,
                             inlined_submod_comments,
                             inlined_rule_comments]
        trailer = ["",""]
        comments = if (null comments_list)
                   then []
                   else (intercalate [""] comments_list) ++ trailer

        -- The modules are:
        --   (1) The main module
        --       (if bit-blasting, then this is the bit-blasted module)
        --   (2) Primitives, if not inlined (Mux, PriMux, etc)
        --   (3) The unblasted module (if bit-blasting),
        --       which is just a wrapper for the bit-blasted module
        --       to give it un-blasted ports
        mods = [mainMod] ++
               prims ++
               (if doBitBlast then [ubMod] else [])

    -- ----------
    -- package elements

        mi = aspkg_name aspack
        ps = aspkg_parameters aspack
        os = filter (\(_,t) -> isNotZeroSized t) (aspkg_outputs aspack)
        is = filter (\(_,t) -> isNotZeroSized t) (aspkg_inputs aspack)
        fs = aspkg_foreign_calls aspack
        signal_info  = aspkg_signal_info aspack
        comment_info = aspkg_comment_info aspack

    -- ----------
    -- create scan ports and scan args
        scanDefs :: [VMItem]
        scanArgs :: [VArg]
        (scanDefs, scanArgs) = createScanStructures pps

        -- separate the signal declarations
        (scan_decls, scan_others) = expVVDWire scanDefs

        -- create groups for the output Verilog
        scan_decl_group = vGroupWithComment False (mergeCommonDecl scan_decls)
                                            ["test scan declaration"]

        scan_def_group = vGroupWithComment False (sort scan_others)
                                           ["test scan definitions"]

    -- ----------
    -- bit blast, if requested by the user

        doBitBlast = PPbitBlast `elem` pps
        -- the bit-blasted ports ("args") and their definitions
        (bargs, bitBlastDefs) = createBitBlast args

        -- separate the signal declarations
        (blast_decls, blast_others) = expVVDWire bitBlastDefs

        -- create groups for the output Verilog
        blast_decl_group =
            vGroupWithComment False (mergeCommonDecl blast_decls)
                              ["bit blast declarations"]
        blast_def_group =
            vGroupWithComment False (sort blast_others)
                              ["bit blast definitions"]

    -- ----------
    -- Create the main module (and un-blasted wrapper, if bit-blasting)

        -- Module name UB un-blasted, BB Bit blasted...
        modnameUB = vId mi
        modnameBB = suff modnameUB "BB"

        -- The module contents are defined below to be:
        --   instantiations and declarations for their ports
        --   definitions for submodule inputs
        --   definitions for all other signals (which will need declaring)
        --   other blocks etc

        -- The order of items in the module is:
        --   scanDef decls, bitBlastDef decls, output signal decls,
        --   insts, rule scheduling decls, remaining decls,
        --   scanDefs, bitBlastDefs, all local defs,
        --   inlined submodule blocks, foreign function blocks

        -- defs for the bit-blasted module
        bbItems = mkModItems True
        -- defs for the un-blasted module
        ubItems = mkModItems False

        mkModItems isBB =
              -- declarations
                -- feature decls
                scan_decl_group ++
                if (isBB) then blast_decl_group else [] ++
                -- module decls
                module_decls ++
              -- definitions
                -- feature defs
                scan_def_group ++
                if (isBB) then blast_def_group else [] ++
                -- module defs
                module_defs ++
              -- blocks
                inst_block_group ++
                foreignfunc_block_group

        module_decls =
            -- output port re-declares
            output_decls_group ++
            -- signals for submodule ports
            -- (depending on flag, this can also include the instantiations)
            inst_decl_groups ++
            -- remaining declarations
            rule_decls_group ++  -- includes method_rule_decls
            mux_decls_group ++
            foreign_decls_group ++
            other_decls_group

        module_defs =
            special_def_groups ++
            method_def_groups ++
            -- depending on flag, either empty or the submod instantiations
            inst_def_groups ++
            rule_def_groups ++
            mux_defs_group ++
            submod_def_groups ++
            other_defs_group


        -- The main module
        -- XXX note, no special port grouping/commenting for bit blasted mod
        mainMod =
            if doBitBlast
            then VModule { vm_name = modnameBB,
                           vm_comments = [],
                           vm_ports = [(bargs,[])],
                           vm_body = bbItems }
            else VModule { vm_name = modnameUB,
                           vm_comments = [],
                           vm_ports = (groupPorts signal_info args),
                           vm_body = ubItems }

        -- The un-blasted wrapper, when bit-blasting
        -- It has the unblasted name, the unblasted ports,
        -- and it contains an instantiation of the bit-blasted module,
        -- wires to connect to its ports, and definitions for the
        -- un-blasted ports based on those wires.
        ubMod = VModule { vm_name = modnameUB,
                          vm_comments = [],
                          vm_ports = (groupPorts signal_info args),
                          vm_body = wrItems }
                where wrItems = [wires bbids, ubInst bbids modnameBB] ++
                                unBlast args
                      bbids = getArgIds bargs
                      wires is = VMDecl (VVDecl VDWire Nothing (map VVar is))

    -- ----------
    -- convert foreign function calls to always blocks

        -- defs_in_foreign_blocks = ids of defs which are assigned in
        --     the foreign blocks and therefore need to be declared "reg"
        (foreignfunc_blocks, defs_in_foreign_blocks) =
           apFst concat $
            apSnd concat $
              unzip $
                mapMaybe (vForeignBlock vco ffmap (aspkg_values aspack)) fs

        -- bool is True b/c foreign function blocks should be separated
        foreignfunc_block_group =
            vGroupWithComment True foreignfunc_blocks
                              ["handling of system tasks"]

    -- ----------
    -- create import-DPI statements, if using DPI

        dpi_decls = if (useDPI flags)
                    then mkDPIDeclarations $ getForeignFunctions ffmap aspack
                    else []

    -- ----------
    -- define a function (vDef) for mapping an ADef to a Verilog item

        -- defs which must be declared as reg, and don't need assigns
        -- because they are assigned in foreign blocks
        defs_as_reg = defs_in_foreign_blocks

        vDef :: ADef -> [VMItem]
        vDef adef@(ADef i t _ _) =
            let vdef = vDefMpd vco adef ffmap
                reg_def = [VMDecl $ VVDecl VDReg (vSize t) [VVar (vId i)]]
            in  -- if it's a reg, just declare the reg
                if (i `elem` defs_as_reg)
                then reg_def
                else -- return the vdef, but
                     -- remove definitions which have 0 sized results
                     case (aType adef) of
                       (ATString Nothing) -> vdef
                       otherwise -> if ((aSize adef) == 0) then [] else vdef

    -- ----------
    -- handle the submodule instances
    --
    -- an instance consists of the module instantiation,
    -- and the declarations for the ports which connect to it.
    -- the output wires need to be created as they do not exist
    -- in the aspack defs.  the input wires exist in the defs
    -- because they have been defined to some value; so we need
    -- to separate the decl from the def.

    -- the function genInstances will create the submodule instance
    -- and declarations for submodule inputs and outputs;
    -- it will handle the inputs which must be high (remove them
    -- and error/warn if they are not high);
    -- it will determine which ports of instantiations are unused,
    -- and remove those port connections;
    -- it will return:
    --   * the package defs (still unconverted from A to V)
    --     without the always_enabled and unused defs
    --   * the Verilog instantiation groups (submod instantiations
    --     and declaration of signals for connecting to the ports):
    --     this is broken into a decl group and a def group;
    --     depending on flags, either everything is in the decl group
    --     and the def group is empty or the instantiations are moved
    --     to the def group (to allow all decls to be first in the module)
    --   * lists of the defs which have already been declared
    --     (separated into those which are inputs to submodules
    --      and others which had to be declared because they were used)
    --   * any Verilog blocks for submodules (such as for inlined Reg)
    --   * any not-always-enabled errors to report

        -- provide foreign blocks, so that it knows which ports are used there
        (ds, inst_decl_groups, inst_def_groups,
         inst_inputs, inst_declared_signals, inst_blocks,
         inout_rewire_map,
         inlined_submod_comments)
             = genInstances errh flags foreignfunc_blocks vDef aspack

        -- currently, inst_blocks are only from inlined registers
        -- (the always blocks and initial blocks)
        -- bool is True b/c register always/initial blocks should be separated
        inst_block_group =
            vGroupWithComment True inst_blocks
                              ["handling of inlined registers"]

    -- ----------
    -- Compute inout information

        all_inouts = computeInouts inout_rewire_map aspack

    -- ----------
    -- Compute the port list of the module

        -- XXX parameters are always given the default value of 0.
        -- XXX might be good to allow the user to specify a default

        args :: [VArg]
        args =        [ VAParameter (vId i) r v
                     | (i, t) <- ps,
                       let (r, v) = case t of
                                      ATBit sz -> (Just (VEConst (sz-1),
                                                         VEConst 0),
                                             VEWConst (mkVId "0") sz 2 0)
                                      ATString _ -> (Nothing, VEString "")
                                      ATReal -> (Nothing, VEReal 0.0)
                                      _ -> (Nothing, VEConst 0) ] ++
                [ VAInput (vId i) (vSize t)
                     | (i, t) <- is ] ++
                filterSharedInout
                  ([ VAInout (vId i) (Just (vId i')) (Just (vSize t))
                         | (i, t, i') <- all_inouts ]) ++
                [ VAOutput (vId o) (vSize t)
                     | (o, t) <- os ] ++
                scanArgs

    -- ----------
    -- Grouping of definitions
    --
    -- separate the defs into groups:
    --   * special outputs (clocks, resets)
    --   * methods
    --   * rules
    --   * inputs to submodules
    --   * used by foreign blocks
    --   * other

        -- remember to not redeclare any signals that needed to be
        -- declared for submodule instantiations
        isPreDeclared = isDeclFromList $ S.fromList inst_declared_signals

        -- make a map to hold the defs, for easy access
        defmap = M.fromList [ (i,d) | d@(ADef i _ _ _) <- ds ]

        -- -----
        -- special outputs
        (special_decls, special_def_groups, defmap2) =
            groupSpecialOutputDefs vDef signal_info defmap

        -- -----
        -- methods
        (method_output_decls, method_rule_decls, method_def_groups, defmap3) =
            groupMethodDefs vDef signal_info defmap2

        -- -----
        -- redeclare module outputs
        -- (module output ports need to be declared as wire/reg for
        --  internal assignment)
        -- (these will come before instances, so no need to filter)

        -- note: output_decls should be the same as if we had
        --       filtered the defs using "os" from the aspack
        --       XXX check for this with an internal error?

        output_decls = special_decls ++ method_output_decls
        output_decls_comment = ["signals for module outputs"]
        output_decls_group =
            vGroupWithComment False (mergeCommonDecl output_decls)
                              output_decls_comment

        -- -----
        -- rules
        (rule_decls, rule_def_groups, defmap4, inlined_rule_comments) =
            groupRuleDefs vDef signal_info comment_info defmap3

        rule_decls_filtered =
            filter (not . isPreDeclared) (method_rule_decls ++ rule_decls)
        rule_decls_comment = ["rule scheduling signals"]
        rule_decls_group =
            vGroupWithComment False (mergeCommonDecl rule_decls_filtered)
                              rule_decls_comment

        -- -----
        -- inputs to submodules
        (submod_def_groups, defmap5) =
            groupSubmoduleDefs vDef inst_inputs defmap4

        -- -----
        -- inputs to muxes (selectors and values)
        -- (if they survive optimization)
        (mux_decls_group, mux_defs_group, defmap6) =
            groupMuxDefs vDef signal_info defmap5


        -- Foreign block decls (should be no corresponding defs)
        -- Foreign block decls include directly written by foreign calls
        -- as well as defs inlinded into foreign blocks.
        foreign_writes = concatMap afc_writes $ concatMap snd fs
        (foreign_decls_group, defmap7) =
            groupForeignBlockDefs vDef (foreign_writes ++ defs_in_foreign_blocks) defmap6

        -- -----
        -- other
        -- (keep in the package order, for lack of a better order)
        ds7 = filter (isADefFromList (M.keys defmap7)) ds
        (other_decls, other_defs) = mkVDeclsAndDefs vDef ds7
        other_decls_filtered = filter (not . isPreDeclared) other_decls

        other_decls_group =
            vGroupWithComment False (mergeCommonDecl other_decls_filtered)
                              ["remaining internal signals"]
        other_defs_group =
            vGroupWithComment False (sort other_defs)
                              ["remaining internal signals"]

    -- ----------
    -- Convert primitives into modules

        -- this looks for all the prim mux instances in the
        -- module and constructs the module definitions for them.
        -- to save work, just hand it the module_defs
        prims = buildPrimModules flags module_defs


-- ==============================
-- Grouping and commenting ports

-- Using the signal info, convert the portlist into a grouped and
-- commented port list, for more readable RTL output

groupPorts :: ASPSignalInfo -> [VArg] -> [([VArg], VComment)]
groupPorts si as =
    let
        -- create pairs of the ports with their name
        named_as = map (\a -> (vidToId (vargName a), a)) as

        -- a function to filter out ports whose name appears in a list
        findIds :: [Id] -> [(Id,VArg)] -> ([VArg],[(Id,VArg)])
        findIds is ports =
            let (found, rest) = partition (\ (i,a) -> i `elem` is) ports
            in  (map snd found, rest)

        -- find the module input args
        (inputs, remaining1) = findIds (aspsi_inputs si) named_as

        -- find the output clocks
        -- (function to be folded over the clock/gate info)
        findClock (clk, gates) (cs, ports) =
            let (ps, remaining) = findIds (clk:gates) ports
            in  ((clk,ps):cs, remaining)

        (output_clks, remaining2) =
            foldr findClock ([], remaining1) (aspsi_output_clks si)

        -- find the output resets
        (output_rsts, remaining3) = findIds (aspsi_output_rsts si) remaining2

        -- find the ports for each method
        -- (function to be folded over the method port info)
        findMethod :: ASPMethodInfo ->
                        ([(AId,String,[VArg])],[(Id,VArg)]) -> ([(AId,String,[VArg])],[(Id,VArg)])
        findMethod (ASPMethodInfo i ty mr me mv args _) (ms, ports) =
            let is = (catMaybes [mr, me, mv]) ++ args
                (ps, remaining) = findIds is ports
            in  ((i,ty,ps):ms, remaining)

        (method_ports, remaining4) =
            foldr findMethod ([], remaining3) (aspsi_methods si)

        -- XXX interface Inouts have not been pulled out
        -- XXX (so they will end up in the unknown_ports list)

        -- this should be empty
        -- (but maybe misc things, like scan ports, end up in the list?)
        unknown_ports = map snd remaining4

        -- ty is the type of the method (action, value, actionvalue)
        -- XXX could sort the ports? (RDY, args, return val, EN)
        mkMethodGroup (i,ty,ps) =
            (ps, [ty ++ " method " ++ getIdString i])

        mkClockGroup (clk,ps) =
            (ps, ["oscillator and gates for output clock " ++ getIdString clk])

    in
        -- no comment on the inputs
        (if (not (null inputs))
           then [(inputs, [])]
           else []) ++
        -- unidentified ports
        (if (not (null unknown_ports))
           then [(unknown_ports, [])]
           else []
         ) ++
        -- methods
        map mkMethodGroup method_ports ++
        -- clocks
        map mkClockGroup output_clks ++
        -- resets
        (if (null output_rsts)
           then []
           else [(output_rsts, ["output resets"])])


-- ==============================

-- produce the decls and assignments for special outputs (clocks and resets)
-- and return the remaining defs
groupSpecialOutputDefs :: (ADef -> [VMItem]) -> ASPSignalInfo ->
                          M.Map AId ADef ->
                          ([VMItem], [VMItem], M.Map AId ADef)
groupSpecialOutputDefs vDef si ds =
    let
        mkForClock (clk, gates) (decls, gs, defs) =
            let (clk_defs, other_defs) = findADefs (clk:gates) defs
                (clk_vdecls, clk_vdefs) = mkVDeclsAndDefs vDef clk_defs
                comment = ["oscillator and gates for output clock " ++
                           getIdString clk]
                -- if (null clk_defs) this returns []
                g = vGroupWithComment False clk_vdefs comment
            in  (clk_vdecls ++ decls, g ++ gs, other_defs)

        mkResetDefGroup rsts defs =
            let (rst_defs, other_defs) = findADefs rsts defs
                (rst_vdecls, rst_vdefs) = mkVDeclsAndDefs vDef rst_defs
                comment = ["output resets"]
                -- if (null rst_vdefs) this returns []
                g = vGroupWithComment False rst_vdefs comment
            in  (rst_vdecls, g, other_defs)

        clk_infos = aspsi_output_clks si
        rst_infos = aspsi_output_rsts si
        (rst_decls, rst_group, ds1) = mkResetDefGroup rst_infos ds
        (vdecls, groups, remaining_defs) =
            foldr mkForClock (rst_decls, rst_group, ds1) clk_infos
    in
        (vdecls, groups, remaining_defs)

-- returns
--  * decls for outputs (RDY and output value)
--  * decls for internal signals (CAN_FIRE_/WILL_FIRE_)
--  * group of defs for both outputs and internal signals
--  * remaining ADefs
groupMethodDefs :: (ADef -> [VMItem]) -> ASPSignalInfo -> M.Map AId ADef ->
                   ([VMItem], [VMItem], [VMItem], M.Map AId ADef)
groupMethodDefs vDef si ds =
    let
        getRuleSignals r =
            case (lookup r (aspsi_rule_sched si)) of
                Nothing -> internalError ("getRuleSignals: " ++ ppString r)
                Just ss -> ss

        -- a function to fold over the method infos
        -- this function identifies:
        --    * method outputs (RDY and/or return val)
        --      which have already been declared, but have defs
        --    * related internal signals
        --      (so far just the sched signals for associated rules)
        mkForMethod :: ASPMethodInfo ->
                       ([VMItem], [VMItem], [VMItem], M.Map AId ADef) ->
                       ([VMItem], [VMItem], [VMItem], M.Map AId ADef)
        mkForMethod (ASPMethodInfo i ty mr _ mv _ rs) (odecls, idecls, gs, defs) =
            let
                -- get the output defs
                output_ids = catMaybes [mv, mr]
                (output_defs, other_defs) = findADefs output_ids defs
                -- get the rule defs
                rule_sched_ids = concatMap getRuleSignals rs
                (rule_defs, other_defs2) = findADefs rule_sched_ids other_defs
                -- convert to Verilog
                (out_vdecls, out_vdefs) = mkVDeclsAndDefs vDef output_defs
                (rule_vdecls, rule_vdefs) = mkVDeclsAndDefs vDef rule_defs
                -- make the method group
                comment = [ty ++ " method " ++ getIdString i]
                -- if (null defs) this returns []
                g = vGroupWithComment False (out_vdefs ++ rule_vdefs) comment
            in  (out_vdecls ++ odecls, rule_vdecls ++ idecls, g ++ gs,
                 other_defs2)
    in
        -- fold over the method infos
        foldr mkForMethod ([], [], [], ds) (aspsi_methods si)

-- returns
--  * decls for scheduling signals (CAN_FIRE_/WILL_FIRE_)
--  * defs for scheduling signals
--  * remaining ADefs
--  * top-level comments, from any rules whose signals were inlined
--    (leaving no place to attach comments)
groupRuleDefs :: (ADef -> [VMItem]) -> ASPSignalInfo -> ASPCommentInfo ->
                 M.Map AId ADef ->
                 ([VMItem], [VMItem], M.Map AId ADef, [String])
groupRuleDefs vDef si ci ds =
    let sched_info = aspsi_rule_sched si
        comment_map = aspci_rules ci
        method_rule_ids = concatMap aspm_assocrules (aspsi_methods si)
        -- the scheduling info for real rules
        -- (scheduling info for methods will be grouped with methods)
        nonmethod_sched_info :: [(AId,[AId])]
        nonmethod_sched_info =
            filter (\(i,v) -> i `notElem` method_rule_ids) sched_info

        mkForRule (rule_id, signal_ids) (decls, gs, defs, inlined_rs) =
            let (rule_defs, other_defs) = findADefs signal_ids defs
                (rule_vdecls, rule_vdefs) = mkVDeclsAndDefs vDef rule_defs
                -- make the rule group
                user_comment = fromMaybe [] (lookup rule_id comment_map)
                comment = ("rule " ++ getIdString rule_id) :
                          indentLines 2 (concatMap lines user_comment)
                -- if (null rule_vdefs) this returns []
                g = vGroupWithComment False rule_vdefs comment
                inlined_rs' = if (null rule_vdefs)
                              then ((rule_id, user_comment):inlined_rs)
                              else inlined_rs
            in  (rule_vdecls ++ decls, g ++ gs, other_defs, inlined_rs')

        (decls, gs, defs, inlined_rule_info) =
            foldr mkForRule ([], [], ds, []) nonmethod_sched_info

        -- compute whether any rule comments need to bubble to the top
        remaining_rule_comments =
            filter (not . null . snd) inlined_rule_info
        top_comments = makeTopComments "rule" remaining_rule_comments
    in
        (decls, gs, defs, top_comments)

-- returns a list of definition groups
-- (as these signals have already been declared)
-- and the remaining defs
groupSubmoduleDefs :: (ADef -> [VMItem]) ->
                      ([(AId,[VId])], [(AId,[VId])], [VId], [VId]) ->
                      M.Map AId ADef ->
                      ([VMItem], M.Map AId ADef)
groupSubmoduleDefs vDef inst_inputs ds =
    let
        (submod_inputs, reg_inputs, rwire_inputs, probe_inputs) = inst_inputs

        -- for grouping inputs to each instance in their own groups
        mkModDefGroup ty (i, ss) (gs, defs) =
            let ss' = map vidToId ss
                (mod_defs, other_defs) = findADefs ss' defs
                (_{-mod_vdecls-}, mod_vdefs) = mkVDeclsAndDefs vDef mod_defs
                comment = [ty ++ " " ++ getIdString i]
                -- if (null mod_vdefs) this returns []
                g = vGroupWithComment False mod_vdefs comment
            in  (g ++ gs, other_defs)

        mkSubmodDefGroup = mkModDefGroup "submodule"
        mkRegDefGroup    = mkModDefGroup "register"

        -- for grouping all wires into one commented group
        -- rather than a comment per wire
        mkWireDefGroup :: VComment -> ([VMItem], M.Map AId ADef) -> [VId] ->
                          ([VMItem], M.Map AId ADef)
        mkWireDefGroup comment (gs, defs) ss =
            let ss' = map vidToId ss
                (wire_defs, other_defs) = findADefs ss' defs
                (_{-wire_vdecls-}, wire_vdefs) = mkVDeclsAndDefs vDef wire_defs
                -- if (null wire_vdefs) this returns []
                g = vGroupWithComment False wire_vdefs comment
            in  (g ++ gs, other_defs)

        mkRWireDefGroup = mkWireDefGroup ["inlined wires"]
        mkProbeDefGroup = mkWireDefGroup ["probes"]

        -- fold over the mods
        (gs1, ds1) = foldr mkSubmodDefGroup ([],ds) submod_inputs
        (gs2, ds2) = foldr mkRegDefGroup (gs1,ds1) reg_inputs
        (gs3, ds3) = mkRWireDefGroup (gs2,ds2) rwire_inputs
        (gs4, ds4) = mkProbeDefGroup (gs3,ds3) probe_inputs
    in
      (gs4, ds4)

-- returns
--  * group for decls (of mux inputs)
--  * group for defs (of mux inputs)
--  * remaining ADefs
-- XXX This currently makes one group for all,
-- XXX but with more info, it could group them according to mux.
-- XXX Also, it could group selectors and values separately.
groupMuxDefs :: (ADef -> [VMItem]) -> ASPSignalInfo -> M.Map AId ADef ->
                ([VMItem], [VMItem], M.Map AId ADef)
groupMuxDefs vDef si ds =
    let mux_input_ids = aspsi_mux_selectors si ++ aspsi_mux_values si
        (mux_defs, other_defs) = findADefs mux_input_ids ds
        (mux_vdecls, mux_vdefs) = mkVDeclsAndDefs vDef mux_defs
        comment = ["inputs to muxes for submodule ports"]
        mux_decl_group =
            vGroupWithComment False (mergeCommonDecl mux_vdecls) comment
        mux_def_group =
            vGroupWithComment False mux_vdefs  comment
    in
        (mux_decl_group, mux_def_group, other_defs)

-- returns
--  * group for decls (of regs for foreign function assignments)
--  * remaining ADefs
-- Does not return a group of defs because these decls are assigned
-- in the foreign function block.
groupForeignBlockDefs :: (ADef -> [VMItem]) -> [AId] -> M.Map AId ADef ->
                ([VMItem], M.Map AId ADef)
groupForeignBlockDefs _ [] ds = ([], ds)
groupForeignBlockDefs vDef foreign_block_ids  ds =
    let (foreign_defs, other_defs) = findADefs foreign_block_ids ds
        (foreign_vdecls, foreign_vdefs) = mkVDeclsAndDefs vDef foreign_defs
        comment = ["declarations used by system tasks"]
        foreign_vgroup = VMGroup { vg_translate_off = True
                                 , vg_body = [foreign_vdecls]
                                 }
    in case foreign_vdefs of
         [] -> ([VMComment comment foreign_vgroup], other_defs)
         _  -> internalError ("groupForeignBlockDefs: " ++ ppReadable (foreign_block_ids, ds))

-- ----------

-- from a list of ADef, make a list of the Verilog decls and a list of
-- the Verilog assignments (whether by assign statement or always block)
mkVDeclsAndDefs :: (ADef -> [VMItem]) -> [ADef] -> ([VMItem], [VMItem])
mkVDeclsAndDefs vDef ds =
    let converted_ds = concatMap vDef ds
    in  expVVDWire converted_ds


-- ==============================
-- Top-level inout handing

computeInouts :: M.Map AId AId -> ASPackage -> [(Id, AType, Id)]
computeInouts inout_rewire_map aspack =
    let
        -- ifc inouts are connected to their expressions
        ifc_inouts = [ (i,t,e) | (ADef i t e _) <- aspkg_inout_values aspack,
                                 isNotZeroSized t ]
        ifc_inout_ids = map fst3 ifc_inouts

        -- arg_inouts are connected to themselves
        arg_inouts = [ (i,t, ASPort t i) | (i,t) <- aspkg_inouts aspack,
                                           isNotZeroSized t,
                                           i `notElem` ifc_inout_ids ]

        all_inouts = ifc_inouts ++ arg_inouts
        rewire_inout (ASPort t i) = fromMaybe i (M.lookup i inout_rewire_map)
        rewire_inout e = internalError ("computeInouts - not port: " ++ ppReadable e)
     in mapThd rewire_inout all_inouts

-- Make sure that a shared inout signal is only declared once
filterSharedInout :: [VArg] -> [VArg]
filterSharedInout args =
    let foldFn :: VArg -> (S.Set VId, [VArg]) -> (S.Set VId, [VArg])
        foldFn a@(VAInout v mv (Just r)) (s,as) =
            let i = fromMaybe v mv
                new_a = VAInout v mv Nothing
            in  if (S.member i s)
                then (s, new_a:as)
                else (S.insert i s, a:as)
        foldFn a@(VAInout _ _ Nothing) (s,as) = (s, a:as)
        foldFn a _ = internalError ("filterSharedInout: unexpected varg: " ++
                                    ppReadable a)
    in  snd $ foldr foldFn (S.empty,[]) args


-- ==============================
-- genInstances

-- Generates the Verilog for submodule instantiations, grouping the
-- module and the port wires for each submodule, and returns the
-- items in order (grouped by type and alphabetical in each group)
-- and returns the remaining module defs.

-- There are several types of instances:
-- * instantiations of Probe modules, where the Verilog module is to be
--   removed, but the write signal remains (for viewing the probe value)
-- * inlined registers, which have no verilog module, but do generate
--   additional always blocks, and have an output which needs to be
--   declared "reg" instead of "wire"
-- * the inputs to inlined rwires are grouped, if the signal is still around
--   XXX we could handle comments on rwire insts, attaching them to the signals
-- * normal instantiations
-- * "ifc args", which are handled like instantiations
--  XXX should make the return type a structure.
-- XXX this function is too big
genInstances :: ErrorHandle -> Flags -> [VMItem] -> (ADef -> [VMItem]) -> ASPackage ->
                ([ADef],    -- filtered (not yet converted) package defs
                 [VMItem],  -- decl groups
                 [VMItem],  -- def groups
                 ([(AId, [VId])], -- submod inputs which don't need declaring
                  [(AId, [VId])], -- (instances, regs, rwires, probes)
                  [VId],
                  [VId]),
                 [VId],     -- other defs that needed to be declared,
                            --   so don't re-declare these either
                 [VMItem],  -- always and initial blocks
                 M.Map AId AId, -- inout rewiring map
                 [String])  -- toplevel comments for inlined submodules
genInstances errh flags ff_blocks vDef aspack =
    let

    -- ----------
    -- the package definitions

        -- converts the adefs to vitems
        defs = concatMap vDef (aspkg_values aspack)
        -- make a size and type map from the vmitems
        sztm = mkSizeAndTypeMap defs

        -- we'll need the inout defs, too, to know which inout ports
        -- of submodule are used (and which should be left unconnected)
        iodefs = concatMap vDef (aspkg_inout_values aspack)

        sos = aspkg_state_outputs aspack

        top_mod_inputs = aspkg_inputs aspack

        rws = aspkg_inlined_ports aspack

        inst_comments = aspci_submod_insts (aspkg_comment_info aspack)

        parent_ps = map fst (aspkg_parameters aspack)

    -- ----------
    -- Sort the instances by name so they are easier to find,
    -- in the generated Verilog

        sortAVInst :: AVInst -> AVInst -> Ordering
        sortAVInst a b = cmpIdByName (avi_vname a) (avi_vname b)

        aspkg_instances :: [AVInst]
        aspkg_instances = sortBy sortAVInst (aspkg_state_instances aspack)

    -- -----------
    -- Inline inout connections
    -- to pacify some picky tools (e.g. Xilinx)
        inout_connect_instances :: [AVInst]
        not_inout_connect_instances :: [AVInst]
        (inout_connect_instances,
         not_inout_connect_instances) =
         if (removeInoutConnect flags)
         then partition isInoutConnect aspkg_instances
         else ([], aspkg_instances)

        mkInoutPair [ASPort t1 i1, ASPort t2 i2] | t1 == t2 = (i1, i2)
        mkInoutPair l = internalError ("bad inout connect: " ++ ppReadable (l, inout_connect_instances))

        inout_pairs = map (mkInoutPair . (drop 1) . avi_iargs) inout_connect_instances

        (inout_rewire_map, inout_inst_wires) = buildInoutConnectInfo inout_pairs

        buildInoutConnectInfo pairs = apSnd M.keys $ foldr addInoutPair (M.empty, M.empty) inout_pairs

        addInoutPair :: (AId, AId) -> (M.Map AId AId, M.Map AId [AId]) -> (M.Map AId AId, M.Map AId [AId])
        addInoutPair (i1, i2) (cm, rcm) | Just ic1 <- M.lookup i1 cm,
                                          Just ic2 <- M.lookup i2 cm =
          if ic1 == ic2
          then (cm, rcm) -- redundant connection
          -- we need to connect everything ic2 is connected to to ic1
          else let ic2_cxns = fromJustOrErr ("ic2 not found: " ++ ppReadable (ic2, rcm)) (M.lookup ic2 rcm)
                   update_cm = M.fromList $ map (\cxn -> (cxn, ic1)) ic2_cxns
               in (M.unionWith (flip const) cm update_cm,
                   M.delete ic2 $ M.adjust ((++) ic2_cxns) ic1 rcm)
        addInoutPair (i1, i2) (cm, rcm) | Just i_shared <- M.lookup i1 cm,
                                          not (M.member i2 cm) = (M.insert i2 i_shared cm,
                                                                  M.adjust ((:) i2) i_shared rcm)
        addInoutPair (i1, i2) (cm, rcm) | Just i_shared <- M.lookup i2 cm,
                                          not (M.member i1 cm) = (M.insert i1 i_shared cm,
                                                                  M.adjust ((:) i1) i_shared rcm)
        addInoutPair (i1, i2) (cm, rcm) =
           if (not (M.member i1 cm) && not (M.member i2 cm)) then
             (M.insert i1 i1 $ M.insert i2 i1 cm,
              M.insert i1 [i1,i2] rcm)
           else internalError ("addInoutPair: " ++ ppReadable ((i1,i2),cm,rcm))
    -- ----------
    -- separate the Reg* instances, when inlining registers

        inlined_reg_instances :: [AVInst]
        noninlined_aspkg_instances :: [AVInst]
        should_inline x = isRegInst x && ((not (isClockCrossingRegInst x)) || (removeCross flags))
        (inlined_reg_instances, noninlined_aspkg_instances) =
            if (removeReg flags)
            then partition should_inline not_inout_connect_instances
            else ([], not_inout_connect_instances)

        (inlined_reg_comments, noninlinedreg_comments) =
            let reg_inst_ids = map avi_vname inlined_reg_instances
            in  partition ((`elem` reg_inst_ids) . fst) inst_comments

    -- ----------
    -- translate the inlined registers into Verilog items

        -- vInlineReg returns the always blocks for implementing the regs
        -- and port info used to declare the Q_OUT (which needs to be declared
        -- as "reg" instead of "wire"), to declare the inputs (separate from
        -- their assignments), and to keep track of any CLK/RSTN uses for
        -- removed unused ports on other modules
        (inlined_reg_blocks, reg_infos) =
            vInlineReg errh flags inlined_reg_instances

        -- generate the reg/wire declarations
        reg_decl_groups =
            map (mkRegGroup sos sztm inlined_reg_comments) reg_infos

        -- the input wire decls (to be later assigned to, but not re-declared)
        reg_inputs :: [(AId, [VId])]
        reg_inputs = map (\((VId _ inst_id _),def_name,c,d,e) -> (inst_id, map fst d)) reg_infos

        -- used by dropUnusedPortWires to know which submod outputs are
        -- used as non-method inputs (clk and rstn) to registers
        reg_uses = concatMap (\((VId _ inst_id _),def_name,c,d,e) -> c) reg_infos

    -- ----------
    -- translate the non-inlined submodule instances
    -- and handle always_enabled attributes

        -- sorted list of the instances:
        --   * inst name
        --   * Verilog instance (VMInst)
        --   * an info tuple of lists of the ports and params of the inst
        inst_infos0 :: [ (AId, VMItem, InstInfo) ]
        inst_infos0 = map (vState flags inout_rewire_map) noninlined_aspkg_instances

        -- if we're removing unused modules,
        -- filter out instances that don't connect any wires
        inst_infos = if (removeUnusedMods flags) then
                         filter (wiredInstance . snd3) inst_infos0
                     else inst_infos0

    -- ----------
    -- Compute which always-high signals aren't set to constant 1

    -- This is now computed before the backend split, in AAddScheduleDefs

    -- ----------
    -- remove input port connection wires which are always high
    --
    -- ports which are always high shouldn't exist in the Verilog module
    -- (because they've been removed by always_enabled)

        -- XXX they have been created with the string "_AlwaysEnabled"
        -- XXX appended to them, so look for that string
        alwaysEnabledString string = (hasSuf "_AlwaysEnabled" string)
        notAlwaysEnabledADef (ADef aid _ _ _) =
            (not (alwaysEnabledString (getIdString aid)))

        -- definitions which are not always_enabled
        filtered_ds = filter notAlwaysEnabledADef (aspkg_values aspack)

        -- note that we start again from the ASP ds, because vDef might expand
        -- them into several items, so easier to filter the one item in ds
        filtered_defs = concatMap vDef filtered_ds

        -- note that we don't remove the always_ready ports from the insts,
        -- because dropUnusedPortWires (below) will remove them

    -- ----------
    -- XXX separate out the ifc_args here?

    {-
        --   See the commented-out code in IExpand.iExpandModuleLam
        --   which creates an instance as the way to make the ifc available.
        --   Since ifc args are not supported, the first list will be empty.
        --   XXX The method for finding "interface arguments" is to look
        --   XXX for the string which CType.ifcArgName creates.
        (ifc_arg_info, real_inst_info) = partition isARG inst_info
            where isARG (VMAssign (VLId (VId s i _)) _)
                            | take 4 s == "ARG_" = True
                  isARG _ = False
    -}

    -- ----------
    -- drop unused port wires

        -- XXX we make fake VMItems for the sole purpose of faking out
        -- dropUnusedPortWires for bypassed inouts
        to_inout_decl i = VMDecl $ vVDecl VDInout Nothing (VVar (vId i))
        inout_inst_defs = map to_inout_decl inout_inst_wires
        all_io_wires = iodefs ++ inout_inst_defs

        (unused_defs, inst_info2)
            = dropUnusedPortWires ff_blocks (filtered_defs ++ all_io_wires) reg_uses inst_infos

        filtered_ds2 =
            let unused_ids = map vidToId unused_defs
                isUsedDef (ADef { adef_objid=i }) = i `notElem` unused_ids
            in  filter isUsedDef filtered_ds

    -- ----------
    -- separate out probes and generate their items

        (submod_infos, probe_infos) = partition notProbe inst_info2

        (probe_comments, all_submod_comments) =
            let probe_ids = map fst3 probe_infos
            in  partition ((`elem` probe_ids) . fst) noninlinedreg_comments

        (probe_inputs, probe_decls_group) =
            mkProbeGroup sos sztm probe_comments probe_infos

    -- ----------
    -- generate a group for inlined rwires whose i/o are still around

        -- user comments on rwires are handled with "inlined_submod_comments"
        -- (note that InlineRWire could convert them to PPdoc on the topmod)
        (rwire_inputs, rwire_decls_group) = mkRWireGroup (mkSizeAndTypeMap filtered_defs) rws

    -- ----------
    -- signals declared so far

        -- if flags indicate to intermingle submod instantiations
        -- with declarations of their ports, then we need a list of
        -- signals declared so far (so we know which not to re-declare)

        -- this list doesn't contain submodule inputs because we're only
        -- concerned with submod outputs and local defs and topmod inputs
        -- (those are the only things that can appear in the ports exprs)
        decls_so_far = rwire_inputs ++
                       map (vId . fst) top_mod_inputs ++
                       map (vId . fst) sos

    -- ----------
    -- generate items for remaining submodules
    -- (including declarations of inputs and outputs)

        (submod_comments, inlined_submod_comments) =
            let submod_ids = map fst3 submod_infos
            in  partition ((`elem` submod_ids) . fst) all_submod_comments

        (submod_inputs, submod_decl_groups, submod_def_groups,
         extra_submod_decls) =
            mkSubmodGroups flags sos sztm submod_comments decls_so_far
                           submod_infos

    -- ----------
    -- convert the comments on inlined submodules to toplevel comments

        top_level_comments = makeTopComments "module" inlined_submod_comments

    -- ----------
    -- sanity check instantiation parameters and port arguments

        -- params must be constant
        bad_submod_ps =
            [ (p, e) | (_, _, (ps, _, _, _, _)) <- submod_infos,
                       (p, e) <- ps,
                       not (isConstVE parent_ps e)
            ]

        -- ports must be top module input, submodule output, or constant
        -- XXX is this checking for anything?
        -- XXX perhaps it is checking for a Verilog requirement on the
        -- XXX legal expressions for a port?  otherwise, it's not needed.
        bad_submod_port_ps =
            [ (p, e) | (_, _, (_, port_ps, _, _, _)) <- submod_infos,
                       (p, e) <- port_ps,
                       -- not constant
                       not (isConstVE parent_ps e),
                       -- if it's a variable reference, it must be an input,
                       -- a submod output, or a definition
                       -- (which is everything, so no need to check)
                       -- a const select of a variable is OK as well
                       case (e) of
                           VEVar v
                             -> False
                           VESelect (VEVar v) e1 e2
                             -> not (isConstVE parent_ps e1 && isConstVE parent_ps e2)
                           VESelect1 (VEVar v) e1
                             -> not (isConstVE parent_ps e1)
                           VEIndex v e1
                             -> not (isConstVE parent_ps e1)
                           _ -> True
            ]

    -- ----------
    -- final item list

        final_ds = filtered_ds2

        -- list the probes first, then the inlined regs, then submodules
        -- (because they are VMGroup, there will be spaces between them)
        inst_decl_groups = probe_decls_group ++
                           rwire_decls_group ++
                           reg_decl_groups ++
                           submod_decl_groups

        -- only non-inlined modules have instantiations
        -- (everything else is pure decls)
        -- if verilogDeclareAllFirst flag is off, then the insts will be
        -- included in the decl groups and this list will be empty
        inst_def_groups  = submod_def_groups

    in
        if (not (null bad_submod_ps))
        then internalError ("genInstances: bad submod params: " ++
                               ppReadable bad_submod_ps)
        else if (not (null bad_submod_port_ps))
        then internalError ("genInstances: bad submod instantiation arg: " ++
                               ppReadable bad_submod_port_ps)
        else
            (final_ds,
             inst_decl_groups,
             inst_def_groups,
             (submod_inputs, reg_inputs, rwire_inputs, probe_inputs),
             extra_submod_decls,
             inlined_reg_blocks,
             inout_rewire_map,
             top_level_comments)


-- a wrapper for mkInstGroup,
-- this creates the decls and defs for non-inlined submodules;
-- if the verilogDeclareAllFirst flag is on, then this is straightforward
-- and the wrapper is trivial, but if the flag is off then work is done
-- to sort the instantiations and declare any needed signals etc
-- (any signals which are pre-declared are returned as the fourth item
-- of the tuple)
mkSubmodGroups ::
    Flags -> [AStateOut] -> SizeAndTypeMap -> [(Id,[String])] -> [VId] ->
    [(AId, VMItem, InstInfo)] ->
    ([(AId, [VId])], [VMItem], [VMItem], [VId])
mkSubmodGroups flags sos sztm submod_comments decls_so_far submod_infos =
    let
        (submod_decl_groups, submod_def_groups) =
            apFst catMaybes $ apSnd catMaybes $
            unzip $
            map (mkInstGroup flags sos sztm submod_comments) submod_infos

        submod_inputs =
            let getInputs (i, _, (_,_,_,ins,_)) = (i, map snd ins)
            in  map getInputs submod_infos
    in
        -- If the verilogDeclareAllFirst flag is on, then we are done;
        -- if not, then "submod_def_groups" will be an empty list and
        -- we need to sort the insts etc to allow the intermingling
        if (verilogDeclareAllFirst flags)
        then (submod_inputs, submod_decl_groups, submod_def_groups, [])
        else
            let
               (new_submod_groups, extra_submod_decls) =
                   fixupSubmodGroups sos sztm submod_infos decls_so_far
                       submod_decl_groups
            in
               -- check that the assumption is OK
               if (null submod_def_groups)
               then (submod_inputs, new_submod_groups, [], extra_submod_decls)
               else internalError "AVerilog mkSubmodGroups: defs not null"


fixupSubmodGroups ::
    [AStateOut] -> SizeAndTypeMap -> [(AId, VMItem, InstInfo)] -> [VId] ->
    [VMItem] -> ([VMItem], [VId])
fixupSubmodGroups sos sztm submod_infos decls_so_far submod_groups =
    let

    -- ----------
    -- tsort the instantiations so that insts whose outputs are inputs
    -- to later insts appear first

        -- we want to sort the groups, but join them with the inst id
        -- for uniqueness.
        -- also, keep some inst info for a later step (adding decls).
        inst_nodes = zipWith (\(i,_,(_,ps,_,_,_)) g -> (i,g,ps))
                             submod_infos submod_groups

        submod_igs = zip submod_infos submod_groups
        inst_edges =
           [ ((i2,g2,ports2), (i1,g1,ports1)) |
                 -- for each inst with inst ports (clocks, resets)
                 ((i1, _, (_, ports1, _, _, _)), g1) <- submod_igs,
                 (_, VEVar in_port) <- ports1,
                 -- for each inst with outputs (special or otherwise)
                 ((i2, _, (_, ports2, special, _, outs)), g2) <- submod_igs,
                 (_, out_port) <- special ++ outs,
                 -- if the connection wire matches
                 in_port == out_port
           ]

        -- G.topSort doesn't seem to catch errors (or not nicely),
        -- so we check for cycles ourselves
        sorted_inst_nodes :: [(AId, VMItem, [(VId,VExpr)])]
        sorted_inst_nodes = unsafePerformIO $ do
            inst_graph <- G.makeGraph (reverse inst_nodes) inst_edges
            cycles <- G.findCycles inst_graph
            let cycle_ids = map (map fst3) cycles
            if (null inst_edges) then
              return (inst_nodes)
             else if (not (null cycles)) then
                  internalError
                    ("genInstances: instantiations are cyclic: " ++
                     ppReadable cycle_ids)
                   else return (G.topSort inst_graph)

    -- ----------
    -- insert decls for non-method input port uses

    -- Some non-method input ports might involve wires that have not
    -- yet been declared.  As a temporary solution, we will simply
    -- declare the signal prior to the instantiation.  Thus, we fold
    -- along the instantiations (rather than map) to keep track of the
    -- wires we have declared so far.

        (final_submod_groups, extra_submod_decls) =
            apFst reverse $
            foldl (addInstPortDecls sztm decls_so_far) ([],[])
                  sorted_inst_nodes
    in
        (final_submod_groups, extra_submod_decls)


-- create a group of Verilog statements for a submodule instantiation
mkInstGroup :: Flags -> [AStateOut] -> SizeAndTypeMap -> [(Id,[String])] ->
               (AId, VMItem, InstInfo) -> (Maybe VMItem, Maybe VMItem)
mkInstGroup flags sos sztm comments_map (instname, vmi, info) =
    let (_, _, special, ins, outs) = info
        -- nub on the output values because there can be permissible overlap between
        -- "special" clock/reset outputs and method outputs
        wire_decls =
            map (mkInstInputDecl sztm instname . snd) ins ++
            map (mkInstOutputDecl sos instname VDWire . snd) (nub (special ++ outs))
        user_comment = case (lookup instname comments_map) of
                           Nothing -> []
                           Just cs -> concatMap lines cs
        inst_comment =
            ("submodule " ++ getIdString instname) : user_comment
        decl_comment =
            ["ports of submodule " ++ getIdString instname]
        -- if we keep decls and instantiation together:
        unified_group =
            Just $ VMComment inst_comment
                       (VMGroup False [mergeCommonDecl wire_decls ++ [vmi]])
        -- if we separate them (so that decls can all be first):
        decl_group = if (null wire_decls)
                     then Nothing
                     else Just $ VMComment decl_comment
                                     (VMGroup False [mergeCommonDecl wire_decls])
        def_group  = Just $ VMComment inst_comment vmi
    in
        if (verilogDeclareAllFirst flags)
        then (decl_group,    def_group)
        else (unified_group, Nothing)

-- create one group of Verilog wire declarations for all probes
-- (each probe has one input, with obvious name, so no need to add a
--  comment and empty line for each probe)
-- (note that there is no instantiation for Probes, just the wire)
mkProbeGroup :: [AStateOut] -> SizeAndTypeMap -> [(Id, [String])] ->
                [(AId, VMItem, InstInfo)] ->
                ([VId], [VMItem])
mkProbeGroup sos sztm comments_map probe_infos =
    let
        getProbeInput (instname, vmi, (_, _, _, inps, _)) =
            map (mkInstInputDecl sztm instname . snd) inps
        -- we drop the vmi and just declare the input port
        -- (there shouldn't be any outputs)
        probe_decls = concatMap getProbeInput probe_infos
        decl_ids = [ i | (VMDecl (VVDecl _ _ [VVar i])) <- probe_decls ]
        -- one comment for the entire group, not per probe
        -- (the inst of each probe is obvious from the wire name)
        -- but include a comment for any attached to a probe
        mkProbeComment instname =
            case (lookup instname comments_map) of
                Nothing -> Nothing
                Just cs -> Just (("Comments for probe " ++
                                  quote (getIdString instname) ++ ":") :
                                 indentLines 2 (concatMap lines cs))
        inst_comments =
            insertBlankLines $
                mapMaybe (mkProbeComment . fst3) probe_infos
        hdr_comment = ["probes"]
        comment = if (null inst_comments)
                  then hdr_comment
                  else hdr_comment ++ [""] ++ inst_comments ++ [""]
        group = VMComment comment (VMGroup False [mergeCommonDecl probe_decls])
    in
        if (null probe_decls)
        then ([], [])
        else (decl_ids, [group])

-- create a group of Verilog statements for an inlined register "instantiation"
mkRegGroup :: [AStateOut] -> SizeAndTypeMap -> [(Id, [String])] ->
              RegInstInfo -> VMItem
mkRegGroup sos sztm comments_map (inst_vid, def_name, _, inps, (out, out_size)) =
    let
        reg_decl = VMDecl (VVDecl VDReg out_size [VVar out])
        -- if the EN is 0, then D_IN might not be defined!
        -- so have a backup in case the signal is not defined
        inp_decls = map (mkInstInputDeclWithDefault sztm) inps
        all_decls = (reg_decl : mergeCommonDecl inp_decls)
        comments = lookupWithDefault comments_map [] (vidToId inst_vid)
    in  VMRegGroup inst_vid
                   def_name
                   comments
                   (VMGroup False [all_decls])

mkRWireGroup :: SizeAndTypeMap -> [AId] -> ([VId], [VMItem])
mkRWireGroup sztm rws =
    let rw_decls = mapMaybe (mkInstInputDeclMaybe sztm . vId) rws
        decl_ids = [ i | (VMDecl (VVDecl _ _ [VVar i])) <- rw_decls ]
        comment = ["inlined wires"]
        group = VMComment comment (VMGroup False [(mergeCommonDecl rw_decls)])
    in  if (null rw_decls)
        then ([],[])
        else (decl_ids, [group])

-- -----

-- when folded left along a tsort'ed list of instances, it inserts additional
-- signal decls for signals used in non-method ports of the instantiations.
-- the resulting list of VMItem groups is in reverse order (due to foldl).
addInstPortDecls :: SizeAndTypeMap -> [VId] ->
                    ([VMItem], [VId]) ->
                    (AId, VMItem, [(VId,VExpr)]) ->
                    ([VMItem], [VId])
addInstPortDecls sztm decls (gs, new_decls) (i, inst_g, ps) =
    let
        -- variables used in the inst which have not already been declared
        -- (prior to submod instances or by an earlier submod inst)
        vs = [ i | (_, VEVar i) <- ps, i `notElem` (decls ++ new_decls) ]
        -- convert to decl
        v_decls = map (mkInstInputDecl sztm i) vs
        -- create a group for it
        decl_g = VMGroup False [mergeCommonDecl v_decls]
    in
        if (null vs)
        then (inst_g:gs, new_decls)
        else (inst_g : decl_g : gs, vs ++ new_decls)

-- -----

-- for a submodule output, lookup the size and create a Verilog decl
-- of the appropriate size (with the given type)
-- (the type is specified, because inlined Reg outputs are of type VDReg)
mkInstOutputDecl :: [AStateOut] -> AId -> VDType -> VId -> VMItem
mkInstOutputDecl sos inst_id decl_type out_port_id =
    let mkDecl i sz = VMDecl (VVDecl decl_type sz [VVar i])
        out_port_aid = vidToId out_port_id
    in  case (lookup out_port_aid sos) of
            Just asz -> mkDecl out_port_id (vSize asz)
            Nothing -> internalError ("mkInstOutputDecl: instance `" ++
                                      getIdString inst_id ++
                                      "' output port not found: " ++
                                      getVIdString out_port_id)

-- for a submodule input, lookup the size and create a Verilog decl
-- of the appropriate size and type (some decls are defined with case-stmt)
mkInstInputDecl :: SizeAndTypeMap -> Id -> VId -> VMItem
mkInstInputDecl sztm inst_id in_port_id =
    let mkDecl i sz t = VMDecl (VVDecl t sz [VVar i])
    in  case (getSizeAndTypeM in_port_id sztm) of
            Just (sz, t) -> mkDecl in_port_id sz t
            Nothing -> internalError ("mkInstInputDecl: instance `" ++
                                      getIdString inst_id ++
                                      "' input port not found: " ++
                                      getVIdString in_port_id ++
                                      "\n  size and type map = " ++
                                      ppReadable sztm)

mkInstInputDeclWithDefault :: SizeAndTypeMap -> (VId, Maybe VRange) -> VMItem
mkInstInputDeclWithDefault sztm (in_port_id, in_port_size) =
    let mkDecl i sz t = VMDecl (VVDecl t sz [VVar i])
    in  case (getSizeAndTypeM in_port_id sztm) of
            Just (sz, t) -> mkDecl in_port_id sz t
            Nothing -> mkDecl in_port_id in_port_size VDWire

mkInstInputDeclMaybe :: SizeAndTypeMap -> VId -> Maybe VMItem
mkInstInputDeclMaybe sztm in_port_id =
    let mkDecl i sz t = VMDecl (VVDecl t sz [VVar i])
    in  case (getSizeAndTypeM in_port_id sztm) of
            Just (sz, t) -> Just (mkDecl in_port_id sz t)
            Nothing -> Nothing

-- -----

-- used to check if instantiation parameter exprs are ok
-- (first argument is a list of ids which are known to be constant --
-- that is, incoming parameters)
isConstVE :: [Id] -> VExpr -> Bool
isConstVE _  (VEConst {}) = True
isConstVE _  (VEWConst {}) = True
isConstVE _  (VEUnknown {}) = True
isConstVE _  (VEString {}) = True
isConstVE _  (VEReal {}) = True
isConstVE _  (VETriConst {}) = True
isConstVE ps (VERepeat e1 e2) = isConstVE ps e1 && isConstVE ps e2
isConstVE ps (VEConcat es) = all (isConstVE ps) es
-- these could be assumed to be False, but let's check anyway
isConstVE ps (VEUnOp _ _ e) = isConstVE ps e
isConstVE ps (VEOp _ e1 _ e2) = isConstVE ps e1 && isConstVE ps e2
isConstVE ps (VESelect e1 e2 e3) = isConstVE ps e1 &&
                                   isConstVE ps e2 && isConstVE ps e3
isConstVE ps (VESelect1 e1 e2) = isConstVE ps e1 && isConstVE ps e2
isConstVE ps (VEIf e1 e2 e3) = isConstVE ps e1 &&
                               isConstVE ps e2 && isConstVE ps e3
-- consider references to Ids to be not constant, unless otherwise told
isConstVE ps (VEVar vid) = (vidToId vid `elem` ps)
isConstVE ps (VEIndex vid idx) = isConstVE ps (VEVar vid) &&
                                 isConstVE ps idx
isConstVE _ (VEFctCall {}) = False
isConstVE _ (VEMacro {}) = True

-- ==============================
-- utilities for pass-through comments

insertBlankLines :: [[String]] -> [String]
insertBlankLines [] = []
insertBlankLines xss = foldr1 (\xs ys -> xs ++ [""] ++ ys) xss

indentLines :: Int -> [String] -> [String]
indentLines n xs =
    let spaces = replicate n ' '
    in  map (spaces ++) xs

makeTopComments :: String -> [(Id, [String])] -> [String]
makeTopComments item_type ics =
    let
        -- merge items that have the same comment
        mergeComment (i,cs) [] = [([i],cs)]
        mergeComment (i,cs) ((is,cs'):rest) =
            if (cs' == cs)
            then (((i:is),cs'):rest)
            else ((is,cs'):(mergeComment (i,cs) rest))

        -- the merged comments list
        ics_merged = foldr mergeComment [] ics

        -- split and indent lines
        splitAndIndent cs = indentLines 2 (concatMap lines cs)

        -- convert them into top-level comments
        mkTopComment ([],cs) = internalError ("makeTopComments mkTopComment")
        mkTopComment ([i],cs) =
            let hdr = "Comments on the inlined " ++ item_type ++ " " ++
                      quote (getIdString i) ++ ":"
            in  hdr : splitAndIndent cs
        mkTopComment (is,cs) =
            let quoted_items = map (quote . getIdString) is
                item_list = intercalate ", " quoted_items
                hdr = "Comments on the inlined " ++ item_type ++ "s " ++
                      item_list ++ ":"
                wrapped_hdr = pretty 78 78 (s2par hdr)
            in  (lines wrapped_hdr) ++ splitAndIndent cs
    in
        insertBlankLines (map mkTopComment ics_merged)


-- ==============================
-- buildPrimModules

-- extracts the instantiated "Prim" definitions from the verilog and builds verilog modules for these
buildPrimModules :: Flags -> [VMItem] -> [VModule]
buildPrimModules flags defs =
    map vMux (muxes `union` primuxes)
    ++ map vPriMux primuxes
    ++ map (vPriEnc rstGateF) (priencs `union` primuxes)
  where
      rstGateF = False -- rstGate flags -- "gate rule fire signals with reset" ??

      muxes = nub (concatMap (getInsts "Mux_") defs)          --- XXX hack
      primuxes = nub (concatMap (getInsts "PriMux_") defs)    --- XXX hack
      priencs = nub (concatMap (getInsts "PriEnc_") defs)     --- XXX hack

getInsts :: String -> VMItem -> [Integer]
getInsts s (VMInst (VId s' _ _) _ _ _) = match s s'
  where match [] s@(c:_) | isDigit c = [read s]
        match (c:cs) (d:ds) | c == d = match cs ds
        match _ _ = []
getInsts s (VMComment _ i) = getInsts s i
getInsts s (VMGroup _ iss) = concatMap (concatMap (getInsts s)) iss
getInsts _ _ = []


-- ==============================
-- Creating test scan ports

createScanStructures :: [PProp] -> ([VMItem],[VArg])
createScanStructures pps = (scanDefs, scanArgs)
    where
    (doScanInsert, nScans) =
        let find [] = (False, 0)
            find (PPscanInsert i : _) = (True, i)
            find (_ : ps) = find ps
        in  find pps
    scanDefs = if doScanInsert then createScanDefs nScans else []
    scanArgs = if doScanInsert then createScanArgs nScans else []


-- Create a [VArg] which has a input scan_en, scan_in[n-1:0], and output scan_out[n-1:0]
createScanArgs :: Integer -> [VArg]
createScanArgs n =
        [ VAInput (mkVId "scan_en") Nothing,
          VAInput (mkVId "scan_in") (Just (VEConst (n-1), VEConst 0)),
          VAOutput (mkVId "scan_out") (Just (VEConst (n-1), VEConst 0))
        ]
--
createScanDefs :: Integer -> [VMItem]
createScanDefs n =
        [ VMDecl (VVDecl
                VDWire
                (Just (VEConst (n-1), VEConst 0))
                [VVar (mkVId "scan_out")])
        ]


-- ==============================
-- Bit-blasting ports

createBitBlast :: [VArg] -> ([VArg],[VMItem])
createBitBlast args =
        let (ass, dss) = unzip (map blast args)
            blast a@(VAParameter {}) = ([a], [])
            blast a@(VAOutput vi@(VId s _ _) msz) =
                let su = map toUpper s
                    iu = mkVId su
--                  w = VMDecl (VVDecl VDWire msz [v])
                in  case msz of
                        Nothing -> if s == su then ([a], []) else
                                ([VAOutput iu msz],
                                 [{-w,-} VMAssign (VLId iu) (VEVar vi)])
                        Just (VEConst n, VEConst 0) ->
                                let vis = vids_sub_name "BBL1" su n
                                    mkOutput i = VAOutput i Nothing
                                in  (map mkOutput vis,
                                     [{-w,-} VMAssign (VLConcat (map VLId vis)) (VEVar vi)])
                        x -> internalError ("blast 1 " ++ ppReadable x)
            blast a@(VAInput vi@(VId s _ _) msz) =
                let su = map toUpper s
                    iu = mkVId su
                    w = VMDecl (VVDecl VDWire msz [VVar vi])
                in  case msz of
                        Nothing -> if s == su then ([a], []) else
                                ([VAInput iu msz],
                                 [w, VMAssign (VLId vi) (VEVar iu)])
                        Just (VEConst n, VEConst 0) ->
                                let vis = vids_sub_name "BBL2" su n
                                    mkOutput i = VAOutput i Nothing
                                in  (map mkOutput vis,
                                     [w, VMAssign (VLId vi) (VEConcat (map VEVar vis))])
                        x -> internalError ("blast 2 " ++ ppReadable x)
            blast a = internalError ("blast 3 " ++ ppReadable a)
        in  (concat ass, concat dss)

vids_sub_name :: a -> String -> Integer -> [VId]
vids_sub_name tag su n =
    [mkVId lname | i <- [0..n],
                   let lname = su ++ "_" ++ itos i]

unBlast :: [VArg] -> [VMItem]
unBlast args =
        let
            unblast :: VArg -> [VMItem]
            unblast a@(VAParameter {}) = []
            unblast a@(VAOutput vi@(VId s _ _) msz) =
                let su = map toUpper s
                    iu = mkVId su
                in  case msz of
                        Nothing -> if s == su then [] else [VMAssign (VLId vi) (VEVar iu)]
                        Just (VEConst n, VEConst 0) ->
                                let vis = vids_sub_name "UBL1" su n
                                in  [VMAssign (VLId vi) (VEConcat (map VEVar vis))]
                        x -> internalError ("unblast 1 " ++ ppReadable x)
            unblast a@(VAInput vi@(VId s _ _) msz) =
                let su = map toUpper s
                    iu = mkVId su
                in  case msz of
                        Nothing -> if s == su then [] else [VMAssign (VLId iu) (VEVar vi)]
                        Just (VEConst n, VEConst 0) ->
                                let vis = vids_sub_name "UBL1" su n
                                in  [VMAssign (VLConcat (map VLId vis)) (VEVar vi)]
                        x -> internalError ("unblast 2 " ++ ppReadable x)
            unblast a = internalError ("unblast 3 " ++ ppReadable a)
        in  concatMap unblast args

-- un blasted
ubInst :: [VId] -> VId -> VMItem
ubInst ids mod = VMInst
                 { vi_module_name  = mod,
                   vi_inst_name    = pref verilogInstancePrefix mod,
                   vi_inst_params  = Right [],
                   vi_inst_ports   = [(i, Just (VEVar i)) | i <- ids]
                 }


-- ------------------------------

-- extract out the ids of the port (IO arguments)
getArgIds :: [VArg] -> [VId]
getArgIds args = concatMap getio args
  where getio (VAInput i _) = [i]
        getio (VAOutput i _) = [i]
        getio (VAParameter {}) = []
        getio (VAInout i mi _) = internalError ("getArgIds getio")


-- ==============================

{-
-- Move the declarations to the front of the list
declsFirst :: [VMItem] -> [VMItem]
declsFirst vss = (mergeCommonDecl ds) ++ (sort ss)
  where (ds,ss) = partition isDecl vss
-}

-- Merge common declarations into one to avoid pages of wire declarations
mergeCommonDecl :: [VMItem] -> [VMItem]
mergeCommonDecl ins =
    -- group decls with common types and merge them
    map mergeOneDecl groupss
  where
    sins    = sort ins  -- is this sort needed?
    groupss = groupBy commonTypes sins

    -- two decls are the same if they are decls without assignment,
    -- and the type (reg/wire) matches and the range (bit-size) matches
    commonTypes :: VMItem -> VMItem -> Bool
    commonTypes (VMDecl vvd1) (VMDecl vvd2) = commonDeclTypes vvd1 vvd2
    commonTypes _ _ = False

    mergeOneDecl :: [VMItem] -> VMItem
    mergeOneDecl [] = internalError ("mergeCommonDecl: unexpected empty list!")
    mergeOneDecl [a] = a
    mergeOneDecl (a@(VMDecl (VVDecl vt vr vars)):as) =
        let -- extract the vars from the other decls
            extrVars :: VMItem -> [VVar]
            extrVars (VMDecl (VVDecl _ _ vars)) = vars
            extrVars _ = []
            -- all the vars, sorted
            merged_vars = sort (vars ++ concatMap extrVars as)
        in  VMDecl (VVDecl vt vr merged_vars)
    mergeOneDecl _ = internalError ("mergeCommonDecl::mergeOneDecl")


-- ==============================

type SizeAndTypeMap = M.Map VId (Maybe VRange, VDType)

mkSizeAndTypeMap :: [VMItem] -> SizeAndTypeMap
mkSizeAndTypeMap defs = M.fromList $
  [ (i, (sz, VDWire)) | VMDecl (VVDWire sz (VVar i) _) <- defs ] ++
  [ (i, (sz, t)) | VMDecl (VVDecl t sz vs) <- defs, VVar i <- vs ]

getSizeAndTypeM :: VId -> SizeAndTypeMap -> Maybe (Maybe VRange, VDType)
getSizeAndTypeM = M.lookup

-- assumes that decls haven't been merged yet
isDeclFromList :: S.Set VId -> VMItem -> Bool
isDeclFromList is (VMDecl (VVDWire _ vv _))  = vvName vv `S.member` is
isDeclFromList is (VMDecl (VVDecl _ _ [vv])) = vvName vv `S.member` is
isDeclFromList _  _ = False

-- lookup defs, maintaining their order, and returning the remaining defs
findADefs :: [AId] -> M.Map AId ADef -> ([ADef], M.Map AId ADef)
findADefs ds defmap =
    let fn i (ds_accum, defmap_accum) =
            case (M.lookup i defmap_accum) of
              Nothing -> (ds_accum, defmap_accum)
              Just d -> (d:ds_accum, M.delete i defmap_accum)
    in  foldr fn ([], defmap) ds

isADefFromList :: [AId] -> ADef -> Bool
isADefFromList is (ADef i _ _ _) = i `elem` is

-- ==============================

-- If the wire connected to the port of an instantiated submodule is unused,
-- then remove the wire and leave the port unconnected (it will appear as
-- empty parentheses in the Verilog).
--
-- Arguments:
--   ff_blocks = converted foreign function calls
--   defs   = module statements which are Not INSTantiationS (defs)
--   insts  = instantiations
--
-- Returns:
--   * ids of unused signals (for removing from the defs)
--   * the instantiations with the unused ports filtered
--
dropUnusedPortWires :: [VMItem] -> [VMItem] -> [VExpr] ->
                       [(AId, VMItem, InstInfo)] ->
                       ([VId], [(AId, VMItem, InstInfo)])
dropUnusedPortWires ff_blocks defs reg_uses inst_infos =
    let
        -- the vars used in the defs and the foreign function calls and
        -- as clk/rst to registers
        used = S.fromList $ vuses (defs ++ ff_blocks) ++ vuses reg_uses
        -- the vars defined with values
        def_ids = S.fromList $ [ v | VMDecl (VVDecl _ _ vs) <- defs, VVar v <- vs ] ++
                               [ v | VMDecl (VVDWire _ (VVar v) _) <- defs ]
        -- just the instantiations
        insts = [ is | (_, is, _) <- inst_infos ]
        -- the ios of the modules
        -- XXX this could come from the aspkg field, but we recompute:
        submod_io = S.fromList $ [ v | (_, _, (_, _, spec, ins, outs)) <- inst_infos,
                                       (_,v) <- spec ++ ins ++ outs ]
        -- unused wires are those which:
        unused = [ i | -- appear only once in the instantiations
                       -- (that is, they do not connect between two instances)
                       (1, i) <- count (vuses insts),
                       -- are submodule inputs or outputs
                       i `S.member` submod_io,
                       -- (for inputs) are not defined with a value
                       i `S.notMember` def_ids,
                       -- (for outputs) are not used in any defs or ffunc calls
                       i `S.notMember` used ]
        inst_infos_filtered = if (null unused)
                              then inst_infos
                              else map (dropIds unused) inst_infos
    in
        (unused, inst_infos_filtered)

notProbe :: (AId, VMItem, InstInfo) -> Bool
notProbe (_, VMInst (VId string _ _) _ _ _, _) = (string /= "Probe")
notProbe item = True

count :: (Ord a) => [a] -> [(Int, a)]
count = let getInfo xs = (length xs, headOrErr "count" xs)
        in  sort . map getInfo . group . sort

dropIds :: [VId] -> (AId, VMItem, InstInfo) -> (AId, VMItem, InstInfo)
dropIds is (i, vmi, info) =
    let
        -- function to drop a port connection from VMInst if it's in is
        dropInstPort (Just (VEVar i)) | i `elem` is = Nothing
        dropInstPort e = e

        -- function to drop ports from the VMInst
        dropFromVMInst (VMInst m n es ves) =
            VMInst m n es (mapSnd dropInstPort ves)
        dropFromVMInst m = internalError ("AVerilog dropIds: " ++ ppReadable m)

        -- function to drop ports from the InstInfo
        dropFromInstInfo (ps, port_ps, special, ins, outs) =
            (ps,
             port_ps,  -- we know that these will not be dropped
             dropFromIdList special,
             dropFromIdList ins,
             dropFromIdList outs)

        -- drop from a list of pairs
        dropFromIdList = filter (\ (a,b) -> b `notElem` is)
    in
        (i, dropFromVMInst vmi, dropFromInstInfo info)


-- ------------------------------

class VUse a where
    vuses :: a -> [VId]

instance VUse VId where
    vuses x = [x]

instance {-# OVERLAPPING #-} VUse String where
    vuses x = []

instance {-# OVERLAPPABLE #-} (VUse a) => VUse [a] where
    vuses xs = concatMap vuses xs

instance (VUse a) => VUse (Maybe a) where
    vuses Nothing = []
    vuses (Just x) = vuses x

instance (VUse a, VUse b) => VUse (a,b) where
    vuses (x,y) = vuses x ++ vuses y

instance (VUse a, VUse b) => VUse (Either a b) where
    vuses (Left es) = vuses es
    vuses (Right as) = vuses as

instance VUse VMItem where
    vuses (VMDecl d) = vuses d
    vuses (VMStmt {vi_body = body}) = vuses body
    vuses (VMAssign l e) = vuses l ++ vuses e
    vuses (VMInst _ _ ps as) = vuses ps ++ vuses as
    vuses (VMGroup _ ll) = concatMap vuses (concat ll)
    vuses _ = []

instance VUse VStmt where
    vuses (VAt e s) = vuses e ++ vuses s
    vuses (Valways s) = vuses s
    vuses (Vinitial s) = vuses s
    vuses (VSeq ss) = vuses ss
    vuses s@(Vcasex {}) = vuses (vs_case_expr s) ++ vuses (vs_case_arms s)
    vuses s@(Vcase {}) = vuses (vs_case_expr s) ++ vuses (vs_case_arms s)
    vuses (VAssign l e) = vuses l ++ vuses e
    vuses (VAssignA l e) = vuses l ++ vuses e
    vuses (Vif e s) = vuses e ++ vuses s
    vuses (Vifelse e s s') = vuses e ++ vuses s ++ vuses s'
    vuses (Vdumpvars _ _) = []
    vuses (VTask _ es) = vuses es
    vuses (VAssert e es) = vuses e ++ vuses es
    vuses (VZeroDelay) = []

instance VUse VLValue where
    vuses (VLId i) = [i]
    vuses (VLConcat ls) = vuses ls
    vuses (VLSub l e) = vuses l ++ vuses e

instance VUse VCaseArm where
    vuses (VCaseArm es s) = vuses es ++ vuses s
    vuses (VDefault s) = vuses s

instance VUse VVDecl where
    vuses (VVDecl _ _ _) = []
    vuses (VVDWire _ _ e) = vuses e

instance VUse VEventExpr where
    vuses (VEEOr e e') = vuses e ++ vuses e'
    vuses (VEEposedge e) = vuses e
    vuses (VEEnegedge e) = vuses e
    vuses (VEE e) = vuses e
    vuses (VEEMacro s e) = vuses e

instance VUse VExpr where
    vuses (VEConst _) = []
    vuses (VEWConst _ _ _ _) = []
    vuses (VEUnknown _ _) = []
    vuses (VEReal _) = []
    vuses (VEString _) = []
    vuses (VETriConst _) = []
    vuses (VEUnOp _ _ e) = vuses e
    vuses (VEOp _ e _ e') = vuses e ++ vuses e'
    vuses (VEVar i) = [i]
    vuses (VEConcat es) = vuses es
    vuses (VEIndex i e) = i : vuses e
    vuses (VESelect e1 e2 e3) = vuses e1 ++ vuses e2 ++ vuses e3
    vuses (VESelect1 e1 e2) = vuses e1 ++ vuses e2
    vuses (VERepeat e e') = vuses e ++ vuses e'
    vuses (VEIf e1 e2 e3) = vuses e1 ++ vuses e2 ++ vuses e3
    vuses (VEFctCall _ es) = vuses es
    vuses (VEMacro {}) = []


-- ==============================
