module InlineWires(aInlineWires) where

import ASyntax
import ASyntaxUtil
import Data.List(partition)
import PFPrint
import IntLit(IntLit(..))
import qualified Data.Map as M
import qualified Data.Set as S
import BackendNamingConventions
import Error(internalError, EMsg, WMsg)
import Flags(Flags, removeCross)

-- import Debug.Trace

--
-- The following contents of the ASPackage are changed:
--   vs    :: [AVInst]    = state elements (Verilog instances)
--   svars :: [AStateOut] = state element outputs (wires coming out of state)
--   defs  :: [ADef]      = local definitions
--
--
-- To inline wires, we do the following:
--
--  (1) Separate out the RWire, RWire0 and BypassWire instances from "vs",
--      leaving all other instances.
--
--  (2) For each wire, we used to create an ADef for the
--      whas and wget ports (RWire0 has no wget port), and define them
--      in terms of the wset and wset_1 ports (the enable and the input
--      data).  (Except when the set is not called, and so we give whas
--      a constant value of False and wget a value of dont-care.)
--      This resulted in unnecessary indirection, and sometimes the rw$set_1
--      signal would remain in the Verilog and not the rw$wget.  So now,
--      instead of indirection, we rename rw$EN_set and rw$set_1 to be
--      rw$whas and rw$wget.  If the set signals aren't defined, then we
--      do have to declare a new def for the outputs, with constant values.
--      Note that we do not define rw$whas for BypassWires (since it should be
--      just a constant 1).
--
--  (3) Create a substitution from (ASPort rw$whas) to (ASDef rw$whas),
--      and substitute over the ASPackage.  (Because the signals are no
--      longer submodule ports, but internally defined signals.)
--
--  (4) The "svars" is a list of state element outputs, so remove all
--      the wire outputs from this list (those are just the def ids).
--
--      But don't lose them; keep them in the "ws" field in the ASPackage.
--      This is a list of ports to inlined modules which should not be
--      inlined if not necessary (for instance, if it only has one use).
--
--  (5) Return the ASPackage with the new defs, with the filtered vs,
--      with the filtered svars, and with the substitution applied to
--      all expressions in the ASPackage (with aSubst).
--

aInlineWires :: Flags -> ASPackage -> (ASPackage, [WMsg], [EMsg])
aInlineWires flags pkg@(ASPackage { aspkg_state_instances = vs,
                              aspkg_state_outputs = svars,
                              aspkg_values = defs,
                              aspkg_signal_info = si }) =
--  trace (ppReadable rws ++ ppReadable ds) $
    (aSubst rmap (pkg { aspkg_state_instances = nonwire_vs,
                        aspkg_state_outputs = nonwire_svars,
                         aspkg_values = (defs' ++ newdefs),
                        aspkg_inlined_ports = ws',
                        aspkg_signal_info = si' }),
     warnings, errors)
  where -- definition map (id -> value)
        defmap = M.fromList [(i, e) | (ADef i _t e _) <- defs]
        defset = M.keysSet defmap
        -- find the RWires and RWire0s, and the remaining
        -- instances which we will leave in the package
        (rws, vs') = partition isRWire vs
        (rw0s, nonrwire_vs) = partition isRWire0 vs'
        (bw0s, nonrwire_vs') = partition isBypassWire0 nonrwire_vs
        should_inline_bw x = isBypassWire x &&
                          ((not (isClockCrossingBypassWire x)) || (removeCross flags))
        (bws, nonwire_vs) = partition should_inline_bw nonrwire_vs'
        -- for each RWire instance, make a tuple of:
        --  * the instance name
        --  * the instance outputs (whas and possibly wget)
        --  * any new defs (only if the value is constant)
        --  * any substitutions on the defs (e.g. replace wsetEn with whas)
        --  * any warnings to trigger
        --  * any errors to trigger
        rwire_tuples = map mkRW rws ++ map mkRW0 rw0s ++
                       map mkBW bws ++ map mkBW0 bw0s

        -- record the rwire output port names in ws
        ws' = concatMap (\(a,b,c,d,e,f) -> b) rwire_tuples

        -- record the signal info for RTL grouping
        rwire_signal_info = map (\(a,b,c,d,e,f) -> (a,"RWire",b)) rwire_tuples
        si_ips = aspsi_inlined_ports si
        si' = si { aspsi_inlined_ports = rwire_signal_info ++ si_ips }

        -- XXX this traverses the package once for every inlines wire
        -- for performance the sub should be aggregated into a map
        -- perform the substitutions
        -- to rename input port defs with the output names
        renameADef s d@(ADef { adef_objid = i }) =
            case (lookup i s) of
                Nothing    -> d
                Just new_i -> d { adef_objid = new_i }
        name_subst = concatMap (\(a,b,c,d,e,f) -> d) rwire_tuples
        defs' = map (renameADef name_subst) defs

        -- any new definitions
        -- (to constants, when the input port was dangling)
        newdefs = concatMap (\(a,b,c,d,e,f) -> c) rwire_tuples

        -- -----
        warnings = concatMap (\(a,b,c,d,e,f) -> e) rwire_tuples
        errors   = concatMap (\(a,b,c,d,e,f) -> f) rwire_tuples

        -- since the RWire output ports are now defined locally and are
        -- not outputs of modules anymore, remove them from the svars list
        (wire_svars, nonwire_svars) =
            partition (\(i,t) -> i `elem` ws') svars

        -- create a map of the rwire values methods to the signals which
        -- now carry their values (whether new def or subst of existing def)
        -- (this will be used to replace ASPort uses with ASDef uses)
        rmap = M.fromList [(i, ASDef t i) | (i, t) <- wire_svars]

        -- functions for making the defs for RWire and BypassWire
        mkRW0 :: AVInst -> (AId,[AId],[ADef],[(AId,AId)],[WMsg],[EMsg])
        mkRW0 (AVInst { avi_vname=i }) = rw_defs i 0 True False

        mkRW :: AVInst  -> (AId,[AId],[ADef],[(AId,AId)],[WMsg],[EMsg])
        mkRW (AVInst { avi_vname=i,
                       avi_iargs=(ASInt _ _ (IntLit _ _ n) : _) }) = rw_defs i n False False
        mkRW (x@(_)) = internalError ("aRWire.mkRW: " ++ ppReadable x)

        mkBW0 :: AVInst  -> (AId,[AId],[ADef],[(AId,AId)],[WMsg],[EMsg])
        mkBW0 (AVInst { avi_vname=i }) = rw_defs i 0 False True

        mkBW :: AVInst  -> (AId,[AId],[ADef],[(AId,AId)],[WMsg],[EMsg])
        mkBW (AVInst { avi_vname=i,
                       avi_iargs=(ASInt _ _ (IntLit _ _ n) : _) }) = rw_defs i n False True
        mkBW (x@(_)) = internalError ("aRWire.mkBW: " ++ ppReadable x)

        -- take in the base module identifier
        -- the number of bits in the data input/output
        -- whether the enable should be 1 (for BypassWire)
        -- return:
        --   instance identifier
        --   list of state element outputs
        --   new internal definitions (that support the inlining)
        --   a substitution (to replace ASVar by ASDef where necessary)
        --   any warnings encountered (i.e. enables not night)
        rw_defs :: AId -> ASize -> Bool -> Bool -> (AId, [AId], [ADef], [(AId, AId)], [WMsg], [EMsg])
        rw_defs i sz is_rwire0 always_en =
            let
                -- the rwire inputs
                rw_en_id   = rwireSetEnId i
                rw_data_id = rwireSetArgId i
                -- the rwire outputs
                rw_has_id  = rwireHasResId i
                rw_get_id  = rwireGetResId i

                -- we no longer report EEnableNotHigh or EEnableAlwaysLow,
                -- as always_enabled property is now checked in AAddScheduleDefs
                (wmsg, emsg) = ([], [])

                -- what signal names are defined locally
                -- if set enable is not defined, then whas is constant False
                (whas_def, whas_subst) =
                    if always_en then
                      -- no definition or substitution if always_enabled
                      ([], [])
                    else if (rw_en_id `S.member` defset) then
                      ([], [(rw_en_id, rw_has_id)])
                    else
                      ([ADef rw_has_id (ATBit 1) aFalse []], [])
                -- even if the enable has been defined, the data might not be
                -- there because the RWire is never set or because the data
                -- size is 0 (though that is probably unnecessary paranoia)
                (wget_def, wget_subst) =
                    if (is_rwire0) then
                        ([], [])
                    else if (rw_data_id `S.member` defset) then
                        ([], [(rw_data_id, rw_get_id)])
                    else
                        ([ADef rw_get_id (ATBit sz) (ASAny (ATBit sz) Nothing) []],
                         [])
                -- the output names
                outputs =
                    -- wget
                    (if is_rwire0 then [] else [rw_get_id]) ++
                    -- whas
                    (if always_en then [] else [rw_has_id])
            in
                (i, outputs, whas_def ++ wget_def, whas_subst ++ wget_subst, wmsg, emsg)
