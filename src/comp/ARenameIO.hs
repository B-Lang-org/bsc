module ARenameIO(
              aRenameIO
              ) where

import qualified Data.Map as M

import Util(mapFst)
import FStringCompat(FString)

import Flags(Flags)
import ASyntax
import BackendNamingConventions(createVerilogNameMap,
                                xLateIdUsingFStringMap)
import Util(fastNub)
import Pragma(DefProp)

-- ==============================
-- Function: aRenameIO
--

-- Renames connections to the ports of instantiated submodules, as a
-- necessary step in generating Verilog for *any* design, even without
-- rename pragmas.  (It converts ASPackage references in
-- method-notation to use the Verilog port port connection wire names,
-- such as the_fifo$DEQ.)

-- Part of inlining registers is to drop the $Q_OUT from the register
-- signal name.  This is accounted for by createVerilogNameMap, so no
-- special handling is needed here.

aRenameIO :: Flags -> ASPackage -> ASPackage
aRenameIO flags pkg =
    let mi    = aspkg_name pkg
        fmod  = aspkg_is_wrapped pkg
        ps    = aspkg_parameters pkg
        exps  = aspkg_outputs pkg
        imps  = aspkg_inputs pkg
        iomps = aspkg_inouts pkg
        vs    = aspkg_state_instances pkg
        svars = aspkg_state_outputs pkg
        defs  = aspkg_values pkg
        iods  = aspkg_inout_values pkg
        fs    = aspkg_foreign_calls pkg
        ws    = aspkg_inlined_ports pkg
        si    = aspkg_signal_info pkg
        cmap  = aspkg_comment_info pkg

        -- This is the submodule connection map
        -- (see comment on "createVerilogNameMap" for examples)
        vmap = createVerilogNameMap flags pkg

        new_pkg =
            ASPackage mi
                      fmod
                      ps
                      exps
                      imps
                      iomps
                      (map (trI vmap) vs)      -- names in state arg exprs
                      -- remove duplicates because output wires may be hooked up
                      -- to more than one method (e.g. FIFOF_.notFull, FIFOF_.i_notFull)
                      (fastNub (mapFst (tr vmap) svars)) -- state output names
                      (map (trD vmap) defs)    -- names of defs & in def exprs
                      (map (trIOD vmap) iods)  -- names in iodef exprs
                      (map (trFB vmap) fs)     -- names in foreign block exprs
                      (map (tr vmap) ws)       -- inlined port names
                      (trSI vmap si)           -- names in signal info
                      cmap  -- instance names should not have changed

    in
        new_pkg


type FSMap = M.Map FString FString
-- ---------------

-- Translation functions

-- Translate connections to instantiated submodules from method names
-- to port names
--
-- Input:
--  * Mapping of port connection signals like "inst$methpart" to "inst$vport"
--
translateId :: FSMap -> AId -> AId
translateId vmap id = xLateIdUsingFStringMap vmap id

-- a short alias
tr :: FSMap -> AId -> AId
tr = translateId

-- translate an instance
trI :: FSMap -> AVInst -> AVInst
trI mp avi@(AVInst { avi_iargs = es }) = avi { avi_iargs = map (trE mp) es }

-- translate an expression
trE :: FSMap -> AExpr -> AExpr
trE mp (APrim aid t o es)   = APrim aid t o (map (trE mp) es)
trE mp (AMethCall t i m es) = AMethCall t i m (map (trE mp) es)
trE mp (ANoInlineFunCall t i f es) = ANoInlineFunCall t i f (map (trE mp) es)
trE mp (AFunCall t i f isC es) = AFunCall t i f isC (map (trE mp) es)
trE mp (ASPort t i)         = ASPort t (tr mp i)
trE mp (ASParam t i)        = ASParam t (tr mp i)
trE mp (ASDef t i)          = ASDef t (tr mp i)
trE mp e                    = e

-- translate a def
trD :: FSMap -> ADef -> ADef
trD mp (ADef i t e p)         = ADef (tr mp i) t (trE mp e) (map (trP mp) p)

-- there are currently no DefProps that mention state ports,
-- so nothing to translate here
trP :: FSMap -> DefProp -> DefProp
trP mp p = p

-- translate an inout def
trIOD :: FSMap -> ADef -> ADef
trIOD mp (ADef i t e p)       = ADef i t (trE mp e) (map (trP mp) p)

-- translate a foreign block
trFB :: FSMap -> AForeignBlock -> AForeignBlock
trFB mp (clks, fcalls) = (map (trE mp) clks, map (trF mp) fcalls)

-- translate a foreign call
trF :: FSMap -> AForeignCall -> AForeignCall
trF mp (AForeignCall id f es ids resets) =
    AForeignCall id f (map (trE mp) es) ids (map (trE mp) resets)

-- translate the signal info
trSI :: FSMap -> ASPSignalInfo -> ASPSignalInfo
trSI mp si =
    let trClk (clk,gates) = (tr mp clk, map (tr mp) gates)

        trM (Nothing) = Nothing
        trM (Just x)  = Just (tr mp x)

        trMeth ami@(ASPMethodInfo i ty mr me vs args rs) =
            ami { aspm_name      = tr mp i,
                  aspm_mrdyid    = trM mr,
                  aspm_menableid = trM me,
                  aspm_resultids = map (tr mp) vs,
                  aspm_inputs    = map (tr mp) args }

    in  ASPSignalInfo {
            aspsi_inputs = map (tr mp) (aspsi_inputs si),
            aspsi_output_clks = map trClk (aspsi_output_clks si),
            aspsi_output_rsts = map (tr mp) (aspsi_output_rsts si),
            aspsi_ifc_iots = map (tr mp) (aspsi_ifc_iots si),
            aspsi_methods = map trMeth (aspsi_methods si),
            -- inlined rwire names are not renamed,
            -- as the signal exists in the defs with the original name
            aspsi_inlined_ports = aspsi_inlined_ports si,
            -- rule scheduling ports are not renamed
            aspsi_rule_sched = aspsi_rule_sched si,
            -- mux signals are not renamed
            aspsi_mux_selectors = aspsi_mux_selectors si,
            aspsi_mux_values = aspsi_mux_values si,
            aspsi_submod_enables = aspsi_submod_enables si
        }


-- ==============================
