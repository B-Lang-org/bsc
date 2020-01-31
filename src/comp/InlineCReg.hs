module InlineCReg(aInlineCReg) where

import ASyntax
import ASyntaxUtil
import Prim
import Data.List(partition)
import PPrint
import IntLit(IntLit(..))
import qualified Data.Map as M
import qualified Data.Set as S
import BackendNamingConventions
import ErrorUtil(internalError)


--
-- The following contents of the ASPackage are changed:
--   vs    :: [AVInst]    = state elements (Verilog instances)
--   svars :: [AStateOut] = state element outputs (wires coming out of state)
--   defs  :: [ADef]      = local definitions
--
-- See comments in the InlineWires package, on which this is based.
-- However, unlike for RWire, we don't rename the input port def to be
-- the output port def, because the CReg output is a mux not a wire.
-- So, unlike for RWire, we need to record both the inputs and outputs
-- as inlined ports (not just the outputs).
--
-- The register part of the CReg module is retained as a RegN/RegUN/RegA
-- instance.  This is separately inlined in the Verilog generation,
-- depending on the -inline-reg flag.
--

aInlineCReg :: ASPackage -> ASPackage
aInlineCReg pkg@(ASPackage { aspkg_state_instances = vs,
                             aspkg_state_outputs = svars,
                             aspkg_values = defs,
                             aspkg_inlined_ports = ips,
                             aspkg_signal_info = si }) =
    let
        -- definition map (id -> value)
        defmap = M.fromList [(i, e) | (ADef i _t e _) <- defs]
        defset = M.keysSet defmap

        -- find the CReg modules
        -- and the remaining instances which we will leave in the package
        (creg_vs, noncreg_vs) = partition isCRegInst vs

        -- for each CReg instance, make a tuple of:
        --  * the instance name
        --  * the instance inputs and outputs
        --  * new Reg instance
        --  * new Reg instance's output ports
        --  * new defs (for the CReg outputs and the Reg inputs)
        creg_tuples = map mkCR creg_vs

        -- record the CReg port names 
        creg_ports = concatMap (\(a,b,c,d,e) -> b) creg_tuples

        -- record the signal info for RTL grouping
        creg_signal_info = map (\(a,b,c,d,e) -> (a,"CReg",b)) creg_tuples
        si_ips = aspsi_inlined_ports si
        si' = si { aspsi_inlined_ports = creg_signal_info ++ si_ips }

        -- any new definitions
        new_defs = concatMap (\(a,b,c,d,e) -> e) creg_tuples

        -- new Reg instances
        new_vs = map (\(a,b,c,d,e) -> c) creg_tuples

        -- since the CReg output ports are now defined locally and are
        -- not outputs of modules anymore, remove them from the svars list
        (creg_svars, noncreg_svars) =
            -- XXX slightly inefficient because creg_ports contains also inputs
            partition (\(i,t) -> i `elem` creg_ports) svars

        -- the output ports for the new Reg instances
        new_reg_svars = concatMap (\(a,b,c,d,e) -> d) creg_tuples

        -- create a map of the CReg output ports to the signals which
        -- now carry their values
        -- (this will be used to replace ASPort uses with ASDef uses)
        portmap = M.fromList [(i, ASDef t i) | (i, t) <- creg_svars]

        -- function for making the tuple for a CReg
        mkCR :: AVInst -> (AId, [AId], AVInst, [(AId, AType)], [ADef])
        mkCR avi =
            let
                ports = 5
                i = avi_vname avi

                width =
                    case (avi_iargs avi) of
                      (ASInt _ _ (IntLit _ _ n) : _) -> n
                      as -> internalError ("aInlineCReg: " ++ ppReadable as)

                dataTy = ATBit width

                makePorts n =
                    [cregReadResId i n,
                     cregWriteEnId i n,
                     cregWriteArgId i n]
                old_creg_ports = concatMap makePorts [0..(ports-1)]

                -- if a write method is unused, create a def for it
                makeUnusedMethodDefs n =
                    let en_id = cregWriteEnId i n
                        arg_id = cregWriteArgId i n
                        en_def = if (en_id `S.member` defset) then
                                     []
                                 else
                                     [ADef en_id (ATBit 1) aFalse []]
                        -- XXX is it unnecessary paranoia to check the data separately?
                        arg_def = if (arg_id `S.member` defset) then
                                      []
                                  else
                                      [ADef arg_id dataTy (ASAny dataTy Nothing) []]
                    in  en_def ++ arg_def

                makeReadResExpr 0 = ASPort dataTy (regReadResId i)
                makeReadResExpr n =
                    let prev_en_e = ASDef aTBool (cregWriteEnId i (n-1))
                        prev_arg_e = ASDef dataTy (cregWriteArgId i (n-1))
                        prev_res_e = ASDef dataTy (cregReadResId i (n-1))
                    in  APrim defaultAId dataTy PrimIf
                            [prev_en_e, prev_arg_e, prev_res_e]

                makeReadResDef n =
                    let res_id = cregReadResId i n
                    in  ADef res_id dataTy (makeReadResExpr n) []

                new_creg_defs =
                    concatMap makeUnusedMethodDefs [0..(ports-1)] ++
                    map makeReadResDef [0..(ports-1)]

                new_reg_avi = cregToReg avi

                new_reg_ports = [(regReadResId i, dataTy)]

                new_reg_defs =
                    [ADef (regWriteEnId i) (ATBit 1) aTrue [],
                     ADef (regWriteArgId i) dataTy (makeReadResExpr ports) []]
            in
                (i,
                 old_creg_ports,
                 new_reg_avi,
                 new_reg_ports,
                 new_creg_defs ++ new_reg_defs)

    in
        aSubst portmap $
          pkg { -- XXX OK that this changes the order?
                aspkg_state_instances = new_vs ++ noncreg_vs
                -- XXX OK that this changes the order?
              , aspkg_state_outputs = new_reg_svars ++ noncreg_svars
              , aspkg_values = defs ++ new_defs
              , aspkg_inlined_ports = ips ++ creg_ports
              , aspkg_signal_info = si'
              }

