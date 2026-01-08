{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
module ASyntax(
        APackage(..),
        getAPackageFieldInfos,
        getAPackageClocks,
        getAPackageInputs,
        getAPackageParamsPortsAndInouts,
        apkgIsMCD,
        apkgExposesClkOrRst,
        AId,
        AMethodId,
        AType(..),
        ASize,
        ARule(..),
        AAssumption(..),
        ARuleId,
        APred,
        AIFace(..),
        AInput,
        AAbstractInput(..),
        AOutput,
        AClock(..),
        AReset(..),
        AInout(..),
        AClockDomain,
        mkOutputWire,
        mkIfcInoutN,
        AExpr(..),
        ADef(..),
        ASPackage(..),
        ASPSignalInfo(..),
        ASPMethodInfo(..),
        ASPCommentInfo(..),
        AStateOut,
        AVInst(..),
        getSpecialOutputs,
        getOutputClockWires,
        getOutputClockPorts,
        getOutputResetPorts,
        getIfcInoutPorts,
        ASchedule(..),
        AScheduler(..),
        AAction(..),
        ANoInlineFun(..),
        ARuleDescr,
        aTZero,
        aTBool,
        aSBool,
        aXSBool,
        aRuleName,
        aRulePred,
        aTNat,
        aTAction,
        aTClock,
        aTReset,
        aTInout,
        aTInout_,
        isStringType,
        isSizedString,
        isUnsizedString,
        dropSize,
        unifyStringTypes,
        isTupleType,
        getArrayElemType,
        getArraySize,
        aIfaceProps,
        aIfaceResTypes,
        aIfaceResIds,
        aIfaceArgs,
        aIfaceArgSize,
        aIfaceRules,
        aIfaceRulesImpl,
        aIfaceSchedNames,
        aIfacePred,
        aiface_vname,
        aiface_argnames_width,
        aIfaceMethods,
        aIfaceHasAction,
        aTrue,
        aFalse,
        isTrue,
        isFalse,
        aNoReset,
        cmpASInt,
        getSchedulerIds,
        dropScheduleIds,
        dropSchedulerIds,
        aNat,
        AForeignCall(..),
        AForeignBlock,
        PPrintExpand(..),
        pPrintExpandFlags,
        ppeString,
        ppeAPackage,
        mkMethId,
        mkMethStr,
        mkMethArgStr,
        mkMethResStr,
        isMethId,
        MethodPart(..),
        getParams,
        getPorts,
        getClocks,
        getResets,
        getInouts,
        getInstArgs,
        defaultAId,
        binOp,
        mkCFCondWireInstId,
        PExpandContext, defContext, bContext, pContext
        ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Data.List(nub, intersect, (\\), partition)
-- import IntegerUtil(integerFormatPref)
import Eval
import PPrint
import IntLit
import Id
import IdPrint
import PreIds(idPrimAction, idClock, idReset, idInout, idInout_, idPreludeRead, idNoReset)
import Prim
import ErrorUtil(internalError)
import Backend
import Pragma
import PreStrings(fsDollar, fsUnderscore, fsEnable, fs_arg, fs_res)
import FStringCompat
-- import Position(noPosition)
import Position
import Data.Maybe
import Util(itos)
import VModInfo
import Wires
import ProofObligation(ProofObligation, MsgFn)
import Flags
import qualified Data.Map as M
import ISyntax(IType)
import InstNodes(InstTree)

-- packages converted from ISyntax
data APackage = APackage {
            -- package name
    apkg_name :: AId,
            -- module wrapped around a non-inlined function
    apkg_is_wrapped :: Bool,
            -- whether module compilation was specific to the chosen backend
    apkg_backend :: Maybe Backend,
            -- size parameters (names in verilog)
    apkg_size_params :: [AId],
            -- package inputs (ports and parameters)
            -- in the order described by wireinfo
            -- (i.e. clock, reset, inouts, provided method arguments,
            -- module arg ports, module arg parameters)
    apkg_inputs :: [AAbstractInput],
            -- table of different clock domains
    apkg_clock_domains :: [AClockDomain],
            -- description of external wires (e.g. clock and reset)
    apkg_external_wires :: VWireInfo,
            -- table of port names to source types
    apkg_external_wire_types :: M.Map VName IType,
            -- table of resets
    apkg_reset_list :: [(ResetId, AReset)],
            -- state elements (Verilog instances)
    apkg_state_instances :: [AVInst],
            -- local defs, in dependency-sorted order?
    apkg_local_defs :: [ADef],
            -- rules, in unspecified order
    apkg_rules :: [ARule],
            -- relationships among rule names
    apkg_schedule_pragmas :: [ASchedulePragma],
            -- interface methods
    apkg_interface :: [AIFace],
            -- comments on submodule instantiations
    apkg_inst_comments :: [(Id, [String])],
            -- instantiation tree of rules and methods
    apkg_inst_tree :: InstTree,
            -- proof obligations which have not yet been discharged
    apkg_proof_obligations :: [(ProofObligation AExpr, MsgFn)]
    } deriving (Eq, Show)

instance NFData APackage where
    rnf (APackage n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17) =
        rnf17 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17

getAPackageFieldInfos :: APackage -> [VFieldInfo]
getAPackageFieldInfos = map aif_fieldinfo . apkg_interface

getAPackageClocks :: APackage -> [AClock]
getAPackageClocks APackage { apkg_clock_domains = acds } = concatMap snd acds

getAPackageInputs :: APackage -> [(AAbstractInput, VArgInfo)]
getAPackageInputs apkg =
    let
        -- get the two fields
        inputs = apkg_inputs apkg
        arginfos = wArgs (apkg_external_wires apkg)

        -- check that they are the same length
        inputs_length = length (apkg_inputs apkg)
        arginfos_length = length arginfos

        args_with_info = zip inputs arginfos
    in
        if (inputs_length /= arginfos_length)
        then internalError ("getAPackageInputs: " ++
                            "length inputs != length arginfos: " ++
                            ppReadable (inputs, arginfos))
        else args_with_info

-- returns the input ports, separated into params, ports and inouts
-- (note that this converts abstract inputs to port inputs)
getAPackageParamsPortsAndInouts :: APackage -> ([AInput], [AInput], [AInput])
getAPackageParamsPortsAndInouts apkg =
    let args_with_info = getAPackageInputs apkg
        drop_info (xs, ys, zs) = (map fst xs, map fst ys, map fst zs)
        cvtToPorts (xs, ys, zs) =
            (concatMap absInputToPorts xs,
             concatMap absInputToPorts ys,
             concatMap absInputToPorts zs)
        (params, rest) = partition (isParam . snd) args_with_info
        (inouts,ports) = partition (isInout . snd) rest
    in  cvtToPorts $ drop_info $ (params, ports, inouts)


apkgIsMCD :: APackage -> Bool
apkgIsMCD apkg =
    let domains = apkg_clock_domains apkg
        clocks = concatMap snd domains
        resets = apkg_reset_list apkg
    in  (length domains /= 1) ||
        (length clocks /= 1) ||
        (length resets > 1)

apkgExposesClkOrRst :: APackage -> Bool
apkgExposesClkOrRst apkg =
    let isClkOrRst (AIClock {}) = True
        isClkOrRst (AIReset {}) = True
        isClkOrRst _ = False
    in  any isClkOrRst (apkg_interface apkg)


-- a scheduled package
-- rules and interface methods have turned into logic connected to state instances
data ASPackage = ASPackage {
        -- package name
         aspkg_name :: AId,
        -- module wrapped around a pure function with pragma no-inline
        aspkg_is_wrapped :: Bool,
        -- parameters (names in Verilog)
        -- (i.e. module args generated as params, size parameters)
        -- XXX there are no size parameters because we don't support
        -- XXX synthesis of size-polymorphic modules
        aspkg_parameters :: [AInput],
        -- package outputs (output clocks/resets, method results/RDY)
        aspkg_outputs :: [AOutput],
        -- package inputs (input clocks/resets, method args/EN, module args)
        -- (i.e. clock, reset, method arguments, module args as ports)
        aspkg_inputs :: [AInput],
        -- package inouts (module args and provided interface)
        aspkg_inouts :: [AInput],
        -- state elements (Verilog instances)
        aspkg_state_instances :: [AVInst],
        -- state element outputs (wires coming out of state elements)
        aspkg_state_outputs :: [AStateOut],
        -- defs (all sorts)
        aspkg_values :: [ADef],
        -- inout defs
        aspkg_inout_values :: [ADef],
        -- foreign function calls (grouped by clock domain)
        aspkg_foreign_calls :: [AForeignBlock],
        -- wire ports from inlined submodules (RWire and CReg)
        --   which shouldn't be unecessarily inlined away
        aspkg_inlined_ports :: [AId],
        -- info about which Ids are for what purpose
        aspkg_signal_info :: ASPSignalInfo,
        -- user comments to be included in the output RTL
        aspkg_comment_info :: ASPCommentInfo
    }
        deriving (Eq, Show)

instance NFData ASPackage where
    rnf (ASPackage n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14) =
        rnf14 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14

data ASPSignalInfo = ASPSignalInfo {
        -- input params, ports, clocks, and resets are all in one list
        -- (can use isParam etc to filter it out)
        aspsi_inputs :: [AId],
        -- the interface output clocks (and possibly empty list of gates)
        aspsi_output_clks :: [(AId,[AId])],
        aspsi_output_rsts :: [AId],
        aspsi_ifc_iots :: [AId],
        -- the ifc methods
        aspsi_methods :: [ASPMethodInfo],

        -- inline submodule info (RWire and CReg)
        -- XXX this somewhat duplicates the aspkg_inlined_ports field
        --   * instance name
        --   * module name as String
        --   * list of ports that became signals
        aspsi_inlined_ports :: [(AId, String, [AId])],

        -- rule scheduling signals
        --   relation from rule name to its CAN_FIRE and WILL_FIRE signals
        aspsi_rule_sched :: [(AId, [AId])],

        -- mux selectors
        --   ids of defs created in AState for the selectors to submod muxes
        aspsi_mux_selectors :: [AId],
        -- mux values
        --   ids of defs created in AState for the values to submod muxes
        aspsi_mux_values :: [AId],
        -- submodule enables
        --   ids of defs created in AState for the enables to submod methods
        aspsi_submod_enables :: [AId]
    }
        deriving (Eq, Show)


instance PPrint ASPSignalInfo where
    pPrint d p aspsi = text "ASPSignalInfo = " <> braces
                       (text "Inputs" <+> pPrint d p (aspsi_inputs aspsi)
                       $+$ text "Output Clocks" <+> pPrint d p (aspsi_output_clks aspsi)
                       $+$ text "Output Resets" <+> pPrint d p (aspsi_output_rsts aspsi)
                       $+$ text "Inouts" <+> pPrint d p (aspsi_ifc_iots aspsi)
                       $+$ text "Methods" <+> pPrint d p (aspsi_methods aspsi)
                       -- $+$ text "Inlined Ports" <+> pPrint d p (aspsi_inlined_ports aspsi)
                       )

        --   relation from method name to
        --     type of method (value, action, actionvalue) as string
        --     ports for RDY, EN, val, args
        --     names of the associated rules (for methods with actions)
data ASPMethodInfo = ASPMethodInfo {
                                    aspm_name :: AId,
                                    aspm_type :: String,
                                    aspm_mrdyid :: Maybe AId,
                                    aspm_menableid :: Maybe AId,
                                    aspm_resultids :: [AId],
                                    aspm_inputs :: [AId],
                                    aspm_assocrules :: [AId]
                                                       }
                   deriving (Eq, Show)

instance PPrint ASPMethodInfo where
    pPrint d p aspmi = text "method:" <+> pPrint d p( aspm_name aspmi)
                       <+> text (aspm_type aspmi) <> equals <>
                       braces ( pPrint d 0 (aspm_mrdyid aspmi) <+>
                                pPrint d 0 (aspm_menableid aspmi) <+>
                                pPrint d 0 (aspm_resultids aspmi) $+$
                                pPrint d 0 (aspm_inputs aspmi) $+$
                                pPrint d 0 (aspm_assocrules aspmi) )



instance NFData ASPSignalInfo where
    rnf (ASPSignalInfo ins oclks orsts iots meths iports rsched muxsels muxvals senables) =
        rnf10 ins oclks orsts iots meths iports rsched muxsels muxvals senables

data ASPCommentInfo = ASPCommentInfo {
        -- comments on submodule instantiations
        aspci_submod_insts :: [(Id, [String])],
        -- comments on rules
        aspci_rules :: [(AId, [String])]
        -- comments on methods
        -- aspsi_methods :: ...
    }
        deriving (Eq, Show)

instance NFData ASPCommentInfo where
    rnf (ASPCommentInfo insts rules) = rnf2 insts rules

-- parallel rule groups; total order on state
-- (first rule in the list writes, present only if there are state conflicts)
data ASchedule = ASchedule {
        asch_scheduler :: [AScheduler],
                        -- list of ruleids is REVERSE ordering for execution
        asch_rev_exec_order :: [ARuleId]
    }
        deriving (Eq, Show)

instance NFData ASchedule where
    rnf (ASchedule sched order) = rnf2 sched order

newtype AScheduler =
          -- esposito: (r,f) s.t.
          --   f is the list of conditions for which
          --        rule r should not fire when enabled
          --   f is expressed as a
          --        list of rules that conflict with the rule r.
          --   In the future, f should be a list of list of rules,
          --      where the sublists are a list of rules which when
          --      enabled should disable the firing of r.
          --      So [[a,b],[c],[d,e,f]] = !(ab) && !c && !(def)
    ASchedEsposito [(ARuleId, [ARuleId])]
        deriving (Eq, Show)

getSchedulerIds :: AScheduler -> [ARuleId]
getSchedulerIds (ASchedEsposito fs) = map fst fs

dropScheduleIds :: [ARuleId] -> ASchedule -> ASchedule
dropScheduleIds dropIds (ASchedule gs order) = (ASchedule gs' order')
  where order' = order \\ dropIds
        gs' = map (dropSchedulerIds dropIds) gs

dropSchedulerIds :: [ARuleId] -> AScheduler -> AScheduler
dropSchedulerIds dropIds sch =
  let result = dropSchedulerIds' dropIds sch in
      -- paranoia check
      if (not . null) (dropIds `intersect` getSchedulerIds result) then
         internalError("ASyntax.dropSchedulerIds " ++ ppReadable dropIds ++
                       "\n" ++ ppReadable sch)
      else result

dropSchedulerIds' :: [ARuleId] -> AScheduler -> AScheduler
dropSchedulerIds' dropIds (ASchedEsposito fs) = ASchedEsposito fs'
  where fs' = [(rid, rs') | (rid, rs) <- fs,
                            not (rid `elem` dropIds),
                            let rs' = rs \\ dropIds]

type AId = Id

type AMethodId = AId

data AType =
         -- Bit k
         ATBit {
            atb_size :: ASize
         }
         -- sized or unsized string
       | ATString {
            ats_maybe_size :: Maybe ASize
         }
       -- Verilog real number
       | ATReal
       -- PrimArray
       | ATArray {
            atr_length :: ASize,
            atr_elem_type :: AType
        }
       -- Tuple type, for methods with multiple return values
       | ATTuple {
            att_elem_types :: [AType]
        }
        -- abstract type, PrimAction, Interface, Clock, ..
        -- (can take size parameters as arguments)
       | ATAbstract {
            ata_id :: AId,
            ata_sizes :: [ASize]
        }
        deriving (Eq, Ord, Show)

instance NFData AType where
    rnf (ATBit sz) = rnf sz
    rnf (ATString msz) = rnf msz
    rnf ATReal = ()
    rnf (ATArray len typ) = rnf2 len typ
    rnf (ATTuple typs) = rnf typs
    rnf (ATAbstract aid args) = rnf2 aid args

instance HasPosition AType where
    getPosition (ATAbstract {ata_id = id}) = getPosition id
    getPosition _                          = noPosition


aTZero, aTBool, aTNat :: AType
aTZero = ATBit 0
aTBool = ATBit 1
aTNat = ATBit 32

aTAction, aTClock, aTReset :: AType
aTAction = ATAbstract idPrimAction []
aTClock  = ATAbstract idClock []
aTReset  = ATAbstract idReset []

aTInout, aTInout_ :: ASize -> AType
aTInout n = ATAbstract idInout [n]
aTInout_ n = ATAbstract idInout_ [n]

-- Useful routines for working with ATString types
isStringType :: AType -> Bool
isStringType (ATString _) = True
isStringType _            = False

isUnsizedString :: AType -> Bool
isUnsizedString (ATString Nothing) = True
isUnsizedString _                  = False

isSizedString :: AType -> Bool
isSizedString (ATString (Just n)) = True
isSizedString _                   = False

dropSize :: AType -> AType
dropSize (ATString (Just _)) = ATString Nothing
dropSize x                   = x

unifyStringTypes :: [AType] -> AType
unifyStringTypes []     = internalError "unifyStringTypes given an empty list"
unifyStringTypes (t:ts) | isUnsizedString t = t
                        | otherwise         = helper t ts
  where helper t []                  = t
        helper t (t1:ts) | t /= t1   = dropSize t
                         | otherwise = helper t ts

isTupleType :: AType -> Bool
isTupleType (ATTuple _) = True
isTupleType _           = False

type ASize = Integer

getArrayElemType :: AType -> AType
getArrayElemType (ATArray _ t) = t
getArrayElemType t = internalError ("getArrayElemType: " ++ ppReadable t)

getArraySize :: AType -> ASize
getArraySize (ATArray sz _) = sz
getArraySize t = internalError ("getArraySize: " ++ ppReadable t)

-- ----------

-- module inputs

-- This a module input (or inout) port at the hardware level.
-- This is how module inputs are expressed post AState.
-- It is also how method inputs are currently represented.
-- (If we want to support method inputs which are synthesized to multiple
-- ports, such as structs with a port for each field, then we would change
-- then to be AAbstractInput.)
type AInput = (AId, AType)

-- These are abstract inputs (including inouts), which can map to one or more
-- hardware ports.  These are used in APackage for module arg inputs, prior to
-- being converted to AInput in AState.
data AAbstractInput =
        -- simple input using one port
        AAI_Port AInput |
        -- clock osc and maybe gate
        AAI_Clock AId (Maybe AId) |
        AAI_Reset AId |
        AAI_Inout AId Integer
        -- room to add other types here, like:
        --   AAI_Struct [(AId, AType)]
        --   ...
    deriving (Eq, Show)

absInputToPorts :: AAbstractInput -> [AInput]
absInputToPorts (AAI_Port p) = [p]
absInputToPorts (AAI_Clock osc Nothing) = [(osc, aTBool)]
absInputToPorts (AAI_Clock osc (Just gate)) = [(osc, aTBool), (gate, aTBool)]
absInputToPorts (AAI_Reset r) = [(r,aTBool)]
absInputToPorts (AAI_Inout r n) = [(r,ATAbstract {ata_id = idInout_, ata_sizes = [n]})]

-- ----------

-- Verilog instance output: name and type
type AStateOut = (AId, AType)

-- module outputs (export list): types can be seen from module definition
type AOutput = (AId, AType)

data AVInst = AVInst {
    avi_vname :: AId,        -- name of Verilog instance
    avi_type :: AType,       -- type (like ATAbstract "Prelude.VReg")
    avi_user_import :: Bool, -- whether it is a foreign module
    -- This field records the types/sizes of method inputs and outputs.
    -- XXX This list corresponds to vFields in the VModInfo, but cannot be
    -- XXX stored there, because VModInfo is created before types are known.
    -- There is a triple for each method in vFields of VModInfo.
    -- The triple contains the types of each argument (in order), maybe
    -- the type of the EN, and the return values.
    -- NOTE: These are the output language types (i.e. ATBit n)
    avi_meth_types :: [([AType], Maybe AType, [AType])],
    -- This field maps source-language types to their corresponding ports
    avi_port_types :: M.Map VName IType,
    avi_vmi :: VModInfo,     -- Verilog names, conflict info, etc.
    avi_iargs :: [AExpr],    -- list of instantiation arguments
    -- The number of used copies of each method (up to the max multiplicity)
    -- To ensure correlation, it is a pair of the method id to its
    -- number of used copies.  (The total multiplicity is in the VFieldInfo.)
    avi_iarray :: [(AId, Integer)]
}
    deriving (Eq, Show)

-- Return output clock and reset wires (including "outhigh" gate ports).
-- Note even though all special wires (so far) have type ATBit 1,
-- it is controllable here.
-- Returns the state-element-output id, the ASyntax type,
-- and the Verilog name of the output port to connect to.
getSpecialOutputs :: AVInst -> [(AId, AType, VPort)]
getSpecialOutputs avi =
    let
        extractClkPorts (_, osc_port, Nothing)        = [osc_port]
        extractClkPorts (_, osc_port, Just gate_port) = [osc_port, gate_port]

        -- throw away the association with the clock/reset name
        clk_ports = concatMap extractClkPorts (getOutputClockPorts avi)
        rst_ports = map snd (getOutputResetPorts avi)
        iot_ports = map snd (getIfcInoutPorts avi)
    in
        -- nub because special wires (e.g. an oscillator)
        -- can theoretically be reused
        nub (clk_ports ++ rst_ports ++ iot_ports)


-- Does not return clock gates ports which are "outhigh"
getOutputClockWires :: AVInst ->
                       [(AId,          -- Clock Id
                         AId,          -- Osc
                         Maybe AId)]   -- Gate
getOutputClockWires avi =
  let
      vmi = avi_vmi avi
      out_clocks = [id | (Clock id) <- vFields vmi]
      mkOscWire osc_name = mkOutputWireId (avi_vname avi) osc_name
      mkGateWire gate_name = mkOutputWireId (avi_vname avi) gate_name
      clock_wires clk_id =
        case (lookupOutputClockWires clk_id vmi) of
            (osc_name, Nothing) ->
                (clk_id, mkOscWire osc_name, Nothing)
            (osc_name, Just gate_name) ->
                (clk_id, mkOscWire osc_name, Just (mkGateWire gate_name))
  in
      map clock_wires out_clocks


getOutputClockPorts :: AVInst ->
                       [(AId,                          -- Clock Id
                         (AId, AType, VPort),          -- Osc
                         Maybe (AId, AType, VPort))]   -- Gate
getOutputClockPorts avi =
  let
      vmi = avi_vmi avi
      out_clocks = [id | (Clock id) <- vFields vmi]
      mkOscPort clk_name =
          (mkOutputWireId (avi_vname avi) clk_name,
           ATBit 1,
           (clk_name, [VPclock]))
      mkGatePort (clk_gate_name, portprops) =
          (mkOutputWireId (avi_vname avi) clk_gate_name,
           ATBit 1,
           (clk_gate_name, (VPclockgate:portprops)))
      clock_ports id =
        case (lookupOutputClockPorts id vmi) of
            (clk_name, Nothing) ->
                (id, mkOscPort clk_name, Nothing)
            (clk_name, Just clk_gate_vport) ->
                (id, mkOscPort clk_name, Just (mkGatePort clk_gate_vport))
  in
      map clock_ports out_clocks


getOutputResetPorts :: AVInst -> [(AId, (AId, AType, VPort))]
getOutputResetPorts avi =
  let
      vmi = avi_vmi avi
      output_resets = [id | (Reset id) <- vFields vmi]
      mkResetPort rst_name = (mkOutputWireId (avi_vname avi) rst_name,
                              ATBit 1,
                              (rst_name, [VPreset]))
      reset_ports id =
          let rst_name = lookupOutputResetPort id vmi
          in  (id, mkResetPort rst_name)
  in
      map reset_ports output_resets

getIfcInoutPorts :: AVInst -> [(AId, (AId, AType, VPort))]
getIfcInoutPorts avi =
  let
      vmi = avi_vmi avi
      res_types = map (\ (_,_,rs) -> rs) (avi_meth_types avi)
      ifc_inouts = [(id,vn,ty)
                     | (Inout id vn _ _, rs) <- zip (vFields vmi) res_types,
                       let ty = case rs of
                                  [r] -> r
                                  _ -> error ("ASyntax.unknown inout " ++ ppReadable id)]


      mkInoutPort ty vname = (mkOutputWireId (avi_vname avi) vname,
                              ty,
                              (vname, [VPinout]))
      inout_ports (id,vn,ty) = (id, mkInoutPort ty vn)
  in
      map inout_ports ifc_inouts


{-
vNParam :: VModInfo -> Integer
vNParam (VModInfo _ _ _ as _ _ _) = length [x | Param x <- as]
-}

getParams :: AVInst -> [AExpr]
getParams avi = [e | (i, e) <- getInstArgs avi, isParam i]

getPorts :: AVInst -> [AExpr]
getPorts avi = [e | (i, e) <- getInstArgs avi, isPort i]

getInstArgs :: AVInst -> [(VArgInfo, AExpr)]
getInstArgs avi = zip (vArgs vi) es
  where vi = avi_vmi avi
        es = avi_iargs avi

getClocks :: AVInst -> [AExpr]
getClocks avi = [e | (i,e) <- getInstArgs avi, isClock i]

getResets :: AVInst -> [AExpr]
getResets avi = [e | (i,e) <- getInstArgs avi, isReset i]

getInouts :: AVInst -> [AExpr]
getInouts avi = [e | (i,e) <- getInstArgs avi, isInout i]

-- local definition
data ADef = ADef {
    adef_objid :: AId,
    adef_type :: AType,
    adef_expr :: AExpr,
    adef_props :: [DefProp]
    }
        deriving (Eq, Ord, Show)

instance HasPosition ADef where
    getPosition adef = getPosition (adef_objid adef )

instance NFData ADef where
    rnf (ADef id typ expr props) = rnf4 id typ expr props

-- last id has original rule if this one comes from a split; Nothing otherwise
-- it's only used as an optimization; it's safe to put Nothing there
data ARule =
    ARule {
        arule_id :: ARuleId,         -- rule name with a suffix
        arule_pragmas :: [RulePragma],    -- rule pragmas,
                                        --   e.g., no-implicit-conditions
        arule_descr :: ARuleDescr,      -- string that describes the rule
        arule_wprops :: WireProps,      -- clock domain and reset information
        arule_pred :: APred,           -- rule predicate (CAN_FIRE)
        arule_actions :: [AAction],    -- rule body (actions)
        arule_assumps :: [AAssumption], -- assumptions that should hold after this rule executes
        arule_parent :: (Maybe ARuleId) -- if this rule came from a split,
                                         --   Just parent rule name
    }
        deriving (Eq, Show)

type ARuleDescr = String

type ARuleId = Id

type APred = AExpr

aRuleName :: ARule -> ARuleId
aRuleName = arule_id

aRulePred :: ARule -> AExpr
aRulePred = arule_pred

data AAssumption =
    AAssumption {
       assump_property :: AExpr, -- property we've assumed holds
       assump_actions  :: [AAction] -- actions to take if the property does NOT hold
                                    -- cannot include method calls
    }
  deriving (Eq, Show)

-- the APred is the implicit condition to the scheduler
data AIFace =   AIDef { aif_name      :: AId,
                        aif_inputs    :: [AInput],
                        aif_props     :: WireProps,
                        aif_pred      :: APred,
                        aif_value     :: ADef,
                        aif_fieldinfo :: VFieldInfo,
                        -- value methods have their own assumptions
                        -- because there is no rule to attach it to
                        aif_assumps :: [AAssumption] }
              | AIAction { aif_inputs    :: [AInput],
                           aif_props     :: WireProps,
                           aif_pred      :: APred,
                           aif_name      :: AId,
                           aif_body      :: [ARule],
                           aif_fieldinfo :: VFieldInfo }
              | AIActionValue { aif_inputs    :: [AInput],
                                aif_props     :: WireProps,
                                aif_pred      :: APred,
                                aif_name      :: AId,
                                aif_body      :: [ARule],
                                aif_value     :: ADef,
                                aif_fieldinfo :: VFieldInfo }
                -- trivial aif_inputs, props, pred?
              | AIClock { aif_name      :: AId,
                          aif_clock     :: AClock,
                          aif_fieldinfo :: VFieldInfo }
              | AIReset { aif_name      :: AId,
                          aif_reset     :: AReset,
                          aif_fieldinfo :: VFieldInfo }
              | AIInout { aif_name      :: AId,
                          aif_inout     :: AInout,
                          aif_fieldinfo :: VFieldInfo }
   deriving (Eq, Show)

aiface_vname :: AIFace -> String
aiface_vname i = getIdString (vf_name (aif_fieldinfo i))

-- wire properties
aIfaceProps :: AIFace -> WireProps
aIfaceProps (AIDef         { aif_props = p }) = p
aIfaceProps (AIAction      { aif_props = p }) = p
aIfaceProps (AIActionValue { aif_props = p }) = p
aIfaceProps _ = emptyWireProps

aIfaceResTypes :: AIFace -> [AType]
-- XXX should be ATAction?
aIfaceResTypes (AIAction { }) = [ATBit 0]
aIfaceResTypes (AIDef { aif_value = (ADef _ t _ _) }) = [t]
aIfaceResTypes (AIActionValue { aif_value = (ADef _ t _ _) }) = [t]
-- should not need type of clock or reset
aIfaceResTypes x = internalError ("aIfaceResTypes: " ++ show x)

aIfaceResIds :: AIFace -> [AId]
aIfaceResIds (AIDef {aif_name=id}) = [id]
aIfaceResIds (AIActionValue {aif_name=id}) = [id]
aIfaceResIds _ = []

aIfaceArgs :: AIFace -> [AInput]
aIfaceArgs (AIClock {}) = []
aIfaceArgs (AIReset {}) = []
aIfaceArgs (AIInout {}) = []
aIfaceArgs f = aif_inputs f

-- associate the internal and external names and width of AIFace args

aiface_argnames_width :: AIFace -> [(AId, String, Integer)]
aiface_argnames_width (AIClock {}) = []
aiface_argnames_width (AIReset {}) = []
aiface_argnames_width aif =
    zip3 (map fst (aif_inputs aif))
        (map (getVNameString . fst) (vf_inputs (aif_fieldinfo aif)))
        (map aIfaceArgSize (aif_inputs aif))


aIfaceArgSize :: AInput -> Integer
aIfaceArgSize (_, ATBit size) = size
aIfaceArgSize x = internalError ("aIfaceArgSize: " ++ show x)

aIfaceRules :: AIFace -> [ARule]
aIfaceRules (AIAction { aif_body = rs}) = rs
aIfaceRules (AIActionValue { aif_body = rs}) = rs
aIfaceRules _ = []

aIfaceRulesImpl :: AIFace -> [(ADef, ARule)]
aIfaceRulesImpl (AIAction { aif_name = i,
                            aif_body = rs }) = map (addRdyToARule rdyId) rs
  where rdyId = mkRdyId i
aIfaceRulesImpl (AIActionValue { aif_name = i,
                                 aif_body = rs }) = map (addRdyToARule rdyId) rs
  where rdyId = mkRdyId i
aIfaceRulesImpl _ = []

addRdyToARule :: Id -> ARule -> (ADef, ARule)
addRdyToARule rdyId r0@(ARule { arule_id = ri, arule_pred = e }) = (d, r)
 where di = mkRdyId (mkRdyId ri)
       d = ADef di aTBool
                (APrim di aTBool PrimBAnd [e, ASDef aTBool rdyId]) []
       r = r0 { arule_pred = (ASDef aTBool di) }

-- The names of value methods and action/actionvalue rules
aIfaceSchedNames :: AIFace -> [ARuleId]
aIfaceSchedNames (AIAction { aif_body = rs}) = map arule_id rs
aIfaceSchedNames (AIActionValue { aif_body = rs}) = map arule_id rs
aIfaceSchedNames (AIDef { aif_name = i }) = [i]
aIfaceSchedNames _ = []

aIfacePred :: AIFace -> APred
aIfacePred ifc@(AIDef {}) = aif_pred ifc
aIfacePred ifc@(AIAction {}) = aif_pred ifc
aIfacePred ifc@(AIActionValue {}) = aif_pred ifc
aIfacePred ifc@(AIClock {}) =
    internalError ("aIfacePred: unexpected clock: " ++ ppReadable ifc)
aIfacePred ifc@(AIReset {}) =
    internalError ("aIfacePred: unexpected reset: " ++ ppReadable ifc)
aIfacePred ifc@(AIInout {}) =
    internalError ("aIfacePred: unexpected inout: " ++ ppReadable ifc)

aIfaceMethods :: [AIFace] -> [AIFace]
aIfaceMethods is =
    let getMethod (AIClock {}) = Nothing
        getMethod (AIReset {}) = Nothing
        getMethod (AIInout {}) = Nothing
        getMethod i            = Just i
    in  mapMaybe getMethod is


aIfaceHasAction :: AIFace -> Bool
aIfaceHasAction (AIAction {})      = True
aIfaceHasAction (AIActionValue {}) = True
aIfaceHasAction _                  = False

-- note no types because they are implicitly action
data AAction
        = ACall {        -- state method call
            aact_objid :: AId,
            acall_methid :: AMethodId,
            aact_args :: [AExpr]        -- first element of the list is the condition
        }
        | AFCall {
            aact_objid :: AId,       -- foreign function call
            afcall_fun :: String,
            afcall_isC :: Bool,
            aact_args :: [AExpr], -- first element of the list is the condition
            -- is it an action inserted by BSC to check an assumption
            aact_assump :: Bool
        }
 -- action part of a foreign ActionValue function
        | ATaskAction {
            aact_objid :: AId,
            ataskact_fun :: String,
            ataskact_isC :: Bool,
            ataskact_cookie :: Integer, -- correlation cookie
            aact_args :: [AExpr], -- first element is the condition
            -- the temporary to set, spliced in later
            ataskact_temp :: (Maybe Id),
            -- include the return value type for easy reference,
            -- and to support foreign functions with ignored values
            ataskact_value_type :: AType,
            -- is it an action inserted by BSC to check an assumption
            aact_assump :: Bool
        }
        deriving (Eq, Ord, Show)

instance NFData AAction where
    rnf (ACall oid mid args) = rnf3 oid mid args
    rnf (AFCall oid fun isC args assump) = rnf5 oid fun isC args assump
    rnf (ATaskAction oid fun isC cookie args temp vtyp assump) =
        rnf8 oid fun isC cookie args temp vtyp assump

data AClock = AClock {
                       aclock_osc  :: AExpr, -- must be of type ATBit 1
                       aclock_gate :: AExpr  -- must be of type ATBit 1
                     }
  deriving(Eq, Ord, Show)
  -- the Ord instance has little meaning - it is used for Maps and the like
  -- the Eq instance should be accurate
  --    (same oscillator and gate ==> same clock)
  -- though it may not catch aliasing

instance PPrint AClock where
  pPrint d p (AClock osc gate) =
    (text "{ osc: ") <+>
        (pPrint d p osc) <+>
        (text "gate: ") <+>
        (pPrint d p gate) <+>
        (text "}")

mkOutputWireId :: AId -> VName -> AId
mkOutputWireId var_id (VName wire_str) =
  let var_fstr  = getIdFString (unQualId var_id)
      wire_fstr = mkFString wire_str
  in mkId
        noPosition
        (concatFString [var_fstr, fsDollar, wire_fstr])

mkOutputWire :: AId -> VName -> AExpr
mkOutputWire var_id wire_name = ASPort (ATBit 1) (mkOutputWireId var_id wire_name)

mkIfcInoutN :: Integer -> AId -> VName -> AExpr
mkIfcInoutN n var_id wire_name = ASPort (aTInout_ n) (mkOutputWireId var_id wire_name)

type AClockDomain = (ClockDomain, [AClock]) -- domain identifier and all the associated clocks

newtype AReset = AReset {
                          areset_wire :: AExpr -- must be of type ATBit 1
                        }
  deriving (Eq, Ord, Show)

newtype AInout = AInout {
                          ainout_wire :: AExpr
                        }
  deriving (Eq, Ord, Show)

instance PPrint AReset where
  pPrint d p (AReset { areset_wire = wire }) = (text "{ wire: ") <+> (pPrint d p wire) <+> (text "}")

instance PPrint AInout where
  pPrint d p (AInout { ainout_wire = wire }) = (text "{ wire: ") <+> (pPrint d p wire) <+> (text "}")

-- Every expression is annotated with its (result) type
        -- all types should be ae_type
        -- all ids should be ae_objid
data AExpr
        = APrim {        -- Verilog primitive (e.g., +)
            ae_objid :: AId,
            ae_type :: AType,
            aprim_prim :: PrimOp,
            ae_args :: [AExpr]
        }
        | AMethCall {
            ae_type :: AType,
            ae_objid :: AId,
            ameth_id :: AMethodId,
            ae_args :: [AExpr]        -- external state method call
        }
        -- like AMethCall, but for the return value of actionvalue methods,
        -- where the return value no longer has to care about the arguments,
        -- because the action (AAction) will handle the muxing and arbitration
        -- of arguments and there is no multiplicity for actionvalue methods
        | AMethValue {
            ae_type :: AType,
            ae_objid :: AId,
            ameth_id :: AMethodId
        }
        | ATuple {
            ae_type :: AType,
            ae_elems :: [AExpr]
        }
        -- selection from an ATTuple
        | ATupleSel {
            ae_type :: AType,
            ae_exp :: AExpr,
            ae_index :: Integer
        }
        -- calls a combinatorial function expressed via module instantiation
        -- XXX this can be created not only via "noinline" in BSV,
        -- XXX but also "foreign" in Classic syntax; consider renaming?
        | ANoInlineFunCall {
            ae_type :: AType,
            ae_objid :: AId,
            ae_fun :: ANoInlineFun,
            ae_args :: [AExpr]
        }
        -- foreign function / task call
        | AFunCall {
            ae_type :: AType,
            ae_objid :: AId,
            ae_funname :: String,
            ae_isC :: Bool,
            ae_args :: [AExpr]        -- external function call
        }
        | ATaskValue { -- value returned by an ActionValue foreign task call
            ae_type :: AType,
            ae_objid :: AId,
            ae_funname :: String,
            ae_isC :: Bool,
            ae_cookie :: Integer -- "cookie" identifying the call for later fixup
                                 -- arguments, etc. handled by the action side of the call
        }
        | ASPort {        -- module ports
            ae_type :: AType,
            ae_objid :: AId
        }
        | ASParam {        -- module parameters
            ae_type :: AType,
            ae_objid :: AId
        }
        | ASDef {        -- reference to local definition or input to module
            ae_type :: AType,
            ae_objid :: AId
        }
        | ASInt {        -- constant
            ae_objid :: AId,
            ae_type :: AType,
            ae_ival :: IntLit
        }
        | ASReal {      -- real-valued constant
            ae_objid :: AId,
            ae_type  :: AType,
            ae_rval  :: Double }
        | ASStr {        -- string literal
            ae_objid :: AId,
            ae_type :: AType,
            ae_strval :: String
        }
        | ASAny {        -- don't care expression
            ae_type :: AType,
            ae_val  :: Maybe (AExpr)
        }
        | ASClock {     -- abstract clock
            ae_type  :: AType,        -- (will vanish after AState)
            ae_clock :: AClock
        }
        | ASReset {     -- abstract reset
            ae_type :: AType,        -- (will vanish after AState),
            ae_expr :: AReset
        }
        | ASInout {     -- abstract inout
            ae_type :: AType,        -- (will vanish after AState),
            ae_expi :: AInout
        }
{-
        -- instead of using ASPort, ASPackage should create these:
        | AWire {
            ae_type :: AType,
            ae_objid :: AId
        }
        -- reset access on a submodule
        | AMReset {
            ae_type :: AType, -- always ATBit 1
            ae_objid :: AId,
            ae_rstid :: AId
        }
        -- oscillator access on a submodule
        | AMOsc {
            ae_type :: AType, -- always ATBit 1
            ae_objid :: AId,
            ae_clkid :: AId
        }
-}
        -- oscillator access on a submodule
        | AMGate {
            ae_type :: AType, -- always ATBit 1
            ae_objid :: AId,
            ae_clkid :: AId
        }
        deriving (Ord, Show)

instance NFData AExpr where
    rnf (APrim oid typ prim args) = rnf4 oid typ prim args
    rnf (AMethCall typ oid mid args) = rnf4 typ oid mid args
    rnf (AMethValue typ oid mid) = rnf3 typ oid mid
    rnf (ATuple typ elems) = rnf2 typ elems
    rnf (ATupleSel typ expr index) = rnf3 typ expr index
    rnf (ANoInlineFunCall typ oid fun args) = rnf4 typ oid fun args
    rnf (AFunCall typ oid fname isC args) = rnf5 typ oid fname isC args
    rnf (ATaskValue typ oid fname isC cookie) = rnf5 typ oid fname isC cookie
    rnf (ASPort typ oid) = rnf2 typ oid
    rnf (ASParam typ oid) = rnf2 typ oid
    rnf (ASDef typ oid) = rnf2 typ oid
    rnf (ASInt oid typ ival) = rnf3 oid typ ival
    rnf (ASReal oid typ rval) = rnf3 oid typ rval
    rnf (ASStr oid typ sval) = rnf3 oid typ sval
    rnf (ASAny typ mval) = rnf2 typ mval
    rnf (ASClock typ clk) = rnf2 typ clk
    rnf (ASReset typ rst) = rnf2 typ rst
    rnf (ASInout typ inout) = rnf2 typ inout
    rnf (AMGate typ oid clkid) = rnf3 typ oid clkid

instance Eq AExpr where
    APrim _ t op aexprs == APrim _ t' op' aexprs' =
        (t == t') && (op == op') && (aexprs == aexprs')

    AMethCall t aid mid aexprs == AMethCall t' aid' mid' aexprs' =
        (t == t') && (mid == mid') && (aexprs == aexprs') && (aid == aid')

    AMethValue t aid mid == AMethValue t' aid' mid' =
        (t == t') && (mid == mid') && (aid == aid')

    ATuple t aexprs == ATuple t' aexprs' =
        (t == t') && (aexprs == aexprs')

    ATupleSel t aexpr index == ATupleSel t' aexpr' index' =
        (t == t') && (index == index') && (aexpr == aexpr')

    ANoInlineFunCall t aid af aexprs == ANoInlineFunCall t' aid' af' aexprs' =
        (t == t') && (af == af') && (aexprs == aexprs') && (aid == aid')

    AFunCall t aid af isC aexprs == AFunCall t' aid' af' isC' aexprs' =
        (t == t') && (af == af') && (isC == isC') && (aexprs == aexprs') && (aid == aid')

    ATaskValue t aid af isC n == ATaskValue t' aid' af' isC' n' =
        (t == t') && (aid == aid') && (af == af') && (isC == isC') && (n == n')

    ASPort t aid == ASPort t' aid' =
        (t == t') && (aid == aid')

    ASParam t aid == ASParam t' aid' =
        (t == t') && (aid == aid')

    ASDef t aid == ASDef t' aid' =
        (t == t') && (aid == aid')

    ASInt _ t il == ASInt _ t' il' =
        (t == t') && (il == il')

    ASReal _ t r == ASReal _ t' r' =
        (t == t') && (r == r')

    ASStr _ t str == ASStr _ t' str' =
        (t == t') && (str == str')

    ASAny t me == ASAny t' me' =
        ((t, me) == (t', me'))

    ASClock t c == ASClock t' c' = c == c' -- t and t' should be aTClock

    ASReset t e  == ASReset t' e' = e == e' -- t and t' should be aTReset

    ASInout t e  == ASInout t' e' = e == e' -- t and t' should be aTInout

    AMGate t oid cid == AMGate t' oid' cid' =
        (t == t') && (oid == oid') && (cid == cid')

    aexpr == aexpr' = False

instance HasPosition AExpr where
    getPosition APrim{ ae_objid = p }       = getPosition p
    getPosition AMethCall{ ae_objid = p }   = getPosition p
    getPosition AMethValue{ ae_objid = p }  = getPosition p
    getPosition ATuple{ ae_elems = e : _ }  = getPosition e
    getPosition ATuple{ ae_elems = [] }     = noPosition -- Is there something better?
    getPosition ATupleSel{ ae_exp = e }     = getPosition e
    getPosition ANoInlineFunCall{ ae_objid = p } = getPosition p
    getPosition AFunCall{ ae_objid = p }    = getPosition p
    getPosition ATaskValue{ ae_objid = p }  = getPosition p
    getPosition ASPort{ ae_objid = p }      = getPosition p
    getPosition ASParam{ ae_objid = p }     = getPosition p
    getPosition ASDef{ ae_objid = p }       = getPosition p
    getPosition ASInt{ ae_objid = p }       = getPosition p
    getPosition ASReal {ae_objid = p }      = getPosition p
    getPosition ASStr{ ae_objid = p }       = getPosition p
    getPosition ASAny{}                     = noPosition -- Is there something better?
    getPosition ASClock{}                   = noPosition -- Is there something better?
    getPosition ASReset{}                   = noPosition -- Is there something better?
    getPosition ASInout{}                   = noPosition -- Is there something better?
    getPosition AMGate{ ae_objid = p }      = getPosition p


-- noinlined function
data ANoInlineFun =
    ANoInlineFun
         -- function nam
         String
         -- numeric types
         [Integer]
         -- port list (inputs,outputs), each is port name and size
         -- XXX sizes all seem to be generated as 0.
         ([(String, Integer)], [(String, Integer)])
         -- when an instance name is assigned to the call, it is stored here
         (Maybe String)
    deriving (Eq, Ord, Show)


-- first element are the oscillators whose edges trigger evaluation
-- second element is the block of function calls
type AForeignBlock = ([AExpr], [AForeignCall])

-- type not required because it is implicitly Action
data AForeignCall =
        AForeignCall {
          afc_name   :: AId,
          afc_fun    :: String,
          afc_args   :: [AExpr], -- first element of the list is the condition
                                 -- (including the WILL_FIRE of the calling rule)
          afc_writes :: [AId],   -- identifiers set by this foreign function call
          afc_resets :: [AExpr]  -- reset wires connected to this foreign function call
          -- inouts not connected to foreign function calls at present
       }
  deriving (Eq, Show)

aSBool :: Bool -> AExpr
aSBool b = ASInt defaultAId aTBool (ilBin (if b then 1 else 0))

-- moved as utility procedures from Synthesize.hs
-- XXX should they check the result type?
isFalse :: AExpr -> Bool
isFalse (ASInt _ _ (IntLit _ _ 0)) = True
isFalse _ = False

isTrue :: AExpr -> Bool
isTrue (ASInt _ _ (IntLit _ _ 1)) = True
isTrue _ = False

-- make an AXExprS which is a boolean
aXSBool :: Bool -> AExpr
aXSBool b = aSBool b

aNat :: Integer -> AExpr
aNat i = ASInt defaultAId aTNat (ilDec i)


aTrue :: AExpr
aTrue = aSBool True

aFalse :: AExpr
aFalse = aSBool False

aNoReset :: AExpr
aNoReset =  ASReset aTReset (AReset (APrim idNoReset (ATBit 1) PrimResetUnassertedVal []))


cmpASInt :: AExpr -> AExpr -> Ordering
cmpASInt (ASInt _ _ (IntLit { ilValue = i }))
         (ASInt _ _ (IntLit { ilValue = i' })) = compare i i'
cmpASInt x y = internalError("cmpASInt: " ++ show x ++ " == " ++ show y)

--------

instance PPrint APackage where
    pPrint d _ apkg =
        (text "APackage" <+> ppId d (apkg_name apkg) <>
         if (apkg_is_wrapped apkg) then text " -- function" else empty) $+$
        (case (apkg_backend apkg) of
             Nothing -> empty
             Just be -> text " -- backend:" <+> pPrint d 0 be) $+$
        text "-- APackage parameters" $+$
        pPrint d 0 (apkg_size_params apkg) $+$
        text "-- APackage arguments" $+$
        foldr (($+$) . pPrint d 0) empty (apkg_inputs apkg) $+$
        text "-- APackage wire info" $+$
        pPrint d 0 (apkg_external_wires apkg) $+$
        text "-- APackage clock domains" $+$
        pPrint d 0 (apkg_clock_domains apkg) $+$
        text "-- APackage resets" $+$
        pPrint d 0 (apkg_reset_list apkg) $+$
        text "-- AP state elements" $+$
        foldr (($+$) . pPrint d 0) empty (apkg_state_instances apkg) $+$
        text "-- AP local definitions" $+$
        foldr (($+$) . pPrint d 0) empty (apkg_local_defs apkg) $+$
        text "-- AP rules" $+$
        foldr (($+$) . pPrint d 0) empty (apkg_rules apkg) $+$
        text "-- AP scheduling pragmas" $+$
        pPrint d 0 (apkg_schedule_pragmas apkg) $+$
        text "-- AP interface" $+$
        foldr ($+$) empty [(text "-- AP  apkg_interface def" <+> pPrint d 0 (apkg_name apkg)) $+$
                           pPrint d 0 i | i <- apkg_interface apkg] $+$
        text "-- AP instance comments" $+$
        foldr (($+$) . ppInstComment d) empty (apkg_inst_comments apkg) $+$
        text "-- AP remaining proof obligations" $+$
        pPrint d 0 (apkg_proof_obligations apkg)

ppInstComment :: PDetail -> (Id, [String]) -> Doc
ppInstComment d (i, cs) =
    pPrint d 0 i <> colon $+$
    vsep (map text cs)

ppV :: PDetail -> (AId, AType) -> Doc
ppV d (i, t) = pPrint d 0 i <+> text "::" <+> pPrint d 0 t <> text ";"

instance PPrint AAbstractInput where
    pPrint d p (AAI_Port v) = ppV d v
    pPrint d p (AAI_Clock osc Nothing) =
        text "clock {" <+>
        (text "osc =" <+> pPrint d 0 osc) <+>
        text "}"
    pPrint d p (AAI_Clock osc (Just gate)) =
        text "clock {" <+>
        (text "osc =" <+> pPrint d 0 osc <> text "," <+>
         text "gate =" <+> pPrint d 0 gate) <+>
        text "}"
    pPrint d p (AAI_Reset r) =
        text "reset {" <+> pPrint d 0 r <+> text "}"
    pPrint d p (AAI_Inout r n) =
        text "inout {" <+> pPrint d 0 r <> text"[" <> pPrint d 0 n <> text"]" <+> text "}"

instance PPrint AVInst where
    pPrint d _ (AVInst i t ui mts pts vi es ns) =
        pPrint d 0 i <+> text "::" <+>
        pPrint d 0 t <+> text "=" <+> (ppVTI d (vi, es, ns) $+$
        text "meth types=" <> pPrint d 0 mts $+$
        text "port types=" <> pPrint d 0 pts)

instance NFData AVInst where
    rnf (AVInst vn typ ui mts pts vmi args arr) =
        rnf8 vn typ ui mts pts vmi args arr

ppVTI :: PDetail -> (VModInfo, [AExpr], [(AId, Integer)]) -> Doc
ppVTI d (vi, es, ns) = sep [pPrint d 0 (vName vi), pPrint d 0 vi, pPrint d 0 es, pPrint d 0 ns]

instance PPrint ASPackage where
    pPrint d p pack@(ASPackage mi fmod ps exps is ios ss sos ds iods fs ws ids cmap) =
        (text "ASPackage" <+> ppId d mi <> if fmod then text " -- function" else text "") $+$
        text "-- ASPackage parameters" $+$
        (text "" <+> sep (map (pPrint d 0) ps) <> text ";") $+$
        text "-- ASPackage outputs" $+$
        (text "" <+> sep (map (pPrint d 0) exps) <> text ";") $+$
        text "-- ASPackage inputs" $+$
        foldr (($+$) . ppV d) (text "") is $+$
        text "-- ASPackage inouts" $+$
        foldr (($+$) . ppV d) (text "") ios $+$
        text "-- ASP state elements" $+$
        foldr (($+$) . pPrint d 0) (text "") ss $+$
        text "-- ASP state elements outputs" $+$
        foldr (($+$) . ppV d) (text "") sos $+$
        text "-- ASP inlined rwire ports" $+$
        foldr (($+$) . pPrint d 0) (text "") ws $+$
        text "-- ASP definitions" $+$
        foldr (($+$) . pPrint d 0) (text "") ds $+$
        text "-- ASP inout definitions" $+$
        foldr (($+$) . pPrint d 0) (text "") iods $+$
        text "-- ASP foreign function calls" $+$
        foldr (($+$) . pPrint d 0) (text "") fs $+$
        text "--ASP Signal Info" $+$ pPrint d 0 (aspkg_signal_info pack)

instance PPrint ASchedule where
     pPrint d p (ASchedule groups order) = (text "parallel:" <+> pPrint d 0 groups)
                                           $+$ (text "order:" <+> pPrint d 0 (reverse order))

instance PPrint AScheduler where
     pPrint d p (ASchedEsposito fs) =
         let ppDep (r,cfs) = pPrint d 0 r <+> text "->" <+> pPrint d 0 cfs
         in  text "esposito:" <+> text "[" <> sep (punctuate (text ",") (map ppDep fs)) <> text "]"


instance PPrint ADef where
    pPrint d _ (ADef i t e props) =
        (pPrint d 0 i <+> text "::" <+> pPrint d 0 t <> text ";") $+$
        (pPrint d 0 i <> text "  =" <+> pPrint d 0 e <> text ";") $+$
        (if (null $ getIdProps i) then empty else
           text "-- IdProp" <+> text (show i) ) $+$
        (if (null props) then empty else
           text "-- Properties" <+> pPrint d 0 props)

pPred :: PDetail -> Int -> APred -> Doc
pPred d p pred = text "pred: " <+> pPrint d p pred

-- XXX cleanup needed.
instance PPrint AIFace where
    -- XXX print assumptions
    pPrint d p ai@(AIDef {} )  =
        (text "--AIDef" <+> pPrint d p (aif_name ai)) $+$
        foldr (($+$) . ppV d) empty (aif_inputs ai) $+$
        pPrint d p (aif_value ai) $+$
        pPred d p (aif_pred ai) $+$
        pPrint d 0 (aif_props ai) $+$
        pPrint d 0 (aif_fieldinfo ai) $+$
        text ""
    pPrint d p ai@(AIAction {} ) =
        (text "--AIAction" <+> pPrint d p (aif_name ai)) $+$
        foldr (($+$) . ppV d) empty (aif_inputs ai) $+$
        pPrint d p (aif_body ai) $+$
        pPred d p (aif_pred ai) $+$
        pPrint d 0 (aif_props ai) $+$
        pPrint d 0 (aif_fieldinfo ai) $+$
        text ""
    pPrint d p ai@(AIActionValue {})  = -- XXX this should be done better
        (text "--AIActionValue" <+> pPrint d p (aif_name ai)) $+$
        foldr (($+$) . ppV d) empty (aif_inputs ai) $+$
        pPrint d p (aif_value ai) $+$
        pPrint d p (aif_body ai) $+$
        pPred d p (aif_pred ai) $+$
        pPrint d 0 (aif_props ai) $+$
        pPrint d 0 (aif_fieldinfo ai) $+$
        text ""
    pPrint d p (AIClock i c _) = pPrint d 0 c
    pPrint d p (AIReset i r _) = pPrint d 0 r
    pPrint d p (AIInout i r _) = pPrint d 0 r

instance PPrint ARule where
    pPrint d@PDDebug _ (ARule s _ _ _ p as _ _) =
        (text "rule" <+> pPrint d 0 s)
    pPrint d _ (ARule s rps sd wp p as asmps _) =
        vcat (map (pPrint d 0) rps) $+$
        (text "rule" <+> pPrint d 0 s <> text (" " ++ show sd) <> text ":") $+$
        (text " when" <+> pPrint d 0 p) $+$
        (text "  ==>" <+> ppActions d as) $+$
        pPrint d 0 asmps $+$
        pPrint d 0 wp

instance PPrint AAssumption where
     pPrint d p (AAssumption pred as) =
        text "assume " <+> pPrint d p pred <+>
        text "else " <+> pPrint d p as

ppActions :: PDetail -> [AAction] -> Doc
ppActions d as = text "{" <+> sep (map ppA as) <+> text "}"
        where ppA a = pPrint d 0 a <> text ";"

-- AFCall/ATaskAction prints i instead of the string name
-- to print the Bluespec function being called, not the foreign one
instance PPrint AAction where
    pPrint d _ (ACall i m (c : es)) | isOne c = pPrint d 0 i <> text "." <> ppMethId d m <+> sep (map (pPrint d 1) es)
    pPrint d _ (ACall i m (c : es)) = sep [
        text "if" <+> pPrint d 0 c <+> text "then",
        nest 2 (pPrint d 0 i <> text "." <> ppMethId d m <+> sep (map (pPrint d 1) es))
        ]
    pPrint d _ (AFCall i _ _ (c : es) _) | isOne c = pPrint d 0 i <+> sep (map (pPrint d 1) es)
    pPrint d _ (AFCall i _ _ (c : es) _) = sep [
        text "if" <+> pPrint d 0 c <+> text "then",
        nest 2 (pPrint d 0 i <+> sep (map (pPrint d 1) es))
        ]
    pPrint d _ (ATaskAction i _ _ n (c : es) _ _ _) | isOne c = pPrint d 0 i <> text ("#" ++ itos(n)) <+> sep (map (pPrint d 1) es)
    pPrint d _ (ATaskAction i _ _ n (c : es) _ _ _) = sep [
        text "if" <+> pPrint d 0 c <+> text "then",
        nest 2 (pPrint d 0 i <> text ("#" ++ itos(n)) <+> sep (map (pPrint d 1) es))
        ]
    pPrint _ _ x = internalError ("PPrint AAction: " ++ show x)

-- AForeignCall prints i instead of the string name
-- to print the Bluespec function being called, not the foreign one

instance PPrint AForeignCall where
   pPrint d _ (AForeignCall i _ (c : es) [] _) | isOne c =
       pPrint d 0 i <+> sep (map (pPrint d 1) es)

   pPrint d _ (AForeignCall i _ (c : es) [] resets) = sep [
       pPrint d 0 resets,
       text "if" <+> pPrint d 0 c <+> text "then",
       nest 2 (pPrint d 0 i <+> sep (map (pPrint d 1) es))
       ]

   pPrint d _ (AForeignCall i _ (c : es) ids _) | isOne c =
       sep (map (ppId d) ids) <+>
       text " <- " <+> pPrint d 0 i <+> sep (map (pPrint d 1) es)

   pPrint d _ (AForeignCall i _ (c : es) ids resets) = sep [
       pPrint d 0 resets,
       text "if" <+> pPrint d 0 c <+> text "then",
       nest 2 (sep (map (ppId d) ids) <+>
               text " <- " <+> pPrint d 0 i <+> sep (map (pPrint d 1) es))
       ]

   pPrint _ _ x = internalError ("pPrint AForeignCall: " ++ show x)

instance NFData AForeignCall where
    rnf (AForeignCall n f a w r) = rnf5 n f a w r

instance NFData ASPMethodInfo where
    rnf (ASPMethodInfo n t mr me mres ins assoc) = rnf7 n t mr me mres ins assoc

instance NFData AScheduler where
    rnf (ASchedEsposito fs) = rnf fs

instance NFData AClock where
    rnf (AClock osc gate) = rnf2 osc gate

instance NFData AReset where
    rnf (AReset wire) = rnf wire

instance NFData AInout where
    rnf (AInout wire) = rnf wire

instance NFData ANoInlineFun where
    rnf (ANoInlineFun name nums ports minst) = rnf4 name nums ports minst

instance NFData AAbstractInput where
    rnf (AAI_Port p) = rnf p
    rnf (AAI_Clock osc mgate) = rnf2 osc mgate
    rnf (AAI_Reset wire) = rnf wire
    rnf (AAI_Inout wire sz) = rnf2 wire sz

instance NFData ARule where
    rnf (ARule rid prags descr wprops pred acts assumps mparent) =
        rnf8 rid prags descr wprops pred acts assumps mparent

instance NFData AAssumption where
    rnf (AAssumption prop acts) = rnf2 prop acts

instance NFData AIFace where
    rnf (AIDef name ins props pred val finfo assumps) =
        rnf7 name ins props pred val finfo assumps
    rnf (AIAction ins props pred name body finfo) =
        rnf6 ins props pred name body finfo
    rnf (AIActionValue ins props pred name body val finfo) =
        rnf7 ins props pred name body val finfo
    rnf (AIClock name clk finfo) = rnf3 name clk finfo
    rnf (AIReset name rst finfo) = rnf3 name rst finfo
    rnf (AIInout name inout finfo) = rnf3 name inout finfo

isOne :: AExpr -> Bool
isOne (ASInt _ _ (IntLit _ _ 1)) = True
isOne _                          = False

instance PPrint AExpr where
--    pPrint d p (APrim aid _ o es@(_:_:_)) | binOp o =
--      pparen (p>0) $ sepList (map (pPrint d 1) es) (text "" <+> pPrint d 1 o <> (text ("_" ++ (createPositionString (getIdPosition aid)))))
    pPrint d p (APrim _ _ o es@(_:_:_)) | binOp o =
      pparen (p>0) $ sepList (map (pPrint d 1) es) (text "" <+> pPrint d 1 o)
    pPrint d p (APrim _ _ PrimCase (e:dd:ces)) =
        (text "case" <+> pPrint d 0 e <+> text "of") $+$
        foldr ($+$) (text "_ ->" <+> pPrint d 0 dd) (f ces)
          where f [] = []
                f (x:y:xs) = (pPrint d 0 x <+> text "->" <+> pPrint d 0 y) : f xs
                f x = internalError ("pPrint AExpr Aprim binOp: " ++ show x)
    pPrint d p (APrim _ _ PrimPriMux es) = pparen (p>0) $
        text "primux" <+> sep (f es)
          where f [] = []
                f (x:y:xs) = pparen True (sep [pPrint d 0 x <> text ",", pPrint d 0 y]) : f xs
                f x = internalError ("pPrint AExpr Aprim PriMux 1: " ++ show x)
    pPrint d p (APrim _ _ PrimMux es) = pparen (p>0) $
        text "mux" <+> sep (f es)
          where f [] = []
                f (x:y:xs) = pparen True (sep [pPrint d 0 x <> text ",", pPrint d 0 y]) : f xs
                f x = internalError ("pPrint AExpr Aprim PriMux 2: " ++ show x)
    pPrint d p (APrim _ _ o es) = pparen (p>0) $ pPrint d 1 o <+> sep (map (pPrint d 1) es)
    pPrint d p (ANoInlineFunCall _ i _ es)  = pparen (p>0) $ pPrint d 1 i <+> sep (map (pPrint d 1) es)
    pPrint d p (AFunCall _ i _ _ es)  = pparen (p>0) $ pPrint d 1 i <+> sep (map (pPrint d 1) es)
    pPrint d p (ATaskValue _ i _ _ n) = pparen (p>0) $ pPrint d 1 i <> text ("#" ++ itos(n))
    pPrint d p (AMethCall _ i m es) =
        pparen (p>0 && not (null es)) $
        pPrint d 1 i <>
        sep (text "." <> ppMethId d m : map (pPrint d 1) es)
    pPrint d p (AMethValue _ i m) =
        pparen (p>0) $ pPrint d 1 i <> text "." <> ppMethId d m
    pPrint d p (ATuple _ es) =
        pparen (p>0) $ parens (commaSep (map (pPrint d 0) es))
    pPrint d p (ATupleSel _ e idx) =
        pparen (p>0) $ pPrint d 0 e <> text "[" <> pPrint d 0 idx <> text "]"
    pPrint d p (ASPort _ i) = pPrint d p i
    pPrint d p (ASParam _ i) = pPrint d p i
    pPrint d p (ASDef _ i) = pPrint d p i
    pPrint d p (ASInt _ (ATBit sz) i) = text (showSizedVeriIntLit sz i)
    pPrint d p (ASInt _ _ i) = text (showVeriIntLit i)
    pPrint d p (ASReal _ _ r) = pPrint d p r
    pPrint d p (ASStr _ _ s) = text (show s)
    pPrint d p (ASAny t Nothing) = ppExprType d t $ text "_"
    pPrint d p (ASAny t (Just v)) = ppExprType d t $ text "_[" <> pPrint d maxPrec v <> text "]"
    pPrint d p (ASClock _ c) = text "clock" <+> pPrint d p c
    pPrint d p (ASReset _ r) = text "reset" <+> pPrint d p r
    pPrint d p (ASInout _ r) = text "inout" <+> pPrint d p r
    pPrint d p (AMGate _ o c) =
        pPrint d 1 o <> text "." <> pPrint d 1 c <> text ".gate"

ppMethId :: PDetail -> Id -> Doc
ppMethId d@PDReadable m = ppId d (unQualId m)
ppMethId d m = ppId d m

ppExprType :: PDetail -> AType -> Doc -> Doc
ppExprType d t e = text "(" <> e <+> text "::" <+> pPrint d 0 t <> text ")"

instance PPrint AType where
    pPrint d p (ATBit n) = text ("Bit " ++ itos n)
    pPrint d p (ATReal)  = text ("Real ")
    pPrint d p (ATString Nothing) = text "String (unsized)"
    pPrint d p (ATString (Just n)) = text ("String (" ++ (itos n) ++ " chars)")
    pPrint d p (ATArray sz ty) =
        text "Array" <+> text (itos sz) <+> pPrint d 0 ty
    pPrint d p (ATTuple ts) =
        text "Tuple" <+> parens (commaSep (map (pPrint d 0) ts))
    pPrint d p (ATAbstract i ns) = sep (text "ABSTRACT: " : pPrint d 0 i : map (pPrint d 0) ns)

binOp :: PrimOp -> Bool
binOp p = p `elem`
        [PrimAdd, PrimSub, PrimAnd, PrimOr, PrimXor,
         PrimMul, PrimQuot, PrimRem,
         PrimSL, PrimSRL, PrimSRA,
         PrimEQ, PrimEQ3,
         PrimULE, PrimULT,
         PrimSLE, PrimSLT,
         PrimBAnd, PrimBOr,
         PrimConcat
        ]


-- PRETTY PRINTING WITH DEFINITION EXPANSION --
data PExpandDef = PExpandDef {defmap :: M.Map AId AExpr
                             ,lookupLimit :: Int
                             ,lookupLevel :: Int}

data PExpandLiteral = Sized | Boolean | Index
                      deriving (Eq)

data PExpandContext =
    PExpandContext {
                    useParen    :: Bool -- if needed
                   ,parentOp    :: Maybe PrimOp
                   ,literal     :: PExpandLiteral
                   }

getP :: PExpandContext -> Int
getP ec = if useParen ec then 1 else 0

-- No parens, show use sized literal
defContext :: PExpandContext
defContext = PExpandContext { useParen=False,
                              parentOp=Nothing,
                              literal=Sized}

-- Boolean Context
bContext :: PExpandContext
bContext = PExpandContext { useParen=False,
                            parentOp=Nothing,
                            literal=Boolean}

-- use parens
pContext :: PExpandContext
pContext = PExpandContext { useParen=True,
                            parentOp=Nothing,
                            literal=Sized}




class (PPrint a) => PPrintExpand a where
    pPrintExpand :: PExpandDef -> PDetail -> PExpandContext -> a -> Doc

pPrintExpandFlags :: (PPrintExpand a) => Flags -> [ADef] -> PDetail -> PExpandContext -> a -> Doc
pPrintExpandFlags flags ds =
    let edef = PExpandDef {defmap = M.fromList [(id,expr) | (ADef id _ expr _) <- ds ]
                          ,lookupLimit = expandATSlimit flags
                          ,lookupLevel = 0 }
  in pPrintExpand edef

ppeString :: (PPrintExpand a) => [ADef] -> PExpandContext -> a -> String
ppeString ds ec =
 let edef = PExpandDef {defmap = M.fromList [(id,expr) | (ADef id _ expr _) <- ds ]
                       ,lookupLimit = 30
                       ,lookupLevel = 0 }
    in init . pretty 60 60 . pPrintExpand edef PDReadable ec

instance (PPrintExpand a) => PPrintExpand [a] where
    pPrintExpand _ d _ [] = text "[]"
    pPrintExpand m d _ xs = let xs' = map (pPrintExpand m d defContext) xs
                            in  text "[" <> commaSep xs' <> text "]"

ppeAPackage :: Int -> PDetail -> APackage -> Doc
ppeAPackage lim d apkg@(APackage { apkg_local_defs = ds }) =
    let edef = PExpandDef { defmap = M.fromList [(id,expr) | (ADef id _ expr _) <- ds ]
                          ,lookupLimit = lim
                          ,lookupLevel = 0 }
     in
        (text "APackage" <+> ppId d (apkg_name apkg) <>
         if apkg_is_wrapped apkg then text " -- function" else text "") $+$
        (case (apkg_backend apkg) of
             Nothing -> empty
             Just be -> text " -- backend:" <+> pPrint d 0 be) $+$
        text "-- APackage parameters" $+$
        pPrint d 0 (apkg_size_params apkg) $+$
        text "-- APackage arguments" $+$
        foldr (($+$) . pPrint d 0) empty (apkg_inputs apkg) $+$
        text "-- APackage wire info" $+$
        pPrint d 0 (apkg_external_wires apkg) $+$
        text "-- APackage clock domains" $+$
        pPrint d 0 (apkg_clock_domains apkg) $+$
        text "-- APackage resets" $+$
        pPrint d 0 (apkg_reset_list apkg) $+$
        text "-- AP state elements" $+$
        foldr (($+$) . ppeVI edef d) empty (apkg_state_instances apkg) $+$
--        text "-- AP local definitions" $+$
--        foldr ($+$) empty (map (pPrintExpand edef d 0) (apkg_local_defs apkg)) $+$
        text "-- AP rules" $+$
        foldr (($+$) . pPrintExpand edef d defContext) empty (apkg_rules apkg) $+$
        text "-- AP scheduling pragmas" $+$
        pPrint d 0 (apkg_schedule_pragmas apkg) $+$
        text "-- AP interface" $+$
        foldr ($+$) empty [(text "-- AP  apkg_interface def" <+> pPrint d 0 (apkg_name apkg)) $+$
                           pPrintExpand edef d defContext i | i <- apkg_interface apkg] $+$
        text "-- AP instance comments" $+$
        foldr (($+$) . ppInstComment d) empty (apkg_inst_comments apkg) $+$
        text "-- AP remaining proof obligations" $+$
        pPrint d 0 (apkg_proof_obligations apkg)

ppeVI :: PExpandDef -> PDetail -> AVInst -> Doc
ppeVI m d (AVInst i t ui mts pts vi es ns) =
    pPrint d 0 i <+> text "::" <+>
    pPrint d 0 t <+> text "=" <+> (ppeVTI m d (vi, es, ns) $+$
    text "meth types=" <> pPrint d 0 mts $+$
    text "port types=" <> pPrint d 0 pts)

ppeVTI :: PExpandDef -> PDetail -> (VModInfo, [AExpr], [(AId, Integer)]) -> Doc
ppeVTI m d (vi, es, ns) =
    sep [pPrint d 0 (vName vi),
         pPrint d 0 vi,
         pPrintExpand m d defContext es,
         pPrint d 0 ns]

instance PPrintExpand AIFace where
    -- XXX print assumptions
    pPrintExpand m d ec (AIDef id is wp g b _ _) =
        (text "--" <+> pPrint d (getP ec) g) $+$
        foldr (($+$) . ppV d) (pPrint d (getP ec) b) is $+$
        text ""
    pPrintExpand m d ec (AIAction is wp g _ rs _) =
        (text "--" <+> pPrint d (getP ec) g) $+$
        foldr (($+$) . ppV d) (pPrintExpand m d ec rs) is $+$
        text ""
    pPrintExpand m d ec (AIActionValue is wp g _ rs b _) =
        (text "--" <+> pPrint d (getP ec) g) $+$
        foldr (($+$) . ppV d) (pPrintExpand m d ec rs) is $+$
        foldr (($+$) . ppV d) (pPrint d (getP ec) b) is $+$
        text ""
    pPrintExpand m d ec (AIClock i c _) = pPrint d (getP ec) c
    pPrintExpand m d ec (AIReset i r _) = pPrint d (getP ec) r
    pPrintExpand m d ec (AIInout i r _) = pPrint d (getP ec) r

instance PPrintExpand ARule where
    -- XXX print assumptions
    pPrintExpand m d@PDDebug _ (ARule s _ _ _ p as _ _) =
        (text "rule" <+> pPrint d 0 s)
    pPrintExpand m d _ (ARule s rps sd wp p as _ _) =
        vcat (map (pPrint d 0) rps) $+$
        (text "rule" <+> pPrint d 0 s <> text (" " ++ show sd) <> text ":") $+$
        (text " when" <+> pPrintExpand m d bContext  p) $+$
        (text "  ==>" <+> ppeActions m d as)

ppeActions :: PExpandDef -> PDetail -> [AAction] -> Doc
ppeActions m d as = text "{" <+> sep (map ppeA as) <+> text "}"
        where ppeA a = pPrintExpand m d defContext a <> text ";"

instance PPrintExpand AAction where
    pPrintExpand m d _ (ACall i meth (c : es)) | isOne c =
        pPrint d 0 i <> text "." <> ppMethId d meth <+> sep (map (pPrintExpand m d pContext) es)
    pPrintExpand m d _ (ACall i meth (c : es)) = sep [
        text "if" <+> pPrintExpand m d bContext c <+> text "then",
        nest 2 (pPrint d 0 i <> text "." <> ppMethId d meth <+> sep (map (pPrintExpand m d pContext) es))
        ]
    pPrintExpand m d _ (AFCall i _ _ (c : es) _) | isOne c = pPrint d 0 i <+> sep (map (pPrintExpand m d pContext) es)
    pPrintExpand m d _ (AFCall i _ _ (c : es) _) = sep [
        text "if" <+> pPrintExpand m d bContext c <+> text "then",
        nest 2 (pPrint d 0 i <+> sep (map (pPrintExpand m d pContext) es))

        ]
    pPrintExpand m d _ (ATaskAction i _ _ n (c : es) _ _ _) | isOne c = pPrint d 0 i <> text ("#" ++ itos(n)) <+> sep (map (pPrintExpand m d pContext) es)
    pPrintExpand m d _ (ATaskAction i _ _ n (c : es) _ _ _) = sep [
        text "if" <+> pPrintExpand m d defContext c <+> text "then",
        nest 2 (pPrint d 0 i <> text ("#" ++ itos(n)) <+> sep (map (pPrintExpand m d pContext) es))

        ]
    pPrintExpand _ _ _  x = internalError ("pPrintExpand AAction: " ++ show x)


isAssocOp :: PrimOp -> Bool
isAssocOp PrimMul = True
isAssocOp PrimAdd = True
isAssocOp PrimOr = True
isAssocOp PrimXor = True
isAssocOp PrimBAnd = True
isAssocOp PrimBOr = True
isAssocOp _ = False

instance PPrintExpand AExpr where
    pPrintExpand m d ec (APrim _ _ PrimConcat es) =
        bropt $ hsep ( punctuate comma docArgs )
            where
               bropt = if (parentOp ec == Just PrimConcat) then id else braces
               ec' = defContext {parentOp = Just PrimConcat}
               docArgs = map (pPrintExpand m d ec') es

    pPrintExpand m d ec (APrim _ _ o es@(_:_:_)) | binOp o, isAssocOp o =
        pparen (p) $ sepList (map (pPrintExpand m d ec') es) (text "" <+> pPrint d 1 o)
            where ec' =  ec {parentOp = Just o, useParen = True}
                  p = (Just o /= parentOp ec) && useParen ec
    pPrintExpand m d ec (APrim _ _ o es@(_:_:_)) | binOp o =
        pparen (p) $ sepList (map (pPrintExpand m d ec') es) (text "" <+> pPrint d 1 o)
            where ec' =  pContext {parentOp = Just o}
                  p = useParen ec

    pPrintExpand m d ec (APrim _ _ PrimCase (e:dd:ces)) =
        (text "case" <+> pPrintExpand m d ec' e <+> text "of") $+$
        foldr ($+$) (text "_ ->" <+> pPrintExpand m d ec' dd) (f ces)
          where ec' = defContext
                f [] = []
                f (x:y:xs) = (pPrintExpand m d ec' x <+> text "->" <+> pPrintExpand m d ec' y) : f xs
                f  x = internalError ("pPrintExpand APrim _ PrimCase: " ++ show x)
    pPrintExpand m d ec (APrim _ _ PrimPriMux es) = pparen (p) $
        text "primux" <+> sep (f es)
          where p = useParen ec
                ec' = defContext { literal= literal ec}
                ecb = defContext { literal=Boolean }
                f [] = []
                f (x:y:xs) = parens (sep [pPrintExpand m d ecb x <> comma,  pPrintExpand m d ec' y]) : f xs
                f  x = internalError ("pPrintExpand APrim _ PrimPriMux: " ++ show x)
    pPrintExpand m d ec (APrim _ _ PrimMux es) = pparen (p) $
        text "mux" <+> sep (f es)
          where p = useParen ec
                ec' = defContext { literal= literal ec}
                ecb = defContext { literal=Boolean }
                f [] = []
                f (x:y:xs) = parens (sep [pPrintExpand m d ecb x <> comma , pPrintExpand m d ec' y]) : f xs
                f  x = internalError ("pPrintExpand APrim: " ++ show x)
    pPrintExpand m d ec (APrim _ _ PrimExtract [var, hi, lo]) =
        pPrintExpand m d pContext var <> lbrack
                       <> (if ( dhi == dlo )
                           then dhi <> rbrack
                           else dhi <> colon <> dlo <> rbrack )
                       where eci = defContext { literal= Index  }
                             dhi = pPrintExpand m d eci hi
                             dlo = pPrintExpand m d eci lo

    pPrintExpand m d ec (APrim _ _ PrimIf [cond, thn, els]) =
         pparen(p) $ pPrintExpand m d ecc cond $$ text "?"
                       <+> pPrintExpand m d ect thn $$ colon
                       <+> pPrintExpand m d ece els
        where p = useParen ec
              ecc = pContext { literal = Boolean }
              ect = defContext {literal = literal ec}
              ece = pContext {literal = literal ec}

    pPrintExpand m d ec (APrim _ _ o es) = pparen (useParen ec) $ pPrint d 1 o <+> sep (map (pPrintExpand m d pContext) es)
    pPrintExpand m d ec (ANoInlineFunCall _ i _ es)  = pPrint d 1 i <>
                                                       ( parens $ sep $ punctuate comma (map (pPrintExpand m d defContext) es))
    pPrintExpand m d ec (AFunCall _ i _ _ es)  = pPrint d 1 i <>
                                                 ( parens $ sep $ punctuate comma (map (pPrintExpand m d defContext) es))
    pPrintExpand m d ec (ATaskValue _ i _ _ n) = pparen (useParen ec) $ pPrint d 1 i <> text ("#" ++ itos(n))
    pPrintExpand m d ec (AMethCall _ i meth []) | qualEq meth idPreludeRead = pPrint d 1 i
    pPrintExpand m d ec (AMethCall _ i meth es) =
               pPrint d 1 i <> text "."
               <> ppMethId d meth
               <> if (null es) then empty else (parens (hsep ( punctuate comma docArgs )) )
                   where
                   docArgs = map (pPrintExpand m d defContext) es
    pPrintExpand m d ec (AMethValue _ i meth) =
        pPrint d 1 i <> text "." <> ppMethId d meth
    pPrintExpand m d ec (ATuple _ es) =
        pparen (useParen ec) $ parens (commaSep (map (pPrintExpand m d defContext) es))
    pPrintExpand m d ec (ATupleSel _ e idx) =
        pparen (useParen ec) $ pPrintExpand m d defContext e <> text ("[" ++ itos idx ++ "]")
    pPrintExpand m d ec (ASPort _ i)  = pPrint d (getP ec) i
    pPrintExpand m d ec (ASParam _ i) = pPrint d (getP ec) i
    pPrintExpand m d ec (ASDef _ i) | isIdWillFire i && (lookupLevel m) > 0 ||
                                      isIdCanFire i && (lookupLevel m) > 1  = pPrint d (getP ec) i
                                    | (lookupLevel m) > (lookupLimit m) = pPrint d (getP ec) i <> text "(...)"
                                    | otherwise =
      let m' = m { lookupLevel = 1 + lookupLevel m }
         in pPrintExpand m' d ec $ defLookup i m
    pPrintExpand m d ec e@(ASInt _ (ATBit 1) i) | literal ec == Boolean, isFalse e  = text "False"
    pPrintExpand m d ec e@(ASInt _ (ATBit 1) i) | literal ec == Boolean, isTrue e   = text "True"
    pPrintExpand m d ec (ASInt _ (ATBit sz) i)  | (literal ec == Index) = text (showVeriIntLit i)
    pPrintExpand m d ec (ASInt _ (ATBit sz) i) = text (showSizedVeriIntLit sz i)
    pPrintExpand m d ec (ASInt _ _ i) = text (showVeriIntLit i)
    pPrintExpand m d ec (ASReal _ _ r) = pPrint d (getP ec) r
    pPrintExpand m d ec (ASStr _ _ s) = text (show s)
    pPrintExpand m d ec (ASAny t _) = ppExprType d t $ text "_"
    pPrintExpand m d ec c@(ASClock { }) = pPrint d (getP ec) c
    pPrintExpand m d ec r@(ASReset { }) = pPrint d (getP ec) r
    pPrintExpand m d ec r@(ASInout { }) = pPrint d (getP ec) r
    pPrintExpand m d ec g@(AMGate { })  = pPrint d (getP ec) g

defLookup :: AId -> PExpandDef -> AExpr
defLookup d ped = M.findWithDefault err d (defmap ped)
    where err = internalError $ "defLookup: no definition `" ++ ppString d ++ "' found"


-- #############################################################################
-- # Some standardized methods for making (default) method strings
-- #############################################################################
data MethodPart =
    MethodArg Integer    | -- argument 1, 2, ... input
    MethodResult Integer | -- return value 1, 2, ... output
    MethodEnable           -- enable signal input
    deriving (Eq)

-- The method syntax is as follows:
--   Arguments are <inst>$<meth>_ARG_<argnum> starting from 1
--     (e.g. the_fifo$enq_ARG_1)
--   Return values are <inst>$<meth>_RES_<resnum> (e.g. the_fifo$first_RES_1)
--   Enable signals are <inst>$EN_<meth> (e.g. the_fifo$EN_enq)
-- Multi-ported methods are <inst>$<meth>_<portnum>_ARG_<argnum>
-- or <inst>$<meth>_<portnum>_RES_<resnum>
-- The portnum is only omitted if the method has one or
-- and infinite number of ports (like a register)
-- XXX these should probably just be a data type rather than Ids
mkMethId :: Id -> Id -> Maybe Integer -> MethodPart -> Id
mkMethId o m ino mp =
        -- trace ("POS O: " ++ (show (getIdPosition o)) ++ " " ++
        --        "POS M: " ++ (show (getIdPosition m))) $
        addIdProps
            (mkId (getIdPosition o) idstring)
            (IdPMeth : (enprops ++ getIdProps o))
        where
          idstring = (mkMethStr o m ino mp)
          enprops = if mp == MethodEnable then [IdP_enable] else []

isMethId :: Id -> Bool
isMethId i = hasIdProp i IdPMeth

mkMethStr :: Id -> Id -> Maybe Integer -> MethodPart -> FString
mkMethStr obj m m_port mp =
    let meth_base = getIdFString (unQualId m)
        meth_port = case m_port of
                      Nothing -> meth_base
                      Just port  -> concatFString
                                      [meth_base,
                                       fsUnderscore,
                                       mkNumFString port]
        base = case mp of
                   MethodArg n -> mkMethArgStr meth_port n
                   MethodResult n -> mkMethResStr meth_port n
                   MethodEnable ->
                       -- XXX are we overloading fsEnable?
                       concatFString [fsEnable, meth_port]
        inst = getIdFString obj
    in  concatFString [inst,
                       fsDollar,
                       base]

mkMethArgStr :: FString -> Integer -> FString
mkMethArgStr meth_port n =
    if (n == 0)
    then internalError "mkMethArgStr"
    else concatFString [meth_port, fsUnderscore, fs_arg, mkNumFString n]

mkMethResStr :: FString -> Integer -> FString
mkMethResStr meth_port n =
    if (n == 0)
    then internalError "mkMethResStr"
    else concatFString [meth_port, fsUnderscore, fs_res, mkNumFString n]

-- #############################################################################
-- #
-- #############################################################################

defaultAId :: Id
defaultAId = mkId noPosition (mkFString "ABC")

-- #############################################################################
-- #
-- #############################################################################

-- name for the wire that tracks a method's calling condition
-- _rule_EN_o$m
mkCFCondWireInstId :: Id -> Id -> Id -> Id
mkCFCondWireInstId object method rule = mkId pos str
  -- method part will be EN_o$m
  where methStr      = mkMethStr object method Nothing MethodEnable
        (_, ruleStr) = getIdFStrings rule
        pos = getIdPosition rule
        str = concatFString [fsUnderscore, ruleStr, fsUnderscore, methStr]
