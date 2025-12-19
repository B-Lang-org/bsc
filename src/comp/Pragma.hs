{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Pragma(
              -- Package and module pragmas
              Pragma(..), PProp(..), PPnm(..),
              getPragmaArgNames, getModulePragmaName,

              -- Rule pragmas
              RulePragma(..), getRulePragmaName,

              -- Schedule pragmas
              SchedulePragma(..),
              CSchedulePragma, ISchedulePragma, ASchedulePragma,
              longnameToId, mapSPIds,
              SPIdMap, substSchedPragmaIds,
              SPIdSplitMap, splitSchedPragmaIds,
              removeSchedPragmaIds,
              isRulePreempt,
              extractSchedPragmaIds,

              isAlwaysRdy,
              isAlwaysEn,
              isEnWhenRdy,

              isGatedInputClk, isGatedDefaultClk,
              hasDefaultClk, hasDefaultRst,
              hasInhighAttribute, hasUnusedAttribute,
              hasRuleHide,
              ppPProp, pvpPProp,

              -- Interface pragmas
              IfcPragma(..),
              noIfcPragmas,getIfcPName,
              filterIArgNames,
              filterPrintIfcArgs,
              getARAEPragmas,
              extractDuplicatePragmas,
              lookupPrefixIfcPragma,
              lookupResultIfcPragma,
              lookupReadyIfcPragma,
              lookupEnSignalIfcPragma,
              lookupRdySignalIfcPragma,
              isAlwaysReadyIfc,
              isAlwaysEnabledIfc,
              getMethodPragmaInfo, getClockPragmaInfo, getResetPragmaInfo, getInoutPragmaInfo,
              isParamModArg, filterPPparam,

              -- Def pragmas
              DefProp(..),
              defPropsHasNoCSE
              ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import qualified Data.Map as M
import Data.Maybe(listToMaybe)
import Data.List(sort)
import qualified Data.Generics as Generic

import Eval(NFData(..), rnf, rnf2, rnf3)
import PPrint
import PVPrint
import Id
import PreIds(idDefaultClock, idDefaultReset)
import ErrorUtil(internalError)
import Util(itos, doubleQuote, findDup)
import SchedInfo
import Position
import IdPrint
--import Util(traces)

-- ========================================================================
-- Pragma
--

data Pragma
        = Pproperties Id [PProp]-- module Id and properties associate with
        | Pnoinline [Id]        -- [Id] is a list of functions which should not be inlined
        deriving (Eq, Ord, Show, Generic.Data, Generic.Typeable)


instance PPrint Pragma where
    pPrint d p (Pproperties i pps) =
        (text "{-# properties" <+> ppId d i <+> text "= { ") <>
          sepList (map (pPrint d 0) pps) (text ",") <> text " } #-}"
    pPrint d p (Pnoinline is) =
        text "{-# noinline" <+> sep (map (ppId d) is) <+> text " #-}"

instance PVPrint Pragma where
    pvPrint d p (Pproperties i pps) =
        foldr ($+$) empty (map (pvpPProp d) pps)
    pvPrint d p (Pnoinline is) =
        text "(* noinline" <+> sep (map (pvpId d) is) <+> text " *)"

instance NFData Pragma where
    rnf (Pproperties i pps) = rnf2 i pps
    rnf (Pnoinline is) = rnf is

instance HasPosition Pragma where
    getPosition (Pproperties i _) = getPosition i
    getPosition (Pnoinline (i:_)) = getPosition i
    getPosition (Pnoinline [])    = internalError "CSyntax:HasPosition(Pragma).getPosition: Pnoinline []"

-- --------------------


-- Module definition properties:
data PProp
        = PPverilog                        -- generate verilog
        | PPforeignImport Id               -- wrapper for a foreign import
            -- (Id is link name, needed for dependency check, if we're
            --  generating the .ba file for the link name, not the src name)
        | PPalwaysReady        [Longname]         -- no ready signals for these methods ([] means all)
        | PPalwaysEnabled [Longname]       -- execute on every cycle
        | PPenabledWhenReady [Longname]    -- enable is equivalent to ready
        | PPscanInsert Integer             -- insert scan chain ports
        | PPbitBlast                       -- do "bit blasting",
                                           --     e.g., split multibit ports
        | PPCLK String                     -- clock port prefix
        | PPGATE String                    -- gate port prefix
        | PPRSTN String                    -- reset port prefix
        | PPclock_osc  [(Id,String)]       -- port name for clock
        | PPclock_gate [(Id,String)]       -- port name for gate
        | PPgate_inhigh [Id]               -- clock args with inhigh gates
        | PPgate_unused [Id]               -- clock args with unused gates
        | PPreset_port [(Id,String)]       -- port name for reset
        | PParg_param [(Id,String)]        -- name for parameter argument
        | PParg_port [(Id,String)]         -- port name for other arguments
        | PParg_clocked_by [(Id,String)]   -- clocks of module arguments
        | PParg_reset_by [(Id,String)]     -- resets of module arguments
        | PPoptions [String]               -- compiler options
        | PPgate_input_clocks [Id]         -- list of clock args with gates
        | PPmethod_scheduling (MethodConflictInfo Longname)
                        -- scheduling constraints for interface arg methods
        | PPdoc String          -- comment to carry through to Verilog
        | PPperf_spec [[Id]]    -- method composition order for performance specs
        | PPclock_family    [Id]   -- ids of input clocks in the same family
        | PPclock_ancestors [[Id]] -- input clock ancestry sequences
        -- module arguments which should generate to params instead of ports
        | PPparam [Id]
        | PPinst_name Id
        | PPinst_hide
        | PPinst_hide_all
        | PPdeprecate String
      deriving (Show, Eq, Ord, Generic.Data, Generic.Typeable)

data PPnm
        = PPnmOne Id
        | PPnmArray Id Integer Integer
      deriving (Show, Eq, Ord)


instance PPrint PProp where
    pPrint d _ (PPscanInsert i) = text "scanInsert = " <+> pPrint d 0 i
    pPrint d _ (PPCLK s) = text ("clock_prefix = " ++ s)
    pPrint d _ (PPGATE s) = text ("gate_prefix = " ++ s)
    pPrint d _ (PPRSTN s) = text ("reset_prefix = " ++ s)
    pPrint d _ (PPclock_osc xs) =
        text "clock_osc = {"
        <> sepList [ text "(" <> ppId d i <> text "," <> (text s) <> text ")"
                   | (i,s) <- xs ]
                   (text ",")
        <> text "}"
    pPrint d _ (PPclock_gate xs) =
        text "clock_gate = {"
        <> sepList [ text "(" <> ppId d i <> text "," <> (text s) <> text ")"
                   | (i,s) <- xs ]
                   (text ",")
        <> text "}"
    pPrint d _ (PPgate_inhigh is) =
        text "gate_inhigh = {" <> sepList (map (ppId d) is) (text ",") <> text "}"
    pPrint d _ (PPgate_unused is) =
        text "gate_unused = {" <> sepList (map (ppId d) is) (text ",") <> text "}"
    pPrint d _ (PPreset_port xs) =
        text "reset_port = {"
        <> sepList [ text "(" <> ppId d i <> text "," <> (text s) <> text ")"
                   | (i,s) <- xs ]
                   (text ",")
        <> text "}"
    pPrint d _ (PParg_param xs) =
        text "arg_param = {"
        <> sepList [ text "(" <> ppId d i <> text "," <> (text s) <> text ")"
                   | (i,s) <- xs ]
                   (text ",")
        <> text "}"
    pPrint d _ (PParg_port xs) =
        text "arg_port = {"
        <> sepList [ text "(" <> ppId d i <> text "," <> (text s) <> text ")"
                   | (i,s) <- xs ]
                   (text ",")
        <> text "}"
    pPrint d _ (PParg_clocked_by xs) =
        text "clocked_by = {"
        <> sepList [ text "(" <> ppId d i <> text "," <> (text s) <> text ")"
                   | (i,s) <- xs ]
                   (text ",")
        <> text "}"
    pPrint d _ (PParg_reset_by xs) =
        text "reset_by = {"
        <> sepList [ text "(" <> ppId d i <> text "," <> (text s) <> text ")"
                   | (i,s) <- xs ]
                   (text ",")
        <> text "}"
    pPrint d _ (PPoptions os) =
        text "options = {"
        <> sepList (map (text . show) os) (text ",")
        <> text "}"
    pPrint d _ (PPdoc comment) = text ("doc = " ++ doubleQuote comment)
    pPrint d _ (PPdeprecate comment) = text ("deprecate = " ++ doubleQuote comment)
    pPrint d _ (PPinst_hide) = text "hide"
    pPrint d p v = text (drop 2 (show v))

instance PPrint PPnm where
    pPrint d _ (PPnmOne i) = ppId d i
    pPrint d _ (PPnmArray i h l) =
        ppId d i
        <> text ("[" ++ itos h ++ ":" ++ itos l ++ "]")

instance PVPrint PProp where
    pvPrint d _ (PPscanInsert i) = text "scan_insert =" <+> pvPrint d 0 i
    pvPrint d _ (PPCLK s) = text ("clock_prefix = " ++ s)
    pvPrint d _ (PPGATE s) = text ("gate_prefix = " ++ s)
    pvPrint d _ (PPRSTN s) = text ("reset_prefix = " ++ s)
    pvPrint d _ (PPclock_osc xs) =
        text "clock_osc = {"
        <> sepList [ text "(" <> pvpId d i <> text "," <> (text s) <> text ")"
                   | (i,s) <- xs ]
                   (text ",")
        <> text "}"
    pvPrint d _ (PPclock_gate xs) =
        text "clock_gate = {"
        <> sepList [ text "(" <> pvpId d i <> text "," <> (text s) <> text ")"
                   | (i,s) <- xs ]
                   (text ",")
        <> text "}"
    pvPrint d _ (PPgate_inhigh is) =
        text "gate_inhigh = {" <> sepList (map (pvpId d) is) (text ",") <> text "}"
    pvPrint d _ (PPgate_unused is) =
        text "gate_unused = {" <> sepList (map (pvpId d) is) (text ",") <> text "}"

    pvPrint d _ (PPreset_port xs) =
        text "reset_port = {"
        <> sepList [ text "(" <> pvpId d i <> text "," <> (text s) <> text ")"
                   | (i,s) <- xs ]
                   (text ",")
        <> text "}"
    pvPrint d _ (PParg_param xs) =
        text "param_port = {"
        <> sepList [ text "(" <> pvpId d i <> text "," <> (text s) <> text ")"
                   | (i,s) <- xs ]
                   (text ",")
        <> text "}"
    pvPrint d _ (PParg_port xs) =
        text "arg_port = {"
        <> sepList [ text "(" <> pvpId d i <> text "," <> (text s) <> text ")"
                   | (i,s) <- xs ]
                   (text ",")
        <> text "}"
    pvPrint d _ (PParg_clocked_by xs) =
        text "clocked_by = {"
        <> sepList [ text "(" <> pvpId d i <> text "," <> (text s) <> text ")"
                   | (i,s) <- xs ]
                   (text ",")
        <> text "}"
    pvPrint d _ (PParg_reset_by xs) =
        text "reset_by = {"
        <> sepList [ text "(" <> pvpId d i <> text "," <> (text s) <> text ")"
                   | (i,s) <- xs ]
                   (text ",")
        <> text "}"
    pvPrint d _ (PPoptions os) = text "options = {" <> sepList (map (text . show) os) (text ",") <> text "}"
    pvPrint d _ (PPverilog) = text "synthesize"
    pvPrint d _ (PPalwaysReady ms) = text "always_ready"
    pvPrint d _ (PPalwaysEnabled ms) = text "always_enabled"
    pvPrint d _ (PPenabledWhenReady ms) = text "enabled_when_ready"
    pvPrint d _ (PPbitBlast) = text "bit_blast"
    pvPrint d _ (PPdoc comment) = text ("doc = " ++ doubleQuote comment)
    pvPrint d _ (PPdeprecate comment) = text ("deprecate = " ++ doubleQuote comment)
    pvPrint d _ (PPparam ids) = text "param = \"" <> sepList (map (pvpId d) ids) (text ",") <> text "\""
    pvPrint d _ (PPinst_name i) = text "inst_name = \"" <> pvpId d i <> text "\""
    pvPrint d _ (PPinst_hide) = text "inst_hide"
    pvPrint d p v = text (drop 2 (show v))

instance PVPrint PPnm where
    pvPrint d _ (PPnmOne i) = pvpId d i
    pvPrint d _ (PPnmArray i h l) = pvpId d i <> text ("[" ++ show h ++ ":" ++ show l ++ "]")

pvpPProp :: PDetail -> PProp -> Doc
pvpPProp d pprop = text "(*" <+> pvPrint d 0 pprop <+> text "*)"

ppPProp :: PDetail -> PProp -> Doc
ppPProp d pprop = text "{-#" <+> pPrint d 0 pprop <+> text "#-};"

instance NFData PProp where
    rnf (PPscanInsert i) = seq i ()
    rnf (PPCLK i) = seq i ()
    rnf (PPGATE i) = seq i ()
    rnf (PPRSTN i) = seq i ()
    rnf (PPclock_osc xs) = rnf xs
    rnf (PPclock_gate xs) = rnf xs
    rnf (PPgate_inhigh is) = rnf is
    rnf (PPgate_unused is) = rnf is
    rnf (PPreset_port xs) = rnf xs
    rnf (PParg_param xs) = rnf xs
    rnf (PParg_port xs) = rnf xs
    rnf (PParg_clocked_by xs) = rnf xs
    rnf (PParg_reset_by xs) = rnf xs
    rnf (PPoptions os) = rnf os
    rnf (PPclock_family is) = rnf is
    rnf (PPclock_ancestors ils) = rnf ils
    rnf x = seq x ()

instance NFData PPnm where
    rnf (PPnmOne i) = rnf i
    rnf (PPnmArray i h l) = rnf3 i h l

getPragmaArgNames :: PProp -> [String]
getPragmaArgNames (PPclock_osc ps)   = [ getIdBaseString i | (i,_) <- ps ]
getPragmaArgNames (PPclock_gate ps)  = [ getIdBaseString i | (i,_) <- ps ]
getPragmaArgNames (PPreset_port ps)  = [ getIdBaseString i | (i,_) <- ps ]
getPragmaArgNames (PParg_param ps)   = [ getIdBaseString i | (i,_) <- ps ]
getPragmaArgNames (PParg_port ps)    = [ getIdBaseString i | (i,_) <- ps ]
getPragmaArgNames (PParg_clocked_by ps) = map (getIdBaseString . fst) ps
getPragmaArgNames (PParg_reset_by ps)   = map (getIdBaseString . fst) ps
getPragmaArgNames (PPgate_inhigh is) = map getIdBaseString is
getPragmaArgNames (PPgate_unused is) = map getIdBaseString is
getPragmaArgNames (PPgate_input_clocks is) = map getIdBaseString is
getPragmaArgNames (PPclock_family is)      = map getIdBaseString is
getPragmaArgNames (PPclock_ancestors is)   = map getIdBaseString (concat is)
getPragmaArgNames (PPparam is)             = map getIdBaseString is
getPragmaArgNames _ = []

getModulePragmaName :: PProp -> String
getModulePragmaName PPverilog                = "synthesize"
getModulePragmaName (PPforeignImport {})     = "foreign"
getModulePragmaName (PPalwaysReady {})       = "always_ready"
getModulePragmaName (PPalwaysEnabled {})     = "always_enabled"
getModulePragmaName (PPenabledWhenReady {})  = "enabled_when_ready"
getModulePragmaName (PPscanInsert {})        = "scan_insert"
getModulePragmaName PPbitBlast               = "bit_blast"
getModulePragmaName (PPCLK {})               = "clock_prefix"
getModulePragmaName (PPGATE {})              = "gate_prefix"
getModulePragmaName (PPRSTN {})              = "reset_prefix"
getModulePragmaName (PPclock_osc {})         = "osc"
getModulePragmaName (PPclock_gate {})        = "gate"
getModulePragmaName (PPgate_inhigh {})       = "inhigh"
getModulePragmaName (PPgate_unused {})       = "unused"
getModulePragmaName (PPreset_port {})        = "reset"
getModulePragmaName (PParg_param {})         = "parameter"
getModulePragmaName (PParg_port {})          = "port"
getModulePragmaName (PParg_clocked_by {})    = "clocked_by"
getModulePragmaName (PParg_reset_by {})      = "reset_by"
getModulePragmaName (PPoptions {})           = "options"
getModulePragmaName (PPgate_input_clocks {}) = "gate_input_clocks"
getModulePragmaName (PPmethod_scheduling {}) = "method_scheduling"
getModulePragmaName (PPdoc {})               = "doc"
getModulePragmaName (PPperf_spec {})         = "perf_spec"
getModulePragmaName (PPclock_family {})      = "clock_family"
getModulePragmaName (PPclock_ancestors {})   = "clock_ancestors"
getModulePragmaName (PPparam {})             = "param"
getModulePragmaName (PPinst_name {})         = "inst_name"
getModulePragmaName (PPinst_hide)            = "inst_hide"
getModulePragmaName (PPinst_hide_all)        = "inst_hide_all"
getModulePragmaName (PPdeprecate {})         = "deprecate"


-- ========================================================================
-- RulePragma
--

data RulePragma
    = RPfireWhenEnabled
    | RPnoImplicitConditions
    | RPaggressiveImplicitConditions
    | RPconservativeImplicitConditions
    | RPnoWarn -- suppress (on a per-rule basis) warnings G0023, G0036, and G0117
    | RPwarnAllConflicts
    | RPcanScheduleFirst
    | RPclockCrossingRule
    | RPdoc String  -- comment to carry through to Verilog
    | RPhide
      deriving (Show, Eq, Ord, Generic.Data, Generic.Typeable)

-- used for classic printing of CSyntax
-- and by various internal dumps of ISyntax/ASyntax
instance PPrint RulePragma where
    pPrint d p RPfireWhenEnabled = text "{-# ASSERT fire when enabled #-}"
    pPrint d p RPnoImplicitConditions =
        text "{-# ASSERT no implicit conditions #-}"
    pPrint d p RPcanScheduleFirst =
        text "{-# ASSERT can schedule first #-}"
    pPrint d p RPaggressiveImplicitConditions =
        text "{-# aggressive_implicit_conditions #-}"
    pPrint d p RPconservativeImplicitConditions =
        text "{-# conservative_implicit_conditions #-}"
    pPrint d p RPnoWarn =
        text "{-# no_warn #-}"
    pPrint d p RPwarnAllConflicts =
        text "{-# warn_all_conflicts #-}"
    pPrint d p RPclockCrossingRule =
        text "{-# clock-crossing rule #-}"
    pPrint d p (RPdoc comment) =
        text ("{-# doc = " ++ doubleQuote comment ++ " #-}")
    pPrint d p RPhide =
        text ("{-# hide #-}")

-- this is used for reporting a failure of a rule assertion
-- (only the first two are assertions, perhaps the data structures
-- should reflect this?)
getRulePragmaName :: RulePragma -> String
getRulePragmaName RPfireWhenEnabled = "fire_when_enabled"
getRulePragmaName RPnoImplicitConditions = "no_implicit_conditions"
getRulePragmaName RPaggressiveImplicitConditions =
                      "aggressive_implicit_conditions"
getRulePragmaName RPconservativeImplicitConditions =
                      "conservative_implicit_conditions"
getRulePragmaName RPnoWarn = "no_warn"
getRulePragmaName RPwarnAllConflicts = "warn_all_conflicts"
getRulePragmaName RPcanScheduleFirst = "can_schedule_first"
getRulePragmaName RPclockCrossingRule = "clock_crossing_rule"
getRulePragmaName (RPdoc {}) = "doc"
getRulePragmaName RPhide     = "hide"

instance NFData RulePragma where
    rnf x = seq x ()


-- ========================================================================
-- SchedulePragma
--

data SchedulePragma id_t
    = SPUrgency [id_t]
    | SPExecutionOrder [id_t]
    | SPMutuallyExclusive [[id_t]]
    | SPConflictFree [[id_t]]
    | SPPreempt [id_t] [id_t]
    | SPSchedule (MethodConflictInfo id_t)
      deriving (Show, Eq, Ord, Generic.Data, Generic.Typeable)

type CSchedulePragma = SchedulePragma Longname
type ISchedulePragma = SchedulePragma Id
type ASchedulePragma = SchedulePragma Id



instance (PPrint t, Ord t) => PPrint (SchedulePragma t) where
    pPrint d p (SPUrgency ids) =
        text "{-# ASSERT descending urgency: " <+>
            pPrint d p ids <+> text "#-}"
    pPrint d p (SPExecutionOrder ids) =
        text "{-# ASSERT execution order: " <+>
            pPrint d p ids <+> text "#-}"
    pPrint d p (SPMutuallyExclusive idss) =
        text "{-# ASSERT mutually exclusive: " <+>
            pPrint d p idss <+> text "#-}"
    pPrint d p (SPConflictFree idss) =
        text "{-# ASSERT conflict-free: " <+>
            pPrint d p idss <+> text "#-}"
    pPrint d p (SPPreempt ids1 ids2) =
        text "{-# ASSERT preempt: " <+>
            pPrint d p ids1 <+> pPrint d p ids2 <+> text "#-}"
    pPrint d p (SPSchedule s) =
        text "{-# ASSERT schedule: " <+>
            pPrint d p s <+>  text "#-}"

-- instance PVPrint ?

instance (NFData t) => NFData (SchedulePragma t) where
    rnf (SPUrgency ids)       = rnf ids
    rnf (SPExecutionOrder ids) = rnf ids
    rnf (SPMutuallyExclusive idss) = rnf idss
    rnf (SPConflictFree idss) = rnf idss
    rnf (SPPreempt ids1 ids2) = rnf2 ids1 ids2
    rnf (SPSchedule s)        = rnf s

-- --------------------

longnameToId :: Longname -> Id
longnameToId ln = foldr1 mkUSId ln

-- Can be used to convert CSchedulePragma to ISchedulePragma,
-- or to map a function over the Ids of a list of pragmas
mapSPIds :: (t1 -> t2) -> [SchedulePragma t1] -> [SchedulePragma t2]
mapSPIds f sps =
    let mapOneSP (SPUrgency ids)       = SPUrgency (map f ids)
        mapOneSP (SPExecutionOrder ids) = SPExecutionOrder (map f ids)
        mapOneSP (SPMutuallyExclusive idss) = SPMutuallyExclusive (map (map f) idss)
        mapOneSP (SPConflictFree idss) = SPConflictFree (map (map f) idss)
        mapOneSP (SPPreempt ids1 ids2) = SPPreempt (map f ids1) (map f ids2)
        mapOneSP (SPSchedule s)        = SPSchedule (mapMethodConflictInfo f s)
    in  map mapOneSP sps

-- --------------------

setpos :: Id -> Id -> Id
setpos id1 id2 = setIdPosition (getIdPosition id1) id2

-- --------------------

type SPIdMap = M.Map Id Id

substSchedPragmaIds :: SPIdMap -> [ISchedulePragma] -> [ISchedulePragma]
substSchedPragmaIds idmap sps =
    let
        -- preserve the position of the original Id
        -- (still point to the name that the user wrote in the source)
        substId id1 =
            case (M.lookup id1 idmap) of
                Just id2 -> setpos id1 id2
                Nothing  -> id1
    in
        mapSPIds substId sps

-- --------------------

type SPIdSplitMap = [(Id,[Id])]

splitSchedPragmaIds :: SPIdSplitMap -> [ASchedulePragma] -> [ASchedulePragma]
splitSchedPragmaIds idsplitmap sps =
    let
        splitId :: Id -> [Id]
        splitId id1 = case (lookup id1 idsplitmap) of
                          Just ids -> map (setpos id1) ids
                          Nothing  -> [id1]

        splitIdList ids =
            let joinFn :: [Id] -> [[Id]] -> [[Id]]
                joinFn xs ys = concatMap (\x -> map (\y -> (x:y)) ys) xs
            in  foldr joinFn [[]] (map splitId ids)

        splitSP (SPUrgency ids) = map SPUrgency (splitIdList ids)

        splitSP (SPExecutionOrder ids) = map SPExecutionOrder (splitIdList ids)

        splitSP (SPMutuallyExclusive idss) =
            [SPMutuallyExclusive (map (concatMap splitId) idss)]

        splitSP (SPConflictFree idss) =
            [SPConflictFree (map (concatMap splitId) idss)]

        splitSP (SPPreempt ids1 ids2) =
            -- Split preempt rules retain the same preempt relationship
            -- individually.
            [SPPreempt (concatMap splitId ids1) (concatMap splitId ids2)]

        splitSP (SPSchedule s) =
            -- Split scheudle rules conservatively have the same relationship as
            -- individually.
            [SPSchedule (concatMapMethodConflictInfo splitId s)]


    in
        concatMap splitSP sps

-- --------------------

removeSchedPragmaIds :: [Id] -> [ASchedulePragma] -> [ASchedulePragma]
removeSchedPragmaIds [] sps = sps
removeSchedPragmaIds ids sps =
    let
        f = (\x -> not (elem x ids))
        filterIds = filter f

        removeSP (SPUrgency xids) = SPUrgency (filterIds xids)
        removeSP (SPExecutionOrder xids) = SPExecutionOrder (filterIds xids)
        removeSP (SPMutuallyExclusive xidss) = SPMutuallyExclusive ((map filterIds) xidss)
        removeSP (SPConflictFree xidss) = SPConflictFree ((map filterIds) xidss)
        removeSP (SPPreempt ids1 ids2) =
            SPPreempt (filterIds ids1) (filterIds ids2)
        removeSP (SPSchedule s) = SPSchedule (filterMethodConflictInfo f s)
    in
        map removeSP sps

-- --------------------

isRulePreempt :: Id -> [ASchedulePragma] -> Bool
isRulePreempt i sps =
    let
        handleOneSP (SPPreempt ids _) = elem i ids
        handleOneSP _ = False
    in
        any handleOneSP sps

-- --------------------

extractSchedPragmaIds :: (Ord id_t) =>  [SchedulePragma id_t] -> [id_t]
extractSchedPragmaIds sps =
    let
        extractSP (SPUrgency ids) = ids
        extractSP (SPExecutionOrder ids) = ids
        extractSP (SPMutuallyExclusive idss) = concat idss
        extractSP (SPConflictFree idss) = concat idss
        extractSP (SPPreempt ids1 ids2) = ids1 ++ ids2
        extractSP (SPSchedule s) = (extractFromMethodConflictInfo s)
    in
        concatMap extractSP sps

-- ========================================================================


isAlwaysEn :: [PProp] -> Id -> Bool
isAlwaysEn [] i = False
isAlwaysEn ((PPalwaysEnabled []):pps) i = True -- always_enabled for whole module (backwards compatible)
isAlwaysEn ((PPalwaysEnabled is):pps) i =
 if i `elem` (map flattenUSId is)
   then True
   else isAlwaysEn pps i
isAlwaysEn (pp:pps) i = isAlwaysEn pps i

-- Given RDY_nm, return if nm is in the list for always_ready
-- NOTE: always_enabled implies always_ready
isAlwaysRdy :: [PProp] -> Id -> Bool
isAlwaysRdy [] i = False
isAlwaysRdy ((PPalwaysReady []):pps) i = isRdyId i -- always_ready for whole module (backwards compatible)
isAlwaysRdy ((PPalwaysEnabled []):pps) i = isRdyId i -- always_enabled for module (backwards compatible)
isAlwaysRdy ((PPalwaysReady is):pps) i = -- traces( "isar: " ++ ppReadable i ++ ":" ++ ppReadable  (map (mkRdyId . flattenUSId) is)) $
 if i `elem` (map (mkRdyId . flattenUSId) is)
   then True
   else isAlwaysRdy pps i
isAlwaysRdy ((PPalwaysEnabled is):pps) i =
 if i `elem` (map (mkRdyId . flattenUSId) is)
   then True
   else isAlwaysRdy pps i
isAlwaysRdy (pp:pps) i = isAlwaysRdy pps i


-- NOTE: always_enabled implies enabled_when_ready
isEnWhenRdy :: [PProp] -> Id -> Bool
isEnWhenRdy [] i = False
isEnWhenRdy ((PPenabledWhenReady []):pps) i = True -- enabled_when_ready for whole module
isEnWhenRdy ((PPalwaysEnabled []):pps) i = True
isEnWhenRdy ((PPenabledWhenReady is):pps) i =
 if i `elem` (map flattenUSId is)
   then True
   else isEnWhenRdy pps i
isEnWhenRdy ((PPalwaysEnabled is):pps) i =
 if i `elem` (map flattenUSId is)
   then True
   else isEnWhenRdy pps i
isEnWhenRdy (pp:pps) i = isEnWhenRdy pps i || isAlwaysEn pps i --always_enabled implies enabled_when_ready


-- ========================================================================

-- the attribute "gate_all_clocks" is implemented by an empty list
gateAllClocks :: [PProp] -> Bool
gateAllClocks pps = elem (PPgate_input_clocks []) pps

-- An input clock is gated if all input clocks are gated
-- (gate_all_clocks with an empty list), or if it is explicitly
-- named in gate_all_clocks, or if there is a non-empty
-- clock_gate attribute for it.  However, if it is gated
-- using "gate_all_clocks", it can still be marked ungated
-- by attribute for it.
isGatedInputClk :: [PProp] -> Id -> Bool
isGatedInputClk pps i =
  let in_list          = or (map is_listed pps)
      on_port          = or (map is_port pps)
      inhigh_or_unused = or (map is_no_port pps)
  in  in_list || on_port || (gateAllClocks pps && (not inhigh_or_unused))
  where is_listed  (PPgate_input_clocks is) = i `elem` is
        is_listed  _                        = False
        is_port    (PPclock_gate ps)        = i `elem` (map fst ps)
        is_port    _                        = False
        is_no_port (PPgate_inhigh is)       = i `elem` is
        is_no_port (PPgate_unused is)       = i `elem` is
        is_no_port _                        = False

isGatedDefaultClk :: [PProp] -> Bool
isGatedDefaultClk pps = isGatedInputClk pps idDefaultClock

hasInhighAttribute :: [PProp] -> Id -> Bool
hasInhighAttribute pps i
  | i == idDefaultClock = hasInhighAttribute pps emptyId
  | otherwise = or [ i `elem` is | PPgate_inhigh is <- pps ]

hasUnusedAttribute :: [PProp] -> Id -> Bool
hasUnusedAttribute pps i
  | i == idDefaultClock = hasUnusedAttribute pps emptyId
  | otherwise = or [ i `elem` is | PPgate_unused is <- pps ]

hasDefaultClk :: [PProp] -> Bool
hasDefaultClk pps = not (any removesDefClk pps)
  where removesDefClk (PPclock_osc ps) = (idDefaultClock,"") `elem` ps
        removesDefClk _                = False

hasDefaultRst :: [PProp] -> Bool
hasDefaultRst pps = not (any removesDefRst pps)
  where removesDefRst (PPreset_port ps) = (idDefaultReset,"") `elem` ps
        removesDefRst _                 = False

hasRuleHide :: [RulePragma] -> Bool
hasRuleHide []         = False
hasRuleHide (RPhide:_) = True
hasRuleHide (_:rest)   = hasRuleHide rest

-- =========================================================================
-- Interface definition pragmas
-- These pragma are associated with interfaces and/or the fields within the interface
-- The first arg is the field name which the attribute is associated with
data IfcPragma
    =  PIArgNames     [Id]      -- arg names used as dummy names (XX this can be removed?)
    | PIPrefixStr     String    -- Method or interface
    | PIResultName    String    -- name for the result of the method AV or value methods
    | PIRdySignalName String    -- name for the ready signal on this method
    | PIEnSignalName  String    -- name for the enable signal
    | PIAlwaysRdy               -- ifc or methods tagged as always ready
    | PIAlwaysEnabled           -- ifc or methods tagged as always enabled
      deriving (Show, Ord, Eq, Generic.Data, Generic.Typeable)

-- type PragmaPair = (Id,String)

instance PPrint IfcPragma where
    pPrint d _ (PIArgNames ids)       = text "arg_names ="   <+>
                                        brackets ( (sepList (map (ppVarId d) ids) comma) )
    pPrint d _ (PIPrefixStr flds)     = text "prefixs ="       <+> doubleQuotes (text flds)
    pPrint d _ (PIRdySignalName flds) = text "ready ="        <+> doubleQuotes (text flds)
    pPrint d _ (PIEnSignalName flds)  = text "enable ="       <+> doubleQuotes (text flds)
    pPrint d _ (PIResultName flds)    = text "result ="       <+> doubleQuotes (text flds)
    pPrint d _ (PIAlwaysRdy )         = text "always_ready "
    pPrint d _ (PIAlwaysEnabled )     = text "always_enabled "

instance PVPrint  IfcPragma where
    pvPrint d _ (PIArgNames ids)       = text "ports ="   <+>
                                         brackets ( (sepList (map (doubleQuotes . (ppVarId d)) ids) comma) )
    pvPrint d _ (PIPrefixStr flds)     = text "prefix ="       <+> doubleQuotes (text flds)
    pvPrint d _ (PIRdySignalName flds) = text "ready ="        <+> doubleQuotes (text flds)
    pvPrint d _ (PIEnSignalName flds)  = text "enable ="       <+> doubleQuotes (text flds)
    pvPrint d _ (PIResultName flds)    = text "result ="       <+> doubleQuotes (text flds)
    pvPrint d _ (PIAlwaysRdy )         = text "always_ready "
    pvPrint d _ (PIAlwaysEnabled )     = text "always_enabled "


instance NFData IfcPragma where
    rnf  (PIArgNames ids)       = rnf ids
    rnf  (PIPrefixStr flds)     = rnf flds
    rnf  (PIRdySignalName flds) = rnf flds
    rnf  (PIEnSignalName flds)  = rnf flds
    rnf  (PIResultName flds)    = rnf flds
    rnf  (PIAlwaysRdy )         = ()
    rnf  (PIAlwaysEnabled )     = ()

-- a means to get a print string from attribute
getIfcPName :: IfcPragma -> String
getIfcPName (PIArgNames fs)       = "port"
getIfcPName (PIPrefixStr pps)     = "prefix"
getIfcPName (PIRdySignalName pps) = "ready"
getIfcPName (PIEnSignalName pps)  = "enable"
getIfcPName (PIResultName pps)    = "result"
getIfcPName (PIAlwaysRdy )        = "always_ready"
getIfcPName (PIAlwaysEnabled )    = "always_enabled"



-- an empty list to keep typing and searching happier
noIfcPragmas :: [IfcPragma]
noIfcPragmas = []


-- convenience function -- extract out PIArgNames ids.
filterIArgNames :: [IfcPragma] -> [Id]
filterIArgNames prags = concatMap getArgNames prags
    where getArgNames :: IfcPragma -> [Id]
          getArgNames (PIArgNames names) = names
          getArgNames _                  = []

filterPrintIfcArgs :: [IfcPragma] -> [IfcPragma]
filterPrintIfcArgs prags = filter isPrintArg prags
    where isPrintArg (PIArgNames names) = False
          isPrintArg x                  = True


isAlwaysReadyIfc :: [IfcPragma] -> Bool
isAlwaysReadyIfc prags = any  isAR prags
    where isAR :: IfcPragma -> Bool
          isAR (PIAlwaysRdy ) = True
          isAR (PIAlwaysEnabled) = True -- AE implies AR
          isAR _              = False

isAlwaysEnabledIfc :: [IfcPragma] -> Bool
isAlwaysEnabledIfc prags = any  isAR prags
    where isAR :: IfcPragma -> Bool
          isAR (PIAlwaysEnabled ) = True
          isAR _                  = False

getARAEPragmas :: [IfcPragma] -> [IfcPragma]
getARAEPragmas prags = filter isARAE prags
    where isARAE (PIAlwaysRdy )     = True
          isARAE (PIAlwaysEnabled ) = True
          isARAE _                  = False


-- and may have different string
-- return the names of any dupliplicate pragma
extractDuplicatePragmas :: [IfcPragma] -> [String]
extractDuplicatePragmas prags = findDup (sort names )
    where names = map getIfcPName prags


lookupReadyIfcPragma :: [IfcPragma] -> Maybe String
lookupReadyIfcPragma iprags = listToMaybe allflds
    where allflds = [ flds | (PIRdySignalName flds)  <- iprags]

lookupPrefixIfcPragma :: [IfcPragma]  -> Maybe String
lookupPrefixIfcPragma iprags = listToMaybe allflds
    where allflds = [ flds | (PIPrefixStr flds)  <- iprags]

lookupRdySignalIfcPragma :: [IfcPragma] -> Maybe String
lookupRdySignalIfcPragma iprags = listToMaybe allflds
    where allflds = [ flds | (PIRdySignalName flds)  <- iprags]

lookupEnSignalIfcPragma :: [IfcPragma] -> Maybe String
lookupEnSignalIfcPragma iprags = listToMaybe allflds
    where allflds = [ flds | (PIEnSignalName flds)  <- iprags]

lookupResultIfcPragma :: [IfcPragma] -> Maybe String
lookupResultIfcPragma iprags = listToMaybe allflds
    where allflds = [ flds | (PIResultName flds)  <- iprags]


-- prefix, Result, ready, enable, args, AR, AE
-- XXX since these are all generated, we can add a new pragma to store these directly thus avoiding the lookup
getMethodPragmaInfo :: [IfcPragma] -> (Maybe String, Maybe String, Maybe String, Maybe String, [Id], Bool, Bool)
getMethodPragmaInfo prags = foldl getFields (Nothing,Nothing, Nothing,Nothing,[],False,False)  prags
    where getFields :: (Maybe String, Maybe String, Maybe String, Maybe String, [Id], Bool, Bool) -> IfcPragma -> (Maybe String, Maybe String, Maybe String, Maybe String, [Id], Bool, Bool)
          getFields (mprefix,mres, mready, menable, [], ar, ae)  (PIArgNames fis)      = (mprefix,mres, mready, menable, fis, ar, ae)
          getFields (Nothing,mres, mready, menable, args, ar, ae) (PIPrefixStr s)      = (Just s,mres, mready, menable, args, ar, ae)
          getFields (mprefix,Nothing, mready, menable, args, ar, ae) (PIResultName s ) = (mprefix,Just s, mready, menable, args, ar, ae)
          getFields (mprefix,mres, Nothing, menable, args, ar, ae) (PIRdySignalName s) = (mprefix,mres, Just s, menable, args, ar, ae)
          getFields (mprefix,mres, mready, Nothing, args, ar, ae) (PIEnSignalName s)   = (mprefix,mres, mready, Just s, args, ar, ae)
          getFields (mprefix,mres, mready, menable, args, False, ae) (PIAlwaysRdy)     = (mprefix,mres, mready, menable, args, True, ae)
          getFields (mprefix,mres, mready, menable, args, ar, False) (PIAlwaysEnabled) = (mprefix,mres, mready, menable, args, ar, True)
          getFields x@(mprefix,mres, mready, menable, args, ar, ae) y                  = internalError( "getMethodPragmaInfo: " ++ show (y))


-- From a set of ifc pragmas, determine:
-- prefix
getClockPragmaInfo :: [IfcPragma] -> (Maybe String)
getClockPragmaInfo prags = foldl getFn (Nothing) prags
  where getFn (Nothing) (PIPrefixStr s) = (Just s)
        getFn x@(mprefix) y =
            internalError("getClockPragmaInfo: " ++ show (x, y))

-- From a set of ifc pragmas, determine:
-- prefix
getResetPragmaInfo :: [IfcPragma] -> (Maybe String)
getResetPragmaInfo prags = foldl getFn (Nothing) prags
  where getFn (Nothing) (PIPrefixStr s) = (Just s)
        getFn x@(mprefix) y =
            internalError("getResetPragmaInfo: " ++ show (x, y))

-- From a set of ifc pragmas, determine:
-- prefix
getInoutPragmaInfo :: [IfcPragma] -> (Maybe String)
getInoutPragmaInfo prags = foldl getFn (Nothing) prags
  where getFn (Nothing) (PIPrefixStr s) = (Just s)
        getFn x@(mprefix) y =
            internalError("getInoutPragmaInfo: " ++ show (x, y))


-- --------------------


isParamModArg :: [PProp] -> Id -> Bool
isParamModArg [] i = False
isParamModArg (PPparam ids:pps) i =
    if (i `elem` ids)
    then True
    else isParamModArg pps i
isParamModArg (_:pps) i = isParamModArg pps i

isPPparam :: PProp -> Bool
isPPparam (PPparam {}) = True
isPPparam _ = False

filterPPparam :: Pragma -> Maybe Pragma
filterPPparam (Pproperties i pprops) =
    let pprops' = filter (not . isPPparam) pprops
    in  if (null pprops')
        then Nothing
        else Just (Pproperties i pprops')
filterPPparam p@(Pnoinline {}) = Just p


-- ========================================================================
-- DefProp (module def pragmas)

data DefProp
  = DefP_Rule Id   -- for method predicates
  | DefP_Method Id -- for method predicates
  | DefP_Instance Id  -- for method predicates
  | DefP_NoCSE -- indicate this def should never be used for CSE
  deriving (Eq, Ord, Show, Generic.Data, Generic.Typeable)

instance PPrint DefProp where
  pPrint _d _i = text . show

instance NFData DefProp where
  rnf (DefP_Rule x) = rnf x
  rnf (DefP_Instance x) = rnf x
  rnf (DefP_Method x) = rnf x
  rnf DefP_NoCSE = ()

-- --------------------

defPropsHasNoCSE :: [DefProp] -> Bool
defPropsHasNoCSE = elem DefP_NoCSE

-- ========================================================================
