module ABin (id_ABin,
             ABin(..),
             ABinModInfo(..),
             ABinForeignFuncInfo(..),
             ABinModSchedErrInfo(..),
             ABinEitherModInfo,
             abemi_path,
             abemi_src_name,
             abemi_apkg,
             abemi_pps,
             abemi_oqt,
             abemi_flags,
             abemi_method_uses_map,
             abemi_warnings,
             abemi_schedule,
             abemi_rule_relation_db
             ) where

import Data.Maybe(isNothing)
import PPrint
import Id(Id)
import Position(Position)
import Pragma(PProp)
import CType(CQType)
import ASyntax
import AScheduleInfo
import AUses(MethodUsesMap)
import ADumpScheduleInfo(MethodDumpInfo)
import VModInfo(VPathInfo)
import ForeignFunctions(ForeignFunction(..))
import Flags(Flags(..))
import Verilog(VProgram)


-- ===============

id_ABin = " $Id: $"

-- ===============

-- ab_version = BSC version which compiled the .ba
data ABin = ABinMod { ab_modinfo :: ABinModInfo,
                      ab_version :: String }
          | ABinForeignFunc { ab_ffuncinfo :: ABinForeignFuncInfo,
                              ab_version :: String }
          | ABinModSchedErr { ab_modschederr_info :: ABinModSchedErrInfo,
                              ab_version :: String }

data ABinModInfo =
    ABinModInfo {
        -- location of the BSV file from which this module was generated
        -- (the "prefix" from "genModule")
        abmi_path :: String,
        -- the name of the BSV package which defined this module
        abmi_src_name :: String,
	-- time when BSC was called to compile the .ba
	--abmi_time :: ClockTime,
	abmi_apkg :: APackage,
	abmi_aschedinfo :: AScheduleInfo,
	-- if this can be used prior to generating abin,
	-- or put into APackage, then it's not needed here:
	abmi_pps :: [PProp],
	-- original type of the module
	-- (this could go in APackage;
	-- like pps, this is taken from GenWrap's WrapInfo)
	-- (for now, the list of preds is empty, so CType would do)
	abmi_oqt         :: CQType,
	abmi_method_dump :: MethodDumpInfo,
	abmi_pathinfo :: VPathInfo,
	abmi_flags       :: Flags,
        -- the generated Verilog
        abmi_vprogram :: Maybe VProgram
    }

data ABinForeignFuncInfo =
    ABinForeignFuncInfo {
        abffi_src_name :: Id,
        abffi_foreign_func :: ForeignFunction
    }

data ABinModSchedErrInfo =
    ABinModSchedErrInfo {
        -- location of the BSV file from which this module was generated
        -- (the "prefix" from "genModule")
        abmsei_path :: String,
        -- the name of the BSV package which defined this module
        abmsei_src_name :: String,
        -- the package prior to scheduling
	abmsei_apkg :: APackage,
        -- the available schedule info
	abmsei_aschederrinfo :: AScheduleErrInfo,
        -- pragmas
	abmsei_pps :: [PProp],
        -- original type of the module
	abmsei_oqt :: CQType,
        -- flags
	abmsei_flags :: Flags
    }

-- ---------------

instance PPrint ABin where
    pPrint d p (ABinMod abmi ver) =
	text "ABin Module" $+$
	nest 2 (text "version:" <+> text ver $+$
		pPrint d 0 abmi)

    pPrint d p (ABinForeignFunc abffi ver) =
	text "ABin Foreign Function" $+$
	nest 2 (text "version:" <+> text ver $+$
		pPrint d 0 abffi)

    pPrint d p (ABinModSchedErr abmsei ver) =
	text "ABin Module (Schedule Error)" $+$
	nest 2 (text "version:" <+> text ver $+$
		pPrint d 0 abmsei)



instance PPrint ABinModInfo where
    pPrint d p (ABinModInfo path srcName apkg aschedinfo pps oqt mi pathinfo flags vprog) =
	text "path:" <+> text path $+$
	text "package:" <+> text srcName $+$
	pPrint d 0 apkg $+$
	pPrint d 0 aschedinfo $+$
        text "pprop:" <+> pPrint d 0 pps $+$
        text "oqt:" <+> pPrint d 0 oqt $+$
	-- no dump of method info
	text "pathinfo:" <+> pPrint d 0 pathinfo $+$
        -- no dump of flags
        text "vprog:" <+> (if (isNothing vprog)
                           then text "Nothing"
                           else text "Just ...") -- no dump of contents


instance PPrint ABinForeignFuncInfo where
    pPrint d p (ABinForeignFuncInfo fid ff) =
	text "src name:" <+> pPrint d 0 fid $+$
	pPrint d 0 ff


instance PPrint ABinModSchedErrInfo where
    pPrint d p (ABinModSchedErrInfo path srcName apkg aschederrinfo pps oqt flags) =
	text "path:" <+> text path $+$
	text "package:" <+> text srcName $+$
	pPrint d 0 apkg $+$
	pPrint d 0 aschederrinfo $+$
        text "pprop:" <+> pPrint d 0 pps $+$
        text "oqt:" <+> pPrint d 0 oqt
        -- no dump of flags


-- ===============

-- module info can either be from a schedule error or successful compile
type ABinEitherModInfo = Either ABinModSchedErrInfo ABinModInfo

-- Convenience functions for getting the common data from either module info

abemi_path :: ABinEitherModInfo -> String
abemi_path m = case m of
                 Left l  -> abmsei_path l
                 Right r -> abmi_path r

abemi_src_name :: ABinEitherModInfo -> String
abemi_src_name m = case m of
                     Left l  -> abmsei_src_name l
                     Right r -> abmi_src_name r

abemi_apkg :: ABinEitherModInfo -> APackage
abemi_apkg m = case m of
                 Left l  -> abmsei_apkg l
                 Right r -> abmi_apkg r

abemi_pps :: ABinEitherModInfo -> [PProp]
abemi_pps m = case m of
                Left l  -> abmsei_pps l
                Right r -> abmi_pps r

abemi_oqt :: ABinEitherModInfo -> CQType
abemi_oqt m = case m of
                Left l  -> abmsei_oqt l
                Right r -> abmi_oqt r

abemi_flags :: ABinEitherModInfo -> Flags
abemi_flags m = case m of
                  Left l  -> abmsei_flags l
                  Right r -> abmi_flags r

-- common schedule information

abemi_method_uses_map :: ABinEitherModInfo -> MethodUsesMap
abemi_method_uses_map m =
    case m of
      Left l  -> asei_method_uses_map (abmsei_aschederrinfo l)
      Right r -> asi_method_uses_map (abmi_aschedinfo r)

abemi_warnings :: ABinEitherModInfo -> [(Position, String, String)]
abemi_warnings m =
    case m of
      Left l  -> asei_warnings (abmsei_aschederrinfo l)
      Right r -> asi_warnings (abmi_aschedinfo r)

-- schedule information that may be missing

abemi_schedule :: ABinEitherModInfo -> Maybe ASchedule
abemi_schedule m =
    case m of
      Left l  -> asei_schedule (abmsei_aschederrinfo l)
      Right r -> Just (asi_schedule (abmi_aschedinfo r))

abemi_rule_relation_db :: ABinEitherModInfo -> Maybe RuleRelationDB
abemi_rule_relation_db m =
    case m of
      Left l  -> asei_rule_relation_db (abmsei_aschederrinfo l)
      Right r -> Just (asi_rule_relation_db (abmi_aschedinfo r))

-- ===============

