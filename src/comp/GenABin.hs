{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Werror -fwarn-incomplete-patterns #-}
module GenABin(genABinFile, readABinFile) where

import Error(internalError, ErrMsg(..), ErrorHandle, bsErrorUnsafe)
import Position

--import Time(ClockTime)
import Backend
import Wires
import ASyntax
import AUses(MethodId(..), UniqueUse(..), UseCond(..), RuleUses(..), ucTrue)
import AScheduleInfo
import ADumpScheduleInfo(RuleConflictType)
import ForeignFunctions
import Flags(Flags(..), DumpFlag(..), ResourceFlag(..), SATFlag(..),
             MsgListFlag(..), Verbosity(..))
import InstNodes(InstNode(..))
import Verilog

import ABin
import BinData
import FileIOUtil(writeBinaryFileCatch)

import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.ByteString as B

-- import Debug.Trace

-- .ba file tag -- change this whenever the .ba format changes
-- See also GenBin.header
header :: [Byte]
header = B.unpack $ TE.encodeUtf8 $ T.pack "bsc-ba-20230831-1"

genABinFile :: ErrorHandle -> String -> ABin -> IO ()
genABinFile errh fn abin =
    writeBinaryFileCatch errh fn (header ++ encode abin)

readABinFile :: ErrorHandle -> String -> [Byte] -> (ABin, String)
readABinFile errh nm s =
    if take (length header) s == header
    then (decode (drop (length header) s), "")
    --then (decodeWithHash (drop (length header) s))
    else bsErrorUnsafe errh [(noPosition, EBinFileVerMismatch nm)]

-- ----------
-- Bin ABin

instance Bin ABin where
  writeBytes (ABinForeignFunc ffinfo version) =
         section "ABinForeignFunc" $
         do -- tag which kind of module
            putI 0
            toBin version
            -- output the foreign function info
            toBin (abffi_src_name ffinfo)
            toBin (abffi_foreign_func ffinfo)
  writeBytes (ABinMod modinfo version) =
         section "ABinMod" $
         do -- tag which kind of module
            putI 1
            toBin version
            -- output module info
            toBin (abmi_path modinfo)
            toBin (abmi_src_name modinfo)
            --toBin (abmi_time modinfo)
            toBin (abmi_apkg modinfo)
            toBin (abmi_aschedinfo modinfo)
            toBin (abmi_pps modinfo)
            toBin (abmi_oqt modinfo)
            toBin (abmi_method_dump modinfo)
            toBin (abmi_pathinfo modinfo)
            toBin (abmi_flags modinfo)
            toBin (abmi_vprogram modinfo)
  writeBytes (ABinModSchedErr modinfo version) =
         section "ABinModSchedErr" $
         do -- tag which kind of module
            putI 2
            toBin version
            -- output module info
            toBin (abmsei_path modinfo)
            toBin (abmsei_src_name modinfo)
            toBin (abmsei_apkg modinfo)
            toBin (abmsei_aschederrinfo modinfo)
            toBin (abmsei_pps modinfo)
            toBin (abmsei_oqt modinfo)
            toBin (abmsei_flags modinfo)
  readBytes = do tag <- getI
                 version <- fromBin
                 case (tag) of
                   0 -> do src_name <- fromBin
                           foreign_func <- fromBin
                           let ffi = ABinForeignFuncInfo src_name foreign_func
                           return (ABinForeignFunc ffi version)
                   1 -> do path <- fromBin
                           srcName <- fromBin
                           --time <- fromBin
                           apkg <- fromBin
                           asched <- fromBin
                           pps <- fromBin
                           oqt <- fromBin
                           mi <- fromBin
                           pathinfo <- fromBin
                           flags <- fromBin
                           vprog <- fromBin
                           let modinfo =
                                   ABinModInfo path srcName apkg asched pps
                                               oqt mi pathinfo flags vprog
                           return (ABinMod modinfo version)
                   2 -> do path <- fromBin
                           srcName <- fromBin
                           apkg <- fromBin
                           aschederr <- fromBin
                           pps <- fromBin
                           oqt <- fromBin
                           flags <- fromBin
                           let modinfo =
                                   ABinModSchedErrInfo path srcName apkg
                                                       aschederr pps oqt flags
                           return (ABinModSchedErr modinfo version)
                   n -> internalError ("GenABin.Bin(ABin): tag = " ++ show n)

-- ----------
-- Bin APackage

instance Bin APackage where
    writeBytes (APackage {
               apkg_name = mi,
               apkg_is_wrapped = is_wrap,
               apkg_backend = be,
               apkg_size_params = ps,
               apkg_inputs = inps,
               apkg_clock_domains = clks,
               apkg_external_wires = wi,
               apkg_external_wire_types = wpt,
               apkg_reset_list = rsts,
               apkg_state_instances = avis,
               apkg_local_defs = ds,
               apkg_rules = rs,
               apkg_schedule_pragmas = asps,
               apkg_interface = aifcs,
               apkg_inst_comments = ics,
               apkg_inst_tree = inst_tree,
               apkg_proof_obligations = pos
           }) = if (null pos)
                then section "APackage" $
                     do toBin mi
                        toBin is_wrap
                        toBin be
                        toBin ps
                        toBin inps
                        toBin clks
                        toBin wi
                        toBin wpt
                        toBin rsts
                        toBin avis
                        toBin ds
                        toBin rs
                        toBin asps
                        toBin aifcs
                        toBin inst_tree
                        toBin ics
                        -- proof obligations not written
                else internalError $ "GenABin.Bin(APackage).readBytes: non-empty proof obligations"
    readBytes = do mi <- fromBin
                   is_wrap <- fromBin
                   be <- fromBin
                   ps <- fromBin
                   inps <- fromBin
                   clks <- fromBin
                   wi <- fromBin
                   wpt <- fromBin
                   rsts <- fromBin
                   avis <- fromBin
                   ds <- fromBin
                   rs <- fromBin
                   asps <- fromBin
                   aifcs <- fromBin
                   inst_tree <- fromBin
                   ics <- fromBin
                   return (APackage {
                             apkg_name = mi,
                             apkg_is_wrapped = is_wrap,
                             apkg_backend = be,
                             apkg_size_params = ps,
                             apkg_inputs = inps,
                             apkg_clock_domains = clks,
                             apkg_external_wires = wi,
                             apkg_external_wire_types = wpt,
                             apkg_reset_list = rsts,
                             apkg_state_instances = avis,
                             apkg_local_defs = ds,
                             apkg_rules = rs,
                             apkg_schedule_pragmas = asps,
                             apkg_interface = aifcs,
                             apkg_inst_comments = ics,
                             apkg_inst_tree = inst_tree,
                             apkg_proof_obligations = []
                                    })

-- ----------
-- Bin Backend

instance Bin Backend where
    writeBytes (Bluesim) = putI 0
    writeBytes (Verilog) = putI 1
    readBytes = do
        i <- getI
        case i of
         0 -> return Bluesim
         1 -> return Verilog
         n -> internalError $ "GenABin.Bin(Backend).readBytes: " ++ show n

-- ----------
-- Bin AAbstractInput

instance Bin AAbstractInput where
    writeBytes (AAI_Port p) = do putI 0; toBin p
    writeBytes (AAI_Clock osc mgate) = do putI 1; toBin osc; toBin mgate
    writeBytes (AAI_Reset r) = do putI 2; toBin r
    writeBytes (AAI_Inout r n) = do putI 3; toBin r; toBin n
    readBytes = do
        i <- getI
        case i of
         0 -> do p <- fromBin; return (AAI_Port p)
         1 -> do osc <- fromBin; mgate <- fromBin; return (AAI_Clock osc mgate)
         2 -> do r <- fromBin; return (AAI_Reset r)
         3 -> do r <- fromBin; n <- fromBin; return (AAI_Inout r n)
         n -> internalError $ "GenABin.Bin(AAbstractInfo).readBytes: " ++ show n

-- ----------
-- Bin ForeignFunction

instance Bin ForeignType where
    writeBytes Void        = do putI 0
    writeBytes (Narrow n)  = do putI 1; toBin n
    writeBytes (Wide n)    = do putI 2; toBin n
    writeBytes Polymorphic = do putI 3
    writeBytes StringPtr   = do putI 4
    readBytes = do i <- getI
                   case i of
                     0 -> return Void
                     1 -> do n <- fromBin; return (Narrow n)
                     2 -> do n <- fromBin; return (Wide n)
                     3 -> return Polymorphic
                     4 -> return StringPtr
                     n -> internalError $ "GenABin.Bin(ForeignType).readBytes: " ++ show n

instance Bin ForeignFunction where
    writeBytes (FF name rt args) = do toBin name; toBin rt; toBin args
    readBytes = do name <- fromBin
                   rt   <- fromBin
                   args <- fromBin
                   return (FF name rt args)

-- ----------
-- Bin AVInst

instance Bin AVInst where
    writeBytes (AVInst i t ui ms pts vmi ias iarr) =
        section "AVInst" $
        do toBin i; toBin t; toBin ui; toBin ms; toBin pts;
           toBin vmi; toBin ias; toBin iarr
    readBytes = do i <- fromBin; t <- fromBin; ui <- fromBin; ms <- fromBin;
                   pts <- fromBin; vmi <- fromBin; ias <- fromBin; iarr <- fromBin;
                   return (AVInst i t ui ms pts vmi ias iarr)

-- ----------
-- Bin ARule

instance Bin ARule where
    writeBytes (ARule i ps d wps pred act asmps mp) =
        section "ARule" $
        do toBin i; toBin ps; toBin d; toBin wps; toBin pred; toBin act;
           toBin asmps; toBin mp
    readBytes =
        do i <- fromBin; ps <- fromBin; d <- fromBin; wps <- fromBin;
           pred <- fromBin; act <- fromBin; asmps <- fromBin; mp <- fromBin;
           return (ARule i ps d wps pred act asmps mp)

instance Bin AAssumption where
    writeBytes (AAssumption p as) = do toBin p; toBin as
    readBytes = do p <- fromBin; as <- fromBin;
                   return (AAssumption p as)

instance Bin AAction where
    writeBytes (ACall i m as) = do putI 0; toBin i; toBin m; toBin as
    writeBytes (AFCall i f isC as isA) =
        do putI 1; toBin i; toBin f; toBin isC; toBin as; toBin isA
    writeBytes (ATaskAction i f isC c as tmp ty isA) =
        do putI 2; toBin i; toBin f; toBin isC; toBin c; toBin as;
           toBin tmp; toBin ty; toBin isA
    readBytes =
        do i <- getI
           case i of
            0 -> do i <- fromBin; m <- fromBin; as <- fromBin;
                    return (ACall i m as)
            1 -> do i <- fromBin; f <- fromBin; isC <- fromBin; as <- fromBin;
                    isA <- fromBin; return (AFCall i f isC as isA)
            2 -> do i <- fromBin; f <- fromBin; isC <- fromBin; c <- fromBin;
                    as <- fromBin; tmp <- fromBin; ty <- fromBin;
                    isA <- fromBin;
                    return (ATaskAction i f isC c as tmp ty isA)
            n -> internalError $ "GenABin.Bin(AAction).readBytes: " ++ show n

instance Bin WireProps where
    writeBytes (WireProps cd rs) = do toBin cd; toBin rs
    readBytes = do cd <- fromBin; rs <- fromBin; return (WireProps cd rs)

-- ----------
-- Bin AIFace

instance Bin AIFace where
    writeBytes (AIDef name is ps pred val vfi asmps) =
        do putI 0; toBin name; toBin is; toBin ps; toBin pred; toBin val;
           toBin vfi; toBin asmps
    writeBytes (AIAction is ps pred name body vfi) =
        do putI 1; toBin is; toBin ps; toBin pred; toBin name; toBin body;
           toBin vfi
    writeBytes (AIActionValue is ps pred name body val vfi) =
        do putI 2; toBin is; toBin ps; toBin pred; toBin name; toBin body;
           toBin val; toBin vfi
    writeBytes (AIClock name clk vfi) =
        do putI 3; toBin name; toBin clk; toBin vfi
    writeBytes (AIReset name rst vfi) =
        do putI 4; toBin name; toBin rst; toBin vfi
    writeBytes (AIInout name iot vfi) =
        do putI 5; toBin name; toBin iot; toBin vfi
    readBytes =
        do i <- getI
           case i of
            0 -> do name <- fromBin; is <- fromBin; ps <- fromBin;
                    pred <- fromBin; val <- fromBin; vfi <- fromBin;
                    asmps <- fromBin;
                    return (AIDef name is ps pred val vfi asmps)
            1 -> do is <- fromBin; ps <- fromBin; pred <- fromBin;
                    name <- fromBin; body <- fromBin; vfi <- fromBin;
                    return (AIAction is ps pred name body vfi)
            2 -> do is <- fromBin; ps <- fromBin; pred <- fromBin;
                    name <- fromBin; body <- fromBin; val <- fromBin;
                    vfi <- fromBin;
                    return (AIActionValue is ps pred name body val vfi)
            3 -> do name <- fromBin; clk <- fromBin; vfi <- fromBin;
                    return (AIClock name clk vfi)
            4 -> do name <- fromBin; rst <- fromBin; vfi <- fromBin;
                    return (AIReset name rst vfi)
            5 -> do name <- fromBin; iot <- fromBin; vfi <- fromBin;
                    return (AIInout name iot vfi)
            n -> internalError $ "GenABin.Bin(AIFace).readBytes: " ++ show n

-- ----------
-- Bin AScheduleInfo

instance Bin AScheduleInfo where
    writeBytes (AScheduleInfo ws mumap rumap rat erdb sorder sch sgraph rrdb vsi) =
        section "AScheduleInfo" $
        do toBin ws; toBin mumap; toBin rumap; toBin rat; toBin erdb;
           toBin sorder; toBin sch; toBin sgraph; toBin rrdb; toBin vsi
    readBytes =
        do ws <- fromBin; mumap <- fromBin; rumap <- fromBin; rat <- fromBin;
           erdb <- fromBin; sorder <- fromBin; sch <- fromBin;
           sgraph <- fromBin; rrdb <- fromBin; vsi <- fromBin;
           return (AScheduleInfo ws mumap rumap rat erdb sorder sch sgraph rrdb vsi)

instance Bin AScheduleErrInfo where
    writeBytes (AScheduleErrInfo ws es mumap rumap rat erdb sorder sch sgraph rrdb vsi) =
        section "AScheduleErrInfo" $
        do toBin ws; toBin es; toBin mumap; toBin rumap; toBin rat; toBin erdb;
           toBin sorder; toBin sch; toBin sgraph; toBin rrdb; toBin vsi
    readBytes =
        do ws <- fromBin; es <- fromBin; mumap <- fromBin; rumap <- fromBin;
           rat <- fromBin; erdb <- fromBin; sorder <- fromBin; sch <- fromBin;
           sgraph <- fromBin; rrdb <- fromBin; vsi <- fromBin;
           return (AScheduleErrInfo ws es mumap rumap rat erdb sorder sch sgraph rrdb vsi)

instance Bin ASchedule where
    writeBytes (ASchedule ss order) = section "ASchedule" $ do toBin ss; toBin order
    readBytes = do ss <- fromBin; order <- fromBin; return (ASchedule ss order)

instance Bin AScheduler where
    writeBytes (ASchedEsposito cs) = toBin cs
    readBytes = do cs <- fromBin; return (ASchedEsposito cs)

-- for RAT
instance Bin MethodId where
    writeBytes (MethodId i m) = section "MethodId" $ do toBin i; toBin m
    readBytes = do i <- fromBin; m <- fromBin; return (MethodId i m)

-- for RAT
instance Bin UniqueUse where
    writeBytes (UUAction a) = section "UUAction" $ do putI 0; toBin a
    writeBytes (UUExpr e c) = section "UUExpr" $ do putI 1; toBin e; toBin c
    readBytes =
        do i <- getI
           case i of
            0 -> do a <- fromBin; return (UUAction a)
            1 -> do e <- fromBin; c <- fromBin; return (UUExpr e c)
            n -> internalError $ "GenABin.Bin(UniqueUse).readBytes: " ++ show n

-- XXX drop use conditions because of sharing issues
-- .ba file size explodes (may be better now with CSE of UseCond)
instance Bin UseCond where
    writeBytes _ = return ()
    readBytes = return ucTrue

instance Bin RuleUses where
    writeBytes (RuleUses pus rus wus) =
        section "RuleUses" $ do toBin pus; toBin rus; toBin wus
    readBytes = do pus <- fromBin; rus <- fromBin; wus <- fromBin
                   return (RuleUses pus rus wus)

instance Bin ExclusiveRulesDB where
    writeBytes erdb = section "ExclusiveRulesDB" $ toBin (erdbToList erdb)
    readBytes = do es <- fromBin; return (erdbFromList es)

instance Bin RuleRelationDB where
    writeBytes (RuleRelationDB dset cmap) =
        section "RuleRelationDB" $ do toBin (S.toList dset)
                                      toBin (M.toList cmap)
    readBytes = do dset_list <- fromBin
                   cmap_list <- fromBin
                   let dset = S.fromList dset_list
                       cmap = M.fromList cmap_list
                   return (RuleRelationDB dset cmap)

instance Bin RuleRelationInfo where
    writeBytes (RuleRelationInfo mCF mSC mRes mCycle mPragma mArb) =
        do toBin mCF; toBin mSC; toBin mRes; toBin mCycle; toBin mPragma;
           toBin mArb
    readBytes =
        do mCF <- fromBin; mSC <- fromBin; mRes <- fromBin;
           mCycle <- fromBin; mPragma <- fromBin; mArb <- fromBin;
           return (RuleRelationInfo mCF mSC mRes mCycle mPragma mArb)

instance Bin Conflicts where
    writeBytes (CUse mms)              = do putI 0; toBin mms
    writeBytes (CCycle rs)             = do putI 1; toBin rs
    writeBytes (CMethodsBeforeRules)   = do putI 2
    writeBytes (CUserEarliness pos)    = do putI 3; toBin pos
    writeBytes (CUserAttribute pos)    = do putI 4; toBin pos
    writeBytes (CUserPreempt pos)      = do putI 5; toBin pos
    writeBytes (CResource m)           = do putI 6; toBin m
    writeBytes (CArbitraryChoice)      = do putI 7
    writeBytes (CFFuncArbitraryChoice) = do putI 8
    readBytes =
        do i <- getI
           case i of
            0 -> do mms <- fromBin; return (CUse mms)
            1 -> do rs <- fromBin; return (CCycle rs)
            2 -> return CMethodsBeforeRules
            3 -> do pos <- fromBin; return (CUserEarliness pos)
            4 -> do pos <- fromBin; return (CUserAttribute pos)
            5 -> do pos <- fromBin; return (CUserPreempt pos)
            6 -> do m <- fromBin; return (CResource m)
            7 -> return CArbitraryChoice
            8 -> return CFFuncArbitraryChoice
            n -> internalError $ "GenABin.Bin(Conflicts).readBytes: " ++ show n

instance Bin SchedNode where
    writeBytes (Sched i) = section "SchedNode" $ do putI 0; toBin i
    writeBytes (Exec i)  = section "SchedNode" $ do putI 1; toBin i
    readBytes =
        do i <- getI
           case i of
            0 -> do i <- fromBin; return (Sched i)
            1 -> do i <- fromBin; return (Exec i)
            n -> internalError $ "GenABin.Bin(SchedNode).readBytes: " ++ show n

instance Bin RuleConflictType where
    writeBytes rct = toBin (fromEnum rct)
    readBytes = fromBin >>= return . toEnum


-- ---------

instance Bin InstNode where
  writeBytes (StateVar i) = do
    putI 0; toBin i
  writeBytes (Rule i) = do
    putI 1; toBin i
  writeBytes (Loc name ctype ignore ignore_name un children) = do
    putI 2; toBin name; toBin ctype;
    toBin ignore; toBin ignore_name; toBin un; toBin children
  readBytes = do
    i <- getI
    case i of
      0 -> do i <- fromBin; return (StateVar i)
      1 -> do i <- fromBin; return (Rule i)
      2 -> do name <- fromBin; ctype <- fromBin;
              ignore <- fromBin; ignore_name <- fromBin;
              un <- fromBin; children <- fromBin;
              return (Loc name ctype ignore ignore_name un children)
      n -> internalError ("GenABin.Bin(InstNode) - tag: " ++ show n)

-- ----------

instance Bin ResourceFlag where
    writeBytes RFoff    = do putI 0
    writeBytes RFsimple = do putI 1

    readBytes = do i <- getI
                   case i of
                     0 -> return RFoff
                     1 -> return RFsimple
                     n -> internalError $ "GenABin.Bin(ResourceFlag).readBytes: " ++ show n

-- (don't keep dump flags)
instance {-# OVERLAPPING #-} Bin [(DumpFlag, Maybe FilePath)] where
    writeBytes _ = return ()
    readBytes    = return []

instance {-# OVERLAPPING #-} Bin (Maybe (DumpFlag, Maybe String)) where
    writeBytes _ = return ()
    readBytes    = return Nothing

-- like dump flags, don't keep verbosity
instance Bin Verbosity where
    writeBytes _ = return ()
    readBytes    = return Normal

instance Bin SATFlag where
    writeBytes SAT_Yices = putI 1
    writeBytes SAT_STP = putI 2
    readBytes = do i <- getI
                   case i of
                     1 -> return SAT_Yices
                     2 -> return SAT_STP
                     n -> internalError $ "GenABin.Bin(SATFlag).readBytes: " ++ show n

instance Bin MsgListFlag where
    writeBytes AllMsgs = putI 0
    writeBytes (SomeMsgs msgs) = do putI 1; toBin msgs
    readBytes = do
      i <- getI
      case i of
        0 -> return AllMsgs
        1 -> do msgs <- fromBin; return (SomeMsgs msgs)
        n -> internalError $ "GenABin.Bin(MsgListFlag).readBytes: " ++ show n

-- should automatically verify no typos at compile-time XXX
instance Bin Flags where
    writeBytes (Flags
                a_000 a_001 a_002 a_003 a_004 a_005 a_006 a_007 a_008 a_009
                a_010 a_011 a_012 a_013 a_014 a_015 a_016 a_017 a_018 a_019
                a_020 a_021 a_022 a_023 a_024 a_025 a_026 a_027 a_028 a_029
                a_030 a_031 a_032 a_033 a_034 a_035 a_036 a_037 a_038 a_039
                a_040 a_041 a_042 a_043 a_044 a_045 a_046 a_047 a_048 a_049
                a_050 a_051 a_052 a_053 a_054 a_055 a_056 a_057 a_058 a_059
                a_060 a_061 a_062 a_063 a_064 a_065 a_066 a_067 a_068 a_069
                a_070 a_071 a_072 a_073 a_074 a_075 a_076 a_077 a_078 a_079
                a_080 a_081 a_082 a_083 a_084 a_085 a_086 a_087 a_088 a_089
                a_090 a_091 a_092 a_093 a_094 a_095 a_096 a_097 a_098 a_099
                a_100 a_101 a_102 a_103 a_104 a_105 a_106 a_107 a_108 a_109
                a_110 a_111 a_112 a_113 a_114 a_115 a_116 a_117 a_118 a_119
                a_120 a_121 a_122 a_123 a_124 a_125 a_126 a_127 a_128 a_129
                a_130 a_131 a_132 a_133) =
       do toBin a_000; toBin a_001; toBin a_002; toBin a_003; toBin a_004;
          toBin a_005; toBin a_006; toBin a_007; toBin a_008; toBin a_009;
          toBin a_010; toBin a_011; toBin a_012; toBin a_013; toBin a_014;
          toBin a_015; toBin a_016; toBin a_017; toBin a_018; toBin a_019;
          toBin a_020; toBin a_021; toBin a_022; toBin a_023; toBin a_024;
          toBin a_025; toBin a_026; toBin a_027; toBin a_028; toBin a_029;
          toBin a_030; toBin a_031; toBin a_032; toBin a_033; toBin a_034;
          toBin a_035; toBin a_036; toBin a_037; toBin a_038; toBin a_039;
          toBin a_040; toBin a_041; toBin a_042; toBin a_043; toBin a_044;
          toBin a_045; toBin a_046; toBin a_047; toBin a_048; toBin a_049;
          toBin a_050; toBin a_051; toBin a_052; toBin a_053; toBin a_054;
          toBin a_055; toBin a_056; toBin a_057; toBin a_058; toBin a_059;
          toBin a_060; toBin a_061; toBin a_062; toBin a_063; toBin a_064;
          toBin a_065; toBin a_066; toBin a_067; toBin a_068; toBin a_069;
          toBin a_070; toBin a_071; toBin a_072; toBin a_073; toBin a_074;
          toBin a_075; toBin a_076; toBin a_077; toBin a_078; toBin a_079;
          toBin a_080; toBin a_081; toBin a_082; toBin a_083; toBin a_084;
          toBin a_085; toBin a_086; toBin a_087; toBin a_088; toBin a_089;
          toBin a_090; toBin a_091; toBin a_092; toBin a_093; toBin a_094;
          toBin a_095; toBin a_096; toBin a_097; toBin a_098; toBin a_099;
          toBin a_100; toBin a_101; toBin a_102; toBin a_103; toBin a_104;
          toBin a_105; toBin a_106; toBin a_107; toBin a_108; toBin a_109;
          toBin a_110; toBin a_111; toBin a_112; toBin a_113; toBin a_114;
          toBin a_115; toBin a_116; toBin a_117; toBin a_118; toBin a_119;
          toBin a_120; toBin a_121; toBin a_122; toBin a_123; toBin a_124;
          toBin a_125; toBin a_126; toBin a_127; toBin a_128; toBin a_129;
          toBin a_130; toBin a_131; toBin a_132; toBin a_133
    readBytes =
       do a_000 <- fromBin; a_001 <- fromBin; a_002 <- fromBin; a_003 <- fromBin; a_004 <- fromBin;
          a_005 <- fromBin; a_006 <- fromBin; a_007 <- fromBin; a_008 <- fromBin; a_009 <- fromBin;
          a_010 <- fromBin; a_011 <- fromBin; a_012 <- fromBin; a_013 <- fromBin; a_014 <- fromBin;
          a_015 <- fromBin; a_016 <- fromBin; a_017 <- fromBin; a_018 <- fromBin; a_019 <- fromBin;
          a_020 <- fromBin; a_021 <- fromBin; a_022 <- fromBin; a_023 <- fromBin; a_024 <- fromBin;
          a_025 <- fromBin; a_026 <- fromBin; a_027 <- fromBin; a_028 <- fromBin; a_029 <- fromBin;
          a_030 <- fromBin; a_031 <- fromBin; a_032 <- fromBin; a_033 <- fromBin; a_034 <- fromBin;
          a_035 <- fromBin; a_036 <- fromBin; a_037 <- fromBin; a_038 <- fromBin; a_039 <- fromBin;
          a_040 <- fromBin; a_041 <- fromBin; a_042 <- fromBin; a_043 <- fromBin; a_044 <- fromBin;
          a_045 <- fromBin; a_046 <- fromBin; a_047 <- fromBin; a_048 <- fromBin; a_049 <- fromBin;
          a_050 <- fromBin; a_051 <- fromBin; a_052 <- fromBin; a_053 <- fromBin; a_054 <- fromBin;
          a_055 <- fromBin; a_056 <- fromBin; a_057 <- fromBin; a_058 <- fromBin; a_059 <- fromBin;
          a_060 <- fromBin; a_061 <- fromBin; a_062 <- fromBin; a_063 <- fromBin; a_064 <- fromBin;
          a_065 <- fromBin; a_066 <- fromBin; a_067 <- fromBin; a_068 <- fromBin; a_069 <- fromBin;
          a_070 <- fromBin; a_071 <- fromBin; a_072 <- fromBin; a_073 <- fromBin; a_074 <- fromBin;
          a_075 <- fromBin; a_076 <- fromBin; a_077 <- fromBin; a_078 <- fromBin; a_079 <- fromBin;
          a_080 <- fromBin; a_081 <- fromBin; a_082 <- fromBin; a_083 <- fromBin; a_084 <- fromBin;
          a_085 <- fromBin; a_086 <- fromBin; a_087 <- fromBin; a_088 <- fromBin; a_089 <- fromBin;
          a_090 <- fromBin; a_091 <- fromBin; a_092 <- fromBin; a_093 <- fromBin; a_094 <- fromBin;
          a_095 <- fromBin; a_096 <- fromBin; a_097 <- fromBin; a_098 <- fromBin; a_099 <- fromBin;
          a_100 <- fromBin; a_101 <- fromBin; a_102 <- fromBin; a_103 <- fromBin; a_104 <- fromBin;
          a_105 <- fromBin; a_106 <- fromBin; a_107 <- fromBin; a_108 <- fromBin; a_109 <- fromBin;
          a_110 <- fromBin; a_111 <- fromBin; a_112 <- fromBin; a_113 <- fromBin; a_114 <- fromBin;
          a_115 <- fromBin; a_116 <- fromBin; a_117 <- fromBin; a_118 <- fromBin; a_119 <- fromBin;
          a_120 <- fromBin; a_121 <- fromBin; a_122 <- fromBin; a_123 <- fromBin; a_124 <- fromBin;
          a_125 <- fromBin; a_126 <- fromBin; a_127 <- fromBin; a_128 <- fromBin; a_129 <- fromBin;
          a_130 <- fromBin; a_131 <- fromBin; a_132 <- fromBin; a_133 <- fromBin
          return (Flags
                a_000 a_001 a_002 a_003 a_004 a_005 a_006 a_007 a_008 a_009
                a_010 a_011 a_012 a_013 a_014 a_015 a_016 a_017 a_018 a_019
                a_020 a_021 a_022 a_023 a_024 a_025 a_026 a_027 a_028 a_029
                a_030 a_031 a_032 a_033 a_034 a_035 a_036 a_037 a_038 a_039
                a_040 a_041 a_042 a_043 a_044 a_045 a_046 a_047 a_048 a_049
                a_050 a_051 a_052 a_053 a_054 a_055 a_056 a_057 a_058 a_059
                a_060 a_061 a_062 a_063 a_064 a_065 a_066 a_067 a_068 a_069
                a_070 a_071 a_072 a_073 a_074 a_075 a_076 a_077 a_078 a_079
                a_080 a_081 a_082 a_083 a_084 a_085 a_086 a_087 a_088 a_089
                a_090 a_091 a_092 a_093 a_094 a_095 a_096 a_097 a_098 a_099
                a_100 a_101 a_102 a_103 a_104 a_105 a_106 a_107 a_108 a_109
                a_110 a_111 a_112 a_113 a_114 a_115 a_116 a_117 a_118 a_119
                a_120 a_121 a_122 a_123 a_124 a_125 a_126 a_127 a_128 a_129
                a_130 a_131 a_132 a_133)

-- ----------

instance Bin VProgram where
    writeBytes (VProgram ms dpis c) = do toBin ms; toBin dpis; toBin c
    readBytes = do ms <- fromBin; dpis <- fromBin; c <- fromBin; return (VProgram ms dpis c)

instance Bin VModule where
    writeBytes (VModule name c ports body) =
        do toBin name; toBin c; toBin ports; toBin body
    readBytes = do name <- fromBin; c <- fromBin; ports <- fromBin;
                   body <-fromBin; return (VModule name c ports body)

instance Bin VDPI where
    writeBytes (VDPI name ret args) =
        do toBin name; toBin ret; toBin args
    readBytes = do name <- fromBin; ret <- fromBin; args <- fromBin;
                   return (VDPI name ret args)

instance Bin VDPIType where
    writeBytes (VDT_void)    = do putI 0
    writeBytes (VDT_byte)    = do putI 1
    writeBytes (VDT_int)     = do putI 2
    writeBytes (VDT_longint) = do putI 3
    writeBytes (VDT_wide n)  = do putI 4; toBin n
    writeBytes (VDT_string)  = do putI 5
    writeBytes (VDT_poly)    = do putI 6
    readBytes = do
      i <- getI
      case i of
        0 -> return VDT_void
        1 -> return VDT_byte
        2 -> return VDT_int
        3 -> return VDT_longint
        4 -> do n <- fromBin; return (VDT_wide n)
        5 -> return VDT_string
        6 -> return VDT_poly
        n -> internalError $ "GenABin(VArg).readBytes: " ++ show n

instance Bin VId where
    writeBytes (VId s i m) = do toBin s; toBin i; toBin m
    readBytes = do s <- fromBin; i <- fromBin; m <- fromBin;
                   return (VId s i m)

instance Bin VArg where
    writeBytes (VAInput i r)       = do putI 0; toBin i; toBin r
    writeBytes (VAInout i i' r)    = do putI 1; toBin i; toBin i'; toBin r
    writeBytes (VAOutput i r)      = do putI 2; toBin i; toBin r
    writeBytes (VAParameter i r d) = do putI 3; toBin i; toBin r; toBin d
    readBytes = do
      i <- getI
      case i of
        0 -> do i <- fromBin; r <- fromBin; return (VAInput i r)
        1 -> do i <- fromBin; i' <- fromBin; r <- fromBin;
                return (VAInout i i' r)
        2 -> do i <- fromBin; r <- fromBin; return (VAOutput i r)
        3 -> do i <- fromBin; r <- fromBin; d <- fromBin;
                return (VAParameter i r d)
        n -> internalError $ "GenABin(VArg).readBytes: " ++ show n

instance Bin VExpr where
    writeBytes (VEConst n)        = do putI 0; toBin n
    writeBytes (VEReal n)         = do putI 1; toBin n
    writeBytes (VEWConst i w b v) = do putI 2; toBin i; toBin w; toBin b;
                                       toBin v
    writeBytes (VEUnknown n s)    = do putI 3; toBin n; toBin s
    writeBytes (VEString s)       = do putI 4; toBin s
    writeBytes (VETriConst ts)    = do putI 5; toBin ts
    writeBytes (VEUnOp i o e)     = do putI 6; toBin i; toBin o; toBin e
    writeBytes (VEOp i e1 o e2)   = do putI 7; toBin i; toBin e1; toBin o;
                                       toBin e2
    writeBytes (VEVar i)          = do putI 8; toBin i
    writeBytes (VEConcat es)      = do putI 9; toBin es
    writeBytes (VEIndex i e)      = do putI 10; toBin i; toBin e
    writeBytes (VESelect e hi lo) = do putI 11; toBin e; toBin hi; toBin lo
    writeBytes (VESelect1 e n)    = do putI 12; toBin e; toBin n
    writeBytes (VERepeat e n)     = do putI 13; toBin e; toBin n
    writeBytes (VEIf c t f)       = do putI 14; toBin c; toBin t; toBin f
    writeBytes (VEFctCall i es)   = do putI 15; toBin i; toBin es
    writeBytes (VEMacro m)        = do putI 16; toBin m;
    readBytes = do
      i <- getI
      case i of
        0 -> do n <- fromBin; return (VEConst n)
        1 -> do n <- fromBin; return (VEReal n)
        2 -> do i <- fromBin; w <- fromBin; b <- fromBin; v <- fromBin;
                return (VEWConst i w b v)
        3 -> do n <- fromBin; s <- fromBin; return (VEUnknown n s)
        4 -> do s <- fromBin; return (VEString s)
        5 -> do ts <- fromBin; return (VETriConst ts)
        6 -> do i <- fromBin; o <- fromBin; e <- fromBin; return (VEUnOp i o e)
        7 -> do i <- fromBin; e1 <- fromBin; o <- fromBin; e2 <- fromBin;
                return (VEOp i e1 o e2)
        8 -> do i <- fromBin; return (VEVar i)
        9 -> do es <- fromBin; return (VEConcat es)
        10 -> do i <- fromBin; e <- fromBin; return (VEIndex i e)
        11 -> do e <- fromBin; hi <- fromBin; lo <- fromBin;
                 return (VESelect e hi lo)
        12 -> do e <- fromBin; n <- fromBin; return (VESelect1 e n)
        13 -> do e <- fromBin; n <- fromBin; return (VERepeat e n)
        14 -> do c <- fromBin; t <- fromBin; f <- fromBin; return (VEIf c t f)
        15 -> do i <- fromBin; es <- fromBin; return (VEFctCall i es)
        16 -> do m <- fromBin;  return (VEMacro m);
        n -> internalError $ "GenABin(VExpr).readBytes: " ++ show n

instance Bin VTri where
    writeBytes v = toBin (fromEnum v)
    readBytes = fromBin >>= return . toEnum

instance Bin VOp where
    writeBytes v = toBin (fromEnum v)
    readBytes = fromBin >>= return . toEnum

instance Bin VMItem where
    writeBytes (VMDecl d)           = do putI 0; toBin d
    writeBytes (VMInst m i pas pos) = do putI 1; toBin m; toBin i; toBin pas;
                                         toBin pos
    writeBytes (VMAssign lv e)      = do putI 2; toBin lv; toBin e
    writeBytes (VMStmt a body)      = do putI 3; toBin a; toBin body
    writeBytes (VMComment c m)      = do putI 4; toBin c; toBin m
    writeBytes (VMRegGroup i s c m) = do putI 5; toBin i; toBin s; toBin c;
                                         toBin m
    writeBytes (VMGroup a body)     = do putI 6; toBin a; toBin body
    writeBytes (VMFunction f)       = do putI 7; toBin f
    readBytes = do
      i <- getI
      case i of
        0 -> do d <- fromBin; return (VMDecl d)
        1 -> do m <- fromBin; i <- fromBin; pas <- fromBin; pos <- fromBin;
                return (VMInst m i pas pos)
        2 -> do lv <- fromBin; e <- fromBin; return (VMAssign lv e)
        3 -> do a <- fromBin; body <- fromBin; return (VMStmt a body)
        4 -> do c <- fromBin; m <- fromBin; return (VMComment c m)
        5 -> do i <- fromBin; s <- fromBin; c <- fromBin; m <- fromBin;
                return (VMRegGroup i s c m)
        6 -> do a <- fromBin; body <- fromBin; return (VMGroup a body)
        7 -> do f <- fromBin; return (VMFunction f)
        n -> internalError $ "GenABin(VMItem).readBytes: " ++ show n

instance Bin VVDecl where
    writeBytes (VVDecl t r vs) = do putI 0; toBin t; toBin r; toBin vs
    writeBytes (VVDWire r v e) = do putI 1; toBin r; toBin v; toBin e
    readBytes = do
      i <- getI
      case i of
        0 -> do t <- fromBin; r <- fromBin; vs <- fromBin;
                return (VVDecl t r vs)
        1 -> do r <- fromBin; v <- fromBin; e <- fromBin;
                return (VVDWire r v e)
        n -> internalError $ "GenABin(VVDecl).readBytes: " ++ show n

instance Bin VDType where
    writeBytes t = toBin (fromEnum t)
    readBytes = fromBin >>= return . toEnum

instance Bin VVar where
    writeBytes (VVar i)     = do putI 0; toBin i
    writeBytes (VArray r i) = do putI 1; toBin r; toBin i
    readBytes = do
      i <- getI
      case i of
        0 -> do i <- fromBin; return (VVar i)
        1 -> do r <- fromBin; i <- fromBin; return (VArray r i)
        n -> internalError $ "GenABin(VVar).readBytes: " ++ show n

instance Bin VLValue where
    writeBytes (VLId i)      = do putI 0; toBin i
    writeBytes (VLConcat vs) = do putI 1; toBin vs
    writeBytes (VLSub v e)   = do putI 2; toBin v; toBin e
    readBytes = do
      i <- getI
      case i of
        0 -> do i <- fromBin; return (VLId i)
        1 -> do vs <- fromBin; return (VLConcat vs)
        2 -> do v <- fromBin; e <- fromBin; return (VLSub v e)
        n -> internalError $ "GenABin(VLValue).readBytes: " ++ show n

instance Bin VStmt where
    writeBytes (VAt e s)         = do putI 0; toBin e; toBin s
    writeBytes (Valways s)       = do putI 1; toBin s
    writeBytes (Vinitial s)      = do putI 2; toBin s
    writeBytes (VSeq ss)         = do putI 3; toBin ss
    writeBytes (Vcasex e as p f) = do putI 4; toBin e; toBin as; toBin p;
                                      toBin f
    writeBytes (Vcase e as p f)  = do putI 5; toBin e; toBin as; toBin p;
                                      toBin f
    writeBytes (VAssign lv e)    = do putI 6; toBin lv; toBin e
    writeBytes (VAssignA lv e)   = do putI 7; toBin lv; toBin e
    writeBytes (Vif c t)         = do putI 8; toBin c; toBin t
    writeBytes (Vifelse c t f)   = do putI 9; toBin c; toBin t; toBin f
    writeBytes (Vdumpvars n is)  = do putI 10; toBin n; toBin is
    writeBytes (VTask i es)      = do putI 11; toBin i; toBin es
    writeBytes (VAssert e es)    = do putI 12; toBin e; toBin es
    writeBytes (VZeroDelay)      = do putI 13
    readBytes = do
      i <- getI
      case i of
        0 -> do e <- fromBin; s <- fromBin; return (VAt e s)
        1 -> do s <- fromBin; return (Valways s)
        2 -> do s <- fromBin; return (Vinitial s)
        3 -> do ss <- fromBin; return (VSeq ss)
        4 -> do e <- fromBin; as <- fromBin; p <- fromBin; f <- fromBin;
                return (Vcasex e as p f)
        5 -> do e <- fromBin; as <- fromBin; p <- fromBin; f <- fromBin;
                return (Vcase e as p f)
        6 -> do lv <- fromBin; e <- fromBin; return (VAssign lv e)
        7 -> do lv <- fromBin; e <- fromBin; return (VAssignA lv e)
        8 -> do c <- fromBin; t <- fromBin; return (Vif c t)
        9 -> do c <- fromBin; t <- fromBin; f <- fromBin; return (Vifelse c t f)
        10 -> do n <- fromBin; is <- fromBin; return (Vdumpvars n is)
        11 -> do i <- fromBin; es <- fromBin; return (VTask i es)
        12 -> do e <- fromBin; es <- fromBin; return (VAssert e es)
        13 -> return VZeroDelay
        n -> internalError $ "GenABin(VStmt).readBytes: " ++ show n

instance Bin VEventExpr where
    writeBytes (VEEOr e1 e2)  = do putI 0; toBin e1; toBin e2
    writeBytes (VEEposedge e) = do putI 1; toBin e
    writeBytes (VEEnegedge e) = do putI 2; toBin e
    writeBytes (VEE e)        = do putI 3; toBin e
    writeBytes (VEEMacro s e) = do putI 4; toBin s; toBin e
    readBytes = do
      i <- getI
      case i of
        0 -> do e1 <- fromBin; e2 <- fromBin; return (VEEOr e1 e2)
        1 -> do e <- fromBin; return (VEEposedge e)
        2 -> do e <- fromBin; return (VEEnegedge e)
        3 -> do e <- fromBin; return (VEE e)
        4 -> do s <- fromBin; e <- fromBin; return (VEEMacro s e)
        n -> internalError $ "GenABin(VEventExpr).readBytes: " ++ show n

instance Bin VCaseArm where
    writeBytes (VCaseArm es s) = do putI 0; toBin es; toBin s
    writeBytes (VDefault s)    = do putI 1; toBin s
    readBytes = do
      i <- getI
      case i of
        0 -> do es <- fromBin; s <- fromBin; return (VCaseArm es s)
        1 -> do s <- fromBin; return (VDefault s)
        n -> internalError $ "GenABin(VCaseArm).readBytes: " ++ show n

instance Bin VFunction where
    writeBytes (VFunction i r d s) = do toBin i; toBin r; toBin d; toBin s
    readBytes = do i <- fromBin; r <- fromBin; d <- fromBin; s <- fromBin;
                   return (VFunction i r d s)

-- ----------
