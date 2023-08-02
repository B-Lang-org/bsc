{-# LANGUAGE CPP #-}
module SimPrimitiveModules ( primMap
                           , NamingFn
                           , TickDirection(..)
                           , tickElem, tickIsPos, tickIsNeg
                           , checkBluesimPrimitives
                           , getPrimDomainInfo
                           , isPrimitiveModule, isFIFO
                           ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import ASyntax
import ASyntaxUtil
import IntLit
import Id(Id, mk_homeless_id, getIdPosition)
import VModInfo(VFieldInfo(..), vName, vClk,
                VClockInfo(..), id_to_vName, getVNameString)
import Wires(ClockDomain(..), initClockDomain)
import PPrint
import CCSyntax(bitsType, CSign(..))
import Error(internalError, ErrMsg(..), ErrorHandle, bsError)

import Control.Monad(when)

-- import Debug.Trace

-- Function which maps module arguments to a module type name
-- and new module arguments.
-- For instance, it could use the first argument to produce a
-- templated type name "Mod<N>", permute, add or drop arguments,
-- etc.
type NamingFn = [AExpr] -> (String,[AExpr])

data ResetType = NRst   -- no reset
               | SRst   -- synchronous reset
               | ARst   -- asynchronous reset
  deriving (Eq, Show)

-- ----------------------
-- Functions for handling module arguments, creating templated
-- types, etc. used for translating primitive modules.

mkErr :: String -> String -> String -> [AExpr] -> String
mkErr mod prim desc args =
    let msg = (text prim) <+> (text "expected module") <+> (text mod) <+>
              (text "to have") <+> (text desc) <+>
              (text "but it was given arguments: ") <+>
              (pPrint PDReadable 0 args)
    in render msg

-- Note: these signatures make sense when you realize that NamingFn is
-- a function type, so there are more arrows than it appears.

-- no template parameters needed
noSizeType :: String -> String -> NamingFn
noSizeType _ prim args =
  let doc = text prim
  in  (render doc, args)

-- one template parameter giving a sized type
sizedType :: String -> String -> NamingFn
sizedType _ prim args@((ASInt _ _ sz):_) =
  let ty_doc = pPrint PDReadable 0 (bitsType (ilValue sz) CTunsigned)
      doc    = (text prim) <> (text "<") <> ty_doc <> (text ">")
  in (render doc, args)
sizedType mod prim args = internalError $ mkErr mod prim "an initial size argument" args

-- one template parameter for an implied size of 0
zeroSizedType :: String -> String -> NamingFn
zeroSizedType mod prim args = sizedType mod prim ((aNat 0):args)

-- one template parameter giving a sized type and a bool argument
sizedTypeWithBoolArg :: Bool -> String -> String -> NamingFn
sizedTypeWithBoolArg b _ prim args@((ASInt _ _ sz):_) =
  let ty_doc = pPrint PDReadable 0 (bitsType (ilValue sz) CTunsigned)
      doc    = (text prim) <> (text "<") <> ty_doc <> (text ">")
  in (render doc, args ++ [aSBool b])
sizedTypeWithBoolArg b mod prim args = internalError $ mkErr mod prim "an initial size argument" args

-- register template parameter for data type, plus added argument
-- describing reset strategy
regType :: ResetType -> String -> String -> NamingFn
regType rtype _ prim args@((ASInt _ _ sz):_) =
  let ty_doc  = pPrint PDReadable 0 (bitsType (ilValue sz) CTunsigned)
      doc     = (text prim) <> (text "<") <> ty_doc <> (text ">")
      rst_arg = case rtype of
                  NRst -> []
                  SRst -> [aFalse]
                  ARst -> [aTrue]
  in (render doc, args ++ rst_arg)
regType _ mod prim args = internalError $ mkErr mod prim "an initial register width argument" args

-- memory template parameters for address and data types
memType :: String -> String -> NamingFn
memType _ prim args@((ASInt _ _ sz1):(ASInt _ _ sz2):_) =
  let ty1_doc   = pPrint PDReadable 0 (bitsType (ilValue sz1) CTunsigned)
      ty2_doc   = pPrint PDReadable 0 (bitsType (ilValue sz2) CTunsigned)
      tmpl_args = ty1_doc <> comma <> ty2_doc
      doc       = (text prim) <> (text "<") <> tmpl_args <> (text ">")
  in (render doc, args)
memType mod prim args = internalError $ mkErr mod prim "addr and data width arguments" args

-- memory template parameters for address and data types, with
-- for file name argument
memFileType :: String -> String -> NamingFn
memFileType _ prim args@(str:(ASInt _ _ sz1):(ASInt _ _ sz2):_) | isStringType (aType str) =
  let ty1_doc   = pPrint PDReadable 0 (bitsType (ilValue sz1) CTunsigned)
      ty2_doc   = pPrint PDReadable 0 (bitsType (ilValue sz2) CTunsigned)
      tmpl_args = ty1_doc <> comma <> ty2_doc
      doc       = (text prim) <> (text "<") <> tmpl_args <> (text ">")
  in (render doc, args)
memFileType mod prim args = internalError $ mkErr mod prim "filename and addr and data width arguments" args

-- BRAM template parameters for address and data types, accounting
-- for pipelining argument before size arguments
bramType :: Integer -> String -> String -> NamingFn
bramType num_ports _ prim args@((ASInt _ _ _):(ASInt _ _ sz1):(ASInt _ _ sz2):_) =
  let ty1_doc   = pPrint PDReadable 0 (bitsType (ilValue sz1) CTunsigned)
      ty2_doc   = pPrint PDReadable 0 (bitsType (ilValue sz2) CTunsigned)
      ty3_doc   = pPrint PDReadable 0 (bitsType             1 CTunsigned)
      tmpl_args = ty1_doc <> comma <> ty2_doc <> comma <> ty3_doc
      doc       = (text prim) <> (text "<") <> tmpl_args <> (text ">")
  in (render doc, args ++ [aNat num_ports])
bramType _ mod prim args = internalError $ mkErr mod prim "addr and data width arguments" args

-- BRAM template parameters for address and data types, accounting
-- for file name and pipelining argument before size arguments
bramFileType :: Integer -> String -> String -> NamingFn
bramFileType num_ports _ prim args@(str:(ASInt _ _ _):(ASInt _ _ sz1):(ASInt _ _ sz2):_) | isStringType (aType str) =
  let ty1_doc   = pPrint PDReadable 0 (bitsType (ilValue sz1) CTunsigned)
      ty2_doc   = pPrint PDReadable 0 (bitsType (ilValue sz2) CTunsigned)
      ty3_doc   = pPrint PDReadable 0 (bitsType             1 CTunsigned)
      tmpl_args = ty1_doc <> comma <> ty2_doc <> comma <> ty3_doc
      doc       = (text prim) <> (text "<") <> tmpl_args <> (text ">")
  in (render doc, args ++ [aNat num_ports])
bramFileType _ mod prim args = internalError $ mkErr mod prim "filename and addr and data width arguments" args

-- BRAM template parameters for address, data and write enable types,
-- accounting for pipelining argument before size arguments
bramEnsType :: Integer -> String -> String -> NamingFn
bramEnsType num_ports _ prim args@((ASInt _ _ _):(ASInt _ _ sz1):(ASInt _ _ sz2):(ASInt _ _ _):(ASInt _ _ sz4):_) =
  let ty1_doc   = pPrint PDReadable 0 (bitsType (ilValue sz1) CTunsigned)
      ty2_doc   = pPrint PDReadable 0 (bitsType (ilValue sz2) CTunsigned)
      ty3_doc   = pPrint PDReadable 0 (bitsType (ilValue sz4) CTunsigned)
      tmpl_args = ty1_doc <> comma <> ty2_doc <> comma <> ty3_doc
      doc       = (text prim) <> (text "<") <> tmpl_args <> (text ">")
  in (render doc, args ++ [aNat num_ports])
bramEnsType _ mod prim args = internalError $ mkErr mod prim "BRAM byte enable and size arguments" args

-- BRAM template parameters for address, data and write enable
-- types, accounting for file name and pipelining argument before
-- size arguments
bramFileEnsType :: Integer -> String -> String -> NamingFn
bramFileEnsType num_ports _ prim args@(str:(ASInt _ _ _):(ASInt _ _ sz1):(ASInt _ _ sz2):(ASInt _ _ _):(ASInt _ _ sz4):_) | isStringType (aType str) =
  let ty1_doc   = pPrint PDReadable 0 (bitsType (ilValue sz1) CTunsigned)
      ty2_doc   = pPrint PDReadable 0 (bitsType (ilValue sz2) CTunsigned)
      ty3_doc   = pPrint PDReadable 0 (bitsType (ilValue sz4) CTunsigned)
      tmpl_args = ty1_doc <> comma <> ty2_doc <> comma <> ty3_doc
      doc       = (text prim) <> (text "<") <> tmpl_args <> (text ">")
  in (render doc, args ++ [aNat num_ports])
bramFileEnsType _ mod prim args = internalError $ mkErr mod prim "filename and BRAM byte enable and size arguments" args


-- FIFO template parameters for data type, plus additional
-- arguments for depth, guardedness, loopiness, etc.

bit_count :: Integer -> Integer
bit_count 0 = 0
bit_count x = 1 + (bit_count (x `div` 2))

fifoType :: String -> String -> NamingFn
fifoType "FIFO1" prim [width@(ASInt _ _ sz), guarded] =
  let ty_doc = pPrint PDReadable 0 (bitsType (ilValue sz) CTunsigned)
      doc    = (text prim) <> (text "<") <> ty_doc <> (text ">")
  in (render doc, [width, aNat 1, guarded, aNat 0])
fifoType "FIFO10" prim args = fifoType "FIFO1" prim ((aNat 0):args)
fifoType "FIFO2" prim [width@(ASInt _ _ sz), guarded] =
  let ty_doc = pPrint PDReadable 0 (bitsType (ilValue sz) CTunsigned)
      doc    = (text prim) <> (text "<") <> ty_doc <> (text ">")
  in (render doc, [width, aNat 2, guarded, aNat 0])
fifoType "FIFO20" prim args = fifoType "FIFO2" prim ((aNat 0):args)
fifoType "SizedFIFO" prim [width@(ASInt _ _ sz), depth, _, guarded] =
  let ty_doc = pPrint PDReadable 0 (bitsType (ilValue sz) CTunsigned)
      doc    = (text prim) <> (text "<") <> ty_doc <> (text ">")
  in (render doc, [width, depth, guarded, aNat 0])
fifoType "SizedFIFO0" prim args = fifoType "SizedFIFO" prim ((aNat 0):args)
fifoType "FIFOL1" prim [width@(ASInt _ _ sz)] =
  let ty_doc = pPrint PDReadable 0 (bitsType (ilValue sz) CTunsigned)
      doc    = (text prim) <> (text "<") <> ty_doc <> (text ">")
  in (render doc, [width, aNat 1, aNat 0, aNat 1])
fifoType "FIFOL10" prim args = fifoType "FIFOL1" prim ((aNat 0):args)
fifoType "FIFOL2" prim [width@(ASInt _ _ sz)] =
  let ty_doc = pPrint PDReadable 0 (bitsType (ilValue sz) CTunsigned)
      doc    = (text prim) <> (text "<") <> ty_doc <> (text ">")
  in (render doc, [width, aNat 2, aNat 0, aNat 1])
fifoType "FIFOL20" prim args = fifoType "FIFOL2" prim ((aNat 0):args)
fifoType "SizedFIFOL" prim [width@(ASInt _ _ sz), depth, _] =
  let ty_doc = pPrint PDReadable 0 (bitsType (ilValue sz) CTunsigned)
      doc    = (text prim) <> (text "<") <> ty_doc <> (text ">")
  in (render doc, [width, depth, aNat 0, aNat 1])
fifoType "SizedFIFOL0" prim args = fifoType "SizedFIFOL" prim ((aNat 0):args)
fifoType "SyncFIFO" prim [width@(ASInt _ _ sz), depth, _] =
  let ty_doc   = pPrint PDReadable 0 (bitsType (ilValue sz) CTunsigned)
      idx_bits = bit_count (ilValue sz)
      idx_doc  = pPrint PDReadable 0 (bitsType idx_bits CTunsigned)
      doc      = (text prim) <> (text "<") <> ty_doc <> comma <>
                                              idx_doc <> (text ">")
  in (render doc, [width, depth, aNat 0])
fifoType "SyncFIFO0" prim args = fifoType "SyncFIFO" prim ((aNat 0):args)
fifoType "SyncFIFO1" prim [width@(ASInt _ _ sz)] =
  let ty_doc   = pPrint PDReadable 0 (bitsType (ilValue sz) CTunsigned)
      idx_bits = bit_count (ilValue sz)
      idx_doc  = pPrint PDReadable 0 (bitsType idx_bits CTunsigned)
      doc      = (text prim) <> (text "<") <> ty_doc <> comma <>
                                              idx_doc <> (text ">")
  in (render doc, [width, aNat 1, aNat 0])
fifoType "SyncFIFO10" prim args = fifoType "SyncFIFO1" prim ((aNat 0):args)
fifoType "SyncFIFOLevel" prim [width@(ASInt _ _ sz), depth, _] =
  let ty_doc   = pPrint PDReadable 0 (bitsType (ilValue sz) CTunsigned)
      idx_bits = bit_count (ilValue sz)
      idx_doc  = pPrint PDReadable 0 (bitsType idx_bits CTunsigned)
      doc      = (text prim) <> (text "<") <> ty_doc <> comma <>
                                              idx_doc <> (text ">")
  in (render doc, [width, depth, aNat 1])
fifoType "SyncFIFOLevel0" prim args = fifoType "SyncFIFOLevel" prim ((aNat 0):args)
fifoType mod prim args = internalError $ mkErr mod prim "FIFO width and depth arguments" args

boolArg :: Bool -> String -> String -> NamingFn
boolArg b _ prim args = (prim, args ++ [aSBool b])

-- TickDirection records clock edges that need to generate
-- "tick" method calls for the primitive.
data TickDirection a = Pos a
                     | Neg a
                     | Both a
  deriving (Eq, Ord, Show)

instance (PPrint a) => PPrint (TickDirection a) where
  pPrint d p (Pos x)  = (text "Pos") <+> (pPrint d p x)
  pPrint d p (Neg x)  = (text "Neg") <+> (pPrint d p x)
  pPrint d p (Both x) = (text "Both") <+> (pPrint d p x)

tickElem :: (TickDirection a) -> a
tickElem (Pos x)  = x
tickElem (Neg x)  = x
tickElem (Both x) = x

tickIsPos :: TickDirection a -> Bool
tickIsPos (Neg _) = False
tickIsPos _       = True;

tickIsNeg :: TickDirection a -> Bool
tickIsNeg (Pos _) = False
tickIsNeg _       = True;

-- Fields: BSV name
--         C++ implementation class
--         functions for determining template arguments
--         names of ports which become "tick" methods
primMap :: [(String, String, String -> String -> NamingFn, [TickDirection String])]
primMap = [ ("RegN",               "Reg",              regType SRst,               [])
          , ("RegUN",              "Reg",              regType NRst,               [])
          , ("RegA",               "Reg",              regType ARst,               [])
          , ("CRegN5",             "CReg",             regType SRst,               [Pos "clk"])
          , ("CRegUN5",            "CReg",             regType NRst,               [Pos "clk"])
          , ("CRegA5",             "CReg",             regType ARst,               [Pos "clk"])
          , ("CrossingBypassWire", "Wire",             sizedTypeWithBoolArg True,  [Pos "clk"])
          , ("CrossingRegN",       "Reg",              regType SRst,               [])
          , ("CrossingRegUN",      "Reg",              regType NRst,               [])
          , ("CrossingRegA",       "Reg",              regType ARst,               [])
          , ("RevertReg",          "Reg",              regType NRst,               [])
          , ("ConfigRegN",         "ConfigReg",        regType SRst,               [])
          , ("ConfigRegUN",        "ConfigReg",        regType NRst,               [])
          , ("ConfigRegA",         "ConfigReg",        regType ARst,               [])
          , ("RWire",              "Wire",             sizedTypeWithBoolArg False, [Pos "clk"])
          , ("RWire0",             "Wire",             zeroSizedType,              [Pos "clk"])
          , ("BypassWire",         "Wire",             sizedTypeWithBoolArg False, [Pos "clk"])
          , ("BypassWire0",        "Wire",             zeroSizedType,              [Pos "clk"])
          , ("FIFO1",              "Fifo",             fifoType,                   [])
          , ("FIFO10",             "Fifo",             fifoType,                   [])
          , ("FIFO2",              "Fifo",             fifoType,                   [])
          , ("FIFO20",             "Fifo",             fifoType,                   [])
          , ("SizedFIFO",          "Fifo",             fifoType,                   [])
          , ("SizedFIFO0",         "Fifo",             fifoType,                   [])
          , ("FIFOL1",             "Fifo",             fifoType,                   [])
          , ("FIFOL10",            "Fifo",             fifoType,                   [])
          , ("FIFOL2",             "Fifo",             fifoType,                   [])
          , ("FIFOL20",            "Fifo",             fifoType,                   [])
          , ("SizedFIFOL",         "Fifo",             fifoType,                   [])
          , ("SizedFIFOL0",        "Fifo",             fifoType,                   [])
          , ("RegFile",            "RegFile",          memType,                    [])
          , ("RegFileLoad",        "RegFile",          memFileType,                [])
          , ("BRAM1",              "BRAM",             bramType 1,                 [Pos "clk"])
          , ("BRAM1Load",          "BRAM",             bramFileType 1,             [Pos "clk"])
          , ("BRAM1BE",            "BRAM",             bramEnsType 1,              [Pos "clk"])
          , ("BRAM1BELoad",        "BRAM",             bramFileEnsType 1,          [Pos "clk"])
          , ("BRAM2",              "BRAM",             bramType 2,                 [Pos "clkA", Pos "clkB"])
          , ("BRAM2Load",          "BRAM",             bramFileType 2,             [Pos "clkA", Pos "clkB"])
          , ("BRAM2BE",            "BRAM",             bramEnsType 2,              [Pos "clkA", Pos "clkB"])
          , ("BRAM2BELoad",        "BRAM",             bramFileEnsType 2,          [Pos "clkA", Pos "clkB"])
          , ("Probe",              "Probe",            sizedType,                  [])
          , ("ProbeWire",          "ProbeWire",        sizedType,                  [])
          , ("Counter",            "Counter",          sizedType,                  [])
          , ("RegTwoN",            "RegTwo",           regType SRst,               [])
          , ("RegTwoUN",           "RegTwo",           regType NRst,               [])
          , ("RegTwoA",            "RegTwo",           regType ARst,               [])
          , ("ClockGen",           "ClockGen",         noSizeType,                 [])
          , ("RegAligned",         "RegAligned",       regType ARst,               [Pos "realClock"])
          , ("SyncBit05",          "Sync1",            noSizeType,                 [Neg "clk_dst"])
          , ("SyncBit1",           "Sync1",            noSizeType,                 [Pos "clk_dst"])
          , ("SyncBit15",          "Sync15",           noSizeType,                 [Both "clk_dst"])
          , ("SyncBit",            "Sync2",            noSizeType,                 [Pos "clk_dst"])
          , ("SyncPulse",          "SyncPulse",        noSizeType,                 [Pos "clk_dst"])
          , ("SyncHandshake",      "SyncHandshake",    noSizeType,                 [Pos "clk_src", Pos "clk_dst"])
          , ("SyncRegister",       "SyncReg",          sizedType,                  [Pos "clk_src", Pos "clk_dst"])
          , ("SyncFIFO",           "SyncFIFO",         fifoType,                   [Pos "clk_src", Pos "clk_dst"])
          , ("SyncFIFO0",          "SyncFIFO",         fifoType,                   [Pos "clk_src", Pos "clk_dst"])
          , ("SyncFIFO1",          "SyncFIFO",         fifoType,                   [Pos "clk_src", Pos "clk_dst"])
          , ("SyncFIFO10",         "SyncFIFO",         fifoType,                   [Pos "clk_src", Pos "clk_dst"])
          , ("SyncFIFOLevel",      "SyncFIFO",         fifoType,                   [Pos "clk_src", Pos "clk_dst"])
          , ("SyncFIFOLevel0",     "SyncFIFO",         fifoType,                   [Pos "clk_src", Pos "clk_dst"])
          , ("BypassCrossingWire", "Wire",             sizedTypeWithBoolArg True,  [Pos "clk"])
          , ("MakeClock",          "MakeClock",        noSizeType,                 [Pos "clk"])
          , ("GatedClock",         "GatedClock",       noSizeType,                 [Both "clk_in"])
          , ("ClockInverter",      "ClockInverter",    noSizeType,                 [Both "clk"])
          , ("GatedClockInverter", "ClockInverter",    noSizeType,                 [Both "clk"])
          , ("ClockDiv",           "ClockDivider",     noSizeType,                 [Pos "clk"])
          , ("GatedClockDiv",      "ClockDivider",     noSizeType,                 [Pos "clk"])
          , ("ClockSelect",        "ClockSelect",      noSizeType,                 [Both "aClk", Both "bClk", Pos "xclk"])
          , ("UngatedClockSelect", "ClockSelect",      noSizeType,                 [Both "aClk", Both "bClk", Pos "xclk"])
          , ("ClockMux",           "ClockMux",         noSizeType,                 [Both "aClk", Both "bClk", Pos "xclk"])
          , ("UngatedClockMux",    "ClockMux",         noSizeType,                 [Both "aClk", Both "bClk", Pos "xclk"])
          , ("MakeReset",          "MakeReset",        boolArg False,              [Pos "clk", Pos "dst_clk"])
          , ("MakeResetA",         "MakeReset",        boolArg True,               [Pos "clk", Pos "dst_clk"])
          , ("MakeReset0",         "MakeReset0",       noSizeType,                 [Pos "clk"])
          , ("SyncReset",          "SyncReset",        boolArg False,              [Pos "clk"])
          , ("SyncResetA",         "SyncReset",        boolArg True,               [Pos "clk"])
          , ("SyncReset0",         "SyncReset0",       noSizeType,                 [])
          , ("InitialReset",       "InitialReset",     noSizeType,                 [Pos "clk"])
          , ("ResetMux",           "ResetMux",         noSizeType,                 [Pos "xclk"])
          , ("ResetEither",        "ResetEither",      noSizeType,                 [])
          , ("ResetToBool",        "ResetToBool",      noSizeType,                 [])
          , ("DualPortRam",        "DualPortRam",      memType,                    [])
          , ("LatchCrossingReg",   "LatchCrossingReg", sizedType,                  [Both "dstClk"])
          ]


primNames :: [String]
primNames = [ n | (n,_,_,_) <- primMap ]

isPrimitiveModule :: String -> Bool
isPrimitiveModule m = m `elem` primNames

-- Check for primitive names that are not yet implemented in Bluesim
checkBluesimPrimitives :: ErrorHandle -> APackage -> IO ()
checkBluesimPrimitives errh apkg =
  let is_bad n = n `elem` [ "JoinClock" ]
      prims = [ (pos, name)
              | avi <- apkg_state_instances apkg
              , let pos = getIdPosition (avi_vname avi)
              , let name = getVNameString (vName (avi_vmi avi))
              ]
      msgs = [ (pos, EBSimMCDUnsupported name)
             | (pos, name) <- prims, is_bad name
             ]
  in when (not (null msgs)) $ bsError errh msgs



-- Get clock domain information for a primitive module.
-- This is used for primitive modules that need information on their
-- clocks set with a set_clk_<N>() method.  Currently, this is
-- used by the supported clock generation primitives (output clocks),
-- as well as primitives that need to know their input clock to correct
-- their internal VCD dumps.
-- The String argument is the primitive name and the output is Nothing
-- if the primitive does not require the clock info, or Just a triple:
-- * an update AVInst (see below)
-- * list of the clock domains in the primitive (for which the set_clk_
--   function needs to be called -- not all domains)
-- * list of output clocks
-- The AVInst argument is the AVInst of the primitive module,
-- because some Verilog primitives (RWire, BypassWire) have input clocks
-- but no clock port, but the merging of clock domains requires a port;
-- so for those primitives, we adjust the VModInfo to add a port, just
-- to make the merging work out.
getPrimDomainInfo :: AVInst -> String ->
                     Maybe (AVInst, [AClockDomain],[AIFace])
getPrimDomainInfo avi "RWire" =
  let -- the input clock needs to be set in order to adjust VCDs
      -- but need to add a port to the VModInfo
      clk_id       = mk_homeless_id "clk"
      osc_id       = mk_homeless_id "CLK"
      aclk         = AClock (ASPort aTBool osc_id) aTrue
      prim_domains = [(initClockDomain,[aclk])]  -- [AClockDomain]
      prim_iface   = []                          -- [AIFace]
      new_avi      = setInputClockPort avi clk_id osc_id
  in Just (new_avi, prim_domains, prim_iface)
getPrimDomainInfo avi "RWire0" =
  let -- the input clock needs to be set in order to adjust VCDs
      -- but need to add a port to the VModInfo
      clk_id       = mk_homeless_id "clk"
      osc_id       = mk_homeless_id "CLK"
      aclk         = AClock (ASPort aTBool osc_id) aTrue
      prim_domains = [(initClockDomain,[aclk])]  -- [AClockDomain]
      prim_iface   = []                          -- [AIFace]
      new_avi      = setInputClockPort avi clk_id osc_id
  in Just (new_avi, prim_domains, prim_iface)
getPrimDomainInfo avi "BypassWire" =
  let -- the input clock needs to be set in order to adjust VCDs
      -- but there are no ports, so no AClock is created
      clk_id       = mk_homeless_id "clk"
      osc_id       = mk_homeless_id "CLK"
      aclk         = AClock (ASPort aTBool osc_id) aTrue
      prim_domains = [(initClockDomain,[aclk])]  -- [AClockDomain]
      prim_iface   = []                          -- [AIFace]
      new_avi      = setInputClockPort avi clk_id osc_id
  in Just (new_avi, prim_domains, prim_iface)
getPrimDomainInfo avi "BypassWire0" =
  let -- the input clock needs to be set in order to adjust VCDs
      -- but there are no ports, so no AClock is created
      clk_id       = mk_homeless_id "clk"
      osc_id       = mk_homeless_id "CLK"
      aclk         = AClock (ASPort aTBool osc_id) aTrue
      prim_domains = [(initClockDomain,[aclk])]  -- [AClockDomain]
      prim_iface   = []                          -- [AIFace]
      new_avi      = setInputClockPort avi clk_id osc_id
  in Just (new_avi, prim_domains, prim_iface)
getPrimDomainInfo avi "Counter" =
  let -- the input clock needs to be set in order to adjust VCDs
      osc_id       = mk_homeless_id "CLK"
      aclk         = AClock (ASPort aTBool osc_id) aTrue
      prim_domains = [(initClockDomain,[aclk])]  -- [AClockDomain]
      prim_iface   = []                          -- [AIFace]
  in Just (avi, prim_domains, prim_iface)
getPrimDomainInfo avi "Probe" =
  let -- the input clock needs to be set in order to adjust VCDs
      osc_id       = mk_homeless_id "CLK"
      aclk         = AClock (ASPort aTBool osc_id) aTrue
      prim_domains = [(initClockDomain,[aclk])]  -- [AClockDomain]
      prim_iface   = []                          -- [AIFace]
  in Just (avi, prim_domains, prim_iface)
getPrimDomainInfo avi "ProbeWire" =
  let -- the input clock needs to be set in order to adjust VCDs
      -- but there are no ports, so no AClock is created
      clk_id       = mk_homeless_id "clk"
      osc_id       = mk_homeless_id "CLK"
      aclk         = AClock (ASPort aTBool osc_id) aTrue
      prim_domains = [(initClockDomain,[aclk])]  -- [AClockDomain]
      prim_iface   = []                          -- [AIFace]
      new_avi      = setInputClockPort avi clk_id osc_id
  in Just (new_avi, prim_domains, prim_iface)
getPrimDomainInfo avi "ClockGen" =
  let -- output clock
      clk_id       = mk_homeless_id "gen_clk"
      osc_id       = mk_homeless_id "CLK_OUT"
      aclk         = AClock (ASPort aTBool osc_id) aTrue
      clk_out      = AIClock clk_id aclk (Clock clk_id)
      prim_domains = [(initClockDomain,[aclk])]  -- [AClockDomain]
      prim_iface   = [clk_out]                   -- [AIFace]
  in Just (avi, prim_domains, prim_iface)
getPrimDomainInfo avi "RegAligned" =
  let -- the input clock needs to be set in order to adjust VCDs
      osc_id       = mk_homeless_id "CLK"
      aclk         = AClock (ASPort aTBool osc_id) aTrue
      in_osc_id    = mk_homeless_id "clk_src"
      clk_in       = AClock (ASPort aTBool in_osc_id) aTrue
      prim_domains = [(ClockDomain 0,[aclk])
                     ,(ClockDomain 1,[clk_in])
                     ]  -- [AClockDomain]
      prim_iface   = []                          -- [AIFace]
  in Just (avi, prim_domains, prim_iface)
getPrimDomainInfo avi prim | isCReg prim =
  let -- the input clock needs to be set in order to adjust VCDs
      osc_id       = mk_homeless_id "CLK"
      aclk         = AClock (ASPort aTBool osc_id) aTrue
      prim_domains = [(initClockDomain,[aclk])]  -- [AClockDomain]
      prim_iface   = []                          -- [AIFace]
  in Just (avi, prim_domains, prim_iface)
getPrimDomainInfo avi "MakeClock" =
  let -- output clock
      clk_id       = mk_homeless_id "new_clk"
      osc_id       = mk_homeless_id "CLK_OUT"
      gate_id      = mk_homeless_id "CLK_GATE_OUT"
      aclk         = AClock (ASPort aTBool osc_id) (ASPort aTBool gate_id)
      clk_out      = AIClock clk_id aclk (Clock clk_id)
      prim_domains = [(initClockDomain,[aclk])]  -- [AClockDomain]
      prim_iface   = [clk_out]                   -- [AIFace]
  in Just (avi, prim_domains, prim_iface)
getPrimDomainInfo avi "GatedClock" =
  let -- output clock
      clk_id       = mk_homeless_id "new_clk"
      osc_id       = mk_homeless_id "CLK_OUT"
      gate_id      = mk_homeless_id "CLK_GATE_OUT"
      aclk         = AClock (ASPort aTBool osc_id) (ASPort aTBool gate_id)
      clk_out      = AIClock clk_id aclk (Clock clk_id)
      prim_domains = [(initClockDomain,[aclk])]  -- [AClockDomain]
      prim_iface   = [clk_out]                   -- [AIFace]
  in Just (avi, prim_domains, prim_iface)
getPrimDomainInfo avi "ClockInverter" =
  let -- output clock
      clk_id       = mk_homeless_id "slowClock"
      osc_id       = mk_homeless_id "CLK_OUT"
      aclk         = AClock (ASPort aTBool osc_id) aTrue
      clk_out      = AIClock clk_id aclk (Clock clk_id)
      prim_domains = [(initClockDomain,[aclk])]  -- [AClockDomain]
      prim_iface   = [clk_out]                   -- [AIFace]
  in Just (avi, prim_domains, prim_iface)
getPrimDomainInfo avi "GatedClockInverter" =
  let -- output clock
      clk_id       = mk_homeless_id "slowClock"
      osc_id       = mk_homeless_id "CLK_OUT"
      gate_id      = mk_homeless_id "CLK_GATE_OUT"
      aclk         = AClock (ASPort aTBool osc_id) (ASPort aTBool gate_id)
      clk_out      = AIClock clk_id aclk (Clock clk_id)
      prim_domains = [(initClockDomain,[aclk])]  -- [AClockDomain]
      prim_iface   = [clk_out]                   -- [AIFace]
  in Just (avi, prim_domains, prim_iface)
getPrimDomainInfo avi "ClockDiv" =
  let -- output clock
      clk_id       = mk_homeless_id "slowClock"
      osc_id       = mk_homeless_id "CLK_OUT"
      aclk         = AClock (ASPort aTBool osc_id) aTrue
      clk_out      = AIClock clk_id aclk (Clock clk_id)
      in_osc_id    = mk_homeless_id "CLK_IN"
      clk          = AClock (ASPort aTBool in_osc_id) aTrue
      prim_domains = [(ClockDomain 0,[aclk])
                     ,(ClockDomain 1,[clk])
                     ]  -- [AClockDomain]
      prim_iface   = [clk_out]                   -- [AIFace]
  in Just (avi, prim_domains, prim_iface)
getPrimDomainInfo avi "GatedClockDiv" =
  let -- output clock
      clk_id       = mk_homeless_id "slowClock"
      osc_id       = mk_homeless_id "CLK_OUT"
      gate_id      = mk_homeless_id "CLK_GATE_OUT"
      aclk         = AClock (ASPort aTBool osc_id) (ASPort aTBool gate_id)
      clk_out      = AIClock clk_id aclk (Clock clk_id)
      in_osc_id    = mk_homeless_id "CLK_IN"
      clk          = AClock (ASPort aTBool in_osc_id) aTrue
      prim_domains = [(ClockDomain 0,[aclk])
                     ,(ClockDomain 1,[clk])
                     ]  -- [AClockDomain]
      prim_iface   = [clk_out]                   -- [AIFace]
  in Just (avi, prim_domains, prim_iface)
getPrimDomainInfo avi "ClockSelect" =
  let -- output clock
      clk_id       = mk_homeless_id "clock_out"
      osc_id       = mk_homeless_id "CLK_OUT"
      gate_id      = mk_homeless_id "CLK_GATE_OUT"
      aclk         = AClock (ASPort aTBool osc_id) (ASPort aTBool gate_id)
      clk_out      = AIClock clk_id aclk (Clock clk_id)
      prim_domains = [(initClockDomain,[aclk])]  -- [AClockDomain]
      prim_iface   = [clk_out]                   -- [AIFace]
  in Just (avi, prim_domains, prim_iface)
getPrimDomainInfo avi "UngatedClockSelect" =
  let -- output clock
      clk_id       = mk_homeless_id "clock_out"
      osc_id       = mk_homeless_id "CLK_OUT"
      aclk         = AClock (ASPort aTBool osc_id) aTrue
      clk_out      = AIClock clk_id aclk (Clock clk_id)
      prim_domains = [(initClockDomain,[aclk])]  -- [AClockDomain]
      prim_iface   = [clk_out]                   -- [AIFace]
  in Just (avi, prim_domains, prim_iface)
getPrimDomainInfo avi "ClockMux" =
  let -- output clock
      clk_id       = mk_homeless_id "clock_out"
      osc_id       = mk_homeless_id "CLK_OUT"
      gate_id      = mk_homeless_id "CLK_GATE_OUT"
      aclk         = AClock (ASPort aTBool osc_id) (ASPort aTBool gate_id)
      clk_out      = AIClock clk_id aclk (Clock clk_id)
      prim_domains = [(initClockDomain,[aclk])]  -- [AClockDomain]
      prim_iface   = [clk_out]                   -- [AIFace]
  in Just (avi, prim_domains, prim_iface)
getPrimDomainInfo avi "UngatedClockMux" =
  let -- output clock
      clk_id       = mk_homeless_id "clock_out"
      osc_id       = mk_homeless_id "CLK_OUT"
      aclk         = AClock (ASPort aTBool osc_id) aTrue
      clk_out      = AIClock clk_id aclk (Clock clk_id)
      prim_domains = [(initClockDomain,[aclk])]  -- [AClockDomain]
      prim_iface   = [clk_out]                   -- [AIFace]
  in Just (avi, prim_domains, prim_iface)
getPrimDomainInfo avi "SyncHandshake" =
  let -- two input clocks need to be set in order to adjust VCDs
      src_osc_id   = mk_homeless_id "sCLK"
      src_clk      = AClock (ASPort aTBool src_osc_id) aTrue
      dst_osc_id   = mk_homeless_id "dCLK"
      dst_clk      = AClock (ASPort aTBool dst_osc_id) aTrue
      prim_domains = [(ClockDomain 0,[src_clk])
                     ,(ClockDomain 1,[dst_clk])
                     ]  -- [AClockDomain]
      prim_iface   = []                          -- [AIFace]
  in Just (avi, prim_domains, prim_iface)
getPrimDomainInfo avi "SyncReset" =
  let -- the input clock needs to be set in order to adjust VCDs
      osc_id   = mk_homeless_id "CLK"
      aclk     = AClock (ASPort aTBool osc_id) aTrue
      prim_domains = [(initClockDomain,[aclk])]  -- [AClockDomain]
      prim_iface   = []                          -- [AIFace]
  in Just (avi, prim_domains, prim_iface)
getPrimDomainInfo avi prim | isFIFO prim =
  let -- the input clock needs to be set in order to adjust VCDs
      osc_id       = mk_homeless_id "CLK"
      aclk         = AClock (ASPort aTBool osc_id) aTrue
      prim_domains = [(initClockDomain,[aclk])]  -- [AClockDomain]
      prim_iface   = []                          -- [AIFace]
  in Just (avi, prim_domains, prim_iface)
getPrimDomainInfo avi prim | isSinglePortBRAM prim =
  let -- the input clock needs to be set in order to adjust VCDs
      osc_id       = mk_homeless_id "CLK"
      aclk         = AClock (ASPort aTBool osc_id) aTrue
      prim_domains = [(initClockDomain,[aclk])]  -- [AClockDomain]
      prim_iface   = []                          -- [AIFace]
  in Just (avi, prim_domains, prim_iface)
getPrimDomainInfo avi prim | isDualPortBRAM prim =
  let -- two input clocks need to be set in order to adjust VCDs
      a_osc_id   = mk_homeless_id "CLKA"
      a_clk      = AClock (ASPort aTBool a_osc_id) aTrue
      b_osc_id   = mk_homeless_id "CLKB"
      b_clk      = AClock (ASPort aTBool b_osc_id) aTrue
      prim_domains = [(ClockDomain 0,[a_clk])
                     ,(ClockDomain 1,[b_clk])
                     ]  -- [AClockDomain]
      prim_iface   = []                          -- [AIFace]
  in Just (avi, prim_domains, prim_iface)
getPrimDomainInfo _ _ = Nothing

setInputClockPort :: AVInst -> Id -> Id -> AVInst
setInputClockPort avi clk_id osc_id =
    let
        osc_vname = id_to_vName osc_id
        new_info = Just (osc_vname, Left False)

        updateOneInf (ci, _) | (ci == clk_id) = (ci, new_info)
        updateOneInf inf = inf

        updateVClockInfo vci =
            vci { input_clocks = map updateOneInf (input_clocks vci) }

        updateVMI vmi = vmi { vClk = updateVClockInfo (vClk vmi) }
    in
        avi { avi_vmi = updateVMI (avi_vmi avi) }


-- Used to identify FIFO primitives which need a clock handle to
-- adjust their VCDs
isFIFO :: String -> Bool
isFIFO s = s `elem` [ "FIFO1"
                    , "FIFO10"
                    , "FIFO2"
                    , "FIFO20"
                    , "SizedFIFO"
                    , "SizedFIFO0"
                    , "FIFOL1"
                    , "FIFOL10"
                    , "FIFOL2"
                    , "FIFOL20"
                    , "SizedFIFOL"
                    , "SizedFIFOL0"
                    ]

-- Used to identify CReg primitives which need a clock handle to
-- adjust their VCDs
isCReg :: String -> Bool
isCReg s = s `elem` [ "CRegN5"
                    , "CRegUN5"
                    , "CRegA5"
                    ]

-- Used to identify BRAM primitives which need one or more clock
-- handles to adjust their VCDs
isSinglePortBRAM :: String -> Bool
isSinglePortBRAM s = s `elem` [ "BRAM1"
                              , "BRAM1Load"
                              , "BRAM1BE"
                              , "BRAM1BELoad"
                              ]
isDualPortBRAM :: String -> Bool
isDualPortBRAM s = s `elem` [ "BRAM2"
                            , "BRAM2Load"
                            , "BRAM2BE"
                            , "BRAM2BELoad"
                            ]
