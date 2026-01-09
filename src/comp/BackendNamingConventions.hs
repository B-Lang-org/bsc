module BackendNamingConventions
    (
     createVerilogNameMap,
     createVerilogNameMapForAVInst,
     xLateIdUsingFStringMap,
     xLateFStringUsingFStringMap,

     isRegInst, isClockCrossingRegInst,
     isRegN, isRegUN, isRegA, isRegAligned,
     getRegClock, getRegReset, getRegInit, getRegWidth,
     mkDIN, mkEN, mkQOUT,
     regReadResId, regWriteEnId, regWriteArgId,

     isRWire, isRWire0, isBypassWire, isBypassWire0, isClockCrossingBypassWire,
     rwireSetEnId, rwireSetArgId, rwireGetResId, rwireHasResId,

     isCRegInst, isCRegN, isCRegUN, isCRegA,
     cregReadResId, cregWriteEnId, cregWriteArgId,
     cregToReg,

     isSyncReg,

     isFIFO, isFIFO0,

     isInoutConnect
    ) where

import Data.Char(isAlphaNum)
import Data.Maybe(mapMaybe)

import FStringCompat
import qualified Data.Map as M
import Id
import PreStrings(fsDollar, fsUnderscore, fsEnable)
import PreIds(idVReg)
import Error
import PPrint
import Flags(Flags, removeReg, removeCross)

import Position(Position, getPosition, noPosition)

import ASyntax
import VModInfo
import SchedInfo(SchedInfo(..), MethodConflictInfo(..))

--import Debug.Trace

-- ==============================
-- Common functions for defining primitives

-- for comparison with the module instances
getAVDefName :: AVInst -> VName
getAVDefName avi = vName (avi_vmi avi)

getAVInputClocks :: AVInst -> [InputClockInf]
getAVInputClocks avi = input_clocks (vClk (avi_vmi avi))

-- ==============================
-- Primitive Wires

rwire, rwire0, bypasswire, bypasswire0, crossbypasswire :: VName
rwire           = VName "RWire"
rwire0          = VName "RWire0"
bypasswire      = VName "BypassWire"
bypasswire0     = VName "BypassWire0"
crossbypasswire = VName "CrossingBypassWire"

isRWire, isRWire0 :: AVInst -> Bool
isRWire  avi = getAVDefName avi == rwire
isRWire0 avi = getAVDefName avi == rwire0

-- distinguish between BypassWire used within a domain
-- and a BypassWire that crosses clock domains
isBypassWire, isClockCrossingBypassWire, isBypassWire0 :: AVInst -> Bool
isBypassWire avi = (getAVDefName avi == bypasswire) || (getAVDefName avi == crossbypasswire);
isClockCrossingBypassWire avi = isBypassWire avi && (length(getAVInputClocks avi) == 2)
isBypassWire0 avi = getAVDefName avi == bypasswire0


-- ---------------
-- Names of RWire methods
-- (inlining happens before methods are renamed to ports)

rwireSetStr, rwireGetStr, rwireHasStr :: String
rwireSetStr = "wset"
rwireGetStr = "wget"
rwireHasStr = "whas"

-- XXX the Id here (with no position) should never be used, only its FString
-- XXX perhaps have version of mkMethId which takes an FString instead of Id?
rwireSetId, rwireGetId, rwireHasId :: Id
rwireSetId = mkId noPosition (mkFString rwireSetStr)
rwireGetId = mkId noPosition (mkFString rwireGetStr)
rwireHasId = mkId noPosition (mkFString rwireHasStr)

rwireSetEnId, rwireSetArgId, rwireGetResId, rwireHasResId :: Id -> Id
rwireSetEnId i  = mkMethId i rwireSetId Nothing MethodEnable
rwireSetArgId i = mkMethId i rwireSetId Nothing (MethodArg 1)
rwireGetResId i = mkMethId i rwireGetId Nothing (MethodResult 1)
rwireHasResId i = mkMethId i rwireHasId Nothing (MethodResult 1)

-- ==============================
-- Primitive CReg

cregn, cregun, crega :: VName
cregn  = VName "CRegN5"
cregun = VName "CRegUN5"
crega  = VName "CRegA5"

isCRegN :: AVInst -> Bool
isCRegN avi = (getAVDefName avi == cregn)

isCRegUN :: AVInst -> Bool
isCRegUN avi = (getAVDefName avi == cregun)

isCRegA :: AVInst -> Bool
isCRegA avi = (getAVDefName avi == crega)

isCRegInst :: AVInst -> Bool
isCRegInst avi = (isCRegN avi) || (isCRegUN avi) || (isCRegA avi)

-- ---------------
-- Names of CReg methods
-- (inlining happens before methods are renamed to ports)

cregReadStr, cregWriteStr :: Int -> String
cregReadStr  n = "port" ++ show (n::Int) ++ "__read"
cregWriteStr n = "port" ++ show (n::Int) ++ "__write"

-- XXX the Id here (with no position) should never be used, only its FString
-- XXX perhaps have version of mkMethId which takes an FString instead of Id?
cregReadId, cregWriteId :: Int -> Id
cregReadId  n = mkId noPosition (mkFString (cregReadStr n))
cregWriteId n = mkId noPosition (mkFString (cregWriteStr n))

cregReadResId, cregWriteEnId, cregWriteArgId :: Id -> Int -> Id
cregReadResId  i n = mkMethId i (cregReadId n)  Nothing (MethodResult 1)
cregWriteEnId  i n = mkMethId i (cregWriteId n) Nothing MethodEnable
cregWriteArgId i n = mkMethId i (cregWriteId n) Nothing (MethodArg 1)

-- ---------------
-- Names of ports and parameters on primtive CReg

cregDINPortStr, cregQOUTPortStr :: Int -> String
cregDINPortStr  n = "D_IN_" ++ show (n::Int)
cregQOUTPortStr n = "Q_OUT_" ++ show (n::Int)

-- ==============================
-- Primitive registers

regn, regun, rega :: VName
regn  = VName "RegN"
regun = VName "RegUN"
rega  = VName "RegA"

configregn, configregun, configrega :: VName
configregn  = VName "ConfigRegN"
configregun = VName "ConfigRegUN"
configrega  = VName "ConfigRegA"

crossregn, crossregun, crossrega :: VName
crossregn  = VName "CrossingRegN"
crossregun = VName "CrossingRegUN"
crossrega  = VName "CrossingRegA"

regaligned :: VName
regaligned = VName "RegAligned"

isRegN :: AVInst -> Bool
isRegN  avi = (getAVDefName avi == regn) ||
              (getAVDefName avi == configregn) ||
              (getAVDefName avi == crossregn)

isRegUN :: AVInst -> Bool
isRegUN avi = (getAVDefName avi == regun) ||
              (getAVDefName avi == configregun) ||
              (getAVDefName avi == crossregun)

isRegA :: AVInst -> Bool
isRegA  avi = (getAVDefName avi == rega) ||
              (getAVDefName avi == configrega) ||
              (getAVDefName avi == crossrega) ||
              (getAVDefName avi == regaligned)

isRegAligned :: AVInst -> Bool
isRegAligned avi = (getAVDefName avi == regaligned)

-- ---------------
-- Identify which instances are registers

-- XXX is there a better way to identify registers?
isRegInst :: AVInst -> Bool
isRegInst avi = (isRegN avi) || (isRegUN avi) || (isRegA avi)

isClockCrossingRegInst :: AVInst -> Bool
isClockCrossingRegInst avi = isRegInst avi && (length(getAVInputClocks avi) > 1)

-- ---------------
-- Names of ports and parameters on primtive registers

clkPortStr, rstnPortStr :: String
clkPortStr    = "CLK"
rstnPortStr   = "RST"

dinPortStr, enPortStr, qoutPortStr :: String
dinPortStr    = "D_IN"
enPortStr     = "EN"
qoutPortStr   = "Q_OUT"

initParamStr, widthParamStr :: String
initParamStr  = "init"
widthParamStr = "width"

-- ---------------
-- Get register ports and parameters

-- find the expression for a port with the given name
findPort :: ErrorHandle -> VName -> AVInst -> AExpr
findPort errh lookupname avi@(AVInst { avi_vmi = vi, avi_iargs = es }) =
    let pairs :: [(VArgInfo, AExpr)]
        pairs = zip (vArgs vi) es
        exprs = [ e | (Port (name,props) mclk mrst, e) <- pairs,
                      name == lookupname ]
    in  case (exprs) of
          [e] -> e
          x ->let msg = (getPosition $ avi_type avi,
                         (EPortNameErrorOnImport
                          (getVNameString $ vName vi)
                          (getVNameString lookupname)))
              in bsErrorUnsafe errh [msg]

-- find the expression for a parameter with the given name
findParam :: VName -> AVInst -> AExpr
findParam lookupname (AVInst { avi_vmi = vi, avi_iargs = es }) =
    let pairs :: [(VArgInfo, AExpr)]
        pairs = zip (vArgs vi) es
        exprs = [ e | (Param name, e) <- pairs,
                      name == lookupname ]
    in  case (exprs) of
          [e] -> e
          x -> internalError ("findParam: " ++ ppReadable (lookupname, pairs))

-- ----------
-- clock and reset

-- The names of the clock and reset ports are hardcoded here.
-- The extraction procedure could be slightly less hardcoded by
-- by looking for PPCLK and PPRSTN properties on the ports.

clkPortName, rstnPortName :: VName
clkPortName = VName clkPortStr
rstnPortName = VName rstnPortStr

getRegClock, getRegReset :: ErrorHandle -> AVInst -> AExpr
getRegClock errh = findPort errh clkPortName
getRegReset errh = findPort errh rstnPortName

-- ----------
-- initialization and width parameters

initParamName, widthParamName :: VName
initParamName = VName initParamStr
widthParamName = VName widthParamStr

getRegInit ,getRegWidth :: AVInst -> AExpr
getRegInit = findParam initParamName
getRegWidth = findParam widthParamName

-- ----------
-- method ports

dinPortName, enPortName, qoutPortName :: VName
dinPortName  = VName dinPortStr
enPortName   = VName enPortStr
qoutPortName = VName qoutPortStr

{-
getRegDIN = findPort dinPortName
getRegEN = findPort enPortName
-}

-- ----------
-- names of the signals attached to the ports

mkDIN, mkEN, mkQOUT :: AVInst -> AId
mkDIN  avi = mkPortName dinPortStr  (promoteAVI avi)
mkEN   avi = mkPortName enPortStr   (promoteAVI avi)
-- When we inline, we now remove the $Q_OUT from the reg name
--mkQOUT avi = mkPortName qoutPortStr (promoteAVI avi)
mkQOUT avi = mkPortNameFromFStr (getIdFString (avi_vname avi)) (promoteAVI avi)

-- XXX need better comment
promoteAVI :: AVInst -> Id
promoteAVI avi = (setIdPosition
                    (getIfcIdPosition (avi_vmi avi))
                    (avi_vname avi))

-- This makes the AId, use vId (or idToVId) to make a VId
mkPortName :: String -> AId -> AId
mkPortName v_port_name v_inst_name =
    let portname_fstr = mkPortNameFStr v_port_name v_inst_name
    in  mkPortNameFromFStr portname_fstr v_inst_name

mkPortNameFromFStr :: FString -> AId -> AId
mkPortNameFromFStr portname_fstr v_inst_name =
    let
        -- the following was copied from vMethId
        -- (is this done in order to carry along properties?)
        portname_id = setIdBase (unQualId v_inst_name) portname_fstr
        --portname_id = mkId noPosition portname_fstr
    in
        portname_id

mkPortNameFStr :: String -> AId -> FString
mkPortNameFStr v_port_name v_inst_name =
    concatFString [getIdFString v_inst_name,
                   fsDollar,
                   mkFString v_port_name]

-- ---------------
-- Given a port name mapping (produced in ARenameIO),
-- update it so that "r$Q_OUT" is shortened to just "r"

updateVerilogNameMapForReg :: AVInst ->
                              [(FString,FString)] -> [(FString,FString)]
updateVerilogNameMapForReg avi ps =
    let oldname = mkPortNameFStr qoutPortStr (avi_vname avi)
        newname = getIdFString (avi_vname avi)
        updPair (a,b) = (a, if (b == oldname) then newname else b)
    in
        map updPair ps

-- ---------------

-- When inlining CReg, we create a Reg in its place.
-- These are functions for the AVInst.

-- XXX AConv throws away the arguments to abstract types
regType :: AType
regType = ATAbstract idVReg []

-- XXX These are in PreStrings
regReadStr, regWriteStr :: String
regReadStr  = "read"
regWriteStr = "write"

-- XXX These are in PreIds, but they're qualified
regReadId, regWriteId :: Position -> Id
regReadId  pos = mkId pos (mkFString regReadStr)
regWriteId pos = mkId pos (mkFString regWriteStr)

-- XXX no position?
regReadResId, regWriteEnId, regWriteArgId :: Id -> Id
regReadResId  i = mkMethId i (regReadId noPosition)  Nothing (MethodResult 1)
regWriteEnId  i = mkMethId i (regWriteId noPosition) Nothing MethodEnable
regWriteArgId i = mkMethId i (regWriteId noPosition) Nothing (MethodArg 1)

regSchedInfo :: SchedInfo Id
regSchedInfo =
    let r = regReadId noPosition -- XXX hopefully the pos doesn't matter
        w = regWriteId noPosition -- XXX
        cfs = [(r,r)]
        sbs = [(r,w)]
        sbrs = [(w,w)]
    in  SchedInfo { methodConflictInfo =
                        MethodConflictInfo cfs sbs [] [] sbrs [] []
                  , rulesBetweenMethods = []
                  , rulesBeforeMethods = []
                  , clockCrossingMethods = []
                  }

-- given a CReg instance, return the associated Reg instance
cregToReg :: AVInst -> AVInst
cregToReg old_avi =
    let
        old_vmi = avi_vmi old_avi

        updVPort new_vn (_, ps) = (new_vn, ps)

        (new_vFields, new_meth_types) =
            let convField (Method nm c r m [] [res] Nothing, ts)
                    | (nm == cregReadId 0)
                    = let nm' = regReadId (getPosition nm)
                          res' = updVPort qoutPortName res
                      in  Just (Method nm' c r m [] [res'] Nothing, ts)
                convField (Method nm c r m [arg] [] (Just en), ts)
                    | (nm == cregWriteId 0)
                    = let nm' = regWriteId (getPosition nm)
                          arg' = updVPort dinPortName arg
                          en' = updVPort enPortName en
                      in  Just (Method nm' c r m [arg'] [] (Just en'), ts)
                convField _ = Nothing
            in  unzip $
                  mapMaybe convField $
                    zip (vFields old_vmi) (avi_meth_types old_avi)

        new_port_types =
            let convPortType (vn, t)
                    | getVNameString vn == cregDINPortStr 0  = Just (VName dinPortStr, t)
                    | getVNameString vn == cregQOUTPortStr 0 = Just (VName qoutPortStr, t)
                    | otherwise = Nothing
            in  M.fromList $
                  mapMaybe convPortType $
                    M.toList (avi_port_types old_avi)

        new_vmi =
            let old_name = vName old_vmi
                new_name | (old_name == cregn)  = regn
                         | (old_name == cregun) = regun
                         | (old_name == crega)  = rega
                         | otherwise = internalError ("aInlineCReg: " ++
                                                      ppReadable old_name)
            in  mkVModInfo new_name
                           (vClk old_vmi)
                           (vRst old_vmi)
                           (vArgs old_vmi)
                           new_vFields
                           regSchedInfo
                           (VPathInfo [])
    in
        AVInst { avi_vname = avi_vname old_avi
               , avi_type = regType
               , avi_user_import = avi_user_import old_avi
               , avi_meth_types = new_meth_types
               , avi_port_types = new_port_types
               , avi_vmi = new_vmi
               , avi_iargs = avi_iargs old_avi
               , avi_iarray = []
               }

-- ==============================
-- Create a Verilog name map

-- For all instantiated submodules, create a mapping of identifiers
-- "inst$methodpart" to the Verilog signal names "inst$vport" which
-- will be connected to the ports of the instantiated module.
-- For example, the map might contain these pairs:
--    [("the_r1$get", "the_r1$Q_OUT")]
--    [("the_r2$set_1", "the_r2$D_IN"), ("the_r2$set", "the_r2$EN")]
--    [("the_arr$sub_1", "the_arr$ADDR_1"),
--     ("the_arr$sub", "the_arr$D_OUT_1"),
--     ("the_arr_1$sub_1", "the_arr$ADDR_2"),
--     ("the_arr_1$sub", "the_arr$D_OUT_2")]

-- XXX consider not generating mappings from a string to itself,
-- XXX to save memory and lookup time

createVerilogNameMap :: Flags -> ASPackage -> M.Map FString FString
createVerilogNameMap flags aspkg =
    let vinsts = aspkg_state_instances aspkg
    in  M.fromList (concatMap (createVerilogNameMapForAVInst flags) vinsts)

-- create a map for one instance
createVerilogNameMapForAVInst :: Flags -> AVInst -> [(FString, FString)]
createVerilogNameMapForAVInst flags avi@(AVInst { avi_vname = inst_id,
                                                  avi_vmi = vminfo }) =
    let -- the default map
        default_map = concatMap (createMapForVMod inst_id) (vFields vminfo)
        -- create a special map for register instance (without $Q_OUT)
        reg_map = updateVerilogNameMapForReg avi default_map
        -- choose which to return
        result = if ((removeReg flags) && (isRegInst avi) && ((not (isClockCrossingRegInst avi)) || (removeCross flags)))
                 then reg_map
                 else default_map
    in  -- trace("result =" ++ (ppReadable result)) $
        result

-- ==============================
-- Clock primitives

syncreg :: VName
syncreg  = VName "SyncRegister"

isSyncReg :: AVInst -> Bool
isSyncReg  avi = (getAVDefName avi == syncreg)

-- ==============================
-- FIFO primitives

fifo1, fifo10, fifo2, fifo20, sizedfifo, sizedfifo0 :: VName
fifo1      = VName "FIFO1"
fifo10     = VName "FIFO10"
fifo2      = VName "FIFO2"
fifo20     = VName "FIFO20"
sizedfifo  = VName "SizedFIFO"
sizedfifo0 = VName "SizedFIFO0"

fifoL1, fifoL10, fifoL2, fifoL20, sizedfifoL, sizedfifoL0 :: VName
fifoL1      = VName "FIFOL1"
fifoL10     = VName "FIFOL10"
fifoL2      = VName "FIFOL2"
fifoL20     = VName "FIFOL20"
sizedfifoL  = VName "SizedFIFOL"
sizedfifoL0 = VName "SizedFIFOL0"

isFIFO :: AVInst -> Bool
isFIFO avi =
    let name = getAVDefName avi
    in  (name == fifo1)      || (name == fifo10)      ||
        (name == fifo2)      || (name == fifo20)      ||
        (name == sizedfifo)  || (name == sizedfifo0)  ||
        (name == fifoL1)     || (name == fifoL10)     ||
        (name == fifoL2)     || (name == fifoL20)     ||
        (name == sizedfifoL) || (name == sizedfifoL0)

isFIFO0 :: AVInst -> Bool
isFIFO0 avi =
    let name = getAVDefName avi
    in  (name == fifo10)      ||
        (name == fifo20)      ||
        (name == sizedfifo0)  ||
        (name == fifoL10)     ||
        (name == fifoL20)     ||
        (name == sizedfifoL0)

-- ============================

-- finding inout connection modules
inoutconnect :: VName
inoutconnect = VName "InoutConnect"

isInoutConnect :: AVInst -> Bool
isInoutConnect avi = getAVDefName avi == inoutconnect

-- ============================
-- Function: createMapForVMod
-- Create AId renaming map based on Verilog port names in a VModInfo
-- i.e. turn in r$get into r$Q_OUT
createMapForVMod :: AId -> VFieldInfo -> [(FString,FString)]
createMapForVMod _ (Clock _) = []
createMapForVMod _ (Reset _) = []
createMapForVMod _ (Inout {}) = []
createMapForVMod inst_id (Method meth_id _ _ mult ins outs me) = -- trace (ppReadable result) $
                                                               result
    where
        result = zip meths_fstr ports_fstr
        (fmeths,fports) = createMapForOneMeth meth_id mult ins outs me
        inst_fstr  = getIdFString inst_id
        addInstId fs = concatFString [inst_fstr, fsDollar, fs]
        meths_fstr = map addInstId fmeths
        ports_fstr = map addInstId fports

-- ---------------

-- For a single method, create two lists:
--   * The Bluespec names for the arguments and RDY/EN
--     (for example, ["set_1","set"] or ["get"])
--     The first items in the list are the arguments, followed by
--     the return value(s) and/or the enable (depending on the type of method).
--   * The Verilog port names corresponding to the Bluespec names
--     (for example, ["D_IN","EN"] or ["Q_OUT"])
-- If the method has multiplicity > 1, then the first list
-- has all of the Bluespec names for the various ports
-- (with meth_<portnum> replacing meth for all of the ids
-- portnum goes from 0..mult - 1 (see mkMethId in ASyntax)
-- the second list then has the Verilog names tagged
-- with port numbers from 1..mult
-- the "method" side of this needs to be synced with
-- mkMethId in ASyntax
-- the two lists should be the same length (this is checked)
createMapForOneMeth :: Id -> Integer ->
                       [VPort] -> [VPort] -> Maybe VPort ->
                       ([FString],[FString])
createMapForOneMeth meth_id mult ins outs me = if check then
                                             -- trace (ppReadable (method_names, verilog_names)) $
                                             (method_names, verilog_names)
                                             else err
    where
      check = length method_names == length verilog_names
      err = internalError ("createMapForOneMeth " ++
                           ppReadable (meth_id, mult, ins, me, outs))
      meth_fstr = getIdFString meth_id

      meth_mult = if mult <= 1 then [meth_fstr]
                  else [ concatFString [meth_fstr, fsUnderscore, mkNumFString n] |
                         n <- [0 .. mult-1] ]

      -- for method "x", make the names "x_ARG_1, x_ARG_2, .." for the ports
      -- make the names x_<port>_ARG_n for multi-ported methods
      method_input_names = [ mkMethArgStr meth_n (toInteger arg_n) |
                             meth_n <- meth_mult, arg_n  <- [1 .. length ins]]
      -- the Verilog port names for the above
      verilog_input_names = map getFStringForVerilogPair ins

      -- names for the output ports
      method_output_names = [ mkMethResStr meth_n (toInteger out_n) |
                              meth_n <- meth_mult, out_n  <- [1 .. length outs]]

      -- the Verilog port names for the above
      verilog_output_names = map getFStringForVerilogPair outs

      -- names for the enable
      (method_enable_names, verilog_enable_name) =
          case (me) of
              Nothing -> ([], [])
              Just p -> (map mkEnableName meth_mult,
                         [getFStringForVerilogPair p])

      mkEnableName fs =  concatFString [fsEnable, fs]

      -- put it all together
      method_names = method_input_names ++
                     method_enable_names ++
                     method_output_names

      verilog_names_pre_mult =
                     verilog_input_names ++
                     verilog_enable_name ++
                     verilog_output_names

      -- handle the multiplicity for verilog names here
      -- note how we go from 1..mult instead of 0..mult-1
      -- as the method side does
      verilog_names = if (mult <= 1)
                      then verilog_names_pre_mult
                      else [concatFString [fs, fsUnderscore, (mkNumFString (toInteger n))] | -- PORT_N
                            fs <- verilog_names_pre_mult,
                            n <- [1..mult]]

-- XXX what is going on here?! can someone add a comment?
getFStringForVerilogPair :: (VName, [VeriPortProp]) -> FString
getFStringForVerilogPair (vname, proplist) =
    let getvns vs = (verilog_cleanup $ getVNameString vs) ++ suffix
        verilog_cleanup = filter isAlphaNum_ . map replace
        isAlphaNum_ c = ((isAlphaNum c) || c == '_')
        replace ' ' = '_'
        replace '?' = 'X'
        replace c = c
        -- XXX inhigh ports don't exist, so we mark them with this string,
        -- XXX which AVerilog looks for
        suffix = if (VPinhigh `elem` proplist) then "_AlwaysEnabled" else ""
    in mkFString (getvns vname)

-- ==============================
-- xLate functions
--

-- For use with the map from "createVerilogNameMap"

xLateIdUsingFStringMap :: M.Map FString FString -> Id -> Id
xLateIdUsingFStringMap fsmap id =
    setIdBase id (xLateFStringUsingFStringMap fsmap (getIdFString id))

xLateFStringUsingFStringMap :: M.Map FString FString -> FString -> FString
xLateFStringUsingFStringMap fsmap fstring =
    M.findWithDefault fstring fstring fsmap

-- ==============================
