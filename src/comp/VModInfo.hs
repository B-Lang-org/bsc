{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
module VModInfo(VModInfo, mkVModInfo,
                vName, vClk, vRst, vArgs, vFields, vSched, vPath,
                VName(..), VPort, VSchedInfo, VMethodConflictInfo,
                VPathInfo(..), VeriPortProp(..),
                VArgInfo(..), isParam, isPort, isClock, isReset, isInout,
                VFieldInfo(..),
                VClockInfo(..), InputClockInf, OutputClockInf,
                VOscPort, VInputGatePort, VOutputGatePort,
                VResetInfo(..), ResetInf, VWireInfo(..),
                getInputClockPorts, getInputResetPorts,
                lookupOutputClockWires, lookupOutputClockPorts,
                lookupInputClockWires,
                lookupOutputResetWire, lookupOutputResetPort,
                lookupInputResetWire,
                lookupIfcInoutWire,
                getOutputClockPortTable, getOutputResetPortTable,
                getVNameString, id_to_vName, id_to_vPort,
                vName_to_id, vPort_to_id,
                getVArgInfoName, getVArgPortClock, getVArgPortReset,
                getVArgInoutClock, getVArgInoutReset,
                getIfcIdPosition,
                str_to_vPort,getVPortString,
                mkNamedEnable,
                mkNamedOutputs,
                mkNamedReady,
                mkNamedInout,
                extractNames
                ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Data.List(partition, nub)
import Data.Maybe(catMaybes)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Generics as Generic

import ErrorUtil
import Id
import IdPrint()
import Position
import SchedInfo
import Util
import Eval(NFData(..), rnf, rnf2, rnf3, rnf4, rnf7)
import PPrint

-- VMODINFO AND SUBSIDIARIES:

-- ===============
-- VName

newtype VName = VName String
        deriving (Show, Ord, Eq, Generic.Data, Generic.Typeable)

instance PPrint VName where
    pPrint _ _ (VName s) = text s

instance NFData VName where
    rnf (VName s) = rnf s

getVNameString :: VName -> String
getVNameString (VName string) = string

-- convert Bluespec identifier to Verilog names
id_to_vName :: Id -> VName
id_to_vName i = VName (getIdBaseString i)

vName_to_id :: VName -> Id
vName_to_id (VName s) = mk_homeless_id s

vPort_to_id :: VPort -> Id
vPort_to_id (VName s, _) = mk_homeless_id s

-- ===============
-- VeriPortProp

-- the order is important for VIOProps ("unused" should come last)
data VeriPortProp = VPreg
                  | VPconst
                  | VPinhigh
                  | VPouthigh
                  | VPclock
                  | VPclockgate
                  | VPreset
                  | VPinout
                  | VPunused
        deriving (Show, Eq, Ord, Generic.Data, Generic.Typeable)

instance NFData VeriPortProp where
    rnf VPreg = ()
    rnf VPconst = ()
    rnf VPinhigh = ()
    rnf VPouthigh = ()
    rnf VPclock = ()
    rnf VPclockgate = ()
    rnf VPreset = ()
    rnf VPinout = ()
    rnf VPunused = ()

instance PPrint VeriPortProp where
    pPrint _ _ VPreg = text "reg"
    pPrint _ _ VPclock = text "clock"
    pPrint _ _ VPconst = text "const"
    pPrint _ _ VPinhigh = text "inhigh"
    pPrint _ _ VPouthigh = text "outhigh"
    pPrint _ _ VPunused = text "unused"
    pPrint _ _ VPreset  = text "reset"
    pPrint _ _ VPinout  = text "inout"
    pPrint _ _ VPclockgate = text "clock gate"


-- ===============
-- VPort

type VPort = (VName, [VeriPortProp])

getVPortString :: VPort -> String
getVPortString (vn,_) = getVNameString vn

id_to_vPort :: Id -> VPort
id_to_vPort i = (id_to_vName i, [])

str_to_vPort :: String -> VPort
str_to_vPort str = (VName str, [])


-- ===============
-- VSchedInfo

type VSchedInfo = SchedInfo Id

type VMethodConflictInfo = MethodConflictInfo Id

-- ===============
-- VPathInfo

newtype VPathInfo = VPathInfo [(VName, VName)]
                  deriving (Show, Ord, Eq, Generic.Data, Generic.Typeable)

instance PPrint VPathInfo where
    pPrint d p (VPathInfo []) =
        s2par "No combinational paths from inputs to outputs"
    pPrint d p (VPathInfo nns) =
        let
            -- function to join paths going to the same output
            joinPaths [] = []
            joinPaths zs@((_,o):_) =
                case (partition ((== o) . snd) zs) of
                    (xs, ys) -> (map fst xs, o) : joinPaths ys

            -- function to display one pair
            ppOne ([i],out) = pPrint d p i <+> text "->" <+> pPrint d p out
            ppOne (ins,out) = text "(" <>
                              sepList (map (pPrint d p) ins) (text ",") <>
                              text ")" <+> text "->" <+> pPrint d p out
        in
            s2par "Combinational paths from inputs to outputs:" $+$
            nest 2 (vcat (map ppOne (joinPaths nns)))

-- for debug output
pShowVPathInfo :: PDetail -> Int -> VPathInfo -> Doc
pShowVPathInfo d p (VPathInfo nns) = pPrint d p nns

instance NFData VPathInfo where
    rnf (VPathInfo nns) = rnf nns


-- ===============
-- VArgInfo

-- describes what an argument to a Verilog module is
-- note that because of Param vs. Port, vNParam is no longer required
-- XXX Port could contain field for the default value?
data VArgInfo = Param VName    -- named module parameter
              -- named module port, with associated clock and reset
              | Port VPort (Maybe Id) (Maybe Id)
              | ClockArg Id    -- named clock
              | ResetArg Id    -- named reset
              -- named module inout, with associated clock and reset
              | InoutArg VName (Maybe Id) (Maybe Id)
              deriving (Show, Ord, Eq, Generic.Data, Generic.Typeable)

isParam :: VArgInfo -> Bool
isParam (Param {}) = True
isParam _ = False

isPort :: VArgInfo -> Bool
isPort (Port {}) = True
isPort _ = False

isClock :: VArgInfo -> Bool
isClock (ClockArg {}) = True
isClock _ = False

isReset :: VArgInfo -> Bool
isReset (ResetArg {}) = True
isReset _ = False

isInout :: VArgInfo -> Bool
isInout (InoutArg {}) = True
isInout _ = False

getVArgInfoName :: VArgInfo -> Id
getVArgInfoName (Param vn)    = vName_to_id vn
getVArgInfoName (Port vp _ _) = vName_to_id (fst vp)
getVArgInfoName (ClockArg i)  = i
getVArgInfoName (ResetArg i)  = i
getVArgInfoName (InoutArg vn _ _) = vName_to_id vn

getVArgPortClock :: VArgInfo -> Maybe Id
getVArgPortClock (Port _ mclk _) = mclk
getVArgPortClock _ = internalError ("getVArgPortClock: not a port")

getVArgPortReset :: VArgInfo -> Maybe Id
getVArgPortReset (Port _ _ mrst) = mrst
getVArgPortReset _ = internalError ("getVArgPortReset: not a port")

-- XXX do these need to be separate from the Port versions?
getVArgInoutClock :: VArgInfo -> Maybe Id
getVArgInoutClock (InoutArg _ mclk _) = mclk
getVArgInoutClock _ = internalError ("getVArgInoutClock: not an inout")

getVArgInoutReset :: VArgInfo -> Maybe Id
getVArgInoutReset (InoutArg _ _ mrst) = mrst
getVArgInoutReset _ = internalError ("getVArgInoutReset: not an inout")

instance NFData VArgInfo where
    rnf (Param x) = rnf x
    rnf (Port x1 x2 x3) = rnf3 x1 x2 x3
    rnf (ClockArg x) = rnf x
    rnf (ResetArg x) = rnf x
    rnf (InoutArg x1 x2 x3) = rnf3 x1 x2 x3

instance PPrint VArgInfo where
    pPrint d p (Param x) = text "param " <> pPrint d 0 x <> text ";"
    pPrint d p (Port x mclk mrst) =
        text "port " <> pPrint d 0 x <+>
        ppMClk d mclk <+> ppMRst d mrst <>
        text ";"
    pPrint d p (ClockArg x) = text "clockarg " <> pPrint d p x <> text ";"
    pPrint d p (ResetArg x) = text "resetarg " <> pPrint d p x <> text ";"
    pPrint d p (InoutArg x mclk mrst) =
        text "inoutarg " <> pPrint d 0 x <+>
        ppMClk d mclk <+> ppMRst d mrst <>
        text ";"

ppMClk :: PDetail -> Maybe Id -> Doc
ppMClk d mclk =
    let clk = case mclk of
                  Nothing -> text "no_clock"
                  Just c  -> pPrint d 0 c
    in  text "clocked_by (" <> clk <> text ")"

ppMRst :: PDetail -> Maybe Id -> Doc
ppMRst d mrst =
    let rst = case mrst of
                  Nothing -> text "no_reset"
                  Just r  -> pPrint d 0 r
    in  text "reset_by (" <> rst <> text ")"


-- ===============
-- VFieldInfo

-- XXX why does the VFieldInfo not contain a ready signal?
data VFieldInfo = Method { vf_name   :: Id, -- method name
                           vf_clock  :: (Maybe Id), -- optional clock
                           -- optional because the method may be combinational
                           vf_reset  :: (Maybe Id), -- optional reset
                           -- optional because the method may be independent of a reset signal
                           vf_mult   :: Integer, -- multiplicity
                           vf_inputs :: [VPort],
                           vf_outputs:: [VPort],
                           vf_enable :: Maybe VPort }
                | Clock { vf_name :: Id } -- output clock name
                                           -- connection information is in the ClockInfo
                | Reset { vf_name :: Id } -- output reset name
                                           -- connection information is in the ResetInfo
                | Inout { vf_name :: Id, -- output inout name
                          vf_inout :: VName,
                          vf_clock :: (Maybe Id), -- optional clock
                          vf_reset :: (Maybe Id) } -- optional reset
                deriving (Show, Ord, Eq, Generic.Data, Generic.Typeable)

instance HasPosition VFieldInfo where
  getPosition (Method { vf_name = n }) = getPosition n
  getPosition (Clock i)                 = getPosition i -- or noPosition?
  getPosition (Reset i)                 = getPosition i -- or noPosition?
  getPosition (Inout { vf_name = n })  = getPosition n

instance NFData VFieldInfo where
    rnf (Method x1 x2 x3 x4 x5 x6 x7) = rnf7 x1 x2 x3 x4 x5 x6 x7
    rnf (Clock x) = rnf x
    rnf (Reset x) = rnf x
    rnf (Inout x1 x2 x3 x4) = rnf4 x1 x2 x3 x4

instance PPrint VFieldInfo where
    pPrint d p (Method n c r m i o e) =
      text "method " <> pouts o <> pPrint d p n <> pmult m <>
      pins i <> pena e <+> ppMClk d c <+> ppMRst d r <>
      text ";"
        where pouts [] = empty
              pouts [po] = pPrint d p po
              pouts o  = text "(" <> sepList (map (pPrint d p) o) (text ",") <> text ")"
              pmult 1 = empty
              pmult n = text "[" <> pPrint d p n <> text "]"
              pins [] = empty
              pins i  = text "(" <> sepList (map (pPrint d p) i) (text ",") <> text ")"
              pena Nothing = empty
              pena (Just en) = text " enable (" <> pPrint d p en <> text ")"
    pPrint d p (Clock i) = text "clock " <> pPrint d p i <> text ";"
    pPrint d p (Reset i) = text "reset " <> pPrint d p i <> text ";"
    pPrint d p (Inout n port c r) =
        text "inout " <> pPrint d p n <+>
        text "(" <> pPrint d p port <> text ")" <+>
        ppMClk d c <+> ppMRst d r <> text ";"


-- ===============
-- VClockInfo

-- describes the clocks imported by a module
type InputClockInf = (Id, Maybe (VOscPort, VInputGatePort))

-- describes the clocks exported by a module
type OutputClockInf = (Id, Maybe (VOscPort, VOutputGatePort))

-- no VeriPortProp needed, so we use VName and not VPort
type VOscPort = VName

-- gate port for input clocks
-- Either there is no port, in which case the boolean indicates
-- whether the gate is assumed True or is unneeded, or there is gate port.
type VInputGatePort = Either Bool VName

-- gate port for output clocks
-- Either there is no port, in which case users should assume a value True,
-- or there is a port, and we annotate whether it is "outhigh" with a
-- port property (VPouthigh)
type VOutputGatePort = Maybe VPort

data VClockInfo = ClockInfo {
                 -- named list of input clocks
                 input_clocks :: [InputClockInf],
                 -- named list of output clocks
                 output_clocks :: [OutputClockInf],
                 -- edges in the ancestor relationships (transitive)
                 -- first clock is parent, second is child
                 ancestorClocks :: [(Id, Id)],
                 -- other sibling relationships
                 -- transitive (but often trumped by ancestry)
                 -- method calls are permitted across sibling relationships
                 -- but *both* gate conditions must be enforced
                 siblingClocks :: [(Id, Id)] }
                deriving (Show, Ord, Eq, Generic.Data, Generic.Typeable)

-- Gets information needed to construct the signals from an output clock clock.
-- If there is no gate port or if the port is outhigh, Nothing is returned.
-- Otherwise, Just the port name is returned.
lookupOutputClockWires :: Id -> VModInfo -> (VName, Maybe VName)
lookupOutputClockWires i vmi =
    case (lookupOutputClock i vmi) of
        -- no gating signal
        (osc_vn, Nothing) -> (osc_vn, Nothing)
        -- outhigh gate port
        (osc_vn, Just (_, pprops))
            | (VPouthigh `elem` pprops) -> (osc_vn, Nothing)
        -- gate port
        (osc_vn, Just (gate_vname,_)) -> (osc_vn, Just gate_vname)

-- Like lookupOutputClockVNames, except that outhigh ports are included
lookupOutputClockPorts :: Id -> VModInfo -> (VName, Maybe VPort)
lookupOutputClockPorts i vmi =
    case (lookupOutputClock i vmi) of
        -- no gating signal
        (osc_vn, Nothing) -> (osc_vn, Nothing)
        -- gate port
        (osc_vn, Just gate_vp) -> (osc_vn, Just gate_vp)

lookupOutputClock :: Id -> VModInfo -> (VOscPort, VOutputGatePort)
lookupOutputClock i vmi =
    case (lookup i (output_clocks (vClk vmi))) of
        Nothing ->
            internalError ("lookupOutputClock unknown clock " ++
                           ppReadable i ++ ppReadable (vClk vmi))
        Just Nothing ->
            internalError ("lookupOutputClock unconnected output clock" ++
                           ppReadable i ++ ppReadable (vClk vmi))
        Just (Just ci) -> ci

-- returns nothing if there are no wires to hook up
lookupInputClockWires :: Id -> VModInfo -> Maybe (VName, Maybe VName)
lookupInputClockWires i vmi =
    case (lookupInputClock i vmi) of
        -- no gating signal
        Just (osc_vn, Left _) -> Just (osc_vn, Nothing)
        -- gate port
        Just (osc_vn, Right gate_vname) -> Just (osc_vn, Just gate_vname)
        Nothing -> Nothing

-- returns nothing if the input clock is unconnected
lookupInputClock :: Id -> VModInfo -> Maybe (VOscPort, VInputGatePort)
lookupInputClock i vmi =
    case (lookup i (input_clocks (vClk vmi))) of
        Nothing ->
            internalError ("lookupInputClock unknown clock " ++
                           ppReadable i ++ ppReadable (vClk vmi))
        Just mci -> mci

-- Used in AState to create defs for output clock ports
-- So this includes gate ports which are "outhigh", since they have to be
-- generated.
getOutputClockPortTable :: VClockInfo ->
                           M.Map Id (VOscPort, VOutputGatePort)
getOutputClockPortTable ClockInfo { output_clocks = ci } =
    M.fromList [(i, ports) | (i, Just ports) <- ci ]

-- Used in APaths, to sanity check that the port names in AAbstractInfo
-- match the port names declared for input clocks in VClockInfo
getInputClockPorts :: VClockInfo -> [VName]
getInputClockPorts (ClockInfo { input_clocks = clocks }) =
    osc_vnames ++ gate_vnames
  where connected_clocks = catMaybes (map snd clocks)
        osc_vnames = map fst connected_clocks
        gate_vnames = snd $ separate (map snd connected_clocks)

instance NFData VClockInfo where
    rnf (ClockInfo x1 x2 x3 x4) = rnf4 x1 x2 x3 x4

instance HasPosition VClockInfo where
  getPosition (ClockInfo { output_clocks = ((id,_):_)}) = getPosition id
  getPosition (ClockInfo { input_clocks = ((id,_):_)}) = getPosition id
  getPosition _ = noPosition

instance PPrint VClockInfo where
    pPrint d p (ClockInfo in_cs out_cs as ss) =
        vcat (map pOutCInf out_cs ++
              map pInCInf in_cs ++
              map pAnc as ++
              map pSib ss)
        where
              pOutCInf (i,mc) = text "clock " <> pPrint d 0 i <>
                                text "(" <> pOutMClk mc <> text ");"
              pOutMClk Nothing = empty
              pOutMClk (Just (vn, mg)) = pPrint d 0 vn <> pOutMGate mg
              pOutMGate Nothing = empty
              pOutMGate (Just (vn, vpps)) =
                  text ", " <> pPortProps vpps <> pPrint d 0 vn
              pPortProps [] = empty
              pPortProps (vp:vpps) =
                  text "{-" <> pPrint d 0 vp <> text "-} " <> pPortProps vpps

              pInCInf (i,mc) = text "clock " <> pPrint d 0 i <>
                               text "(" <> pInMClk mc <> text ");"
              pInMClk Nothing = empty
              pInMClk (Just (vn, mg)) = pPrint d 0 vn <> pInMGate mg
              pInMGate (Left True)  = text ", {-inhigh-}"
              pInMGate (Left False) = text ", {-unused-}"
              pInMGate (Right vn)   = text ", " <> pPrint d 0 vn

              pAnc (i,j) = text "ancestor (" <> pPrint d 0 i <> text ", " <>
                           pPrint d 0 j <> text ");"
              pSib (i,j) = text "sibling (" <> pPrint d 0 i <> text ", " <>
                           pPrint d 0 j <> text ");"


-- ===============
-- VResetInfo

-- reset name, Verilog port (optional), clock (optional)
type ResetInf = (Id, (Maybe VName, Maybe Id))

-- basic information on reset signals
-- more information to be added (sync/async, clock relationships, etc.)
data VResetInfo = ResetInfo {
                   input_resets  :: [ResetInf],
                   output_resets :: [ResetInf]
                  }
  deriving(Show, Ord, Eq, Generic.Data, Generic.Typeable)

-- Gets info needed to construct the signals from an output reset.
-- (Currently the same as getting the port name.)
lookupOutputResetWire :: Id -> VModInfo -> VName
lookupOutputResetWire = lookupOutputResetPort

lookupOutputResetPort :: Id -> VModInfo -> VName
lookupOutputResetPort = lookupOutputReset -- no interpretation needed

lookupOutputReset :: Id -> VModInfo -> VName
lookupOutputReset i vmi =
    case (lookup i (output_resets (vRst vmi))) of
        Nothing ->
            internalError ("lookupOutputReset unknown reset " ++
                           ppReadable i ++ ppReadable (vRst vmi))
        Just (Nothing, _) ->
            internalError ("lookupOutputReset unconnected output reset" ++
                           ppReadable i ++ ppReadable (vRst vmi))
        Just (Just ri, _) -> ri

-- returns nothing if there is no wire to hook up
lookupInputResetWire :: Id -> VModInfo -> Maybe VName
lookupInputResetWire = lookupInputReset -- no interpretation needed

-- returns nothing if the input reset is unconnected
lookupInputReset :: Id -> VModInfo -> Maybe VName
lookupInputReset i vmi =
    case (lookup i (input_resets (vRst vmi))) of
        Nothing ->
            internalError ("lookupInputReset unknown reset " ++
                           ppReadable i ++ ppReadable (vRst vmi))
        Just (mri, _) -> mri

-- Used in AState to create defs for output reset ports
getOutputResetPortTable :: VResetInfo -> M.Map Id VName
getOutputResetPortTable ResetInfo { output_resets = out_rinfos } =
    M.fromList [(i, vn) | (i, (Just vn, _)) <- out_rinfos]

instance PPrint VResetInfo where
    pPrint d p (ResetInfo in_rs out_rs) = vcat (map pRInf (out_rs ++ in_rs))
      where t = text
            pRInf (i,(mn,mc)) =
                t"reset " <> pPrint d p i <>
                t"(" <> pMRst mn <> t")" <+>
                t"clocked_by(" <> pMClk mc <> t");"
            pMRst Nothing  = empty
            pMRst (Just n) = pPrint d p n
            pMClk Nothing  = t"no_clock"
            pMClk (Just c) = pPrint d p c

-- Used in APaths, to sanity check that the port names in AAbstractInfo
-- match the port names declared for input resets in VResetInfo
getInputResetPorts :: VResetInfo -> [VName]
getInputResetPorts (ResetInfo { input_resets = in_resets }) =
    catMaybes (map (fst . snd) in_resets)

instance NFData VResetInfo where
  rnf (ResetInfo x1 x2) = rnf2 x1 x2

-- ===============
-- Inout

-- There is no VInoutInfo, but AConv needs to be able to lookup a port name
-- the same as it does for clocks and reset.

lookupIfcInoutWire :: Id -> VModInfo -> VName
lookupIfcInoutWire i vmi =
    let fis = vFields vmi
        vports = [ p | f@(Inout { vf_inout = p }) <- fis,
                       (vf_name f == unQualId i) ]
    in  case vports of
            [p] -> p
            _ -> internalError ("lookupIfcInoutWire: " ++
                                ppReadable (i,vports))

-- ===============
-- VModInfo

data VModInfo = VModInfo {
        -- name of Verilog module to use
        vName  :: VName,
        vClk   :: VClockInfo,
        vRst   :: VResetInfo,
        vArgs  :: [VArgInfo],
        vFields :: [VFieldInfo],
        vSched :: VSchedInfo,
        vPath  :: VPathInfo
        }
        deriving (Show, Ord, Eq, Generic.Data, Generic.Typeable)

mkVModInfo :: VName -> VClockInfo -> VResetInfo ->
              [VArgInfo] -> [VFieldInfo] ->
              VSchedInfo -> VPathInfo -> VModInfo
mkVModInfo vName vClk vRst
           vArgs vFields
           vSched vPath | check = vm
                        | otherwise = internalError ("VModInfo: " ++ ppReadable vm ++
                                                     ppReadable sched_pairs ++
                                                     ppReadable meth_pairs)

 where vm = VModInfo vName vClk vRst vArgs vFields vSched vPath
       -- ----------
       -- check the method conflict info for consistency and completeness
       -- XXX check the rest of the SchedInfo fields?

       vMethConf = methodConflictInfo vSched

       check = -- every pair is accounted for
               S.fromList sched_pairs == S.fromList meth_pairs &&
               -- no pair has more than one annotation
               length sched_pairs == length meth_pairs
       -- remove duplicates within a commutative annotation set
       -- e.g. (a, b) CF (a, b) ==> (a, a) (a, b) (b, b)
       -- NOT  (a, b) CF (a, b) ==> (a, a) (a, b) (b, a) (a, b)
       cleanup = fastNub . (map ordPair)
       sched_pairs = map ordPair $
                     (cleanup (sCF vMethConf)) ++ sSB vMethConf ++
                     (cleanup (sP  vMethConf)) ++ sSBR vMethConf ++
                     (cleanup (sC  vMethConf)) ++ me_pairs ++ ext_pairs
       ext_pairs  = selfPairs (sEXT vMethConf)
       -- might have duplicates if a method is annotated ME with itself
       me_pairs   = nub $ concatMap allPairs (sME vMethConf)
       meth_pairs = map ordPair $ uniquePairs meths ++ selfPairs meths
       meths      = [ n | Method { vf_name = n } <- vFields ]

{-
-- This is presumably for debugging output?
pePrint d p v = text $ concat [
            "VModInfo {vName = ", show (vName v),
            ", vClk = ", show (vClk v),
            ", vRst = ", show (vRst v),
            ", vArgs = ", show (vArgs v),
            ", vFields = ", show (vFields v),
            ", vSched = VSchedInfo {sCF = ", sit re_id2 (sCF . vSched),
                ", sSB = ", sit re_id2 (sSB . vSched),
            ", vPath = ", show (vPath v),
            "}}" ]
    where
        sit a b = "[" ++ intercalate "," (map a (b v)) ++ "]"
{ -
        re_id (a, b, c) =
                "(" ++ getIdString a
                ++ "," ++ show b
                ++ "," ++ show c
                ++ ")"
- }
        re_id2 (a, b) = "(" ++ getIdString a ++ "," ++ getIdString b ++ ")"
-}

instance PPrint VModInfo where
    pPrint d p v = pparen True
        (sep
            [text "VModInfo",
            pPrint d 10 (vName v),
            pPrint d 10 (vClk v),
            pPrint d 10 (vRst v),
            pPrint d 10 (vArgs v),
            pPrint d 10 (vFields v),
            pPrint d 10 (vSched v),
            pShowVPathInfo d 10 (vPath v)])

instance NFData VModInfo where
    rnf x@(VModInfo x1 x2 x3 x4 x5 x6 x7) = rnf7 x1 x2 x3 x4 x5 x6 x7


-- ===============
-- VWireInfo

-- data that needs to be piped from the evaluator to wrapper generation
data VWireInfo = WireInfo {
                  wClk  :: VClockInfo,
                  wRst  :: VResetInfo,
                  wArgs :: [VArgInfo]
                 } deriving (Eq, Show, Generic.Data, Generic.Typeable)


instance NFData VWireInfo where
  rnf (WireInfo clk rst args) = rnf3 clk rst args

instance PPrint VWireInfo where
  pPrint d p (WireInfo clk rst args) =
    text "clock info " <+> pPrint d p clk $+$
    text "reset info " <+> pPrint d p rst $+$
    text "arg info "   <+> pPrint d p args


-- #############################################################################
-- #
-- #############################################################################

getIfcIdPosition :: VModInfo -> Position
getIfcIdPosition (VModInfo _ clk _ _ [] _ _) = getPosition clk
getIfcIdPosition (VModInfo mod_name clk reset args fields schedule path)
                                             = getPosition fields

-- #############################################################################
-- #
-- #############################################################################

-- The name is changed to keep the position information from the base id.
mkNamedEnable :: VFieldInfo -> Id
mkNamedEnable vfi = if (newStr == "") then baseid else setIdBaseString baseid newStr
    where  baseid = mkEnableId (vf_name vfi)
           newStr = maybe ""  getVPortString (vf_enable vfi)

mkNamedOutputs :: VFieldInfo -> [Id]
mkNamedOutputs vfi = map (setIdBaseString baseid) newStrs
    where  baseid = (vf_name vfi)
           newStrs = map getVPortString (vf_outputs vfi)

-- VFieldInfo does not have a ready field, so we just use the default construction for the ready signal.
-- in aState we merge method and RDY_method to do the right thing.
mkNamedReady :: VFieldInfo -> Id
mkNamedReady vfi = baseid -- if (newStr == "") then baseid else setIdBaseString baseid newStr
    where  baseid = mkRdyId (vf_name vfi)

mkNamedInout :: VFieldInfo -> Id
mkNamedInout vfi = setIdBaseString baseid newStr
    where  baseid = (vf_name vfi)
           newStr = getVNameString (vf_inout vfi)

---------------------------   Name extraction from VFieldInfo
-- extract possible port Ids from a VField Info
-- return value  is result, ready, enable
extractNames :: VFieldInfo -> ([Id], Id, Id )
extractNames vfi = (result, ready, enable)
    where result = mkNamedOutputs vfi
          ready  = mkNamedReady vfi
          enable = mkNamedEnable vfi
