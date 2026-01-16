{-# LANGUAGE CPP #-}
module SimCCBlock( SBId
                 , SBMap
                 , SimCCBlock(..)
                 , SimCCSched(..)
                 , SimCCClockGroup(..)
                 , SimCCReset(..)
                 , SimCCGateInfo
                 , SimCCFn(..)
                 , SimCCFnStmt(..)
                 , StmtConv
                 , StmtsConv
                 , ConvState(..)
                 , SBFnSet
                 , initialState
                 , mkResetFnName
                 , mkSetClkFnName
                 , mkGateAssign
                 , mkGateConst
                 , mkLiteralName
                 , mkStringLiteralName
                 , simCCBlockToClassDeclaration
                 , simCCBlockToClassDefinition
                 , simCCScheduleToFunctionDefinition
                 , moduleType
                 , clockType
                 , get_rule_fns
                 , get_method_fns
                 , defs_written
                 , defs_read
                 , lookupSB
                 , isPrimBlock
                 , primBlocks
                 , isWideDef
                 , adjustInstQuals
                 , pfxModel
                 , pfxMod
                 , pfxInst
                 , pfxPort
                 , pfxMeth
                 , renameIds
                 ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Id
import Prim
import ASyntax
import ASyntaxUtil
import SimDomainInfo(DomainId)
import Wires(ClockDomain, noClockDomain, writeClockDomain)
import VModInfo(VName(..), vName_to_id)
import CCSyntax
import ForeignFunctions
import SimPrimitiveModules
import qualified Data.Map as M
import qualified Data.Set as S
import IntLit
import IntegerUtil(aaaa)
import PPrint hiding (char, int)
import Util(itos, headOrErr, initOrErr, lastOrErr, unconsOrErr,
            snd3, makePairs, concatMapM)
import Eval
import ErrorUtil(internalError)

import Data.Maybe
import Data.List(partition, intersperse, intercalate, nub, sortBy, genericDrop)
import Data.List.Split(wordsBy)
import Numeric(showHex)
import Control.Monad(when)
import Control.Monad.State(State, gets, modify)
import Data.Char(toLower)
import qualified Data.Map as Map

-- import Debug.Trace

type SBId  = Int
type SBMap = M.Map SBId SimCCBlock

-- Lookup an SBId in an SBMap, generating an error for an unknown id
lookupSB :: SBMap -> SBId -> SimCCBlock
lookupSB sb_map sbid =
  case M.lookup sbid sb_map of
     (Just sb) -> sb
     Nothing   -> internalError ("Unknown SBId: " ++ (show sbid))

-- Get a C++ type combinator for a SimCCBlock with specified arguments
moduleType :: SimCCBlock -> [AExpr] -> (CCFragment -> CCFragment)
moduleType sb args = userType (pfxMod ++ (fst (sb_naming_fn sb args)))

-- Group rules/methods by domains
type SBFnSet = (Maybe ClockDomain, [(AId, SimCCFn)])

-- A SimCCBlock represents a class that implements some subset
-- of the simulation logic for a module.  Typically, there is
-- a SimCCBlock that implements the fast module core, and other
-- SimCCBlocks which layer over it to compute values for debug
-- visibility.
data SimCCBlock =
  SimCCBlock { sb_id :: SBId                       -- unique identifier
             , sb_name :: String                   -- block name
             , sb_naming_fn :: NamingFn            -- module naming function
             , sb_domains :: [ClockDomain]         -- clock domains
             , sb_state :: [(SBId,AId,[AExpr])]    -- sub-modules
             , sb_parameters :: [(AType,AId,Bool)] -- instantiation parameters
             , sb_resetDefs :: [(AType,AId)]       -- reset values
             -- method enable, argument and return value ports
             , sb_methodPorts :: [(AType,AId,VName)]
             , sb_publicDefs :: [(AType,AId)]      -- defs available outside
             , sb_privateDefs :: [(AType,AId)]     -- defs private to the block
             , sb_rules :: [SBFnSet]               -- functions for rules
             , sb_methods :: [SBFnSet]             -- functions for methods
             , sb_resets :: [SimCCFn]              -- reset functions
             -- defs which receive values from AV tasks
             , sb_taskDefs :: [AId]
             -- resets from submods paired with the Id of the submod
             -- and the output reset Id
             -- (for calling 'set_rst_fn' on the submod)
             , sb_resetSources :: [(AId,(AId, AId))]
             -- resets coming in as instantiation arguments
             , sb_inputResets :: [AId]
             -- resets output in the module's interface
             , sb_outputResets :: [AId]
             -- clock input ports
             , sb_inputClocks :: [(AId,ClockDomain)]
             -- clock gate numbering
             , sb_gateMap :: [AExpr]  -- numbering is [0..]
             }

instance Eq SimCCBlock where
  a == b = and [ (sb_id a) == (sb_id b)
               , (sb_name a) == (sb_name b)
               , (sb_domains a) == (sb_domains b)
               , (sb_state a) == (sb_state b)
               , (sb_parameters a) == (sb_parameters b)
               , (sb_resetDefs a) == (sb_resetDefs b)
               , (sb_methodPorts a) == (sb_methodPorts b)
               , (sb_publicDefs a) == (sb_publicDefs b)
               , (sb_privateDefs a) == (sb_privateDefs b)
               , (sb_rules a) == (sb_rules b)
               , (sb_methods a) == (sb_methods b)
               , (sb_resets a) == (sb_resets b)
               , (sb_taskDefs a) == (sb_taskDefs b)
               , (sb_resetSources a) == (sb_resetSources b)
               , (sb_inputResets a) == (sb_inputResets b)
               , (sb_outputResets a) == (sb_outputResets b)
               , (sb_inputClocks a) == (sb_inputClocks b)
               , (sb_gateMap a) == (sb_gateMap b)
               ]

instance Show SimCCBlock where
  show sb = let fields = [ show (sb_id sb)
                         , show (sb_name sb)
                         , show (sb_domains sb)
                         , show (sb_state sb)
                         , show (sb_parameters sb)
                         , show (sb_resetDefs sb)
                         , show (sb_methodPorts sb)
                         , show (sb_publicDefs sb)
                         , show (sb_privateDefs sb)
                         , show (sb_rules sb)
                         , show (sb_methods sb)
                         , show (sb_resets sb)
                         , show (sb_taskDefs sb)
                         , show (sb_resetSources sb)
                         , show (sb_inputResets sb)
                         , show (sb_outputResets sb)
                         , show (sb_inputClocks sb)
                         , show (sb_gateMap sb)
                         ]
            in "SimCCBlock {" ++ intercalate ", " fields ++ "}"

get_rule_fns :: SimCCBlock -> [SimCCFn]
get_rule_fns sb = map snd (concatMap snd (sb_rules sb))

get_method_fns :: SimCCBlock -> [SimCCFn]
get_method_fns sb = map snd (concatMap snd (sb_methods sb))

-- A SimCCFn is a named function (with arguments) and a sequence
-- of statements consisting of assignments to either local defs or
-- defs in a SimCCBlock.  The statements in the SimCCFn body are ordered
-- to preserve parallel update semantics.
data SimCCFn = SimCCFn { sf_name    :: String         -- function name
                       , sf_args    :: [(AType,AId)]  -- function arguments
                       , sf_retType :: Maybe AType    -- return type
                       , sf_body    :: [SimCCFnStmt]  -- function body
                       }
  deriving (Eq, Show)

data SimCCFnStmt = -- Bool is whether the var is a port (else a def)
                   SFSDef Bool (AType,AId) (Maybe AExpr) -- declare local var
                 -- Bool is whether the var is a port (else a def)
                 | SFSAssign Bool AId AExpr             -- var = expr    OR
                                                        -- var = vMethod(...)
                 | SFSAction AAction                    -- aMethod(...)
                 -- Bool is whether the var is a port (else a def)
                 -- AType is for assigning an undet value when the method/task is not called
                 | SFSAssignAction Bool AId AAction AType  -- var = avMethod(...)
                 | SFSRuleExec ARuleId                  -- rule()
                 | SFSCond AExpr [SimCCFnStmt] [SimCCFnStmt]  -- if cond ...
                 -- calls corresponding to BSV methods
                 | SFSMethodCall AId AId [AExpr]        -- obj.meth(args)
                 -- calls to reset/clock functions
                 | SFSFunctionCall AId String [AExpr]   -- obj.func(args)
                 | SFSResets [SimCCFnStmt]              -- if (reset) ...
                 | SFSReturn (Maybe AExpr)              -- return OR return e
                 | SFSOutputReset AId AExpr
                       -- calls the resetFn of the parent for the output reset
                       -- with the expr as the reset value
  deriving (Eq, Ord, Show)


isReturn :: SimCCFnStmt -> Bool
isReturn (SFSReturn _) = True
isReturn _             = False

-- List of Ids (in raw form) which are written in a function.
-- Since both defs and ports can be written, and they are in separate
-- namespaces, the Ids are returned as a pair, with a boolean indicating
-- which namespace (True for ports)
defs_written :: SimCCFnStmt -> [(Bool, AId)]
defs_written (SFSDef isPort (_,aid) (Just _)) = [(isPort, aid)]
defs_written (SFSAssign isPort aid _)         = [(isPort, aid)]
defs_written (SFSAssignAction isPort aid _ _) = [(isPort, aid)]
defs_written (SFSCond _ ts fs)                = (concatMap defs_written ts) ++
                                                (concatMap defs_written fs)
defs_written (SFSResets rs)                   = concatMap defs_written rs
defs_written _                                = []

-- List of Ids (in raw form) which are read in a function.
-- This does not distinguish reads of ports from reads of defs!
defs_read :: SimCCFnStmt -> [AId]
defs_read (SFSDef _ _ (Just e))      = aVars e
defs_read (SFSAssign _ _ e)          = aVars e
defs_read (SFSAction act)            = aVars act
defs_read (SFSAssignAction _ _ act _) = aVars act
defs_read (SFSCond e ts fs)          = (aVars e) ++
                                       (concatMap defs_read ts) ++
                                       (concatMap defs_read fs)
defs_read (SFSMethodCall _ _ args)   = concatMap aVars args
defs_read (SFSFunctionCall _ _ args) = concatMap aVars args
defs_read (SFSResets stmts)          = concatMap defs_read stmts
defs_read (SFSReturn (Just e))       = aVars e
defs_read (SFSOutputReset _ e)       = aVars e
defs_read _                          = []

-- Rename the Ids in a SimCCFnStmt based on an Id map
mapId :: Map.Map Id Id -> Id -> Id
mapId idmap i = Map.findWithDefault i i idmap

mapExpr :: Map.Map Id Id -> AExpr -> AExpr
mapExpr idmap e = exprMap fn e
  where fn (ASDef t i) = Just (ASDef t (mapId idmap i))
        fn expr        = Nothing

mapAct ::  Map.Map Id Id -> AAction -> AAction
mapAct idmap act = mapAExprs (exprMap fn) act
  where fn (ASDef t i) = Just (ASDef t (mapId idmap i))
        fn expr        = Nothing

renameIds :: Map.Map Id Id -> SimCCFnStmt -> SimCCFnStmt
renameIds m (SFSDef b (t,i) Nothing) = SFSDef b (t, mapId m i) Nothing
renameIds m (SFSDef b (t,i) (Just e)) = SFSDef b (t, mapId m i) (Just (mapExpr m e))
renameIds m (SFSAssign b i e) = SFSAssign b (mapId m i) (mapExpr m e)
renameIds m (SFSAction act) = SFSAction (mapAct m act)
renameIds m (SFSAssignAction b i act t) = SFSAssignAction b (mapId m i) (mapAct m act) t
renameIds m (SFSCond e ts es) = SFSCond (mapExpr m e)
                                        (map (renameIds m) ts)
                                        (map (renameIds m) es)
renameIds m (SFSMethodCall o mid args) = SFSMethodCall (mapId m o) mid (map (mapExpr m) args)
renameIds m (SFSFunctionCall o fn args) = SFSFunctionCall (mapId m o) fn (map (mapExpr m) args)
renameIds m (SFSResets ss) = SFSResets (map (renameIds m) ss)
renameIds m (SFSReturn (Just e)) = SFSReturn (Just (mapExpr m e))
renameIds m (SFSOutputReset i e) = SFSOutputReset (mapId m i) (mapExpr m e)
renameIds _ s = s

-- A SimCCSched pairs a clock edge with the SimCCFns that should be
-- executed on the edge and possibly also after the edge.
data SimCCSched =
  SimCCSched { sched_clock :: AExpr    -- the clock for the schedule
             , sched_posedge :: Bool   -- for the posedge of the clock?
             , sched_fn :: SimCCFn     -- the schedule function definition
             , sched_after_fn :: Maybe SimCCFn   -- sched fn after edge
             }
  deriving (Eq, Show)


-- A SimCCClockGroup represents a group of per-instance clocks
-- that all refer to a single clock by a canonical name
data SimCCClockGroup =
  SimCCClockGroup { grp_canonical :: AClock
                  , grp_instances :: [DomainId]
                  }
  deriving (Eq, Show)

-- A SimCCReset represents a reset function along with the information
-- needed to register the reset function at run-time.
data SimCCReset =
  SimCCReset { rst_number    :: Integer
             , rst_port      :: Maybe (String, String)
             , rst_function  :: SimCCFn
             }
  deriving (Eq, Show)

-- SimCCGateInfo is a list of the gate sources for each numbered gate
-- of an instance.  A gate source is either a constant boolean value
-- or a port on a primitive module, represented by a qualified Id.
type SimCCGateInfo = [(String, [(Int, Either Bool AId)])]

-- the name for the reset method, for a particular reset name
mkResetFnName :: AId -> String
mkResetFnName i = "reset_" ++ getIdBaseString i

-- the name of the field in a child module which holds the pointer to a
-- reset function of the parent module (for asserting an output reset)
mkResetFnDefName :: AId -> String
mkResetFnDefName i = "reset_fn_" ++ getIdBaseString i

resetFnDefType :: CCFragment -> CCFragment
resetFnDefType = userType "tResetFn"

mkSetResetFnName :: AId -> String
mkSetResetFnName rstId = "set_reset_fn_" ++ getIdBaseString rstId


-- these match definitions in bluesim_types.h
badClockHandleName :: String
badClockHandleName = "BAD_CLOCK_HANDLE"

clockType :: CCFragment -> CCFragment
clockType = userType "tClock"

-- convert a clock domain into a string
clkDomString :: ClockDomain -> String
clkDomString dom = if (dom == noClockDomain)
                   then badClockHandleName
                   else show (writeClockDomain dom)

-- the name of the field in which the clock handle for a domain is stored
mkClkDefName :: ClockDomain -> String
mkClkDefName dom = "__clk_handle_" ++ (clkDomString dom)

mkSetClkFnName :: ClockDomain -> String
mkSetClkFnName dom = "set_clk_" ++ (clkDomString dom)

-- name for a static wrapper to a method
mkStaticName :: String -> String
mkStaticName s = "static_" ++ s

-- Static methods use this name for the incoming void*
myThis :: String
myThis = "my_this"

mkLiteralName :: Integer -> Integer -> String
mkLiteralName nBits val | nBits > 64 =
    "UWide_literal_" ++ (show nBits) ++ "_h" ++ (showHex val "")
                        | otherwise =
    "Arg_literal_" ++ (show nBits) ++ "_h" ++ (showHex val "")

mkStringLiteralName :: Integer -> String
mkStringLiteralName n = "__str_literal_" ++ (show n)

-- convert an AType into a combinator for the appropriate C type
aTypeToCType :: AType -> (CCFragment -> CCFragment)
aTypeToCType (ATBit size) = (`ofType` (bitsType size CTunsigned))
aTypeToCType (ATString _) = (`ofType` (classType "std::string"))
aTypeToCType (ATReal) = (`ofType` doubleType)
aTypeToCType (ATTuple ts) = userType "WideData"
aTypeToCType (ATArray _ _) = internalError "Unexpected array"
aTypeToCType (ATAbstract _ _) = internalError "Unexpected abstract type"

-- ===============

pfxPort, pfxParam, pfxDef, pfxMeth, pfxInst, pfxMod, pfxArg, pfxModel :: String

pfxPort = "PORT_"
pfxParam = "PARAM_"
pfxDef = "DEF_"
pfxMeth = "METH_"
pfxInst = "INST_"
pfxMod = "MOD_"
pfxArg = "ARG_"
pfxModel = "MODEL_"

-- convert an AId for a port into a CCExpr with full path qualification
aPortIdToC :: AId -> CCExpr
aPortIdToC id =
    let (qs, v) = adjustInstQuals id
        v' = pfxPort ++ v
        (p, ps) = unconsOrErr "SimCCBlock.aPortIdToC" $
                    qs ++ [v']
    in  foldl cDot (var p) ps

aUnqualPortIdToString :: AId -> String
aUnqualPortIdToString id = pfxPort ++ getIdBaseString id

-- convert an AId for a port into a CCFragment with full path qualification
aPortIdToCLval :: AId -> CCFragment
aPortIdToCLval id = stmt (aPortIdToC id)

-- convert an AId for a param into a CCExpr with full path qualification
aParamIdToC :: AId -> CCExpr
aParamIdToC id =
    let (qs, v) = adjustInstQuals id
        v' = pfxParam ++ v
        (p, ps) = unconsOrErr "SimCCBlock.aParamIdToC" $
                    qs ++ [v']
    in  foldl cDot (var p) ps

-- convert an AId for a param into a CCFragment with full path qualification
aParamIdToCLval :: AId -> CCFragment
aParamIdToCLval id = stmt (aParamIdToC id)

-- convert an AId for a def into a CCExpr with full path qualification
aDefIdToC :: AId -> CCExpr
aDefIdToC id =
    let (qs, v) = adjustInstQuals id
        v' = pfxDef ++ v
        (p, ps) = unconsOrErr "SimCCBlock.aDefIdToC" $
                    qs ++ [v']
    in  foldl cDot (var p) ps

aUnqualDefIdToString :: AId -> String
aUnqualDefIdToString id = pfxDef ++ getIdBaseString id

-- convert an AId for a def into a CCFragment with full path qualification
aDefIdToCLval :: AId -> CCFragment
aDefIdToCLval id = stmt (aDefIdToC id)

aInstMethIdToC :: AId -> AId -> CCExpr
aInstMethIdToC instId methId =
    let -- drop the qualifier on the method (its package)
        m = getIdBaseString methId
        m' = pfxMeth ++ m
    in  (aInstIdToC instId) `cDot` m'

-- convert an AId for an inst into a CCExpr with full path qualification
aInstIdToC :: AId -> CCExpr
aInstIdToC id =
    let (qs, v) = adjustInstQuals id
        (p, ps) = unconsOrErr "SimCCBlock.aInstIdToC" $
                    qs ++ (if (null v) then [] else [pfxInst ++ v])
    in  foldl cDot (var p) ps

aUnqualInstIdToString :: AId -> String
aUnqualInstIdToString id = pfxInst ++ getIdBaseString id

-- convert an AId for an inst into a CCFragment with full path qualification
aInstIdToCLval :: AId -> CCFragment
aInstIdToCLval id = stmt (aInstIdToC id)

-- convert an AId for a func arg into a CCExpr with full path qualification
aArgIdToC :: AId -> CCExpr
aArgIdToC id =
    let v = getIdBaseString id
        v' = pfxArg ++ v
    in  -- check that the argument has no qualifier
        if (getIdQualString id == "")
        then var v'
        else internalError ("aArgIdToC: " ++ ppReadable id)

-- convert an AId for a func arg into a CCFragment with full path qualification
aArgIdToCLval :: AId -> CCFragment
aArgIdToCLval id = stmt (aArgIdToC id)

-- convert an AId for a rule into a CCExpr with full path qualification
aRuleIdToC :: AId -> CCExpr
aRuleIdToC id =
    let (qs, v) = adjustInstQuals id
        -- rule names need no additional prefix
        v' = v
        (p, ps) = unconsOrErr "SimCCBlock.aRuleIdToC" $
                    qs ++ [v']
    in  foldl cDot (var p) ps

-- convert the unique Int for a clock gate into a CCFragment referencing
-- the local array of clock gate pointers
aGateIdToC :: Int -> CCExpr
aGateIdToC num = cDeref $ cIndex (var "clk_gate") (mkUInt32 (toInteger num))

mkGateConst :: Bool -> CCFragment
mkGateConst b =
    let c = mkBit $ if b then 1 else 0
        v = mkVar $ "CONST_gate_" ++ if b then "true" else "false"
    in  static $ (v `assign` c) `ofType` bitsType 1 CTunsigned

mkGateDecls :: Integer -> [CCFragment]
mkGateDecls sz = [ decl $ arraySz sz $ ptr $
                              mkVar "clk_gate" `ofType` bitsType 1 CTunsigned ]

mkGateAssign :: String -> String -> Int -> Either Bool AId -> CCFragment
mkGateAssign top inst num gate_src =
    let
        srcToCExpr (Right portId) =
            -- XXX the arrow syntax requires a string
            (var top) `cArrow` (ppString (aPortIdToC portId))
        srcToCExpr (Left True) = var "CONST_gate_true"
        srcToCExpr (Left False) = var "CONST_gate_false"

        -- XXX the arrow syntax requires a string
        meth = if (inst == "")
               then "clk_gate"
               else let -- aInstIdToC will accept an Id with no base
                        instId = setIdQualString (mk_homeless_id "") inst
                    in  ppString $ cDot (aInstIdToC instId) "clk_gate"
        gate_arr = (var top) `cArrow` meth

        gate_elem = cIndex gate_arr (mkUInt32 (toInteger num))
    in
        assign (stmt gate_elem) (cAddr (srcToCExpr gate_src))

adjustInstQuals :: AId -> ([String], String)
adjustInstQuals id =
    let v = getIdBaseString id
        qs = wordsBy (=='.') (getIdQualString id)
        qs' = map (pfxInst ++) qs
    in  (qs', v)

-- ===============

-- check if an aexpr is just a var id, or other situation not to deal by wop
hasWop :: AExpr -> Bool
hasWop (APrim { aprim_prim = p }) = (p /= PrimIf)
hasWop (ATuple _ _) = True
hasWop (ATupleSel _ _ _) = True
hasWop _ = False

-- ---------------------
-- The primitive modules

-- This is a list of SimCCBlocks describing primitive modules
primBlocks :: [SimCCBlock]
primBlocks =
  let mods = [ (name, (f name mod)) | (name, mod, f, _) <- primMap ]
      mkMod n (name,fn) = SimCCBlock n name fn
                              [] [] [] [] [] [] [] [] [] [] [] [] [] [] [] []
  in zipWith mkMod [1..] mods

-- Test if a block is one of the primitive blocks
isPrimBlock :: SBId -> Bool
isPrimBlock id = any (\sb -> (sb_id sb) == id) primBlocks


-- ========================================
-- Utility for converting AExprs to CCExprs

-- The conversion is done in a State monad which records:
--   1. values of wide literals appearing in converted
--      expressions, since these cannot be generated inline
--      in C/C++ and must be declared and defined outside
--      of the expressions in which they occur. We also generate
--      out-of-line literals for narrow literals which are passed
--      as polymorphic arguments to foreign functions, since
--      these will be passed as unsigned int*s.
--   2. values of string literals appearing in converted
--      expressions, since these need to be std::string
--      values defined outside of the expressions in which they
--      occur, so that embedded null characters are handled.
--   3. whether any expression contained a foreign function
--      whose arguments were copied, so that the memory can
--      be released after the function returns.
-- It also keeps the map from foreign function names to
-- ForeignFunctions, which is read but not written.
data ConvState = CS { literals :: [(ASize,Integer)]
                    , str_literal_count :: Integer
                    , str_map :: M.Map String Integer
                    , copied_args :: Bool
                    , function_map :: ForeignFuncMap
                    -- wide data declared in block scopes (looked up by scope)
                    , blk_wdata :: WideDefMap
                    -- wide data declared in the current func's scope
                    , func_wdata :: [AId]
                    -- arguments, when converting inside a function
                    , func_args :: [AId]
                    -- unique ids for gate expressions
                    , gate_map :: M.Map AExpr Int
                    -- choice for don't-care values ("0", "1", or "A")
                    , undet_type :: String
                    }
  deriving (Eq,Show);

type WideDefMap = M.Map String [AId]

initialState :: ForeignFuncMap -> WideDefMap -> String -> ConvState
initialState ff_map wdef_map undet_type =
    CS [] 1 M.empty False ff_map wdef_map [] [] M.empty undet_type

type ExprConv  = State ConvState CCExpr
type ExprsConv = State ConvState [CCExpr]
type StmtConv  = State ConvState CCFragment
type StmtsConv = State ConvState [CCFragment]

setHasCopiedArg :: State ConvState ()
setHasCopiedArg = modify (\s -> s { copied_args = True })

clearHasCopiedArg :: State ConvState ()
clearHasCopiedArg = modify (\s -> s { copied_args = False })

addLit :: (ASize,Integer) -> State ConvState ()
addLit (w,n) = do lits <- gets literals
                  modify (\s -> s { literals = ((w,n):lits) })

addStringLit :: String -> State ConvState ()
addStringLit s = do sm <- gets str_map
                    case M.lookup s sm of
                      (Just n)  -> return ()
                      (Nothing) -> do n <- gets str_literal_count
                                      let sm' = M.insert s n sm
                                      modify (\s -> s { str_literal_count = n+1
                                                      , str_map = sm' })

getStringLiteralName :: String -> State ConvState String
getStringLiteralName s =
    do sm <- gets str_map
       case M.lookup s sm of
         (Just n) -> return $ mkStringLiteralName n
         Nothing  -> internalError $ "unknown string literal: " ++ s

setFuncWData :: [AId] -> State ConvState ()
setFuncWData wids = modify (\s -> s {func_wdata = wids})

setFuncArgs :: [AId] -> State ConvState ()
setFuncArgs args = modify (\s -> s {func_args = args})

setGateMap :: [AExpr] -> State ConvState ()
setGateMap gs = let gmap = M.fromList (zip gs [0..])
                in  modify (\s -> s {gate_map = gmap})

getWDataTest :: State ConvState (AId -> Bool)
getWDataTest = do
   bwdata <- gets blk_wdata
   fwdata <- gets func_wdata
   let f i = if (i `elem` fwdata)
             then True
             else let qual = getIdQualString i
                      base = unQualId i
                      wdefs = M.findWithDefault [] qual bwdata
                  in  base `elem` wdefs
   return f

isWideDef :: (AType, AId) -> Bool
isWideDef (t, _) = wideDataType t

mkUndetVal :: AType -> State ConvState CCExpr
mkUndetVal ty = do
  tgt <- gets undet_type
  let n = aSize ty
      v = case tgt of
            "0" -> 0
            "1" -> (2^n) - 1
            "A" -> aaaa n
            _   -> -- this situation should have been rejected when
                   -- we checked command-line flags
                   internalError $
                     "SimCCBlock.mkUndetVal: unexpected undet type: "
                     ++ show tgt
  aExprToCExpr noRet $ ASInt dummy_id (ATBit n) (ilSizedHex n v)

-- ----------------------
-- Support for primitives

sizedName :: String -> Integer -> String
sizedName name sz | sz <=  8  = name ++ "8"
sizedName name sz | sz <= 32  = name ++ "32"
sizedName name sz | sz <= 64  = name ++ "64"
sizedName name sz {- sz>64 -} = name ++ "Wide"

mkMask :: Integer -> CCExpr
mkMask sz | sz <= 8  = mkUInt8  ((2 ^ sz) - 1)
mkMask sz | sz <= 32 = mkUInt32 ((2 ^ sz) - 1)
mkMask sz | sz <= 64 = mkUInt64 ((2 ^ sz) - 1)
mkMask sz = internalError $ "mkMask for wide data (" ++ (show sz) ++ " bits)"

-- Mask off bits of an expression result beyond its desired bit size
-- For an expression which is already of size 32 or 64, no masking
-- is necessary, but expressions of other sizes need masking.
-- Specifically, expressions of size 8 do still need masking because
-- they may actually have been promoted to size 32 by C semantics.
addMask :: Integer -> CCExpr -> CCExpr
addMask sz expr
    | (sz == 32) || (sz == 64) = expr
    | sz < 64 = (mkMask sz) `cBitAnd` expr
addMask sz expr = (var (sizedName "mask" sz)) `cCall` [mkUInt32 sz,expr]

-- cast an expression to the correct type for its desired size

-- Generate an expression for a simple unary operator (!, ~, -)
simplePrim1 :: (Maybe (Bool,AId)) -> (CCExpr -> CCExpr) -> String -> AExpr
            -> ExprConv
simplePrim1 ret op op_name arg =
    do wdata_test <- getWDataTest
       v <- aExprToCExpr noRet arg
       let (w_ret, w_wret) =
               case ret of
                 Nothing            -> ([], False)
                 (Just (False,aid)) -> ([aDefIdToC aid], (wdata_test aid))
                 (Just (True,aid))  -> ([aPortIdToC aid], (wdata_test aid))
       if w_wret
         then do let wop_name = var ("wop_"++op_name)
                 return $ wop_name `cCall` (v:w_ret)
         else do return $ op v

-- Generate an expression for a simple binary operator (one which does
-- not need masking because it doesn't generate high bits).
simplePrim2 :: (Maybe (Bool,AId))
            -> (CCExpr -> CCExpr -> CCExpr) -> String
            -> AExpr -> AExpr -> ExprConv
simplePrim2 ret op op_name arg1 arg2 =
    do wdata_test <- getWDataTest
       v1 <- aExprToCExpr noRet arg1
       v2 <- aExprToCExpr noRet arg2
       let (w_ret,w_wret) = -- w_wret is true if ret exists & is wide-data
               case ret of
                 Nothing            -> ([], False)
                 (Just (False,aid)) -> ([aDefIdToC aid], (wdata_test aid))
                 (Just (True,aid))  -> ([aPortIdToC aid], (wdata_test aid))
       if w_wret
         then do let wop_name = var ("wop_"++op_name)
                 return $ wop_name `cCall` ([v1, v2]++w_ret)
         else do return $ v1 `op` v2

-- Generate an expression for a simple N-ary operator (one which does
-- not need masking because it doesn't generate high bits).
simplePrimN :: (Maybe (Bool,AId))
            -> (CCExpr -> CCExpr -> CCExpr) -> String
            -> [AExpr] -> ExprConv
simplePrimN ret op op_name args =
    do wdata_test <- getWDataTest
       vs <- mapM (aExprToCExpr noRet) args
       let (w_ret,w_wret) = -- w_wret is true if ret exists & is wide-data
               case ret of
                 Nothing -> ([], False)
                 (Just (False,aid)) -> ([aDefIdToC aid], (wdata_test aid))
                 (Just (True,aid))  -> ([aPortIdToC aid], (wdata_test aid))
       if w_wret
-- XXX we will need to support vararg wop_ for {&,|,^} if we ever
-- XXX start generating AExprs that could contain wide n-ary versions
         then do let wop_name = var ("wop_"++op_name)
                 return $ wop_name `cCall` (vs++w_ret)
         else do return $ foldl1 op vs

-- Generate an expression for a unary operator that requires masking
maskedPrim1 :: (Maybe (Bool,AId)) -> ASize -> (CCExpr -> CCExpr) -> String
               -> AExpr -> ExprConv
maskedPrim1 ret out_width op op_name arg =
    do v <- simplePrim1 ret op op_name arg
       if out_width > 64
         then return v
         else return $ addMask out_width v

-- Generate an expression for a binary operator that requires masking
maskedPrim2 :: (Maybe (Bool,AId)) -> Integer
            -> (CCExpr -> CCExpr -> CCExpr) -> String
            -> AExpr -> AExpr -> ExprConv
maskedPrim2 ret out_width op op_name arg1 arg2 =
    do v <- simplePrim2 ret op op_name arg1 arg2
       if out_width > 64
         then return v
         else return $ addMask out_width v

-- Generate an expression for a multiplication operator.
-- Multiplication is special because we want to use the built-in operator
-- but must also deal with the larger size of the result,
-- which is not part of the C/C++ semantics for multiplication.
mulPrim :: (Maybe (Bool,AId)) -> Integer -> String -> AExpr -> AExpr -> ExprConv
mulPrim ret out_width op_name arg1 arg2 =
    let promote out_w in_w x
           | out_w > 64 && in_w <= 64 =
                  (var "WideData") `cCall` [mkUInt32 in_w, x]
           | (bitsType out_w CTunsigned) /= (bitsType in_w CTunsigned) =
                  cCast (bitsType out_w CTunsigned) x
           | otherwise = x
    in do v1 <- aExprToCExpr noRet arg1
          v2 <- aExprToCExpr noRet arg2
          wdata_test <- getWDataTest
          let p_v1 = promote out_width (aSize arg1) v1
              p_v2 = promote out_width (aSize arg2) v2
              (w_ret,w_wret) =
                  case ret of
                    Nothing -> ([], False)
                    (Just (False,aid)) -> ([aDefIdToC aid], (wdata_test aid))
                    (Just (True,aid))  -> ([aPortIdToC aid], (wdata_test aid))
          if w_wret
            then return $ (var ("wop_"++op_name)) `cCall` ([p_v1, p_v2]++w_ret)
            else return $ addMask out_width (p_v1 `cMul` p_v2)

-- Generate an expression for a wide extraction operator.  Wide
-- bit/part extracts are special because we want to optimize the
-- primitive selection based on whether the extraction is byte/word
-- aligned or not.
wideExtractPrim :: (Maybe (Bool,AId)) -> Integer -> AExpr -> Integer -> Integer -> ExprConv
wideExtractPrim ret out_width e hi lo =
    do v <- aExprToCExpr noRet e
       wdata_test <- getWDataTest
       let (w_ret,w_wret) =
             case ret of
               Nothing -> ([], False)
               (Just (False,aid)) -> ([aDefIdToC aid], (wdata_test aid))
               (Just (True,aid))  -> ([aPortIdToC aid], (wdata_test aid))
       if w_wret
         then return $ (var "wop_primExtractWide") `cCall` ([ mkUInt32 out_width
                                                            , mkUInt32 (aSize e), v
                                                            , mkUInt32 32, mkUInt32 hi
                                                            , mkUInt32 32, mkUInt32 lo
                                                            ] ++ w_ret)
         else if (out_width > 32)
              then mkPrimCall ret out_width "Extract" [e, aNat hi, aNat lo]
              else if (((lo `rem` 32) == 0) && (out_width == 32))
                   then return $ (v `cDot` "get_whole_word") `cCall` [ mkUInt32 (lo `quot` 32) ]
                   else if ((lo `quot` 32) == (hi `quot` 32))
                        then if (out_width > 8)
                             then return $ (v `cDot` "get_bits_in_word32") `cCall` [ mkUInt32 (lo `quot` 32)
                                                                                   , mkUInt32 (lo `rem` 32)
                                                                                   , mkUInt32 (hi - lo + 1)
                                                                                   ]
                             else return $ (v `cDot` "get_bits_in_word8")  `cCall` [ mkUInt32 (lo `quot` 32)
                                                                                   , mkUInt32 (lo `rem` 32)
                                                                                   , mkUInt32 (hi - lo + 1)
                                                                                   ]
                        else mkPrimCall ret out_width "Extract" [e, aNat hi, aNat lo]

-- Generate an expression for a wide concatenation operator.
-- Wide concats are special because we need to handle 2, 3 or more
-- arguments of arbitrary sizes and we want to optimize the primitive
-- selection based on whether the concat segments are word aligned
-- or not.
wideConcatPrim :: (Maybe (Bool,AId)) -> Integer -> [AExpr] -> ExprConv
wideConcatPrim ret out_width args =
    do arg_exprs <- mapM (aExprToCExpr noRet) args
       let arg_widths = map aSize args
           shift_amounts = tail $ scanr (+) 0 arg_widths
       wdata_test <- getWDataTest
       let (w_ret,w_wret) =
             case ret of
               Nothing -> ([], False)
               (Just (False,aid)) -> ([aDefIdToC aid], (wdata_test aid))
               (Just (True,aid))  -> ([aPortIdToC aid], (wdata_test aid))
           add_concat_part :: CCExpr -> (CCExpr,Integer,Integer) -> CCExpr
           add_concat_part base (e,sh,w) =
             if (((sh `rem` 32) == 0) && (w == 32))
             then (base `cDot` "set_whole_word") `cCall` [e, mkUInt32 (sh `quot` 32)]
             else if ((sh `quot` 32) == ((sh + w) `quot` 32))
                  then (base `cDot` "set_bits_in_word") `cCall` [e, mkUInt32 (sh `quot` 32), mkUInt32 (sh `rem` 32), mkUInt32 w]
                  else (base `cDot` "build_concat") `cCall` [e, mkUInt32 sh, mkUInt32 w]
       if w_wret
         then do return $ foldl add_concat_part (head w_ret) (zip3 arg_exprs shift_amounts arg_widths)
         else do return $ foldl add_concat_part ((var "bs_wide_tmp") `cCall` [mkUInt32 out_width]) (zip3 arg_exprs shift_amounts arg_widths)

-- -------------------------------------------------
-- Converting expressions from ASyntax into CCSyntax

-- Make a call to a primitive function
mkPrimCall :: (Maybe (Bool,AId)) -> Integer -> String -> [AExpr] -> ExprConv
mkPrimCall ret sz name args =
  do arg_list <- mapM mkArg args
     let arg_sizes = [ mkUInt32 (arg_size a) | a <- args ]
         sized_arg_list =concat (zipWith (\a b->[a,b]) arg_sizes arg_list)
         arg_list' = (mkUInt32 sz):sized_arg_list
         w_ret = case ret of
                   Nothing -> []
                   (Just (False,aid)) -> [aDefIdToC aid]
                   (Just (True,aid))  -> [aPortIdToC aid]
         (arg_list_ret, call_name) =
             if (sz > 64 && not (null w_ret))
             then ((arg_list'++(w_ret)), ("wop_prim" ++ (sizedName name sz)))
             else (arg_list', "prim" ++ (sizedName name sz))
     return $ (var call_name) `cCall` arg_list_ret
  where arg_size :: AExpr -> ASize
        arg_size expr = case (aType expr) of
                          (ATString Nothing) -> 0
                          (ATReal)           -> 0
                          _                  -> aSize expr
        -- overload resolution needs specific information on argument types
        mkArg expr = if (isConst expr)              ||
                        (isStringType (aType expr)) ||
                        ((aType expr) == ATReal) ||
                        (isTupleType (aType expr)) ||
                        ((aSize expr) > 64)
                     then aExprToCExpr noRet expr
                     else do cexpr <- aExprToCExpr noRet expr
                             return $ (bitsType (aSize expr) CTunsigned) `cCast` cexpr

numWords :: Integer -> CCExpr
numWords n = mkUInt32 ((n + 31) `div` 32)

-- convert an argument list into a list of CExprs for a particular
-- function call
convertArgList :: [Argument] -> ExprsConv
convertArgList args = convert args (encodeArgs args)
  where convert [] _ = return []
        convert ((SimHdl):rest)    str = do rest' <- convert rest str
                                            return ((var "sim_hdl"):rest')
        convert ((Module):rest)    str = do rest' <- convert rest str
                                            return ((var "this"):rest')
        convert ((ArgStr):rest)    str = do rest' <- convert rest str
                                            return ((mkStr str):rest')
        convert ((Arg e):rest)     str = do e' <- aExprToCExpr noRet e
                                            rest' <- convert rest str
                                            return (e':rest')
        convert ((Field e f):rest) str = do e' <- aExprToCExpr noRet e
                                            rest' <- convert rest str
                                            return ((e' `cDot` f):rest')
        convert ((Ptr (ASInt _ ty val)):rest) str | aSize ty <= 64 =
          do let w  = aSize ty
                 x  = ilValue val
                 e' = (var (mkLiteralName w x)) `cDot` "data"
             addLit (w,x) -- record the literal for out-of-line generation
             rest' <- convert rest str
             return (e':rest')
        convert ((Ptr e):rest)     str = do e' <- aExprToCExpr noRet e
                                            rest' <- convert rest str
                                            return ((cAddr e'):rest')
        convert ((Copy a@(Arg _)):rest) str =
          do e' <- convertSingle a str
             rest' <- convert rest str
             setHasCopiedArg
             let copy = (var "copy_arg") `cCall` [e']
             return (copy:rest')
        convert ((Copy a):rest) str =
          do e' <- convertSingle a str
             rest' <- convert rest str
             setHasCopiedArg
             let arg_list = case argExpr a of
                              (Just e) -> [e', numWords (aSize e) ]
                              Nothing  -> [e']
                 copy = (var "copy_arg") `cCall` arg_list
             return (copy:rest')
        convert ((NoConst a):rest) str = do e' <- convert [a] str
                                            rest' <- convert rest str
                                            let cast = var "const_cast<char*>"
                                            return ((cast `cCall` e'):rest')
        convert (Null:rest)        str = do rest' <- convert rest str
                                            return (mkNULL:rest')
        convert ((Alloc n r):rest)   str =
          do rest' <- convert rest str
             setHasCopiedArg
             let fn = if r then (var "return_arg") else (var "ignore_arg")
                 alloc = fn `cCall` [ numWords n ]
             return (alloc:rest')
        convertSingle e str =
          do es' <- convert [e] str
             case es' of
               [e'] -> return e'
               _ -> internalError ("convertSingle: unexpected list")


wrapReturn :: (Maybe (Bool,AId)) -> CCExpr -> CCExpr
wrapReturn (Just (False,aid)) call =
  (var "write_return") `cCall` [ cGroup (call `cComma` (mkUInt32 0))
                               , cAddr (aDefIdToC aid)
                               ]
wrapReturn (Just (True,aid)) call =
  (var "write_return") `cCall` [ cGroup (call `cComma` (mkUInt32 0))
                               , cAddr (aPortIdToC aid)
                               ]
wrapReturn Nothing    call = call

-- Use this for expressions which should never use a return argument
noRet :: (Maybe (Bool,AId))
noRet = Nothing

-- Helper function to verify the correct number of arguments
argCount :: (Int -> Bool) -> [AExpr] -> (a -> a)
argCount pred args =
  if pred (length args)
  then id
  else internalError $ "aExprToCExpr: wrong number of arguments:\n" ++
                       "  " ++ (ppReadable args) ++ "\n"

getConstVal :: AExpr -> Maybe Integer
getConstVal (ASInt _ _ l@(IntLit {})) = Just (ilValue l)
getConstVal _ = Nothing

-- convert an AExpr into a CExpr
-- The first argument is used when the value must be written explicitly
-- to the output rather than simply returned (used with wide/polymoprhic
-- expressions).
aExprToCExpr :: (Maybe (Bool,AId)) -> AExpr -> ExprConv
aExprToCExpr ret p@(APrim _ _ PrimAdd args) = argCount (==2) args $
  maskedPrim2 ret (aSize p) (cAdd) (toWString PrimAdd) (args!!0) (args!! 1)
aExprToCExpr ret p@(APrim _ _ PrimSub args) = argCount (==2) args $
  maskedPrim2 ret (aSize p) (cSub) (toWString PrimSub) (args!!0) (args!! 1)
aExprToCExpr ret p@(APrim _ _ PrimMul args) = argCount (==2) args $
  mulPrim ret (aSize p) (toWString PrimMul) (args!!0) (args!! 1)
aExprToCExpr ret p@(APrim _ _ PrimQuot args) = argCount (==2) args $
  maskedPrim2 ret (aSize p) (cQuot) (toWString PrimQuot) (args!!0) (args!! 1)
aExprToCExpr ret p@(APrim _ _ PrimRem args) = argCount (==2) args $
  maskedPrim2 ret (aSize p) (cRem) (toWString PrimRem) (args!!0) (args!! 1)
aExprToCExpr ret (APrim _ _ PrimAnd args) = argCount (>1) args $
  simplePrimN ret (cBitAnd) (toWString PrimAnd) args
aExprToCExpr ret (APrim _ _ PrimOr args) = argCount (>1) args $
  simplePrimN ret (cBitOr) (toWString PrimOr) args
aExprToCExpr ret (APrim _ _ PrimXor args) = argCount (>1) args $
  simplePrimN ret (cBitXor) (toWString PrimXor) args
aExprToCExpr ret p@(APrim _ _ PrimSL args) = argCount (==2) args $
  mkPrimCall ret (aSize p) "ShiftL" args
aExprToCExpr ret p@(APrim _ _ PrimSRL args) = argCount (==2) args $
  mkPrimCall ret (aSize p) "ShiftR" args
aExprToCExpr ret p@(APrim _ _ PrimSRA args) = argCount (==2) args $
  mkPrimCall ret (aSize p) "ShiftRA" args
aExprToCExpr ret p@(APrim _ _ PrimInv args) = argCount (==1) args $
  maskedPrim1 ret (aSize p) (cCompl) (toWString PrimInv) (args!!0)
aExprToCExpr ret p@(APrim _ _ PrimNeg args) = argCount (==1) args $
  maskedPrim1 ret (aSize p) (cUMinus) (toWString PrimNeg) (args!!0)
aExprToCExpr _ (APrim _ _ PrimEQ args) = argCount (==2) args $
  simplePrim2 noRet (cEq) (toWString PrimEQ) (args!!0) (args!!1)
-- Bluesim isn't 4-state, so PrimEQ3 is the same as PrimEQ
aExprToCExpr _ (APrim _ _ PrimEQ3 args) = argCount (==2) args $
  simplePrim2 noRet (cEq) (toWString PrimEQ) (args!!0) (args!!1)
aExprToCExpr _ (APrim _ _ PrimULE args) = argCount (==2) args $
  simplePrim2 noRet (cLe) (toWString PrimULE) (args!!0) (args!!1)
aExprToCExpr _ (APrim _ _ PrimULT args) = argCount (==2) args $
  simplePrim2 noRet (cLt) (toWString PrimULT) (args!!0) (args!!1)
aExprToCExpr _ p@(APrim _ _ PrimSLE args) = argCount (==2) args $
  mkPrimCall noRet (aSize p) "SLE" args
aExprToCExpr _ p@(APrim _ _ PrimSLT args) = argCount (==2) args $
  mkPrimCall noRet (aSize p) "SLT" args
aExprToCExpr _ (APrim _ _ PrimIf args) = argCount (==3) args $
  do c  <- aExprToCExpr noRet (args!!0)
     v1 <- aExprToCExpr noRet (args!!1)
     v0 <- aExprToCExpr noRet (args!!2)
     return $ cTernary c v1 v0
aExprToCExpr ret p@(APrim _ _ PrimSignExt args) = argCount (==1) args $
  mkPrimCall ret (aSize p) "SignExt" args
aExprToCExpr ret p@(APrim _ _ PrimZeroExt args) = argCount (==1) args $
  mkPrimCall ret (aSize p) "ZeroExt" args
aExprToCExpr ret p@(APrim _ _ PrimTrunc args) = argCount (==1) args $
  mkPrimCall ret (aSize p) "Trunc" args
aExprToCExpr ret p@(APrim _ _ PrimExtract args) = argCount (==3) args $
  let mhi = getConstVal (args!!1)
      mlo = getConstVal (args!!2)
  in case (mhi,mlo) of
      (Just hi, Just lo) -> if ((aSize p) > 64) || ((aSize (args!!0)) > 64)
                            then wideExtractPrim ret (aSize p) (args!!0) hi lo
                            else do v <- aExprToCExpr noRet (args!!0)
                                    let out_width = aSize p
                                        out_type = bitsType out_width CTunsigned
                                        v' = v `cRShift` (mkUInt32 lo)
                                        v'' = if (hi == (aSize (args!!0)) - 1)
                                              then v'
                                              else addMask out_width v'
                                    return $ out_type `cCast` v''
      _ -> mkPrimCall ret (aSize p) "Extract" args
aExprToCExpr ret p@(APrim _ _ PrimConcat args) = argCount (>=2) args $
  if (aSize p) <= 64
  then do let arg_widths = map aSize args
              arg_types  = map (\w -> bitsType w CTunsigned) arg_widths
              out_width  = aSize p
              out_type   = bitsType out_width CTunsigned
          arg_exprs <- mapM (aExprToCExpr noRet) args
          let arg_exprs_cast = [ if (t == out_type) then e else (out_type `cCast` e)
                               | (e,t) <- zip arg_exprs arg_types
                               ]
              shift_amounts = tail $ scanr (+) 0 arg_widths
              shifted_exprs = zipWith cLShift arg_exprs_cast (map mkUInt32 shift_amounts)
              or_together   = foldl1 cBitOr shifted_exprs
          return $ addMask out_width or_together
  else wideConcatPrim ret (aSize p) args
aExprToCExpr _ (APrim _ _ PrimBAnd args) = argCount (>1) args $
  simplePrimN noRet (cAnd) (toWString PrimBAnd) args
aExprToCExpr _ (APrim _ _ PrimBOr args) = argCount (>1) args $
  simplePrimN noRet (cOr) (toWString PrimBOr) args
aExprToCExpr _ (APrim _ _ PrimBNot args) = argCount (==1) args $
  simplePrim1 noRet (cNot) (toWString PrimBNot) (args!!0)
aExprToCExpr _ p@(APrim _ _ PrimStringConcat args) = argCount (==2) args $
  simplePrim2 noRet (cAdd) (ppString PrimAdd) (args!!0) (args!! 1)
aExprToCExpr _ p@(APrim _ _ _ _) =
  internalError ("unhandled primitive: " ++ (show p))
aExprToCExpr _ (AMethCall _ id mid args) =
  do arg_list <- mapM (aExprToCExpr noRet) args
     return $ (aInstMethIdToC id mid) `cCall` arg_list
aExprToCExpr ret e@(ATuple _ exprs) =
  wideConcatPrim ret (aSize e) exprs
aExprToCExpr ret (ATupleSel t e idx) =
  wideExtractPrim ret (aSize t) e (aSize t + sizeAfter - 1) sizeAfter
  where sizeAfter = sum $ map aSize $ genericDrop idx $ att_elem_types $ ae_type e
aExprToCExpr _ e@(AMGate _ id clkid) =
  do gmap <- gets gate_map
     case (M.lookup e gmap) of
       Just num -> return $ aGateIdToC num
       Nothing -> internalError ("Unexpected clock gate: AMGate " ++
                                 getIdString id ++ "." ++ getIdString clkid)
aExprToCExpr _ (ASParam _ id) = do return $ aParamIdToC id
aExprToCExpr _ e@(ASPort  _ id) =
    do args <- gets func_args
       gmap <- gets gate_map
       return $ if (id `elem` args)
                then aArgIdToC id
                else case (M.lookup e gmap) of
                       Just num -> aGateIdToC num
                       Nothing  -> aPortIdToC id
aExprToCExpr _ (ASDef   _ id) = do return $ aDefIdToC id
aExprToCExpr _ (ASInt _ (ATBit w) val) | w == 1    =
  do return $ mkBit (ilValue val)
                                       | w <= 8    =
  do return $ mkUInt8 (ilValue val)
                                       | w <= 32   =
  do return $ mkUInt32 (ilValue val)
                                       | w <= 64   =
  do return $ mkUInt64 (ilValue val)
                                       | otherwise =
  do let x = ilValue val
     addLit (w,x) -- record the wide literal for out-of-line generation
     return $ var (mkLiteralName w x)
aExprToCExpr _ (ASReal _ _ val) = return $ mkDouble val
aExprToCExpr _ (ASStr _ _ str) =
--  do return $ mkStr str
  do addStringLit str
     nm <- getStringLiteralName str
     return $ var nm
aExprToCExpr ret f@(AFunCall {}) =
  do ff_map <- gets function_map
     let (ret_style,name,arg_list) = mkCallExpr ff_map ret f
         ret' = case ret_style of
                  Buffered  -> ret
                  otherwise -> Nothing
     args <- convertArgList arg_list
     return $ wrapReturn ret' ((var name) `cCall` args)
aExprToCExpr _ (ASAny ty _) =
  internalError "ASAny should not exist past SimExpand"
aExprToCExpr _ x = internalError ("Unhandled expr: " ++ (show x))

-- ==============================================
-- Converting SimCCBlock structures into CCSyntax

-- Generate a C method declaration from a SimCCFn
simFnToCDeclaration :: SimCCFn -> CCFragment
simFnToCDeclaration (SimCCFn name args ret _) =
  let arg_list = [ (aTypeToCType ty) (aArgIdToCLval id) | (ty,id) <- args]
      rt = maybe void aTypeToCType ret
  in  decl $ function rt (mkVar name) arg_list

-- Generate a declaration for a static wrapper, which takes a class pointer
simFnToStaticCDeclaration :: SimCCFn -> CCFragment
simFnToStaticCDeclaration (SimCCFn name args ret _) =
  let class_ptr = ptr $ void (mkVar myThis)
      arg_list = [ (aTypeToCType ty) (aArgIdToCLval id) | (ty,id) <- args]
      rt = maybe void aTypeToCType ret
      static_name = mkStaticName name
  in  static $ decl $ function rt (mkVar static_name) (class_ptr:arg_list)

-- Generate a C statement from a SimCCFnStmt
simFnStmtToCStmt :: SimCCFnStmt -> StmtConv
simFnStmtToCStmt (SFSDef isPort (ty@(ATString _),aid) Nothing) =
  do let dst = if isPort then aPortIdToCLval aid else aDefIdToCLval aid
     return $ decl $ (aTypeToCType ty) dst
simFnStmtToCStmt (SFSDef isPort (ty@(ATReal),aid) Nothing) =
  do let dst = if isPort then aPortIdToCLval aid else aDefIdToCLval aid
     return $ decl $ (aTypeToCType ty) dst
simFnStmtToCStmt (SFSDef isPort (ty,aid) Nothing) =
  let w = aSize ty
      dst = if isPort then aPortIdToCLval aid else aDefIdToCLval aid
      typed_id = (aTypeToCType ty) dst
  in if w > 64 || isTupleType ty   -- for wide data, use (bits,false) constructor to avoid initialization penalty
     then return $ construct typed_id [mkUInt32 w, mkBool False]
     else return $ decl typed_id
simFnStmtToCStmt (SFSDef isPort (ty@(ATString (Just sz)),aid) (Just expr)) =
  do let dst = if isPort then aPortIdToCLval aid else aDefIdToCLval aid
         typed_id = (aTypeToCType ty) dst
     v <- aExprToCExpr noRet expr
     return $ construct typed_id [v, mkUInt32 sz]
simFnStmtToCStmt (SFSDef isPort (ty,aid) (Just expr)) =
  do ff_map <- gets function_map
     let isCase (APrim _ _ PrimCase _) = True
         isCase _ = False
     when (isCase expr) $
         internalError ("Case definition cannot have initializer")
     when (wideReturn ff_map expr || polyReturn ff_map expr) $
         internalError "Wide/polymorphic definition cannot have initializer"
     let dst = if isPort then aPortIdToCLval aid else aDefIdToCLval aid
         typed_id = (aTypeToCType ty) dst
     v <- aExprToCExpr (Just (False,aid)) expr
     return $ decl $ typed_id `assign` v
-- eventually, we may want to create SFSSwitch and have a pass that transforms
-- a list of SimCCFnStmt so that PrimCase in SFSDef and SFSAssign are handled
-- as SFSSwitch (and we can move other stmts into the arms, as further opt)
simFnStmtToCStmt (SFSAssign isPort aid
                      (APrim _ _ PrimCase (idx:def:flat_arms))) =
  do c_idx <- aExprToCExpr noRet idx
     let arms = makePairs flat_arms
         -- Combine arms with the same result value; reordering is assumed
         -- to be OK because the expressions should be constant
         -- First, eliminate the arms that have the same value as the default.
         (_, arms') = partition ((== def) . snd) arms
         -- Then combine all the explicit indices.
         arms_combined =
           let combineFn [] = []
               combineFn ((n, e) : nes) =
                 let (common_nes, nes') = partition ((== e) . snd) nes
                     common_ns = map fst common_nes
                 in (n:common_ns, e) : combineFn nes'
           in  combineFn arms'
         armToCCFragment (ns, e) = do
           -- sort the indices, so that it's consistent and looks nice
           let ns' = sortBy cmpASInt ns
           c_ns <- mapM (aExprToCExpr noRet) ns'
           c_e <- simFnStmtToCStmt (SFSAssign isPort aid e)
           let (ns_empty, n_last) = (initOrErr "armToCCFragment" c_ns,
                                     lastOrErr "armToCCFragment" c_ns)
           return $ [ (n, []) | n <- ns_empty ] ++
                    [ (n_last, [c_e, break_loop]) ]
     c_arms <- concatMapM armToCCFragment arms_combined
     c_def <- simFnStmtToCStmt (SFSAssign isPort aid def)
     return $ switch c_idx c_arms (Just [c_def])
simFnStmtToCStmt (SFSAssign isPort aid expr) =
  do ff_map <- gets function_map
     wdata_test <- getWDataTest
     v <- aExprToCExpr (Just (isPort,aid)) expr
     let b_wop = (hasWop expr) && (wdata_test aid)
     if wideReturn ff_map expr || polyReturn ff_map expr || b_wop
       then do return $ stmt v
       else do let dst = if isPort
                         then aPortIdToCLval aid
                         else aDefIdToCLval aid
               return $ dst `assign` v
simFnStmtToCStmt (SFSAction act) =
  do (_, cond, call) <- aActionToCFunCall noRet act
     return $ if_cond cond (stmt call) Nothing
simFnStmtToCStmt s@(SFSAssignAction isPort aid act ty) =
  do (ret_style, cond, call) <- aActionToCFunCall (Just (isPort,aid)) act
     case ret_style of
       Direct    -> do let dst = if isPort
                                 then aPortIdToCLval aid
                                 else aDefIdToCLval aid
                       undet <- mkUndetVal ty
                       return $ if_cond cond
                                  (dst `assign` call)
                                  (Just (dst `assign` undet))
       otherwise -> return $ if_cond cond (stmt call) Nothing
simFnStmtToCStmt (SFSRuleExec ruleId) =
  return $ stmt $ (aRuleIdToC ruleId) `cCall` []
simFnStmtToCStmt (SFSCond cond [t] []) =
  do c <- aExprToCExpr noRet cond
     s <- simFnStmtToCStmt t
     return $ if_cond c s Nothing
simFnStmtToCStmt (SFSCond cond [] [f]) =
  do c <- aExprToCExpr noRet cond
     s <- simFnStmtToCStmt f
     return $ if_cond (cNot c) s Nothing
simFnStmtToCStmt (SFSCond cond t []) =
  do c <- aExprToCExpr noRet cond
     s <- mapM simFnStmtToCStmt t
     return $ if_cond c (block s) Nothing
simFnStmtToCStmt (SFSCond cond [] f) =
  do c <- aExprToCExpr noRet cond
     s <- mapM simFnStmtToCStmt f
     return $ if_cond (cNot c) (block s) Nothing
simFnStmtToCStmt (SFSCond cond t f) =
  do c <- aExprToCExpr noRet cond
     s1 <- mapM simFnStmtToCStmt t
     s2 <- mapM simFnStmtToCStmt f
     return $ if_cond c (block s1) (Just (block s2))
simFnStmtToCStmt (SFSMethodCall obj meth args) =
  do arg_list <- mapM (aExprToCExpr noRet) args
     return $ stmt $ (aInstMethIdToC obj meth) `cCall` arg_list
simFnStmtToCStmt (SFSFunctionCall obj func args) =
  do arg_list <- mapM (aExprToCExpr noRet) args
     return $ stmt $ ((aInstIdToC obj) `cDot` func) `cCall` arg_list
simFnStmtToCStmt (SFSResets stmts) =
  do let c = (var "do_reset_ticks") `cCall` [ var "simHdl" ]
     s <- mapM simFnStmtToCStmt stmts
     return $ if_cond c (block s) Nothing
simFnStmtToCStmt (SFSReturn Nothing) = do return $ ret Nothing
simFnStmtToCStmt (SFSReturn (Just expr)) =
  do v <- aExprToCExpr noRet expr
     return $ ret (Just v)
simFnStmtToCStmt (SFSOutputReset rstId expr) =
  do let rstFn = mkResetFnDefName rstId
     rst_expr <- aExprToCExpr noRet expr
     -- make a call to the resetFn: reset_fn(parent, rst_in)
     let rstCall = stmt $ (var rstFn) `cCall` [var "parent", rst_expr]
     -- if the resetFn field is not set, then do nothing
     return $ if_cond (var rstFn) rstCall Nothing

-- helper func to convert an AAction to its condition and its CFunCall,
-- for embedding in a larger CC statement
aActionToCFunCall :: (Maybe (Bool,AId)) -> AAction
                     -> State ConvState (ReturnStyle, CCExpr, CCExpr)
aActionToCFunCall _ c@(ACall id mth_id aargs) =
  do cargs <- mapM (aExprToCExpr noRet) aargs
     let (cond, arg_list) =
           case cargs of
             (x:xs) -> (x, xs)
             _ -> internalError ("aActionToCFunCall: missing cond in ACall args")
     let call = (aInstMethIdToC id mth_id) `cCall` arg_list
     return (Direct, cond, call)
aActionToCFunCall Nothing act@(AFCall {}) =
  do ff_map <- gets function_map
     let c = headOrErr "action has no condition" (aact_args act)
         (_,name,arg_list) = mkCallAction ff_map Nothing act
     cond <- aExprToCExpr noRet c
     args <- convertArgList arg_list
     let call = (var name) `cCall` args
     return (None, cond, call)
aActionToCFunCall ret act@(ATaskAction {}) =
  do ff_map <- gets function_map
     let c = headOrErr "action has no condition" (aact_args act)
         (ret_style,name,arg_list) = mkCallAction ff_map ret act
     cond <- aExprToCExpr noRet c
     args <- convertArgList arg_list
     let call = (var name) `cCall` args
         ret' = case ret_style of
                  Buffered  -> do aid <- ataskact_temp act
                                  return (maybe False fst ret, aid)
                  otherwise -> Nothing
     return (ret_style, cond, wrapReturn ret' call)
aActionToCFunCall ret act =
  internalError $
    "aActionToCFunCall: unexpected return/action combination: " ++
    (ppReadable (ret,act))

-- Generate a definition for a static wrapper, which takes a class pointer
simFnToStaticCDefinition :: String -> SimCCFn -> CCFragment
simFnToStaticCDefinition cls (SimCCFn name args rty _) =
  let class_ptr = ptr $ void (mkVar myThis)
      arg_list = [ (aTypeToCType ty) (aArgIdToCLval id) | (ty,id) <- args]
      rt = maybe void aTypeToCType rty
      prefix = cls ++ "::"
      static_name = mkStaticName name
      func = function rt (mkVar (prefix ++ static_name)) (class_ptr:arg_list)
      -- cast the void* to class*
      real_ptr = cCast (ptrType (classType cls)) (var myThis)
      -- call the non-static reset member function
      wrapped_call = let f = real_ptr `cArrow` name
                         as = map (aArgIdToC . snd) args
                     in  f `cCall` as
      body = block [ if (isNothing rty)
                     then stmt wrapped_call
                     else ret (Just wrapped_call) ]
  in  define func body

prefixSimFnName :: String -> SimCCFn -> SimCCFn
prefixSimFnName s (SimCCFn name args ret stmts) =
    SimCCFn (s ++ name) args ret stmts

-- Generate a C method definition from a SimCCFn
simFnToCDefinition :: Bool -> (Maybe String) ->
                      [CCFragment] -> [CCFragment] ->
                      SimCCFn -> StmtConv
simFnToCDefinition is_static scope c_args prologue
                   fn@(SimCCFn name args ret stmts) =
  do let prefix = maybe "" (++ "::") scope
         arg_list = c_args ++
                    [ (aTypeToCType ty) (aArgIdToCLval id) | (ty,id) <- args]
         rt = maybe void aTypeToCType ret
         (return_stmts,non_return_stmts) = partition isReturn stmts
         wdata_fn = concatMap (wideLocalDef) stmts
     setFuncWData wdata_fn
     setFuncArgs (map snd args)
     body_stmts <- mapM simFnStmtToCStmt non_return_stmts
     final_stmts <- mapM simFnStmtToCStmt return_stmts
     has_copies <- gets copied_args
     let free_copies = if has_copies
                       then [ stmt $ (var "delete_arg_copies") `cCall` [] ]
                       else []
         body = block (prologue ++ body_stmts ++ free_copies ++ final_stmts)
     clearHasCopiedArg
     setFuncArgs []
     let def = define (function rt (mkVar (prefix ++ name)) arg_list) body
     return $ if is_static
              then static def
              else def

-- Helper routine for creating submodule member declarations
memberDecl :: SBMap -> SBId -> AId -> [AExpr] -> CCFragment
memberDecl sb_map sbid aid args =
  decl $ (moduleType (lookupSB sb_map sbid) args) (aInstIdToCLval aid)

-- Helper routine for building constructor functions.
-- Constructors are not represented as SimCCFn, because
-- they have additional initializer lists and implicit
-- return types.
mkCtor :: Maybe String -> SimCCBlock  -> CCFragment
mkCtor scope sb =
  let prefix = maybe "" (++ "::") scope
      args = [ (aTypeToCType ty) (aArgIdToCLval arg_id)
             | (ty, arg_id, isPort) <- sb_parameters sb
             ]
  in ctor (mkVar (prefix ++ pfxMod ++ (sb_name sb)))
          ([ (userType "tSimStateHdl") $ (mkVar "simHdl")
           , ptr . constant . CCSyntax.char $ (mkVar "name")
           , ptr . (userType "Module") $ (mkVar "parent")
           ] ++ args)

-- Add arguments for a constructor determined by the SimCCBlock.
-- This is used for FIFOs, where we want to use the same C++ module
-- with extra arguments to disambiguate FIFO1, FIFO2, SizedFIFO, etc.
addSBArgs :: SBMap -> (SBId,AId,[AExpr]) -> (AId,[AExpr])
addSBArgs sb_map (sbid,aid,args) =
  let sb = lookupSB sb_map sbid
  in (aid, snd (sb_naming_fn sb args))

-- Create an initlist for use with `withInits`
mkStateInitList :: [(AId,[AExpr])] -> ExprsConv
mkStateInitList state_defs =
  -- we replace any references to ports or parameters with the argument,
  -- since the memory location for ports may not be initialized yet
  let replaceInputs (ASPort t i)  = ASPort t i
      replaceInputs (ASParam t i) = ASPort t i
      replaceInputs x             = x
      mkOne (aid,args) =
          do let args' = mapAExprs replaceInputs  args
             arg_list <- mapM (aExprToCExpr noRet) args'
             let name = mkStr (getIdBaseString aid)
             return $ cCall (aInstIdToC aid)
                        ([var "simHdl", name, var "this"] ++ arg_list)
  in mapM mkOne state_defs

mkWideInitList :: [(AId,[AExpr])] -> ExprsConv
mkWideInitList wide_defs =
  let mkOne (aid,args) =
          do arg_list <- mapM (aExprToCExpr noRet) args
             return $ cCall (aDefIdToC aid) arg_list
  in  mapM mkOne wide_defs

-- For ports, we initialize one-bit ports to False, so that
-- all enables and readys are covered.  For wide ports, we set the size
-- and clear the data.
mkPortInit :: (AType,AId,VName) -> [CCFragment]
mkPortInit ((ATBit 1),_,vn) =
  [ assign (aPortIdToCLval (vName_to_id vn)) (mkBool False) ]
mkPortInit ((ATBit n),_,vn) | n > 64 =
  let p = aPortIdToC (vName_to_id vn)
  in [ stmt $ p `cDot` "setSize" `cCall` [ mkUInt32 n ]
     , stmt $ p `cDot` "clear" `cCall` []
     ]
mkPortInit ((ATBit n),_,vn) | n > 32 =
  [ assign (aPortIdToCLval (vName_to_id vn)) (mkUInt64 0) ]
mkPortInit ((ATBit n),_,vn) =
  [ assign (aPortIdToCLval (vName_to_id vn)) (mkUInt32 0) ]
mkPortInit (t@(ATTuple _),_,vn) =
  let p = aPortIdToC (vName_to_id vn)
  in [ stmt $ p `cDot` "setSize" `cCall` [ mkUInt32 $ aSize t ]
     , stmt $ p `cDot` "clear" `cCall` []
     ]
mkPortInit p = internalError ("SimCCBlock.mkPortInit: " ++ ppReadable p)

-- Create a call to the "set_reset_fn" for submodules with output resets
mkResetInit :: (AId,(AId,AId)) -> CCFragment
mkResetInit (wire, (submod, reset)) =
  let rst_fn_name = mkStaticName $ mkResetFnName wire
      rst_fn_ref  = cAddr (var rst_fn_name)
      set_fn_name = mkSetResetFnName reset
      set_fn = (aInstIdToC submod) `cDot` set_fn_name
  in
      stmt $ cCall set_fn [rst_fn_ref]

-- Set the reset fns for this module to NULL
mkOutputResetInit :: AId -> CCFragment
mkOutputResetInit rstId =
  let def_name = mkResetFnDefName rstId
  in  (mkVar def_name) `assign` mkNULL

-- These should match the tSymTag definitions in src/sim/bluesim_types.h
data Symbol = SymModule AId
            | SymDef AId Integer
            | SymParam AId Integer
            | SymPort  AId Integer
            | SymRule
            | SymUnknown
  deriving (Eq,Ord,Show)

instance PPrint Symbol where
  pPrint d _ (SymModule i)  = (text "Module") <+> (pPrint d 0 i)
  pPrint d _ (SymDef i _)   = (text "Def") <+> (pPrint d 0 i)
  pPrint d _ (SymParam i _) = (text "Param") <+> (pPrint d 0 i)
  pPrint d _ (SymPort i _)  = (text "Port") <+> (pPrint d 0 i)
  pPrint _ _ SymRule        = (text "Rule")
  pPrint _ _ SymUnknown     = (text "Unknown")

-- Setup for symbol data
mkSymbolHdr :: Int -> [CCFragment]
mkSymbolHdr n = [ (mkVar "symbol_count") `assign` (mkUInt32 (toInteger n)) ] ++
                if (n > 0)
                then [ (mkVar "symbols") `assign` (newArray (classType "tSym") (var "symbol_count"))
                     ]
                else []

-- Call symbol init method
mkSymbolCall :: Int -> CCFragment
mkSymbolCall n = stmt $ var ("init_symbols_" ++ (show n)) `cCall` []

-- Initialize entry for one symbol
mkSymbolInit :: (Int,(String, Symbol)) -> [CCFragment]
mkSymbolInit (num, (name, sym)) =
  let sym_ptr = cAddr ((var "symbols") `cIndex` (mkUInt32 (toInteger num)))
      args = [ sym_ptr, mkStr name ] ++ (getSymArgs sym)
  in [ stmt $ (var "init_symbol") `cCall` args ]
  where getSymArgs (SymModule i)   = [ var "SYM_MODULE", cAddr (aInstIdToC i) ]
        getSymArgs (SymDef i sz)   = [ var "SYM_DEF", cAddr (aDefIdToC i), mkUInt32 sz ]
        getSymArgs (SymParam i sz) = [ var "SYM_PARAM", cCast (ptrType voidType) $ cAddr (aParamIdToC i), mkUInt32 sz ]
        getSymArgs (SymPort i sz)  = [ var "SYM_PORT", cAddr (aPortIdToC i), mkUInt32 sz ]
        getSymArgs SymRule         = [ var "SYM_RULE" ]
        getSymArgs s = internalError $ "mkSymbolInit: unknown symbol type '" ++
                                       (ppReadable s) ++ "'"

-- Identify the reset infos which are outputs of submodules
filterOutputResets :: [(AId,(AId,AId))] -> [SimCCFn] -> [SimCCFn]
filterOutputResets srcs fns =
    let src_fn_names = map (mkResetFnName . fst) srcs
    in  filter (\fn -> sf_name fn `elem` src_fn_names) fns

-- void set_reset_fn_gen_rst(tResetFn fn) { reset_fn = fn; }
setResetFnProto :: Maybe String -> AId -> CCFragment
setResetFnProto scope rstId =
  let prefix = maybe "" (++ "::") scope
      fn_name = mkSetResetFnName rstId
  in  function void (mkVar (prefix ++ fn_name))
                    [resetFnDefType (mkVar "fn")]

setResetFnDef :: Maybe String -> AId -> CCFragment
setResetFnDef scope rstId =
  let def_name = mkResetFnDefName rstId
      def_assign = (mkVar def_name) `assign` (var "fn")
  in  define (setResetFnProto scope rstId) (block [def_assign])

-- void set_clk_n(const char* s) { __clk_handle_n = bk_get_or_define_clock(s); }
setClkFnProto :: Maybe String -> ClockDomain -> CCFragment
setClkFnProto scope dom =
  let prefix = maybe "" (++ "::") scope
      fn_name = mkSetClkFnName dom
  in  function void (mkVar (prefix ++ fn_name))
                    [ptr . constant . CCSyntax.char $ (mkVar "s")]

setClkFnDef :: Maybe String -> ClockDomain -> CCFragment
setClkFnDef scope dom =
  let def_name = mkClkDefName dom
      handle = (var "bk_get_or_define_clock") `cCall` [var "sim_hdl", var "s"]
      def_assign = (mkVar def_name) `assign` handle
  in  define (setClkFnProto scope dom) (block [def_assign])

-- Functions used for generating the dump() methods for a SimCCBlock
dumpFnProto :: Maybe String -> Bool -> String -> CCFragment
dumpFnProto scope with_handle fn_name =
  let prefix = maybe "" (++ "::") scope
      harg = if with_handle then [clockType (mkVar "handle")] else []
      iarg = [unsigned . int $ (mkVar "indent")]
  in function void (mkVar (prefix ++ fn_name)) (harg ++ iarg)

vcdHdrFnProto :: Maybe String -> CCFragment
vcdHdrFnProto scope =
  let prefix = maybe "" (++ "::") scope
  in function (unsigned . int) (mkVar (prefix ++ "dump_VCD_defs"))
                               [ unsigned . int $ (mkVar "levels") ]

vcdDumpFnProto :: SimCCBlock -> Maybe String -> String -> Bool -> CCFragment
vcdDumpFnProto sb scope name with_levels =
  let prefix = maybe "" (++ "::") scope
      args = [ (userType "tVCDDumpType") $ (mkVar "dt") ] ++
             (if (with_levels) then [ unsigned . int $ (mkVar "levels") ] else []) ++
             [ reference . (moduleType sb []) $ (mkVar "backing") ]
  in function void (mkVar (prefix ++ name)) args

vcdFnProto :: SimCCBlock -> Maybe String -> CCFragment
vcdFnProto sb scope = vcdDumpFnProto sb scope "dump_VCD" True

mkSubCall :: AId -> String -> [CCExpr] -> Maybe CCFragment -> CCFragment
mkSubCall inst fn args lval =
  let rhs = ((aInstIdToC inst) `cDot` fn) `cCall` args
  in case lval of
       (Just lhs) -> lhs `assign` rhs
       Nothing    -> stmt $ rhs

mkVCDDef :: Map.Map (Bool, AId) ClockDomain -> (AType, AId, Bool) -> [CCFragment]
mkVCDDef clk_map (ty,aid,isPort) =
  let name      = getIdBaseString aid
      def       = if isPort then (aPortIdToC aid) else (aDefIdToC aid)
      -- we lookup based on the AId in a map made by calling "defs_written"
      -- this requires that the Ids be paired with whether it is a port
      -- (since ports and defs are in separate namespaces)
      aid'      = (isPort, aid)
      dom       = M.lookup aid' clk_map
      set_lag   = case dom of
                    (Just d) -> [ stmt $ (var "vcd_set_clock") `cCall`
                                  [ var "sim_hdl", var "num",  var (mkClkDefName d) ] ]
                    Nothing  -> []
      args = [var "sim_hdl"] ++ (mkVCDCallArgs VCDDef ty name def)
      write_def = [ stmt $ (var "vcd_write_def") `cCall` args ]

  in set_lag ++ write_def

-- Symbol initialization function prototype
symInitFnProto :: (Maybe String) -> Int -> CCFragment
symInitFnProto scope n =
    let prefix = maybe "" (++ "::") scope
    in function void (mkVar (prefix ++ "init_symbols_" ++ (show n))) []

isOkId :: Id -> Bool
isOkId i = not ((isInternal i) || (isBadId i) || (isFromRHSId i))

-- Generate a class declaration for the SimCCBlock.
-- The declaration will include all of the state elements and local
-- defs, along with rule and method declarations.
simCCBlockToClassDeclaration :: SBMap -> SimCCBlock -> CCFragment
simCCBlockToClassDeclaration sb_map sb =
  let clks        = [ decl $ clockType (mkVar (mkClkDefName dom))
                    | dom <- sb_domains sb]
      clk_defs    = [comment "Clock handles" (private clks)]
      gates       = mkGateDecls (toInteger (length (sb_gateMap sb)))
      gate_defs   = [comment "Clock gate handles" (public gates)]
      st          = [ memberDecl sb_map sbid aid args
                    | (sbid,aid,args) <- sb_state sb]
      state       = [comment "Module state" (public st)]
      ctr         = decl $ mkCtor Nothing sb
      constructor = [comment "Constructor" (public [ctr])]
      num_symbols = sum [ length (sb_parameters sb)
                        , length (sb_methodPorts sb)
                        , length [ () | (_,i) <- sb_publicDefs sb, isOkId i]
                        , length (sb_state sb)
                        , length (concatMap snd (sb_rules sb))
                        ]
      num_symbol_groups = max 1 ((num_symbols + 200) `div` 500)
      sym_init_protos = map (decl . (symInitFnProto Nothing)) [0..(num_symbol_groups-1)]
      symbol_init_fns = [comment "Symbol init methods" (private sym_init_protos)]
      adefs       = [ decl $ constant $
                                 (aTypeToCType ty) (aParamIdToCLval arg_id)
                    | (ty, arg_id, False) <- sb_parameters sb ]
      -- XXX params only need to be public if they are used in rule
      -- XXX predicates
      param_defs  = [comment "Instantiation parameters" (public adefs)]
      rdefs       = [ decl $ (aTypeToCType ty) (aPortIdToCLval id)
                    | (ty,id) <- sb_resetDefs sb ]
      reset_defs  = [comment "Reset signal definitions" (private rdefs)]
      mpdefs      = [ decl $ (aTypeToCType ty) (aPortIdToCLval arg_id)
                    | (ty, arg_id, True) <- sb_parameters sb ] ++
                    [ decl $ (aTypeToCType ty) (aPortIdToCLval (vName_to_id vn))
                    | (ty,_,vn) <- sb_methodPorts sb ]
      port_defs   = [ comment "Port definitions" (public mpdefs)]
      pdefs       = [ decl $ (aTypeToCType ty) (aDefIdToCLval id)
                    | (ty,id) <- sb_publicDefs sb ]
      public_defs = [comment "Publicly accessible definitions" (public pdefs)]
      ldefs       = [ decl $ (aTypeToCType ty) (aDefIdToCLval id)
                    | (ty,id) <- sb_privateDefs sb ]
      local_defs  = [comment "Local definitions" (private ldefs)]
      rls         = map simFnToCDeclaration (get_rule_fns sb)
      rules       = [comment "Rules" (public rls)]
      mths        = map (simFnToCDeclaration
                           . prefixSimFnName pfxMeth) (get_method_fns sb)
      methods     = [comment "Methods" (public mths)]
      rsts        = map simFnToCDeclaration (sb_resets sb)
      resets      = [comment "Reset routines" (public rsts)]
      static_rsts = map simFnToStaticCDeclaration
                      (filterOutputResets (sb_resetSources sb) (sb_resets sb))
      static_resets = [comment "Static handles to reset routines"
                               (public static_rsts)]
      rst_fn_fs   = [ decl $ resetFnDefType (mkVar (mkResetFnDefName rstId))
                        | rstId <- sb_outputResets sb ]
      rst_fn_fields =
                    [comment ("Pointers to reset fns in parent module " ++
                              "for asserting output resets")
                             (private rst_fn_fs)]
      set_rst_fns = [comment ("Functions for the parent module " ++
                              "to register its reset fns")
                             (public (map (decl . (setResetFnProto Nothing))
                                          (sb_outputResets sb)))]
      set_clk_fns = [comment ("Functions to set the elaborated clock id")
                             (public (map (decl . (setClkFnProto Nothing))
                                          (sb_domains sb)))]
      state_dump  = [comment "State dumping routine"
                             (public [decl $ dumpFnProto Nothing False "dump_state"])]
      vcd_hdr     = decl $ vcdHdrFnProto Nothing
      is_string_type (ATString _) = True
      is_string_type _            = False
      has_members = any (not . null) [ sb_resetDefs sb
                                     , [ (t,i)
                                       | (t,i) <- ((sb_privateDefs sb) ++ (sb_publicDefs sb))
                                       , not (is_string_type t)
                                       ]
                                     ]
      has_prims = or [ isPrimBlock sub | (sub,_,_) <- sb_state sb ]
      has_submodules = or [ not (isPrimBlock sub) | (sub,_,_) <- sb_state sb ]
      vcd_changes = [ decl $ vcdFnProto sb Nothing ]
                    ++
                    (if has_members
                     then [decl $ vcdDumpFnProto sb Nothing "vcd_defs" False]
                     else [])
                    ++
                    (if has_prims
                     then [decl $ vcdDumpFnProto sb Nothing "vcd_prims" False]
                     else [])
                    ++
                    (if has_submodules
                     then [decl $ vcdDumpFnProto sb Nothing "vcd_submodules" True]
                     else [])
      vcd         = [comment "VCD dumping routines" (public (vcd_hdr:vcd_changes))]
      class_decl  = c_class (pfxMod ++ (sb_name sb)) (Just "Module") $
                    concat [ clk_defs
                           , gate_defs
                           , param_defs
                           , state
                           , constructor
                           , symbol_init_fns
                           , reset_defs
                           , port_defs
                           , public_defs
                           , local_defs
                           , rules
                           , methods
                           , resets
                           , static_resets
                           , rst_fn_fields
                           , set_rst_fns
                           , set_clk_fns
                           , state_dump
                           , vcd
                           ]
      comment_str = "Class declaration for the " ++ (sb_name sb) ++ " module"
  in comment comment_str (decl class_decl)

-- Generate the initializations for defs, to be called from the ctor.
-- For wide data, we call a constructor with the size.
-- For defs which will hold system tasks, we initialize the value to "aaaa"
-- (unless it is wide, in which case the constructor for wide data already
-- does that).
mkCtorInit :: S.Set AId -> (AType,AId) -> Maybe (AId,[AExpr])
mkCtorInit task_id_set (aty@(ATBit sz),aid)
  | sz > 64     = Just (aid,[aNat sz])
  | (S.member aid task_id_set)
                = let val = ASInt defaultAId aty (ilHex (aaaa sz))
                  in  Just (aid,[val])
  | otherwise   = Nothing
mkCtorInit _ (aty@(ATTuple _),aid) =
  Just (aid, [ aNat (aSize aty) ])
-- system tasks shouldn't be returning other types (like String),
-- so no need to consult the task_id_set
mkCtorInit _ _  = Nothing

data VCDCallType = VCDDef | VCDX | VCDVal | VCDChange

mkVCDCallArgs :: VCDCallType -> AType -> String -> CCExpr -> [CCExpr]
mkVCDCallArgs ct ty name def =
  let size_arg = case ty of
                   (ATString Nothing) -> [ mkUInt32 0 ]
                   otherwise          -> [ mkUInt32 (aSize ty) ]
  in case ct of
       VCDDef    -> [ cPostInc (var "num"), mkStr name ] ++ size_arg
       VCDX      -> [ cPostInc (var "num") ] ++ size_arg
       VCDVal    -> [ cPostInc (var "num"), def ] ++ size_arg
       VCDChange -> [ var "num", def ] ++ size_arg

-- Defines the ordering we want for symbol names.
-- This needs to match the ordering used in the match_key function
-- in src/sim/module.cxx.
symOrd :: (String,Symbol) -> (String,Symbol) -> Ordering
symOrd (str1,sym1) (str2,sym2) =
    case (strCmp str1 str2) of
      LT -> LT
      EQ -> compare sym1 sym2
      GT -> GT
  where strCmp [] [] = EQ
        strCmp [] _  = LT
        strCmp _  [] = GT
        strCmp (c1:cs1) (c2:cs2) =
            case (compare (toLower c1) (toLower c2)) of
              LT -> LT
              EQ -> case (compare c1 c2) of
                      LT -> LT
                      EQ -> strCmp cs1 cs2
                      GT -> GT
              GT -> GT

simCCBlockToClassDefinition :: SBMap -> M.Map (Bool,AId) ClockDomain ->
                               SimCCBlock -> StmtsConv
simCCBlockToClassDefinition sb_map sch_map sb =
  do let scope = Just (pfxMod ++ (sb_name sb))
         state_defs = map (addSBArgs sb_map) (sb_state sb)
         task_id_set = S.fromList (sb_taskDefs sb)
         pub_def_inits = mapMaybe (mkCtorInit task_id_set) (sb_publicDefs sb)
         pri_def_inits = mapMaybe (mkCtorInit task_id_set) (sb_privateDefs sb)
         symbols = sortBy symOrd $ [ (getIdString i, SymParam i sz)
                                   -- deliberately drop non-bit parameters
                                   -- i.e. real & string
                                   | (ATBit sz, i, False) <- sb_parameters sb
                                   ] ++
                                   [ (getIdString i, SymPort i (aSize t))
                                   | (t, i, True) <- sb_parameters sb ] ++
                                   [ (getIdString i, SymPort i (aSize t))
                                   | (t, _, vn) <- sb_methodPorts sb
                                   , let i = vName_to_id vn ] ++
                                   [ (getIdString i, SymDef i (aSize t))
                                   | (t, i) <- sb_publicDefs sb
                                   , isOkId i ] ++
                                   [ (getIdString i, SymModule i)
                                   | (_, i, _) <- sb_state sb ] ++
                                   [ (getIdString i, SymRule)
                                   | (i,_) <- concatMap snd (sb_rules sb) ]
         num_symbols = length symbols
         -- we split up symbol initialization to avoid triggering
         -- gcc optimizer performance problems
         num_symbol_groups = max 1 ((num_symbols + 200) `div` 500)
         symbol_group_size = num_symbols `div` num_symbol_groups
         splitUp 1 sz xs = [xs]
         splitUp n sz xs = let (group,rest) = splitAt sz xs
                           in group:(splitUp (n-1) sz rest)
         symbol_groups = splitUp num_symbol_groups symbol_group_size (zip [0..] symbols)
     -- put the gate map into the state
     setGateMap (sb_gateMap sb)
     -- since state inits can refer to ctor arguments, declare them
     setFuncArgs (map snd3 (sb_parameters sb))
     stateinitlist <- mkStateInitList state_defs
     setFuncArgs []
     wideinitlist <- mkWideInitList (pub_def_inits ++ pri_def_inits)
     let initlist' =
             -- call the superclass constructor
             [ (var "Module") `cCall` [var "simHdl", var "name", var "parent"] ] ++
             -- initialize clock handles
             [ (var (mkClkDefName dom)) `cCall` [var badClockHandleName]
             | dom <- sb_domains sb
             ] ++
             -- set any instantiation parameters
             [ (aParamIdToC aid) `cCall` [aArgIdToC aid]
             | (_,aid,False) <- sb_parameters sb
             ] ++
             -- instantiate submodules
             stateinitlist ++
             -- initialize reset defs (to be off)
             [ (aPortIdToC aid) `cCall` [mkUInt8 1]
             | (_,aid) <- sb_resetDefs sb
             ] ++
             -- initialize module argument ports
             [ (aPortIdToC aid) `cCall` [aArgIdToC aid]
             | (_,aid,True) <- sb_parameters sb
             ] ++
             -- initialize wide defs
             wideinitlist
         port_inits =
             -- module argument ports were already taken care of,
             -- leaving just method ports to be initialized
             (concatMap mkPortInit (sb_methodPorts sb))
         reset_inits = map mkResetInit (sb_resetSources sb)
         output_reset_inits = map mkOutputResetInit (sb_outputResets sb)
         symbol_inits = (mkSymbolHdr num_symbols) ++
                        (map mkSymbolCall [0..(num_symbol_groups-1)])
         ctor_body = port_inits ++ reset_inits ++
                     output_reset_inits ++ symbol_inits
         constructor = define (mkCtor scope sb) (block ctor_body)
                           `withInits` initlist'
     rules   <- mapM (simFnToCDefinition False scope [] []) (get_rule_fns sb)
     methods <- mapM (simFnToCDefinition False scope [] []
                        . prefixSimFnName pfxMeth) (get_method_fns sb)
     resets  <- mapM (simFnToCDefinition False scope [] []) (sb_resets sb)
     let static_resets =
             map (simFnToStaticCDefinition (pfxMod ++ (sb_name sb)))
                 (filterOutputResets (sb_resetSources sb) (sb_resets sb))
     let set_rst_fns = map (setResetFnDef scope) (sb_outputResets sb)
     let set_clk_fns = map (setClkFnDef scope) (sb_domains sb)

     -- ----------------------
     -- Symbol init routines

     let symbol_init_fns =
             [ define proto (block body)
             | (n,syms) <- (zip [0..] symbol_groups)
             , let proto = symInitFnProto scope n
             , let body = concatMap mkSymbolInit syms
             ]

     -- ----------------------
     -- State dumping routines

     let label = stmt $ (var "printf") `cCall` [ mkStr "%*s%s:\n"
                                               , var "indent"
                                               , mkStr ""
                                               , var "inst_name"
                                               ]
     let hasState sb =
           let (prims,subs) = partition isPrimBlock
                                        [ sbid | (sbid,_,_) <- sb_state sb ]
           in (not (null prims)) || (any hasState (map (lookupSB sb_map) subs))
     let state_dump_body =
           if (not (hasState sb))
           then block []
           else block ([label] ++
                       [ mkSubCall inst
                                   "dump_state"
                                   [(var "indent") `cAdd` (mkUInt32 2)]
                                   Nothing
                         | (_,inst,_) <- (sb_state sb) ])
     let state_dump = define (dumpFnProto scope False "dump_state") state_dump_body

     -- --------------------
     -- VCD dumping routines

     let ids_by_clock = [ (fromJust clk, nub rl_ids)
                        | (clk, rls) <- sb_rules sb
                        , isJust clk
                        , let rules = map snd rls
                        , let rl_ids = concatMap defs_written
                                                 (concatMap sf_body rules)
                        ]
         rl_map = M.fromList [ (i,d) | (d,is) <- ids_by_clock, i <- is ]
         mc_map = M.fromList [ (i,c)
                             | (c, mths) <- sb_methods sb
                             , i <- map fst mths
                             ]
         -- RDY methods now get marked with the clock of the method,
         -- so this indirection should no longer be needed.
         lookupMClk i | isRdyId i = M.findWithDefault Nothing (dropReadyPrefixId i) mc_map
                      | otherwise = M.findWithDefault Nothing i mc_map
         (ms1,ms2) = partition (\(c,_) -> c == (Just noClockDomain))
                               (sb_methods sb)
         ms1' = M.toList $ M.unionsWith (++) $
                [ M.singleton (lookupMClk i) [(i,f)]
                | (i,f) <- concatMap snd ms1
                ]
         methods' = ms1' ++ ms2
         ids_by_clock' = [ (fromJust clk, nub mth_ids)
                         | (clk, mths) <- methods'
                         , (isJust clk) && (fromJust clk /= noClockDomain)
                         , let ms = map snd mths
                         , let mth_ids = concatMap defs_written
                                                   (concatMap sf_body ms)
                         ]
         meth_map = M.fromList [ (i,d) | (d,is) <- ids_by_clock', i <- is ]
         clk_map = M.unions [ rl_map, meth_map, sch_map ]
         prims = sortBy cmpIdByName
                        (catMaybes [ if isPrimBlock sub
                                     then Just inst
                                     else Nothing
                                   | (sub,inst,_) <- sb_state sb ])
         sub_modules = sortBy cmpIdByName
                              (catMaybes [ if isPrimBlock sub
                                           then Nothing
                                           else Just inst
                                         | (sub,inst,_) <- sb_state sb ])
         cmp_def (_,i1,_) (_,i2,_) = i1 `cmpIdByName` i2
         is_string_type (ATString _) = True
         is_string_type _            = False
         members = sortBy cmp_def $
                          [ (t,i,True)
                          | (t,i) <- (sb_resetDefs sb)
                          ] ++
                          [ (t,i,False)
                          | (t,i) <- ((sb_privateDefs sb) ++
                                      (sb_publicDefs sb))
                          , not (is_string_type t)
                          ]
         ports = sortBy cmp_def
                        [ (t,vName_to_id vn,True)
                        | (t,_,vn) <- sb_methodPorts sb ]
         num_ids = (length members) + (length ports) + (length prims)

         -- vcd definitions function

         num_init = [ (mkVar "vcd_num") `assign`
                         ((var "vcd_reserve_ids") `cCall`
                                 [var "sim_hdl", mkUInt32 (toInteger num_ids)])
                    , decl $ (unsigned . int) $
                        (mkVar "num") `assign` (var "vcd_num")
                    ]
         clk_def_loop = [ for (decl $ (unsigned . int) $ (mkVar "clk") `assign` (mkUInt32 0))
                              ((var "clk") `cLt` ((var "bk_num_clocks") `cCall` [var "sim_hdl"]))
                              (stmt $ cPreInc (var "clk"))
                              (stmt $ (var "vcd_add_clock_def") `cCall` [ var "sim_hdl"
                                                                        , var "this"
                                                                        , (var "bk_clock_name") `cCall` [var "sim_hdl", var "clk"]
                                                                        , (var "bk_clock_vcd_num") `cCall` [var "sim_hdl", var "clk"]
                                                                        ])
                        ]
         clk_aliases = [ stmt $ (var "vcd_write_def") `cCall` [var "sim_hdl",num,name,sz]
                       | (port, dom) <- sb_inputClocks sb
                       , let clk = var (mkClkDefName dom)
                       , let num = (var "bk_clock_vcd_num") `cCall` [var "sim_hdl", clk]
                       , let name = mkStr (getIdString port)
                       , let sz = mkUInt32 1
                       ]
         prim_calls = [ mkSubCall inst "dump_VCD_defs"
                                       [var "num"]
                                       (Just (mkVar "num"))
                        | inst <- prims ]
         sub_calls = [ mkSubCall inst "dump_VCD_defs"
                                      [var "l"]
                                      (Just (mkVar "num"))
                        | inst <- sub_modules ]
         member_calls = concatMap (mkVCDDef clk_map) members
         port_calls   = concatMap (mkVCDDef clk_map) ports
         new_l = cTernary ((var "levels") `cEq` (mkUInt32 0))
                          (mkUInt32 0)
                          ((var "levels") `cSub` (mkUInt32 1))
         vcd_recurse =
           [ decl $ (unsigned . int) $ (mkVar "l") `assign` new_l ] ++
           sub_calls
         scope_start = [ stmt $ (var "vcd_write_scope_start") `cCall` [var "sim_hdl", var "inst_name"] ]
         scope_end = [ stmt $ (var "vcd_write_scope_end") `cCall` [var "sim_hdl"] ]
         vcd_dump_defs_body =
           block (scope_start ++
                  num_init ++
                  clk_def_loop ++
                  clk_aliases ++
                  member_calls ++
                  port_calls ++
                  prim_calls ++
                  (if (null sub_calls)
                   then []
                   else [ if_cond ((var "levels") `cNe` (mkUInt32 1))
                                  (block vcd_recurse)
                                  Nothing
                        ]) ++
                  scope_end ++
                  [ ret (Just (var "num")) ]
                  )
         vcd_dump_defs = define (vcdHdrFnProto scope) vcd_dump_defs_body

         -- value dumping functions

         def_name  Nothing  i = aDefIdToC i
         def_name  (Just x) i = x `cDot` (aUnqualDefIdToString i)
         port_name Nothing  i = aPortIdToC i
         port_name (Just x) i = x `cDot` (aUnqualPortIdToString i)
         vcd_write ct (ty,aid,isPort) =
           let name        = getIdBaseString aid
               name_fn     = if isPort then port_name else def_name
               def         = name_fn Nothing aid
               backing_def = name_fn (Just (var "backing")) aid
           in [ stmt $ (var "vcd_write_val") `cCall`
                         ([var "sim_hdl"] ++ (mkVCDCallArgs ct ty name def))
              , (stmt backing_def) `assign` def
              ]
         vcd_write_x (ty,aid,isPort) =
           let name_fn = if isPort then port_name else def_name
               def     = name_fn Nothing aid
           in  stmt $ (var "vcd_write_x") `cCall`
                        ([var "sim_hdl"] ++ (mkVCDCallArgs VCDX ty "" def))
         vcd_write_changed target@(ty,aid,isPort) =
           let name_fn     = if isPort then port_name else def_name
               def         = name_fn Nothing aid
               backing_def = name_fn (Just (var "backing")) aid
           in [ if_cond (backing_def `cNe` def)
                        (block (vcd_write VCDChange  target))
                        Nothing
              , stmt $ cPreInc (var "num")
              ]
         member_calls_xs = map vcd_write_x members
         member_calls_changed = concatMap vcd_write_changed members
         member_calls_all = concatMap (vcd_write VCDVal) members
         port_calls_xs = map vcd_write_x ports
         port_calls_changed = concatMap vcd_write_changed ports
         port_calls_all = concatMap (vcd_write VCDVal) ports
         vcd_defs_proto = vcdDumpFnProto sb scope "vcd_defs" False
         vcd_defs_body =
           block [ decl $ (unsigned . int) $
                                (mkVar "num") `assign` (var "vcd_num")
                 , if_cond ((var "dt") `cEq` (var "VCD_DUMP_XS"))
                           (block (member_calls_xs ++ port_calls_xs))
                           (Just (if_cond ((var "dt") `cEq` (var "VCD_DUMP_CHANGES"))
                                          (block (member_calls_changed ++ port_calls_changed))
                                          (Just (block (member_calls_all ++ port_calls_all)))))
                  ]
         vcd_prims_proto = vcdDumpFnProto sb scope "vcd_prims" False
         vcd_prims_body =
           block [ mkSubCall inst
                             "dump_VCD"
                             [ var "dt"
                             , (var "backing") `cDot` (aUnqualInstIdToString inst)
                             ]
                             Nothing
                 | inst <- prims
                 ]
         vcd_submodules_proto = vcdDumpFnProto sb scope "vcd_submodules" True
         vcd_submodules_body =
           block [ mkSubCall inst
                             "dump_VCD"
                             [ var "dt"
                             , var "levels"
                             , (var "backing") `cDot` (aUnqualInstIdToString inst)
                             ]
                             Nothing
                 | inst <- sub_modules
                 ]
         vcd_dump_body =
           block ((if (null members)
                   then []
                   else [ stmt $ (var "vcd_defs") `cCall` [var "dt", var "backing"] ])
                  ++
                   (if (null prims)
                    then []
                    else [ stmt $ (var "vcd_prims") `cCall` [var "dt", var "backing"] ])
                  ++
                   (if (null sub_modules)
                    then []
                    else [ if_cond ((var "levels") `cNe` (mkUInt32 1))
                                   (stmt $ (var "vcd_submodules") `cCall` [ var "dt"
                                                                          , (var "levels") `cSub` (mkUInt32 1)
                                                                          , var "backing"
                                                                          ])
                                   Nothing
                         ])
                 )
         vcd_dump = define (vcdFnProto sb scope) vcd_dump_body
         vcd_dump_fns = (if (null members)
                         then []
                         else [ define vcd_defs_proto vcd_defs_body ])
                        ++
                        (if (null prims)
                         then []
                         else [ define vcd_prims_proto vcd_prims_body ])
                        ++
                        (if (null sub_modules)
                         then []
                         else [ define vcd_submodules_proto vcd_submodules_body ])
         vcds = [vcd_dump_defs, vcd_dump] ++ vcd_dump_fns

     -- -------------------
     -- Put it all together
     let fns =  [comment "Constructor" constructor]
             ++ [comment "Symbol init fns" (blankLines 0)]
             ++ symbol_init_fns
             ++ [comment "Rule actions" (blankLines 0)]
             ++ rules
             ++ [comment "Methods" (blankLines 0)]
             ++ methods
             ++ [comment "Reset routines" (blankLines 0)]
             ++ resets
             ++ [comment "Static handles to reset routines" (blankLines 0)]
             ++ static_resets
             ++ [comment ("Functions for the parent module " ++
                          "to register its reset fns") (blankLines 0)]
             ++ set_rst_fns
             ++ [comment "Functions to set the elaborated clock id"
                         (blankLines 0)]
             ++ set_clk_fns
             ++ [comment "State dumping routine" state_dump]
             ++ [comment "VCD dumping routines" (blankLines 0)]
             ++ vcds
     return $ intersperse (blankLines 1) fns

-- Generate the schedule function definitions for a SimCCSched.
-- We do not collect wide temporaries of top modules in schedule because
-- they are used in boolean computations only which do not need optimized
-- function implementation
simCCScheduleToFunctionDefinition :: SimCCBlock -> SimCCSched -> StmtsConv
simCCScheduleToFunctionDefinition top ssched =
  do let c_args = [ (userType "tSimStateHdl") (mkVar "simHdl")
                  , (ptr . void) (mkVar "instance_ptr") ]
         top_decl = let ty = moduleType top []
                        -- XXX for cCast, we need the type, not a combinator
                        modName = pfxMod ++ fst (sb_naming_fn top [])
                        inst_ptr_ty = ptrType (classType modName)
                        inst = cCast inst_ptr_ty (var "instance_ptr")
                    in  decl . reference . ty $
                            (mkVar "INST_top") `assign` (cDeref inst)
         schedFnToCDef = simFnToCDefinition True Nothing c_args [top_decl]
     fn1 <- schedFnToCDef (sched_fn ssched)
     case (sched_after_fn ssched) of
       (Just f) -> do fn2 <- schedFnToCDef f
                      return [fn1,fn2]
       Nothing  -> return [fn1]


-- ========================
-- Helper routines for collecting wide data declarations
wideLocalDef :: SimCCFnStmt -> [AId]
wideLocalDef (SFSDef _ (ty, aid) _) = if wideDataType ty
                                      then [aid]
                                      else []
wideLocalDef _ = []

-- return True if this type is represented as wide data
-- (i.e. it is larger than 64 bits, or it is a tuple)
wideDataType :: AType -> Bool
wideDataType (ATBit sz) = sz > 64
wideDataType (ATTuple ts) = True
wideDataType _ = False


-- ========================
-- Pretty-printing routines

ppSBId :: SBId -> Doc
ppSBId id = text (itos id)

instance PPrint SimCCBlock where
  pPrint d p sb =
    let label =     (text "SimCCBlock")
                <+> (text (sb_name sb))
                <+> (pparen True (ppSBId (sb_id sb)))
                <>  colon
        state = (text "state:") <+> (pPrint d 0 (sb_state sb))
        rst_defs = (text "reset defs:") <+> (pPrint d 0 (sb_resetDefs sb))
        pub_defs = (text "public defs:") <+> (pPrint d 0 (sb_publicDefs sb))
        pri_defs = (text "private defs:") <+> (pPrint d 0 (sb_privateDefs sb))
        rules = (text "rules:") <+> (pPrint d 0 (sb_rules sb))
        methods = (text "methods:") <+> (pPrint d 0 (sb_methods sb))
        resets = (text "resets:") <+> (pPrint d 0 (sb_resets sb))
        task_defs = (text "task defs:") <+> (pPrint d 0 (sb_taskDefs sb))
        reset_srcs = (text "reset srcs:") <+> (pPrint d 0 (sb_resetSources sb))
        input_resets =
            (text "input resets:") <+> (pPrint d 0 (sb_inputResets sb))
        output_resets =
            (text "output resets:") <+> (pPrint d 0 (sb_outputResets sb))
        body = vsep [ state
                    , rst_defs
                    , pub_defs
                    , pri_defs
                    , rules
                    , methods
                    , resets
                    , task_defs
                    , reset_srcs
                    , input_resets
                    , output_resets
                    ]
    in label $+$ (nest 2 body)

ppDecl :: (AType,AId) -> Doc
ppDecl (ty,id) = (pPrint PDReadable 0 ty) <+> (pPrint PDReadable 0 id)

instance PPrint SimCCFn where
  pPrint d p (SimCCFn name args ret body) =
    let ty = case ret of
               (Just t) -> pPrint d 0 t
               Nothing  -> text "void"
        arg_list = pparen True (sepList (map ppDecl args) comma)
        stmts = vsep (map (pPrint d 0) body)
    in (ty <+> (text name) <> arg_list) $+$ (nest 2 stmts)

instance PPrint SimCCFnStmt where
  pPrint d p (SFSDef _ decl Nothing) = (text "define") <+> (ppDecl decl)
  pPrint d p (SFSDef _ decl (Just expr)) =
    (text "define") <+> (ppDecl decl) <+> (text "=") <+> (pPrint d 0 expr)
  pPrint d p (SFSAssign _ aid expr) =
    (pPrint d 0 aid) <+> (text "=") <+> (pPrint d 0 expr)
  pPrint d p (SFSAction action) = pPrint d 0 action
  pPrint d p (SFSAssignAction _ aid action _) =
    (pPrint d 0 aid) <+> (text "=") <+> (pPrint d 0 action)
  pPrint d p (SFSRuleExec ruleId) =
    (pPrint d 0 ruleId)
  pPrint d p (SFSCond cond t f) =
    (text "if (") <> (pPrint d 0 cond) <> (text ")") $+$
    (nest 2 (vsep (map (pPrint d 0) t))) $+$
    (text "else") $+$
    (nest 2 (vsep (map (pPrint d 0) f)))
  pPrint d p (SFSMethodCall obj meth args) =
    (pPrint d 0 obj) <> (text ".") <> (text (getIdBaseString meth)) <>
    (pparen True (commaSep (map (pPrint d 0) args)))
  pPrint d p (SFSFunctionCall obj func args) =
    (pPrint d 0 obj) <> (text ".") <> (text func) <>
    (pparen True (commaSep (map (pPrint d 0) args)))
  pPrint d p (SFSResets stmts) =
    (text "if (do_reset_ticks())") $+$
    (nest 2 (vsep (map (pPrint d 0) stmts)))
  pPrint d p (SFSReturn Nothing) = (text "return")
  pPrint d p (SFSReturn (Just expr)) = (text "return") <+> (pPrint d 0 expr)
  pPrint d p (SFSOutputReset rstId val) =
    (text "assertOutputReset(" <>
     pPrint d 0 rstId <> text ", " <> pPrint d 0 val <> text ")")

instance PPrint SimCCSched where
  pPrint d p (SimCCSched clk edge fn blocks) =
    let label   = text "SimCCSched"
        clk_str = (if edge then (text "posedge") else (text "negedge")) <+>
                  (pPrint d 0 clk)
        func    = pPrint d 0 fn
        blks    = (text "applies to blocks:") <+> (pPrint d 0 blocks)
    in label <+> clk_str <> (text ":") $+$ (nest 2 (func $+$ blks))

instance PPrint SimCCClockGroup where
  pPrint d p (SimCCClockGroup canonical instances) =
    let name = pPrint d 0 canonical
        inst_list = pPrint d 0 instances
    in name <+> (text "names") <+> inst_list

instance PPrint SimCCReset where
  pPrint d p (SimCCReset n port fn) =
    let label = (text "SimCCReset ") <+> (pparen True (text (show n)))
        name  = case port of
                  Just (i,p) -> text (i ++ "$" ++ p)
                  Nothing    -> text "primary reset"
        func  = pPrint d 0 fn
    in label <+> name <> (text ":") $+$ (nest 2 func)

-- ==================================================
-- NFData instances (needed by phase dumping routines)

instance NFData SimCCBlock where
  rnf (SimCCBlock n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19) =
    rnf19 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19

instance NFData SimCCFn where
  rnf (SimCCFn n a r b) = rnf4 n a r b

instance NFData SimCCFnStmt where
  rnf (SFSDef b t me) = rnf3 b t me
  rnf (SFSAssign b id e) = rnf3 b id e
  rnf (SFSAction act) = rnf act
  rnf (SFSAssignAction b id act t) = rnf4 b id act t
  rnf (SFSRuleExec rid) = rnf rid
  rnf (SFSCond e ts fs) = rnf3 e ts fs
  rnf (SFSMethodCall id1 id2 es) = rnf3 id1 id2 es
  rnf (SFSFunctionCall id fn es) = rnf3 id fn es
  rnf (SFSResets stmts) = rnf stmts
  rnf (SFSReturn me) = rnf me
  rnf (SFSOutputReset id e) = rnf2 id e

instance NFData SimCCSched where
  rnf (SimCCSched clk pos fn aft) = rnf4 clk pos fn aft

instance NFData SimCCClockGroup where
  rnf (SimCCClockGroup can insts) = rnf2 can insts

instance NFData SimCCReset where
  rnf (SimCCReset num port fn) = rnf3 num port fn
