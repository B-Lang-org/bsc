{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, DeriveDataTypeable #-}
module ISyntax(
        IPackage(..),
        IDef(..),
        IKind(..),
        IType(..),
        IExpr(..),
        ConTagInfo(..),
        IConInfo(..),
        IRules(..),
        IRule(..),
        IEFace(..),
        IModule(..),
        IAbstractInput(..),
        IStateVar(..),
        PortTypeMap,
        IClock,
        IReset,
        IInout,
        ILazyArray,
        ArrayCell(..),
        Pred(..),
        PTerm(..),
        getClockMap,
        getResetMap,
        getVModInfo,
        iRUnion,
        iRUnionPreempt,
        iRUnionUrgency,
        iRUnionExecutionOrder,
        iRUnionMutuallyExclusive,
        iRUnionConflictFree,
        iREmpty,
        uniquifyRules,
        fdVars,
        normITAp,
        splitITAp,
        aTVars,
        fTVars,
        itArrow,
        iToCT,
        iToCK,
        iAp,
        iAP,
        fVars,
        ftVars,
        aVars,
        mkNumConT,
        showTypeless,
        showTypelessRules,
        getIExprPosition,
        getITypePosition,
        getIExprPositionCross,
--        getITypePositionCross,
        getIRuleId,
        getIRuleStateLoc,
        sameClockDomain,
        inClockDomain,
        getClockDomain,
        isNoClock,
        isMissingDefaultClock,
        makeClock,
        getClockWires,
        setClockWires,
        makeReset,
        getResetWire,
        getResetClock,
        getResetId,
        isNoReset,
        isMissingDefaultReset,
        makeInout,
        getInoutWire,
        getInoutClock,
        getInoutReset,
        getWireInfo,
        isIConInt, isIConReal, isIConParam
        ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import System.IO(Handle)
import qualified Data.Map as M
import Data.List(intercalate)

import qualified Data.Array as Array
import IntLit
import Undefined
import Eval
import Id
import Wires(ResetId, ClockDomain, ClockId, noClockId, noResetId, noDefaultClockId, noDefaultResetId, WireProps)
import IdPrint
import PreIds(idSizeOf, idId, idBind, idReturn, idPack, idUnpack, idMonad, idLiftModule, idBit, idFromInteger, idTNumToStr)
import Backend
import Prim(PrimOp(..))
import TypeOps
import ConTagInfo
import VModInfo(VModInfo, vArgs, vName, VName(..), {- VeriPortProp(..), -}
                VArgInfo(..), VFieldInfo(..), isParam, VWireInfo)
import Pragma(Pragma, PProp, RulePragma, ISchedulePragma,
              CSchedulePragma, SchedulePragma(..), DefProp,
              extractSchedPragmaIds, removeSchedPragmaIds, mapSPIds)
import Position
import Data.Maybe
import FStringCompat(mkNumFString)

import qualified Data.Set as S
import Flags
import Error(internalError, EMsg, ErrMsg(..))
import PFPrint
import IStateLoc(IStateLoc)
import IType
import qualified Data.Generics as Generic

-- ============================================================
-- IPackage, IModule

-- A package of top-level definitions and pragmas
-- * This corresponds to a .bo file.
-- * During iExpand, top-level defs for modules are synthesized
--   and those defs are replaceds with new defs that are merely
--   import-BVI of the generated module.
--
data IPackage a
        = IPackage {
              -- package name
              ipkg_name :: Id,
              -- linked packages (name, signature)
              ipkg_depends :: [(Id, String)],
              -- pragmas
              ipkg_pragmas :: [Pragma],
              -- definition list
              ipkg_defs :: [IDef a]
          }
     deriving (Eq, Ord, Show, Generic.Data, Generic.Typeable)

-- An elaborated module
-- * These are created during iExpand for each module to be synthesized
--   from the IPackage.
data IModule a
        = IModule {
                imod_name :: Id,                      -- module name
                imod_is_wrapped :: Bool,              -- function wrapper?
                imod_backend_specifc :: Maybe Backend,
                imod_external_wires :: VWireInfo,     -- boundary wire information (clock, reset, arguments, etc.)
                imod_pragmas :: [Pragma],             -- all top level pragmas
                -- XXX The list of type args is always empty (unused).
                -- If we supported generation of modules with numeric type
                -- variables, they would be in this list.
                imod_type_args :: [(Id, IKind)],      -- package type arguments
                imod_wire_args :: [IAbstractInput],   -- package (wire) arguments
                imod_clock_domains :: [(ClockDomain, [IClock a])], -- clocks (internal and external)
                imod_resets :: [IReset a],              -- resets (internal and external)
                imod_state_insts :: [(Id, IStateVar a)], -- state elements
                imod_port_types :: PortTypeMap, -- map from state variable -> port -> source type
                imod_local_defs :: [IDef a],            -- local definitions
                imod_rules :: IRules a,                 -- rules
                imod_interface :: [IEFace a],           -- package interface
                imod_ffcallNo :: Int,                    -- next available unique ffcalNo
                -- comments on submodule instantiations
                imod_instance_comments :: [(Id, [String])]
          }
         deriving (Show, Generic.Data, Generic.Typeable)

getWireInfo :: IModule a -> VWireInfo
getWireInfo = imod_external_wires

-- Map from submod instance name to a map from port to its source type.
-- Toplevel ports of the current module are represented in the same map
-- using the Nothing value in place of an instance name.
type PortTypeMap = M.Map (Maybe Id) (M.Map VName IType)

data IDef a = IDef Id IType (IExpr a) [DefProp]
        deriving (Eq, Ord, Show, Generic.Data, Generic.Typeable)

data IAbstractInput =
        -- simple input using one port
        IAI_Port (Id, IType) |
        -- clock osc and maybe gate
        IAI_Clock Id (Maybe Id) |
        IAI_Reset Id |
        IAI_Inout Id Integer
        -- room to add other types here, like:
        --   IAI_Struct [(Id, IType)]
    deriving (Eq, Show, Generic.Data, Generic.Typeable)

data IEFace a = IEFace {
        -- This is either an actual method or a ready signal for another
        -- method.  Use 'isRdyId' to determine which.  Use 'mkRdyId' on
        -- the name of an actual method to construct the name of its
        -- associated ready method.
        ief_name :: Id,
        -- arguments
        ief_args :: [(Id, IType)],
        -- Prior to 'iSplitIface', 'ief_value' contains the expression for
        -- the whole method and 'ief_body' is empty.  After 'iSplitIface',
        -- 'ief_value' contains the return value (if any) and 'ief_body'
        -- contains the rules (the Actions) (if any).
        -- XXX Should we use a different type for these two forms?
        ief_value :: (Maybe (IExpr a, IType)),
        ief_body :: (Maybe (IRules a)),
        ief_wireprops :: WireProps,
        ief_fieldinfo :: VFieldInfo
     }
    deriving (Show, Generic.Data, Generic.Typeable)


-- ---------------
-- IStateVar

-- a state variable (foreign module instantiation)
data IStateVar a = IStateVar {
    isv_is_arg :: Bool,           -- real state variable (or argument)
    isv_is_user_import :: Bool,   -- whether it is a foreign module
    isv_uid :: Int,               -- unique number
    isv_vmi :: VModInfo,          -- foreign module info
    isv_iargs :: [IExpr a],       -- params + arguments
    isv_type :: IType,            -- type of the svar (like "Prelude.VReg")
    -- The next list corresponds to vFields in the VModInfo, but cannot be
    -- stored there, because VModInfo is created before types are known:
    isv_meth_types :: [[IType]],  -- method types
    isv_clocks :: [(Id, IClock a)], -- named clocks
    isv_resets :: [(Id, IReset a)], -- named resets
    isv_isloc :: IStateLoc        -- instantiation path
}
    deriving (Show, Generic.Data, Generic.Typeable)

getResetMap :: IStateVar a -> [(Id, IReset a)]
getResetMap = isv_resets

getClockMap :: IStateVar a -> [(Id, IClock a)]
getClockMap = isv_clocks

getVModInfo :: IStateVar a -> VModInfo
getVModInfo = isv_vmi

instance Eq (IStateVar a) where
    a == b =  isv_uid a == isv_uid b

instance Ord (IStateVar a) where
    a `compare` b =  isv_uid a `compare` isv_uid b

-- ==============================
-- IRule

-- last Id is original rule if rule has been split, Nothing otherwise
-- (argument descriptions are guesses based on ARule)
data IRule a =
    IRule {
      -- rule name
      irule_name :: Id,
      -- rule pragmas, e.g., no-implicit-conditions
      irule_pragmas :: [RulePragma],
      -- String that describes the rule
      irule_description :: String,
      -- Rule wire properties
      irule_wire_properties :: WireProps,
      -- Rule predicate
      irule_pred :: (IExpr a),
      -- Rule body
      irule_body :: (IExpr a),
      {- orig rule - for splitting -}
      irule_original :: (Maybe Id),
      -- Instantiation hierarchy
      irule_state_loc :: IStateLoc
      }
    deriving (Show, Generic.Data, Generic.Typeable)

instance NFData (IRule a) where
    rnf (IRule i ps s wp r1 r2 orig isl) = rnf8 i ps s wp r1 r2 orig isl

getIRuleId :: IRule a -> Id
getIRuleId = irule_name

getIRuleStateLoc :: IRule a -> IStateLoc
getIRuleStateLoc = irule_state_loc

data IRules a = IRules [ISchedulePragma] [IRule a]
    deriving (Show, Generic.Data, Generic.Typeable)

instance NFData (IRules a) where
    rnf (IRules sps rs) = rnf2 sps rs


-- renames the rules according to the Id,Id list
renameIRules :: [(Id,Id)] -> IRules a -> IRules a
renameIRules [] rls = rls
renameIRules idmap rls@(IRules schedPara rules) = IRules newSchedPara newRules
    where
    newRules = map (renameIRule idmap) rules
    newSchedPara = mapSPIds (renameFromMap idmap) schedPara --  map (renameSchedPara idmap) schedPara

renameIRule ::  [(Id,Id)] -> IRule a -> IRule a
renameIRule idmap orig = newRule
    where
    newId = lookup (irule_name orig) idmap
    newRule = if ( isNothing newId )
              then orig
              else orig {irule_name = (fromJust newId)}

renameFromMap ::  (Eq a) =>  [(a,a)] -> a -> a
renameFromMap idmap id = fromMaybe id newId
    where
    newId = lookup id idmap

-- Return a new second set of rules, with names changed to not clash
-- with a first set of rules
uniquifyRules :: Flags -> Integer -> IRules a -> IRules a -> (Integer, IRules a)
uniquifyRules flags suf r1@(IRules _ rs1) r2@(IRules sps2 rs2) =
    if (ruleNameCheck flags)
    then let rids1 = map getIRuleId rs1
             rids2 = map getIRuleId rs2
             -- rename the rules in r2 if needed
             (_, idmap) = genUniqueIdsAndMap rids1 rids2
         in  (suf, renameIRules idmap r2)
    else let fn r (n, m, rs) = let oldname = irule_name r
                                   (basename, _) = stripId_Suffix oldname
                                   newname = addId_Suffix basename n
                                   r' = r { irule_name = newname }
                                   m' = ((oldname,newname):m)
                               in  (n+1, m', r':rs)
             (suf', idmap, rs2') = foldr fn (suf, [], []) rs2
             sps2' = mapSPIds (renameFromMap idmap) sps2
         in  (suf', IRules sps2' rs2')

iRUnion :: Flags -> Integer -> IRules a -> IRules a -> (Integer, IRules a, [EMsg])
iRUnion flags suf r1@(IRules _ rs1) r2 =
    let (suf', r2_unique@(IRules _ rs2)) = uniquifyRules flags suf r1 r2
        (errs, sps) = checkRUnionAttributes r1 r2_unique
    in  (suf', IRules sps (rs1 ++ rs2), errs)

iRUnionPreempt :: Flags -> Integer -> IRules a -> IRules a -> (Integer, IRules a, [EMsg])
iRUnionPreempt flags suf r1@(IRules _ rs1) r2 =
    let (suf', r2_unique@(IRules _ rs2)) = uniquifyRules flags suf r1 r2
        (errs, sps) = checkRUnionAttributes r1 r2_unique
        sps3 = [SPPreempt (map getIRuleId rs1) (map getIRuleId rs2)]
    in  (suf', IRules (sps3 ++ sps) (rs1 ++ rs2), errs)

iRUnionUrgency :: Flags -> Integer -> IRules a -> IRules a -> (Integer, IRules a, [EMsg])
iRUnionUrgency flags suf r1@(IRules _ rs1) r2 =
    let (suf', r2_unique@(IRules _ rs2)) = uniquifyRules flags suf r1 r2
        (errs, sps) = checkRUnionAttributes r1 r2_unique
        sps3 = [ SPUrgency [rid1, rid2]
                   | rid1 <- map getIRuleId rs1,
                     rid2 <- map getIRuleId rs2 ]
    in  (suf', IRules (sps3 ++ sps) (rs1 ++ rs2), errs)

iRUnionExecutionOrder :: Flags -> Integer -> IRules a -> IRules a -> (Integer, IRules a, [EMsg])
iRUnionExecutionOrder flags suf r1@(IRules _ rs1) r2 =
    let (suf', r2_unique@(IRules _ rs2)) = uniquifyRules flags suf r1 r2
        (errs, sps) = checkRUnionAttributes r1 r2_unique
        sps3 = [ SPExecutionOrder [rid1, rid2]
                   | rid1 <- map getIRuleId rs1,
                     rid2 <- map getIRuleId rs2 ]
    in  (suf', IRules (sps3 ++ sps) (rs1 ++ rs2), errs)

iRUnionPairwiseSchedPragma :: Flags -> Integer
                           -> ([[Id]] -> ISchedulePragma)
                           -> IRules a -> IRules a -> (Integer, IRules a, [EMsg])
iRUnionPairwiseSchedPragma flags suf sched_pragma r1@(IRules _ rs1) r2 =
    let (suf', r2_unique@(IRules _ rs2)) = uniquifyRules flags suf r1 r2
        (errs, sps) = checkRUnionAttributes r1 r2_unique
        sps3 = [sched_pragma [ map getIRuleId rs1, map getIRuleId rs2 ]]
    in  (suf', IRules (sps3 ++ sps) (rs1 ++ rs2), errs)

iRUnionMutuallyExclusive :: Flags -> Integer -> IRules a -> IRules a -> (Integer, IRules a, [EMsg])
iRUnionMutuallyExclusive flags suf r1 r2 =
    iRUnionPairwiseSchedPragma flags suf SPMutuallyExclusive r1 r2

iRUnionConflictFree :: Flags -> Integer -> IRules a -> IRules a -> (Integer, IRules a, [EMsg])
iRUnionConflictFree flags suf r1 r2 =
    -- trace "iRUnionConflictFree" $
    iRUnionPairwiseSchedPragma flags suf SPConflictFree r1 r2

iREmpty :: IRules a
iREmpty = IRules [] []

-- Check that all rule attribute are defined in the given (joined) rules
-- XXX Is that the behavior we want?
-- Return the pragmas with the bad names filtered out
checkRUnionAttributes :: IRules a -> IRules a -> ([EMsg], [ISchedulePragma])
checkRUnionAttributes (IRules sps1 rs1) (IRules sps2 rs2) =
    let
        definedIds = map getIRuleId rs1 ++ map getIRuleId rs2
        attrIds = extractSchedPragmaIds (sps1 ++ sps2)

        testMap  = M.fromList $ zip definedIds (repeat (0 :: Int ))
        checkMap = M.fromList $ zip attrIds (repeat (0 :: Int ))

        badIds :: [Id]
        badIds = map fst $ M.toList $ M.difference checkMap testMap

        mkErr i = (getIdPosition i, EUnknownRuleIdAttribute (pfpString i))
        msgs = map mkErr badIds
        sps' = if (null badIds)
               then sps1 ++ sps2
               else removeSchedPragmaIds badIds (sps1 ++ sps2)
    in
        (msgs, sps')


normITAp :: IType -> IType -> IType
normITAp (ITAp (ITCon op _ _) (ITNum x)) (ITNum y) | isJust (res) =
    mkNumConT (fromJust res)
  where res = opNumT op [x, y]
normITAp (ITCon op _ _) (ITNum x) | isJust (res) =
    mkNumConT (fromJust res)
  where res = opNumT op [x]
normITAp (ITAp (ITCon op _ _) (ITStr x)) (ITStr y) | isJust (res) =
    ITStr (fromJust res)
  where res = opStrT op [x, y]
normITAp (ITCon op _ _) (ITNum x) | op == idTNumToStr =
    ITStr (mkNumFString x)

normITAp f@(ITCon op _ _) a | op == idSizeOf && notVar a =
        -- trace ("normITAp: " ++ ppReadable (ITAp f a)) $
           ITAp f a
  where notVar (ITVar _) = False
        notVar _ = True

normITAp f@(ITCon op _ _) a | op == idId = a

normITAp f a = ITAp f a

aTVars :: IType -> S.Set Id
aTVars (ITForAll i _ t) = S.insert i (aTVars t)
aTVars (ITAp f a) = (aTVars f) `S.union` (aTVars a)
aTVars (ITVar i) = S.singleton i
aTVars (ITCon _ _ _) = S.empty
aTVars (ITNum _) = S.empty
aTVars (ITStr _) = S.empty

fTVars :: IType -> S.Set Id
fTVars (ITForAll i _ t) = S.delete i (fTVars t)
fTVars (ITAp f a) = fTVars f `S.union` fTVars a
fTVars (ITVar i) = S.singleton i
fTVars (ITCon _ _ _) = S.empty
fTVars (ITNum _) = S.empty
fTVars (ITStr _) = S.empty


splitITAp :: IType -> (IType, [IType])
splitITAp (ITAp f a) = let (l, as) = splitITAp f
                       in  (l, as ++ [a])
splitITAp t = (t, [])


-- ==============================
-- IExpr

-- a is a placeholder type for the actual data stored in heap cells
-- so that all things that work on generic IExprs do not touch the heap
-- and to prevent exposing evaluator implementation details in ISyntax
data IExpr a
        = ILam Id IType (IExpr a)        -- vanishes after IExpand
        | IAps (IExpr a) [IType] [IExpr a]
        | IVar Id                        -- vanishes after IExpand
        | ILAM Id IKind (IExpr a)        -- vanishes after IExpand
        | ICon Id (IConInfo a)
        -- IRef is only used during reduction, it refers to a "heap" cell
        | IRefT IType !Int a                  -- vanishes after IExpand
          deriving (Generic.Data, Generic.Typeable)

instance Show (IExpr a) where
  show (ILam i t e)   = "(ILam " ++ show i ++ " " ++ show t ++ " " ++ show e ++ ")"
  show (IAps f ts es) = "(IAps " ++ show f ++ " " ++ show ts ++ " " ++ show es ++ ")"
  show (IVar i)       = "(IVar " ++ show i ++ ")"
  show (ILAM i k e)   = "(ILAM " ++ show i ++ " " ++ show k ++ " " ++ show e ++ ")"
  show (ICon i ic)    = "(ICon " ++ show i ++ " " ++ show ic ++ ")"
  show (IRefT t p _)  = "(IRefT " ++ show t ++ " " ++ "_" ++ show p ++ ")"

cmpE :: IExpr a -> IExpr a -> Ordering
cmpE (ILam i1 _ e1)  (ILam i2 _ e2)  =
        case compare i1 i2 of
        EQ -> cmpE e1 e2
        o  -> o
cmpE (ILam _ _ _)    _               = LT

cmpE (IAps _  _ _)   (ILam _ _ _)    = GT
cmpE (IAps e1 ts1 es1) (IAps e2 ts2 es2) =
        case compare e1 e2 of
        EQ ->
                case compare es1 es2 of
                EQ -> compare ts1 ts2
                o -> o
{-
                case compare ts1 ts2 of
                EQ -> compare es1 es2
                o  -> o
-}
        o  -> o
cmpE (IAps _  _ _)   _               = LT

cmpE (IVar _)        (ILam _ _ _)    = GT
cmpE (IVar _)        (IAps _ _ _)    = GT
cmpE (IVar i1)       (IVar i2)       = compare i1 i2
cmpE (IVar _)        _               = LT

cmpE (ILAM _ _ _)    (ILam _ _ _)    = GT
cmpE (ILAM _ _ _)    (IAps _ _ _)    = GT
cmpE (ILAM _ _ _)    (IVar _)        = GT
cmpE (ILAM i1 _ e1)  (ILAM i2 _ e2)  =
        case compare i1 i2 of
        EQ -> cmpE e1 e2
        o  -> o
cmpE (ILAM _ _ _)    (IRefT _ _ _)   = GT -- ???????

cmpE (ILAM _  _ _)   _               = LT

cmpE (ICon _ _)      (ILam _ _ _)    = GT
cmpE (ICon _ _)      (IAps _ _ _)    = GT
cmpE (ICon _ _)      (IVar _)        = GT
cmpE (ICon i1 ic1) (ICon i2 ic2)     =
        case compare i1 i2 of
        EQ -> case (cmpC ic1 ic2) of
                -- inlined positions need to be considered in equality tests
                EQ -> let mposs1 = getIdInlinedPositions i1
                          mposs2 = getIdInlinedPositions i2
                      in  compare mposs1 mposs2
                o  -> o
        o  -> o
cmpE (ICon _ _)      _               = LT

cmpE (IRefT _ _ _)   (ILam _ _ _)    = GT
cmpE (IRefT _ _ _)   (IAps _ _ _)    = GT
cmpE (IRefT _ _ _)   (IVar _)        = GT
cmpE (IRefT _ _ _)   (ICon _ _)      = GT
cmpE (IRefT _ p1 _)  (IRefT _ p2 _)  = compare p1 p2                -- XXX

cmpE (IRefT _ _ _)     (ILAM _ _ _)  = LT -- ??????????

{- all cases are covered above, so the compiler complains about this line:
cmpE e1              e2              = internalError ("not match in cmpE " ++ ppReadable (e1,e2))
-}

instance Eq (IExpr a) where
    x == y  =  cmpE x y == EQ
    x /= y  =  cmpE x y /= EQ

instance Ord (IExpr a) where
    compare x y = cmpE x y

-- ==============================
-- IClock

-- ISyntax clocks
data IClock a = IClock { ic_id      :: ClockId,      -- unique id
                         ic_domain  :: ClockDomain,  -- unique id for clock "family"
                         ic_wires   :: IExpr a       -- expression for clock wires
                                              -- will be ICSel of (ICStateVar) or ICTuple of ICModPorts / ICInt (1) for ungated clocks
                                              -- theoretically ICTuple (ICInt (0), ICInt (0)) for noClock, but should  not appear
                     } deriving (Generic.Data, Generic.Typeable)

-- break recursion of wires so that showing a clock does not loop
instance Show (IClock a) where
  show (IClock clockid domain wires) = "IClock id: " ++ (show clockid) ++ " domain: " ++ (show domain) ++ " " ++ (ppString wires)

-- simple instance for now
instance PPrint (IClock a) where
  pPrint p d c = text (show c)

instance Eq (IClock a) where
  IClock {ic_id = x} == IClock {ic_id = y} = x == y

instance Ord (IClock a) where
  IClock {ic_id = x} `compare` IClock {ic_id = y} = x `compare` y

instance NFData (IClock a) where
  -- XXX clock wires can be recursive (so just check equality)
  rnf c = (c==c) `seq` ()

makeClock :: ClockId -> ClockDomain -> IExpr a -> IClock a
makeClock clockid domain wires = IClock { ic_id     = clockid,
                                          ic_domain = domain,
                                          ic_wires  = wires }

getClockWires :: IClock a -> IExpr a
getClockWires = ic_wires

-- used to implement primReplaceClockGate
setClockWires :: IClock a -> IExpr a -> IClock a
setClockWires ic e = ic { ic_wires = e }

getClockDomain :: IClock a -> ClockDomain
getClockDomain = ic_domain

-- noClock value defined in ISyntaxUtil
isNoClock :: IClock a -> Bool
isNoClock IClock {ic_id = clockid} = clockid == noClockId

--
isMissingDefaultClock :: IClock a -> Bool
isMissingDefaultClock (IClock {ic_id = clockid}) = clockid == noDefaultClockId

sameClockDomain :: IClock a -> IClock a -> Bool
sameClockDomain (IClock {ic_domain = d1}) (IClock {ic_domain = d2}) = d1 == d2

inClockDomain :: ClockDomain -> IClock a -> Bool
inClockDomain d (IClock {ic_domain = d'}) = d == d'

-- ==============================
-- IReset

-- ISyntax resets
-- XXX this will change as reset is more fully implemented
data IReset a = IReset { ir_id   :: ResetId, -- unique id
                         ir_clock :: IClock a, -- associated clock (may be noClock)
                         -- reset_sync :: Bool, -- synchronous or asynchronous
                         ir_wire :: IExpr a  -- expression for reset wire
                                             -- currently must be an ICModPort or 0,
                                             -- since we do not support reset output
                       } deriving (Generic.Data, Generic.Typeable)

-- must break recursion of wire so showing a reset output does not loop
instance Show (IReset a) where
  show (IReset resetid clock wire) = "IReset id: " ++ (show resetid) ++ " clock: " ++ (show clock) ++ " " ++ (ppString wire)

-- simple instance for now
instance PPrint (IReset a) where
  pPrint p d r = text (show r)

instance Eq (IReset a) where
  IReset {ir_id = x} == IReset {ir_id = y} = x == y

instance Ord (IReset a) where
  IReset {ir_id = x} `compare` IReset {ir_id = y} = x `compare` y

instance NFData (IReset a) where
  -- XXX reset wires can be recursive (so just check equality)
  rnf r = (r==r) `seq` ()

makeReset :: ResetId -> IClock a -> IExpr a -> IReset a
makeReset i c w = IReset { ir_id = i, ir_clock = c, ir_wire = w }

getResetWire :: IReset a -> IExpr a
getResetWire = ir_wire

getResetClock :: IReset a -> IClock a
getResetClock = ir_clock

getResetId :: IReset a -> ResetId
getResetId = ir_id

-- noReset defined in ISyntaxUtil (like noClock)
isNoReset :: IReset a -> Bool
isNoReset IReset { ir_id = i } = i == noResetId

isMissingDefaultReset :: IReset a -> Bool
isMissingDefaultReset (IReset { ir_id = i }) = i == noDefaultResetId

-- ==============================
-- IInout

data IInout a =
    IInout { io_clock :: IClock a, -- associated clock (may be noClock)
             io_reset :: IReset a, -- associated reset (may be noReset)
             io_wire :: IExpr a  -- expression for inout wire
           } deriving (Generic.Data, Generic.Typeable)

instance Show (IInout a) where
  show (IInout clock reset wire) =
      "IInout clock: " ++ show clock ++ " reset: " ++ show reset ++
      " |" ++ ppReadable wire ++ "|"

instance PPrint (IInout a) where
  pPrint p d r@IInout { io_wire = wire } = pPrint p d wire

instance NFData (IInout a) where
  -- XXX wires can be recursive, so just check the other parts
  rnf (IInout c r w) = (c==c) `seq` (r==r) `seq` ()

makeInout :: IClock a -> IReset a -> IExpr a -> IInout a
makeInout c r w = IInout { io_clock = c, io_reset = r, io_wire = w }

getInoutClock :: IInout a -> IClock a
getInoutClock = io_clock

getInoutReset :: IInout a -> IReset a
getInoutReset = io_reset

getInoutWire :: IInout a -> IExpr a
getInoutWire = io_wire

-- ==============================
-- Primitive Arrays

-- We guarantee that ICLazyArray elements are references during IExpand,
-- using this type for the elements.
-- This ensures that the equality check in "improveIf" is inexpensive.
-- After IExpand, we can't have heap refs anymore, so we convert ICLazyArray
-- into application of PrimBuildArray to the element expressions.
--
data ArrayCell a = ArrayCell { ac_ptr :: Int, ac_ref :: a }
                   deriving (Generic.Data, Generic.Typeable)

instance Show (ArrayCell a) where
  show (ArrayCell i _) = "_" ++ show i

instance NFData (ArrayCell a) where
  rnf (ArrayCell i _) = rnf i

type ILazyArray a = Array.Array Integer (ArrayCell a)

-- NFData instance for Array is provided by Control.DeepSeq

-- ==============================
-- Pred

-- Predicates used for implicit conditions.
-- most utility functions in IExpandUtils
newtype Pred a = PConj (PSet (PTerm a))
        deriving (Eq, Ord, Show, Generic.Data, Generic.Typeable)

instance PPrint (Pred a) where
    pPrint d p (PConj ps) = pPrint d p (S.toList ps)

instance PPrint (PTerm a) where
    pPrint d p (PAtom e) = pPrint d p e
    pPrint d p (PIf c t e) = text "PIf(" <> sepList [pPrint d 0 c, pPrint d 0 t, pPrint d 0 e] (text ",") <> text ")"
    pPrint d p (PSel idx _ es) = text "PSel(" <> sepList (pPrint d 0 idx : map (pPrint d 0) es) (text ",") <> text ")"

instance NFData (Pred a) where
-- XXX - see if we can get away with not forcing
--       the internal Pred structure
--       worried about Array/Reset/Clock-like issues
   rnf p = ()

type PSet a = S.Set a
data PTerm a = PAtom (IExpr a)
             | PIf (IExpr a) (Pred a) (Pred a)
             | PSel (IExpr a) Integer [Pred a]
        deriving (Eq, Ord, Show, Generic.Data, Generic.Typeable)

-- ==============================
-- IConInfo

data IConInfo a =
          -- top level definition
          --  iconDef has the definition body
          -- may be _ if the ICDef was read from a .bo file and has not been fixed-up yet
          -- these disappear in IExpand and do not exists in IModule
          ICDef { iConType :: IType, iConDef :: IExpr a }
        | ICPrim { iConType :: IType, primOp :: PrimOp } -- primitive
          -- foreign function; foports specifies input and output port names in verilog
          -- (for functions implemented via module instantiation - primarily "noinlined")
          -- Nothing in foports indicates this is a "true" foreign function
          -- (positional module instantiation is no longer supported)
          -- fcallNo is a cookie used to mark foreign function calls during elaboration
          -- so an association can be made between the Action and Value parts of an
          -- ActionValue call (e.g. $fopen or $stime) for use deep in the output codegens
        | ICForeign { iConType :: IType,
                      fName :: String,
                      isC :: Bool,
                      foports :: Maybe ([(String, Integer)], [(String, Integer)]),
                      fcallNo :: Maybe Integer }
          -- constructor
        | ICCon { iConType :: IType, conTagInfo :: ConTagInfo }
          -- function that tests whether its argument is the right kind of a constructor
          --  eventually cancels out and turns into ICInt 0 (false) or 1 (true)
        | ICIs { iConType :: IType, conTagInfo :: ConTagInfo }
          -- function that projects the data associated with a particular constructor
          -- only used after doing appropriate ICIs, otherwise turns into _,
          --   which is "convenient for some transformations" (_s can be "optimized later")
          -- (used to bind variables in pattern matching)
        | ICOut { iConType :: IType, conTagInfo :: ConTagInfo  }
          -- tuple constructor
          -- fieldIds names fields of struct that turned into this tuple
        | ICTuple { iConType :: IType, fieldIds :: [Id] }
          -- select field selNo out of tuple that has numSel fields
        | ICSel { iConType :: IType, selNo :: Integer, numSel :: Integer }
          -- reference to a Verilog module; vMethTs has types of method arguments
        | ICVerilog { iConType :: IType,
                      isUserImport :: Bool,
                      vInfo :: VModInfo,
                      vMethTs :: [[IType]] }
          -- underscores of different varieties:
          --   - user-inserted (IUDontCare)
          --   - unreachable _ (IUNotUsed) (needed for some expression data structs)
          --   - pattern matching failure (IUNoMatch)
        | ICUndet { iConType :: IType, iuKind :: UndefKind, imVal :: Maybe (IExpr a) }
          -- numeric integer literal
        | ICInt { iConType :: IType, iVal :: IntLit }
          -- numeric real literal
        | ICReal { iConType :: IType, iReal :: Double }
          -- string literal
        | ICString { iConType :: IType, iStr :: String }
          -- character literal
        | ICChar { iConType :: IType, iChar :: Char }
          -- IO handle
        | ICHandle { iConType :: IType, iHandle :: Handle }
          -- instantiated Verilog module
        | ICStateVar { iConType :: IType, iVar :: IStateVar a }
          -- interface method argument variable
          -- only exists after expansion
          -- note that the identifier for the port comes from the id of the surrounding ICon
        | ICMethArg { iConType :: IType }
          -- external module input (either as port or parameter)
          -- Only exists after expansion.
          -- Note that the identifier for the port/param comes from
          -- the id of the surrounding ICon.
          -- ICModPort is used for dynamic inputs (including clock and reset wires)
        | ICModPort { iConType :: IType }
        | ICModParam { iConType :: IType }
          -- reference to a local def in a module
          -- (similar to ICDef, which is a reference to a package def)
          -- this is created in iExpand, so it only exists in IModule
          -- and does not appear in IPackage
          -- XXX consider renaming it to ICModDef?
        | ICValue { iConType :: IType, iValDef :: IExpr a }
          -- module arguments that are interfaces -- NO LONGER SUPPORTED
        | ICIFace { iConType :: IType, ifcTyId :: Id, ifcIds :: [(Id, Integer, Bool)] }
          -- a constructor containing rule pragmas, which is used in the
          -- arguments to PrimRule.
          -- only exists before expansion
        | ICRuleAssert { iConType :: IType, iAsserts :: [RulePragma] }
          -- a constructor containing scheduling pragmas, which is used
          -- as an argument to PrimAddSchedPragmas (applied to rules).
          -- only exists before expansion
        | ICSchedPragmas { iConType :: IType, iPragmas :: [CSchedulePragma] }
        | ICClock { iConType :: IType, iClock :: IClock a }
        | ICReset { iConType :: IType, iReset :: IReset a } -- iReset has effective type itBit1
        | ICInout { iConType :: IType, iInout :: IInout a }
        -- uninit is used to give simpler error messages for completely uninitialized bit vectors / vectors
        | ICLazyArray { iConType :: IType, iArray :: ILazyArray a, uninit :: Maybe (IExpr a, IExpr a)}
        | ICName { iConType :: IType, iName :: Id }
        | ICAttrib { iConType :: IType, iAttributes :: [(Position,PProp)] }
          -- This was updated to support a list of positions,
          -- though most uses are a single position
        | ICPosition { iConType :: IType, iPosition :: [Position] }
        | ICType { iConType :: IType, iType :: IType }
        | ICPred { iConType :: IType, iPred :: Pred a }
        deriving (Show, Generic.Data, Generic.Typeable)

ordC :: IConInfo a -> Int
-- XXX This definition would be nice, but it imposes a (Data a) context
--ordC x = Generic.constrIndex (Generic.toConstr x)
ordC (ICDef { }) = 0
ordC (ICPrim { }) = 1
ordC (ICForeign { }) = 2
ordC (ICCon { }) = 3
ordC (ICIs { }) = 4
ordC (ICOut { }) = 5
ordC (ICTuple { }) = 6
ordC (ICSel { }) = 7
ordC (ICVerilog { }) = 8
ordC (ICUndet { }) = 9
ordC (ICInt { }) = 10
ordC (ICReal { }) = 11
ordC (ICString { }) = 12
ordC (ICChar { }) = 13
ordC (ICHandle { }) = 14
ordC (ICStateVar { }) = 15
ordC (ICMethArg { }) = 16
ordC (ICModPort { }) = 17
ordC (ICModParam { }) = 18
ordC (ICValue { }) = 19
ordC (ICIFace { }) = 20
ordC (ICRuleAssert { }) = 21
ordC (ICSchedPragmas { }) = 22
ordC (ICClock { }) = 23
ordC (ICReset { }) = 24
ordC (ICInout { }) = 25
ordC (ICLazyArray { }) = 26
ordC (ICName { }) = 27
ordC (ICAttrib { }) = 28
ordC (ICPosition { }) = 29
ordC (ICType { }) = 30
ordC (ICPred { }) = 31

instance Eq (IConInfo a) where
    x == y  =  cmpC x y == EQ
    x /= y  =  cmpC x y /= EQ

instance Ord (IConInfo a) where
    compare x y = cmpC x y

cmpC :: IConInfo a -> IConInfo a -> Ordering
cmpC c1 c2 =
    case compare (ordC c1) (ordC c2) of
    LT -> LT
    GT -> GT
    EQ ->
        case c1 of
        ICDef { } -> EQ
        ICPrim { } -> EQ
        ICForeign { } -> compare (fcallNo c1) (fcallNo c2)
        -- XXX ICCon should check conNo and numCon instead of relying
        -- on the identifier equality from ICon
        ICCon { iConType = t1 } -> compare t1 (iConType c2)
        ICIs { iConType = t1 } -> compare t1 (iConType c2)
        ICOut { iConType = t1 } -> compare t1 (iConType c2)
        ICTuple { iConType = t1 } -> compare t1 (iConType c2)
        ICSel { iConType = t1 } -> compare t1 (iConType c2)
        ICVerilog { iConType = t1, vInfo = s1 } ->
            -- ignores method types and whether they are user imports or not
            compare (t1, s1) (iConType c2, vInfo c2)
        ICUndet { iConType = t1, imVal = mval1 } -> compare (t1, mval1) (iConType c2, imVal c2)
        ICInt { iConType = t1, iVal = i1 } -> compare (t1, i1) (iConType c2, iVal c2)
        ICReal { iConType = t1, iReal = r1 } -> compare (t1, r1) (iConType c2, iReal c2)
        ICString { iConType = t1, iStr = s1 } -> compare (t1, s1) (iConType c2, iStr c2)
        ICChar { iChar = chr1 } ->
            -- the type should always be Char (should we compare anyway?)
            compare chr1 (iChar c2)
        ICHandle { } -> EQ
        ICStateVar { iVar = n1 } -> compare n1 (iVar c2)
        ICValue { } -> EQ
        ICMethArg { } -> EQ
        ICModPort { } -> EQ
        ICModParam { } -> EQ
        ICIFace { ifcTyId = ti1, ifcIds = is1 } -> compare (ti1, is1) (ifcTyId c2, ifcIds c2)
        ICRuleAssert { iAsserts = asserts } -> compare asserts (iAsserts c2)
        ICSchedPragmas { iPragmas = pragmas } -> compare pragmas (iPragmas c2)
        -- the ICon Id is not sufficient for equality comparison for Clk/Rst
        ICClock { iClock = clock1 } -> compare clock1 (iClock c2)
        ICReset { iReset = reset1 } -> compare reset1 (iReset c2)
        -- for Inout, the ICon Id is the correct Id
        ICInout { } -> EQ
        ICLazyArray { iArray = arr } -> compare (map ac_ptr (Array.elems arr))
                                                (map ac_ptr (Array.elems (iArray c2)))
        ICName { iName = n } -> compare n (iName c2)
        ICAttrib { iAttributes = pps } ->
            let pps_no_pos = map snd pps
                pps2_no_pos = map snd (iAttributes c2)
            in  compare pps_no_pos pps2_no_pos
        ICPosition { iPosition = p1 } -> compare p1 (iPosition c2)
        ICType {iType = t1 } -> compare t1 (iType c2)
        ICPred {iPred = p1 } -> compare p1 (iPred c2)

isIConInt, isIConReal, isIConParam :: IExpr a -> Bool
isIConInt (ICon _ (ICInt { })) = True
isIConInt _ = False

isIConReal (ICon _ (ICReal { })) = True
isIConReal _ = False

isIConParam (ICon _ (ICModParam { })) = True
isIConParam _ = False

-- ============================================================
-- value/type substitution, free value/type variables
-- (tSubst, eSubst, etSubst have been moved to ISyntaxSubst)

-- --------------------

-- All variables
aVars :: IExpr a -> S.Set Id
aVars (ILam i t e) = S.insert i (aVars e `S.union` fTVars t)
aVars (IVar i) = S.singleton i
aVars (ILAM i _ e) = S.insert i (aVars e)
aVars (IAps f ts es) = (aVars f) `S.union`
                        (S.unions (map fTVars ts)) `S.union`
                        (S.unions (map aVars es))
aVars (ICon _ (ICUndet {imVal = Just e})) = aVars e
aVars (ICon _ _) = S.empty  -- XXX
aVars (IRefT _ _ _) = S.empty

-- --------------------

-- Free variables
fVars :: IExpr a -> S.Set Id
fVars (ILam i _ e) = S.delete i (fVars e)
fVars (IVar i) = S.singleton i
fVars (ILAM _ _ e) = fVars e
fVars (IAps f ts es) = fVars f `S.union` (S.unions (map fVars es))
fVars (ICon _ (ICUndet {imVal = Just e})) = fVars e
fVars (ICon _ _) = S.empty
fVars (IRefT _ _ _) = S.empty

-- --------------------

-- All definitions and variables
fdVars :: IExpr a -> [Id]
fdVars e = S.toList (fdVars' e)

fdVars' :: IExpr a -> S.Set Id
fdVars' (ILam i _ e) = fdVars' e
fdVars' (IVar i) = S.singleton i
fdVars' (ILAM _ _ e) = fdVars' e
fdVars' (IAps f ts es) = fdVars' f `S.union` (S.unions (map fdVars' es))
fdVars' (ICon i (ICDef { })) = S.singleton i
fdVars' (ICon i (ICValue { })) = S.singleton i
fdVars' (ICon i (ICUndet {imVal = Just e})) = fdVars' e
fdVars' (ICon _ _) = S.empty
fdVars' (IRefT _ _ _) = S.empty

-- --------------------

-- Free type variables
ftVars :: IExpr a -> S.Set Id
ftVars (ILam i _ e) = ftVars e
ftVars (IVar i) = S.empty
ftVars (ILAM i _ e) = S.delete i (ftVars e)
ftVars (IAps f ts es) = (ftVars f) `S.union` (S.unions (map fTVars ts))
                                     `S.union` (S.unions (map ftVars es))
ftVars (ICon _ (ICUndet {imVal = Just e})) = ftVars e
ftVars (ICon _ _) = S.empty                -- XXX
ftVars (IRefT _ _ _) = S.empty

-- ============================================================
-- PPrint (for those instances not defined alongside the type, above)

pPrintLink :: PDetail -> Int -> (Id, String) -> Doc
pPrintLink d i (mi, hash) = (ppId d mi) <+> (text hash)

instance PPrint (IPackage a) where
 pPrint d p (IPackage mi lps ps ds) =
        (text "IPackage" <+> ppId d mi) $+$
        (text "  --linked packages") $+$
        foldr (($+$) . pPrintLink d 0) (text "") lps $+$
        (text "  --pragmas ")  $+$
        foldr (($+$) . pPrint d 0) (text "") ps $+$
        (text "  --idefs ")  $+$
        foldr (sep (text "next def..........................................................") . ppDef d) (text "") ds
  where sep a b c = b $+$ a $+$ c

instance PPrint (IModule a) where
 pPrint d p (IModule mi fmod be wi ps ks as clks rsts vs pts ds rs ifc ffcalNo cmap) =
        (text "IModule" <+> ppId d mi <> if fmod then text " -- function" else text "") $+$
        (case be of
             Nothing -> empty
             Just be -> text " -- backend specific:" <+> pPrint d 0 be) $+$
        text "-- wire info" $+$
        pPrint d p wi $+$
        text "-- pragmas" $+$
        foldr (($+$) . pPrint d 0) (text "") ps $+$
        text "-- imod parameters" $+$
        foldr (($+$) . ppMV d) (text "") ks $+$
        text "-- imod args" $+$
        foldr (($+$) . pPrint d 0) (text "") as $+$
        text "-- imod clock domains" $+$
        foldr (($+$) . pPrint d 0) (text "") clks $+$
        foldr (($+$) . pPrint d 0) (text "") rsts $+$
        text "-- imod state instances" $+$
        foldr (($+$) . ppSV) (text "") vs $+$
        text "-- port types" $+$
        foldr (($+$) . ppPT) (text "") (M.toList pts) $+$
        text "-- imod local defs" $+$
        foldr (($+$) . ppDef d) (text "") ds $+$
        text "-- imod rules" $+$
        pPrint d 0 rs $+$
        text "" $+$
        text "-- imod interface" $+$
        foldr (($+$) . pPrint d 0) (text "") ifc
  where ppSV (i, sv) = ppId d i <> pPrint d 0 sv
        ppPT (i, m) =
            foldr ($+$) (text "")
                [ ppPort i port <> text " :: " <>
                  pPrint d 0 ty | (VName port, ty) <- M.toList m ]
          where ppPort Nothing p = text p
                ppPort (Just i) p = ppId d i <> text ("$" ++ p)

ppMV :: (PPrint a) => PDetail -> (Id, a) -> Doc
ppMV d (i, ty) = ppId d i <+> text "::" <+> pPrint d 0 ty

instance PPrint (IEFace a) where
    pPrint d p (IEFace i vs et rules wp fi)
        =       text "-- args" $+$
                foldr (($+$) . ppMV d) b vs
              where b =        text "-- body" $+$
                        (case et of
                          Just (e,t) -> ppDef d $ IDef i t e []
                          _ -> empty ) $+$
                        text "-- rules" $+$
                        pPrint d 0 rules $+$
                        text "-- wire properties" $+$
                        pPrint d 0 wp $+$
                        text "-- field info" $+$
                        pPrint d 0 fi $+$
--                      text "-- guard" $+$
--                        ppDef d wi wt we $+$
                        text ""

instance PPrint IAbstractInput where
    pPrint d p (IAI_Port (i,ty)) = ppId d i <+> text "::" <+> pPrint d 0 ty
    pPrint d p (IAI_Clock osc Nothing) =
        text "clock {" <+>
        (text "osc =" <+> pPrint d 0 osc) <+>
        text "}"
    pPrint d p (IAI_Clock osc (Just gate)) =
        text "clock {" <+>
        (text "osc =" <+> pPrint d 0 osc <> text "," <+>
         text "gate =" <+> pPrint d 0 gate) <+>
        text "}"
    pPrint d p (IAI_Reset r) =
        text "reset {" <+> pPrint d 0 r <+> text "}"
    pPrint d p (IAI_Inout r n) =
        text "inout {" <+> pPrint d 0 r <> text"[" <> pPrint d 0 n <> text"]" <+> text "}"

instance PPrint (IStateVar a) where
    pPrint d p sv@(IStateVar _ _ _ vi xs t _ _ _ _) =
        let ps = [e | (i,e) <- zip (vArgs vi) xs, isParam i]
            as = [(v,e) | (Port (v,_) _ _, e) <- zip (vArgs vi) xs]
            ppPortConnection (VName s,e) =
                text ("." ++ s ++ "(") <> pPrint d 0 e <> text ")"
        in  text " ::" <+> pPrint d 0 t <+> text "=" <+> pPrint d 0 (vName vi) <>
            (case ps of
              [] -> text ""
              _ -> text " #(" <>
                   sepList (map (pPrint d 0) ps) (text ",")
                   <> text ")") <>
            (case as of
              [] -> text ""
              _ -> text " (" <>
                   sepList (map ppPortConnection as) (text ",") <>
                   text ")")


instance PPrint (IRule a) where
    pPrint d p (IRule {
                   irule_name = longname,
                   irule_pragmas = rps,
                   irule_description = s,
                   irule_pred = c,
                   irule_body = a }) =
        (text "" <+> vcat (map (pPrint d 0) rps)) $+$
        (text "" <+> text (show longname) <> text ":") $+$
        (text "" <+> text (show s) <> text ":") $+$
        (text "  when" <+> pPrint d 0 c) $+$
        (text "   ==>" <+> pPrint d 0 a)

instance PPrint (IRules a) where
    pPrint d p (IRules sps rs) =
        foldr (($+$) . pPrint d 0) (text "") sps $+$
        foldr (($+$) . pPrint d 0) (text "") rs

ppQuant :: PPrint a => String -> PDetail -> Int -> Id -> a -> IExpr b -> Doc
ppQuant s d p i t e =
    pparen (p>0) (sep [text s <> pparen True (pPrint d 0 i <>text" ::" <+> pPrint d 0 t) <+> text ".", pPrint d 0 e])
    --pparen (p>0) (text s <> pparen True (pPrint d 0 i <>text" ::" <+> pPrint d 0 t) <+> text "." <+> pPrint d 0 e)

instance PPrint (IDef a) where
    pPrint d _p def = ppDef d def

ppDef :: PDetail -> IDef a -> Doc
ppDef d (IDef i t e p) =
    sep [pPrint d 0 i <+> text "::", nest 2 (pPrint d 0 t)] $+$
    sep [pPrint d 0 i <+> text "=", nest 2 (pPrint d 0 e)] $+$
    (if (null $ getIdProps i) then empty else
       text "-- IdProp:" <+> text (show i) ) $+$
    (if (null p) then empty else
       text "-- Properties:" <+> text (show p
             -- avoid line wrap in what is supposed to be a comment
                                      ))

instance PPrint (IExpr a) where
    pPrint d p (ILam i t e) = ppQuant "\\ "  d p i t e
    pPrint d p e@(IAps (ICon _ (ICPrim { primOp = PrimJoinActions })) _ _) =
        let getActions (IAps (ICon _ (ICPrim { primOp = PrimJoinActions })) _ [e1, e2]) = getActions e1 ++ getActions e2
            getActions e = [e]
            as = getActions e
        in  text "{" <+> sepList (map (pPrint d 0) as) (text ";") <+> text "}"
    pPrint d p (IAps (ILam i t e') [] (e:es)) = pparen (p > 0) $
        (text "let" <+> ppDef d (IDef i t e [])) $+$
        (text "in  " <> pPrint d 0 (iAps e' es))
    pPrint d p (ICon i (ICUndet t _ Nothing)) = text "_ :: " <+> pPrint d maxPrec t
    pPrint d p (ICon i (ICUndet t _ (Just v))) = text "_[" <> pPrint d maxPrec v <> text "]"
    pPrint d@PDReadable p (ICon i (ICDef _ _)) = ppId d i <> text "="
    pPrint d@PDReadable p (ICon i (ICVerilog { vInfo = vi })) = pparen True $ text "verilog" <+> pPrint d 0 vi
    pPrint d@PDReadable p (ICon i (ICIs _ _)) = ppId d i <> text "?"
    pPrint d@PDReadable p (ICon i (ICOut _ _)) = text "out" <> ppId d i
    pPrint d@PDReadable p (ICon i (ICSel _ _ _)) = text "." <> ppId d i
    pPrint d@PDReadable _ (ICon i (ICPrim _ p)) = text (show p)
    pPrint d@PDReadable _ (ICon i (ICIFace _ _ is)) = ppId d i <> text"{" <> sep (map (pPrint d 10) is) <> text "}"
    pPrint d@PDReadable _ (ICon i (ICLazyArray {})) = ppId d i <> text "[Array]"
--    pPrint d@PDReadable _ (ICon id con) = ppId d id <> text (": " ++ show con)
    pPrint d p (IVar i) = ppId d i -- <> text ":V"
    pPrint d p (ILAM i k e) = ppQuant "/\\ "  d p i k e
    pPrint d p (IAps f ts es) = pparen (p>(maxPrec-1)) $
        sep (pPrint d (maxPrec-1) f : map (nest 2 . (text"\183" <>) . pPrint d maxPrec) ts ++ map (nest 2 . pPrint d maxPrec) es)
    pPrint d p (ICon _ (ICString t s)) = text (show s)
    pPrint d p (ICon _ (ICChar _ c)) = text (show c)
    pPrint d@PDDebug p (ICon _ (ICInt { iConType = t, iVal = i })) = pPrint d p i <> text "::" <> pPrint d maxPrec t
    pPrint d p (ICon _ (ICInt { iConType = t, iVal = i })) = pPrint d p i
    pPrint d p (ICon _ (ICReal { iConType = t, iReal = r })) = pPrint d p r
    pPrint d@PDDebug p (ICon i ict) = ppId d i <> text "::" <> pPrint d maxPrec (iConType ict)
    pPrint d p ict@(ICon i (ICForeign {fcallNo = (Just n)})) = ppId d i <> text ("#" ++ show n)
    pPrint d p (ICon i ict) = ppId d i
    pPrint d p (IRefT _ ptr _) = text ("_") <> pPrint d 0 ptr

-- ============================================================
-- Hyper (for those instances not defined alongside the type, above)

instance NFData (IPackage a) where
    rnf (IPackage i lps ps ds) = rnf4 i ps lps ds

instance NFData (IModule a) where
    rnf (IModule x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) =
        rnf16 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16

instance NFData (IEFace a) where
    rnf (IEFace x1 x2 x3 x4 x5 x6) = rnf6 x1 x2 x3 x4 x5 x6

instance NFData IAbstractInput where
    rnf (IAI_Port p) = rnf p
    rnf (IAI_Clock o mg) = rnf2 o mg
    rnf (IAI_Reset r) = rnf r
    rnf (IAI_Inout r n) = rnf2 r n

instance NFData (IDef a) where
    rnf (IDef i t e p) = rnf4 i t e p

instance NFData (IExpr a) where
    rnf (ILam i t e) = rnf3 i t e
    rnf (IAps e ts es) = rnf3 e ts es
    rnf (IVar i) = rnf i
    rnf (ILAM i k e) = rnf3 i k e
    rnf (ICon i ic) = rnf2 i ic
    rnf (IRefT t p _) = rnf t

instance NFData (IConInfo a) where
--    rnf (ICDef x1 x2) = rnf2 x1 x2
    rnf ic@(ICDef x1 x2) = ()                        -- XXX a hack to avoid circular defs
    rnf (ICPrim x1 x2) = rnf2 x1 x2
    rnf (ICForeign x1 x2 x3 x4 x5) = rnf5 x1 x2 x3 x4 x5
    rnf (ICCon x1 x2) = rnf2 x1 x2
    rnf (ICIs x1 x2) = rnf2 x1 x2
    rnf (ICOut x1 x2) = rnf2 x1 x2
    rnf (ICTuple x1 x2) = rnf2 x1 x2
    rnf (ICSel x1 x2 x3) = rnf3 x1 x2 x3
    rnf (ICVerilog x1 x2 x3 x4) = rnf4 x1 x2 x3 x4
    rnf (ICUndet x1 x2 x3) = rnf3 x1 x2 x3
    rnf (ICInt x1 x2) = rnf2 x1 x2
    rnf (ICReal x1 x2) = rnf2 x1 x2
    rnf (ICString x1 x2) = rnf2 x1 x2
    rnf (ICChar x1 x2) = rnf2 x1 x2
    rnf (ICHandle x1 x2) = rnf2 x1 x2
    rnf (ICStateVar x1 x2) = rnf2 x1 x2
    rnf (ICMethArg x1) = rnf x1
    rnf (ICModPort x1) = rnf x1
    rnf (ICModParam x1) = rnf x1
--    rnf (ICValue x1 x2 x3) = rnf3 x1 x2 x3        -- XXX causes cycles somehow
    rnf (ICValue x1 x2) = ()
    rnf (ICIFace x1 x2 x3) = rnf3 x1 x2 x3
    rnf (ICRuleAssert x1 x2) = rnf2 x1 x2
    rnf (ICSchedPragmas x1 x2) = rnf2 x1 x2
    rnf (ICClock x1 x2) = rnf2 x1 x2
    rnf (ICReset x1 x2) = rnf2 x1 x2
    rnf (ICInout x1 x2) = rnf2 x1 x2
    rnf (ICName x1 x2) = rnf2 x1 x2
    rnf (ICAttrib x1 x2) = rnf2 x1 x2
    rnf (ICLazyArray x1 x2 x3) = rnf3 x1 x2 x3
    rnf (ICPosition x1 x2) = rnf2 x1 x2
    rnf (ICType x1 x2) = rnf2 x1 x2
    rnf (ICPred x1 x2) = rnf2 x1 x2

instance NFData (IStateVar a) where
    rnf x = (x==x) `seq` ()                -- XXX (does not evaluate IStateVar components)

-- ============================================================
-- XRef (and other utilities?) beyond this point


-- #############################################################################
-- #
-- #############################################################################

getIExprPositionCross :: IExpr a -> Position
getIExprPositionCross iexpr =
    if (True)
       then (getIExprPositionCrossInternal 0 iexpr)
       else noPosition

-- getITypePositionCross :: IType -> Position
-- getITypePositionCross itype =
--     if (True)
--        then (getITypePositionCrossInternal 0 itype)
--        else noPosition

-- #############################################################################
-- #
-- #############################################################################

getIExprPositionCrossInternal :: Int -> IExpr a -> Position
getIExprPositionCrossInternal 10 _ = noPosition

getIExprPositionCrossInternal n (ILam i _ e) =
    let pos = (getIExprPositionCrossInternal (n + 1) e)
    in  firstPos [pos, getIdPosition i]

getIExprPositionCrossInternal n (IAps e ts es) =
    let pos = (getIExprPositionCrossInternal (n + 1) e)
    in  firstPos (pos : (map (getIExprPositionCrossInternal (n + 1)) es))

getIExprPositionCrossInternal _ (IVar i) = getIdPosition i

getIExprPositionCrossInternal n (ILAM i _ e) =
    let pos = (getIExprPositionCrossInternal (n + 1) e)
    in  firstPos [pos, getIdPosition i]

-- getIExprPositionCrossInternal n (ICon i (ICPrim t op)) =
--     getITypePositionCrossInternal (n + 1) t

getIExprPositionCrossInternal _ (ICon i (ICSel _ _ _)) =
    if (isPassThroughOp i)
        then -- trace("DDD " ++ (pfpString i)) $
             noPosition
        else -- trace("CCC " ++ (pfpString i)) $
             (getIdPosition i)


getIExprPositionCrossInternal _ (ICon i _) = getIdPosition i
getIExprPositionCrossInternal n (IRefT t _ _) = getITypePositionCrossInternal (n + 1) t


getITypePositionCrossInternal :: Int -> IType -> Position
getITypePositionCrossInternal 10 _ = noPosition

getITypePositionCrossInternal n (ITForAll i _ t) =
    let pos = (getIdPosition i)
    in  firstPos [pos, (getITypePositionCrossInternal (n + 1) t)]

getITypePositionCrossInternal n (ITAp t t') =
    let t_pos = getITypePositionCrossInternal (n + 1) t
        t'_pos = getITypePositionCrossInternal (n + 1) t'
        pos_list = [t_pos, t'_pos]
    in  firstPos pos_list

getITypePositionCrossInternal _ (ITVar i) = getIdPosition i
getITypePositionCrossInternal _ (ITCon i _ _) = getIdPosition i
getITypePositionCrossInternal _ (ITNum _) = noPosition
getITypePositionCrossInternal _ (ITStr _) = noPosition



-- #############################################################################
-- # A bunch of operators we don't want messing with "real" position info.
-- #############################################################################

idMonadNoPos, idBindNoPos, idFromIntegerNoPos, idReturnNoPos :: Id
idMonadNoPos = idMonad noPosition
idBindNoPos = idBind noPosition
idFromIntegerNoPos = idFromInteger noPosition
idReturnNoPos = idReturn noPosition

isPassThroughOp :: Id -> Bool
isPassThroughOp i = (i == idBit) ||
                    (i == idMonadNoPos) ||
                    (i == idBindNoPos) ||
                    (i == idFromIntegerNoPos) ||
                    (i == idLiftModule) ||
                    (i == idPack) ||
                    (i == idReturnNoPos) ||
                    (i == idUnpack)

-- #############################################################################
-- #
-- #############################################################################

getIExprPosition :: IExpr a -> Position

getIExprPosition (ILam i t e) =
    let t_pos = getITypePosition t
        i_pos = getIExprPosition e
        pos_list = [getIdPosition i, t_pos, i_pos]
    in  firstPos pos_list

getIExprPosition (IAps e ts es) =
    let t_pos_list = map getITypePosition ts
        i_pos_list = map getIExprPosition es
        pos_list = getIExprPosition e : t_pos_list ++ i_pos_list
    in  firstPos pos_list

getIExprPosition (IVar i) = getIdPosition i

getIExprPosition (ILAM i _ e) = firstPos [getIdPosition i, getIExprPosition e]
-- getIExprPosition (ICon i (ICPrim t op)) = getITypePosition t
getIExprPosition (ICon i _) = getIdPosition i
getIExprPosition (IRefT t _ _) = getITypePosition t

getITypePosition :: IType -> Position
getITypePosition (ITForAll i _ t) = firstPos [getIdPosition i, getITypePosition t]

getITypePosition (ITAp t t') =
    let t_pos = getITypePosition t
        t'_pos = getITypePosition t'
        pos_list = [t_pos, t'_pos]
    in  firstPos pos_list

getITypePosition (ITVar i) = getIdPosition i
getITypePosition (ITCon i _ _) = getIdPosition i
getITypePosition (ITNum _) = noPosition
getITypePosition (ITStr _) = noPosition

--------

iAP :: IExpr a -> IType -> IExpr a
iAP (IAps f ts []) t = IAps f (ts ++ [t]) []
iAP f t = IAps f [t] []

iAp :: IExpr a -> IExpr a -> IExpr a
iAp (IAps f ts es) e = IAps f ts (es ++ [e])
iAp f e = IAps f [] [e]

iAps :: IExpr a -> [IExpr a] -> IExpr a
iAps f [] = f
iAps f es = IAps f [] es

mkNumConT :: Integer -> IType
mkNumConT i =
    if i < 0 then
        internalError ("mkNumCon: " ++ show i)
    else
        ITNum i

--------

-- shallow printing that avoids looping
showTypeless :: IExpr a -> String
showTypeless (ILam i _ e) = "(ILam " ++ (show i) ++ " _ " ++ (showTypeless e) ++ ")"
showTypeless (IAps e _ es) = "(IAps " ++ (showTypeless e) ++ " _ " ++ showTypelessList es ++ ")"
showTypeless (IVar i) = "(IVar " ++ (show i) ++ ")"
showTypeless (ILAM i k e) = "(ILAM " ++ (show i) ++ " " ++ (show k) ++ " " ++ (showTypeless e) ++ ")"
showTypeless (ICon i ci) = "(ICon " ++ (show i) ++ " " ++ (showTypelessCI ci) ++ " )"
showTypeless (IRefT _ i _) = "(IRefT " ++ "_" ++ (show i) ++ ")"

showTypelessRule :: IRule a -> String
showTypelessRule (IRule {
                     irule_name = n,
                     irule_pragmas = rps,
                     irule_description = s,
                     irule_pred = c,
                     irule_body = a }) =
    "(IRule " ++ (show n) ++ "\n\t" ++ (show rps) ++ "\n\t" ++
    (show s) ++ "\n\t" ++ (showTypeless c) ++ "\n\t" ++
    (showTypeless a) ++ "\n)"

showTypelessRules :: IRules a -> String
showTypelessRules (IRules sps rs) =
    "(IRules " ++ show sps ++ " [" ++
    foldr1 (\x y -> x ++ ", " ++ y) (map showTypelessRule rs) ++ "])"

showTypelessCI :: IConInfo a -> String
showTypelessCI (ICDef {iConType = t, iConDef = e}) = "(ICDef)"
showTypelessCI (ICPrim {iConType = t, primOp = p}) = "(ICPrim _ " ++ (show p) ++ ")"
showTypelessCI (ICForeign {iConType = t, fName = n, isC = b, foports = f}) = "(ICForeign _ " ++ n ++ " " ++ show b ++ " " ++ (show f) ++ ")"
showTypelessCI (ICCon {iConType = t, conTagInfo = cti}) = "(ICCon _ " ++ (ppReadable cti) ++ ")"
showTypelessCI (ICIs {iConType = t, conTagInfo = cti}) = "(ICIs _ " ++ (ppReadable cti) ++ ")"
showTypelessCI (ICOut {iConType = t, conTagInfo = cti}) = "(ICOut _ " ++ (ppReadable cti) ++ ")"
showTypelessCI (ICTuple {iConType = t, fieldIds = fs}) = "(ICTuple _ " ++ (show fs) ++ ")"
showTypelessCI (ICSel {iConType = t, selNo = i, numSel = j}) = "(ICSel _ " ++ (show i) ++ " " ++ (show j) ++ ")"
showTypelessCI (ICVerilog {iConType = t, isUserImport = ui, vInfo = v, vMethTs = vts}) = "(ICVerilog _ " ++ {--(show v)--} "<vmodinfo>" ++ " [_])"
showTypelessCI (ICUndet {iConType = t, iuKind = k, imVal = Nothing}) = "(ICUndet _ _ )"
showTypelessCI (ICUndet {iConType = t, iuKind = k, imVal = Just v})  = "(ICUndet _ _ [" ++ ppReadable v ++ "])"
showTypelessCI (ICInt {iConType = t, iVal = v}) = "(ICInt _ " ++ (show v) ++ ")"
showTypelessCI (ICReal {iConType = t, iReal = v}) = "(ICReal _ " ++ (show v) ++ ")"
showTypelessCI (ICString {iConType = t, iStr = s}) = "(ICString _ " ++ (show s) ++ ")"
showTypelessCI (ICChar {iConType = t, iChar = c}) = "(ICChar _ " ++ (show c) ++ ")"
showTypelessCI (ICHandle {iConType = t, iHandle = h}) = "(ICHandle _ " ++ (show h) ++ ")"
showTypelessCI (ICStateVar {iConType = t, iVar = v}) = "(ICStateVar _ " ++ (showTypelessStateVar v) ++ ")"
showTypelessCI (ICMethArg {iConType = t}) = "(ICMethArg _ )"
showTypelessCI (ICModPort {iConType = t}) = "(ICModPort _ )"
showTypelessCI (ICModParam {iConType = t}) = "(ICModParam _ )"
showTypelessCI (ICValue {iConType = t, iValDef = e}) = "(ICValue)"
showTypelessCI (ICIFace {iConType = t, ifcTyId = i, ifcIds = ids}) = "(ICIFace _ " ++ (show i) ++ " " ++ (show ids) ++ ")"
showTypelessCI (ICRuleAssert {iConType = t, iAsserts = rps}) = "(ICRuleAssert _ " ++ (show rps) ++ ")"
showTypelessCI (ICSchedPragmas {iConType = t, iPragmas = sps}) = "(ICSchedPragmas _ " ++ (show sps) ++ ")"
showTypelessCI (ICClock {iConType = t, iClock = clock}) = "(ICClock)"
showTypelessCI (ICReset {iConType = t, iReset = reset}) = "(ICReset)"
showTypelessCI (ICInout {iConType = t, iInout = inout}) = "(ICInout)"
showTypelessCI (ICName  {iConType = t, iName = name}) = "(ICName _ " ++ (show name) ++ ")"
showTypelessCI (ICAttrib {iConType = t, iAttributes = pps}) = "(ICAttrib _ " ++ (show (map snd pps)) ++ ")"
showTypelessCI (ICLazyArray {iConType = t, iArray = arr}) = "(ICLazyArray _ " ++ (ppReadable (map ac_ptr (Array.elems arr))) ++ ")"
showTypelessCI (ICPosition {iConType = t, iPosition = pos}) = "(ICPosition _ " ++ (show pos) ++ ")"
showTypelessCI (ICType {iType = t}) = "(ICType _ " ++ (show t) ++ ")"
showTypelessCI (ICPred {iPred = p}) = "(ICPred _ " ++ (show p) ++ ")"

showTypelessStateVar :: IStateVar a -> String
showTypelessStateVar (IStateVar b ui i v es ts mts ncs nrs l) =
    "(IStateVar " ++ (show b) ++ " "
    ++ (show i)
    ++ " <vmodinfo> "
    ++ " <params + args>" {-- showTypelessList es --}
    ++ "_"
    ++ " [[_]] "
    ++ "<IStateLoc>" ++ ")"

showTypelessList :: [IExpr a] -> String
showTypelessList es = "[" ++ intercalate ", " (map showTypeless es) ++ "]"

-- #############################################################################
-- #
-- #############################################################################
