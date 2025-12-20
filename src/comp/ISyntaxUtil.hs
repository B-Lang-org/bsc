module ISyntaxUtil where

import System.IO(Handle, BufferMode(..))
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe(fromMaybe)
import Util(flattenPairs)
import IntLit
import Undefined
import PPrint(ppReadable, ppString)
import ErrorUtil(internalError)
import Position(noPosition, Position)
import StdPrel
import Prim
import Id
import PreIds
import ISyntax
import ISyntaxSubst(tSubst)
import Wires
import VModInfo(vFields, VFieldInfo(..), lookupOutputClockWires)
import CType(TISort(..), StructSubType(..))

--import Debug.Trace

infixr 8 `itFun`

-- Types
itFun :: IType -> IType -> IType
itFun t t' = ITAp (ITAp itArrow t) t'

isFunType :: IType -> Bool
isFunType t = not (null (drop 1 (itSplit t)))

itSplit :: IType -> [IType]
itSplit (ITAp (ITAp arr a) r) | arr == itArrow = a : itSplit r
itSplit t = [t]

itBool, itBit :: IType
itBool = ITCon idBool IKStar tiBool
itBit = ITCon idBit (IKNum `IKFun` IKStar) tiBit

aitBit :: IType -> IType
aitBit t = ITAp itBit t

it0, it1 :: IType
it0 = mkNumConT 0
it1 = mkNumConT 1

itBitN :: Integer -> IType
itBitN n = aitBit (mkNumConT n)

itBit0, itBit1, itNatSize, itNat, itInteger, itReal :: IType
itBit0 = itBitN 0
itBit1 = itBitN 1
itNatSize = mkNumConT 32
itNat = aitBit itNatSize
itInteger = ITCon idInteger IKStar tiInteger
itReal = ITCon idReal IKStar tiReal

itClock, itReset, itInout, itInout_ :: IType
itClock = ITCon idClock IKStar tiClock
itReset = ITCon idReset IKStar tiReset
itInout  = ITCon idInout  (IKNum `IKFun` IKStar) tiInout
itInout_ = ITCon idInout_ (IKNum `IKFun` IKStar) tiInout

itInoutT :: IType -> IType
itInoutT t = ITAp itInout t

itInout_N :: Integer -> IType
itInout_N n = ITAp itInout_ (mkNumConT n)

itPrimArray :: IType
itPrimArray = ITCon idPrimArray (IKStar `IKFun` IKStar) tiPrimArray

itPair :: IType -> IType -> IType
itPair t1 t2 =
    let k = IKStar `IKFun` IKStar `IKFun` IKStar
    in  ITAp (ITAp (ITCon idPrimPair k tiPair) t1) t2

icPair :: Id -> IExpr a
icPair i = ICon i (ICTuple ct [idPrimFst, idPrimSnd])
  where ct = ITForAll i1 IKStar
              (ITForAll i2 IKStar
               ((ITVar i1) `itFun` (ITVar i2) `itFun` pair_t))
        pair_t = itPair (ITVar i1) (ITVar i2)
        (i1, i2) = take2tmpVarIds

itPosition, itPrimGetPosition :: IType
itPosition = ITCon idPosition IKStar tiPosition
-- type for position extraction primitives
-- PrimGetEvalPosition is only the first example of this
itPrimGetPosition = ITForAll i IKStar (ITVar i `itFun` itPosition)
 where i = take1tmpVarIds

itName :: IType
itName = ITCon idName IKStar tiName

itType :: IType
itType = ITCon idType IKStar tiType

itPred :: IType
itPred = ITCon idPred IKStar tiPred

itSchedPragma :: IType
itSchedPragma = ITCon idSchedPragma IKStar tiSchedPragma

-- type of the Clock constructor
itClockCons, itAction, itPrimUnit :: IType
itClockCons = itBit1 `itFun` itBit1 `itFun` itClock -- XXX is this right?
itAction = ITCon idPrimAction IKStar tiAction
itPrimUnit = ITCon idPrimUnit IKStar tiUnit

-- an unstructured type where it is safe to optimize
-- away undefined values
-- isSimpleType (ITAp c (ITNum n)) | c == itBit = True
isSimpleType :: IType -> Bool
isSimpleType t = t == itInteger ||
                 t == itReal ||
                 t == itString ||
                 t == itChar

isitAction :: IType -> Bool
isitAction (ITAp (ITCon i (IKFun IKNum IKStar)
                     (TIstruct SStruct [_,_] ) ) (ITNum x))
    | (i == idActionValue_) = (x == 0)
isitAction (ITAp (ITCon i (IKFun IKStar IKStar) _) t)
    | (i == idActionValue)  = t == itPrimUnit
isitAction x = (x == itAction)

-- note this returns false for x == - because ActionValue_ 0 is really an Action
isitActionValue_ :: IType -> Bool
isitActionValue_ (ITAp (ITCon i (IKFun IKNum IKStar)
                           (TIstruct SStruct [_,_] ) ) (ITNum x))
    | x > 0 = (i == idActionValue_)
isitActionValue_ _ = False

isitActionValue :: IType -> Bool
isitActionValue (ITAp (ITCon i (IKFun IKStar IKStar) _) t) =
    i == idActionValue && t /= itPrimUnit
isitActionValue _ = False

isitInout_ :: IType -> Bool
isitInout_ (ITAp (ITCon i (IKFun IKNum IKStar) _ ) (ITNum x)) = (i == idInout_)
isitInout_ _ = False

getInout_Size :: IType -> Integer
getInout_Size (ITAp ic (ITNum n)) | ic == itInout_ = n
getInout_Size t =
    internalError ("getInout_Size: type is not Inout_: " ++ ppReadable t)


getAV_Size :: IType -> Integer
getAV_Size (ITAp (ITCon i (IKFun IKNum IKStar)
                           (TIstruct SStruct [_,_] ) ) (ITNum x)) |
    (i == idActionValue_) = x
getAV_Size t = internalError ("getAV_Size: type is not AV_: " ++ ppReadable t)

getAVType :: IType -> Maybe IType
getAVType (ITAp (ITCon i (IKFun IKStar IKStar) _) t) | i == idActionValue = Just t
getAVType _ = Nothing

itRules, itString, itChar, itHandle, itBufferMode, itFmt :: IType
itRules = ITCon idRules IKStar tiRules
itString = ITCon idString IKStar tiString
itChar = ITCon idChar IKStar tiChar
itHandle = ITCon idHandle IKStar tiHandle
itBufferMode = ITCon idBufferMode IKStar tiBufferMode
itFmt = ITCon idFmt IKStar tiFmt

itStringAt, itFmtAt :: Position -> IType
itStringAt pos = ITCon (idStringAt pos) IKStar tiString
itFmtAt pos = ITCon (idFmtAt pos) IKStar tiFmt

itList, itMaybe :: IType -> IType
itList t = ITAp (ITCon idList (IKFun IKStar IKStar) tiList) t
itMaybe t = ITAp (ITCon idMaybe (IKFun IKStar IKStar) tiMaybe) t

isBitType :: IType -> Bool
isBitType (ITAp c n) = c == itBit
isBitType _ = False

-- extension point for ActionValue methods
isActionType :: IType -> Bool
isActionType x = (x == itAction) || (isitActionValue_ x) || (isitAction x)

-- extension point for ActionValue methods
isValueType :: IType -> Bool
isValueType x | (isitActionValue_ x) && (getAV_Size x > 0) = True
isValueType (ITAp t n) | t == itBit = True
isValueType _ = False

-- Constructors
iMkLit :: IType -> Integer -> IExpr a
iMkLit t i = ICon idIntLit (ICInt { iConType = t, iVal = ilDec i })

iMkLitAt :: Position -> IType -> Integer -> IExpr a
iMkLitAt pos t i =
    let ci = setIdPosition pos idIntLit
    in  ICon ci (ICInt { iConType = t, iVal = ilDec i })

iMkLitWB :: IType -> Maybe Integer -> Integer -> Integer -> IExpr a
iMkLitWB t w b i =
    let lit = IntLit { ilValue = i, ilBase = b, ilWidth = w }
    in  ICon idIntLit (ICInt { iConType = t, iVal = lit })

iMkLitWBAt :: Position ->
              IType -> Maybe Integer -> Integer -> Integer -> IExpr a
iMkLitWBAt pos t w b i =
    let ci = setIdPosition pos idIntLit
        lit = IntLit { ilValue = i, ilBase = b, ilWidth = w }
    in  ICon ci (ICInt { iConType = t, iVal = lit })

iMkLitSize :: Integer -> Integer -> IExpr a
iMkLitSize s i =
{-
    if i >= 2^s then
        trace ("big literal " ++ show i ++ " in " ++ show s ++ " bits") $ iMkLit (itBitN s) i
    else
-}
        iMkLit (itBitN s) i

iMkLitSizeAt :: Position -> Integer -> Integer -> IExpr a
iMkLitSizeAt pos s i = iMkLitAt pos (itBitN s) i

iMkRealLit :: Double -> IExpr a
iMkRealLit d = ICon idRealLit (ICReal { iConType = itReal, iReal = d })

iMkRealLitAt :: Position -> Double -> IExpr a
iMkRealLitAt pos d =
    let i = setIdPosition pos idRealLit
    in  ICon i (ICReal { iConType = itReal, iReal = d })

iMkPairAt :: Position -> IType -> IType -> IExpr a -> IExpr a -> IExpr a
iMkPairAt pos t1 t2 e1 e2 =
    let i = setIdPosition pos idPrimPair
        c = icPair i
    in  iAps c [t1,t2] [e1, e2]

iMkTripleAt :: Position ->
               IType -> IType -> IType ->
               IExpr a -> IExpr a -> IExpr a -> IExpr a
iMkTripleAt pos t1 t2 t3 e1 e2 e3 = iAps c [t1, pair_t] [e1, iAps c [t2, t3] [e2, e3]]
  where i = setIdPosition pos idPrimPair
        c = icPair i
        pair_t = itPair t2 t3

iMkPosition :: Position -> IExpr a
iMkPosition pos = iMkPositions [pos]

iMkPositions :: [Position] -> IExpr a
iMkPositions poss = ICon idPositionLit (ICPosition itPosition poss)

-- utility for code that expects only one position in ICPosition
getICPosition :: String -> [Position] -> Position
getICPosition _   [pos] = pos
getICPosition str poss  = internalError (str ++ ": " ++ ppReadable poss)

iMkName :: Id -> Id -> IExpr a
iMkName id name = ICon id (ICName itName name)

icType :: Id -> IType -> IExpr a
icType i t = ICon i (ICType { iConType = itType, iType = t })

icPred :: Pred a -> IExpr a
icPred p = ICon idPredLit (ICPred { iConType = itPred, iPred = p })

icUndet :: IType -> UndefKind -> IExpr a
icUndet t u = icUndetAt noPosition t u

icUndetAt :: Position -> IType -> UndefKind -> IExpr a
icUndetAt pos t u = ICon (dummyId pos) (ICUndet t u Nothing)

iMkString :: String -> IExpr a
iMkString s = ICon idStringLit (ICString itString s)

iMkStringAt :: Position -> String -> IExpr a
iMkStringAt pos s = ICon (setIdPosition pos idStringLit) (ICString itString s)

iMkStrConcat :: IExpr a -> IExpr a -> IExpr a
iMkStrConcat istr1 istr2 = iAps iConcatCon [] [istr1, istr2]
    where itStr = itString
          iConcatCon :: IExpr a
          iConcatCon = (ICon idPrimStringConcat
                        (ICPrim (itStr `itFun` (itStr `itFun` itStr))
                         PrimStringConcat))

iMkCharAt :: Position -> Char -> IExpr a
iMkCharAt pos c = ICon (setIdPosition pos idCharLit) (ICChar itChar c)

iMkHandle :: Handle -> IExpr a
iMkHandle h = ICon idHandleLit (ICHandle itHandle h)

iMkBufferMode :: BufferMode -> IExpr a
iMkBufferMode NoBuffering =
  IAps icPrimChr [mkNumConT 2, itBufferMode] [iMkLitSize 2 0]
iMkBufferMode LineBuffering =
  IAps icPrimChr [mkNumConT 2, itBufferMode] [iMkLitSize 2 1]
iMkBufferMode (BlockBuffering msz) =
  let ic_ty = (itMaybe itInteger) `itFun` itBufferMode
      cti = ConTagInfo { conNo = 2, numCon = 3, conTag = 2, tagSize = 2 }
      ic = ICon idBlockBuffering
             (ICCon { iConType = ic_ty, conTagInfo = cti })
      e = case msz of
             Nothing -> iMkInvalid itInteger
             Just sz -> iMkValid itInteger (iMkLit itInteger (toInteger sz))
  in  IAps ic [] [e]

iMkInvalid :: IType -> IExpr a
iMkInvalid t = IAps icPrimChr [mkNumConT 1, itMaybe t] [iMkLitSize 1 0]

iMkValid :: IType -> IExpr a -> IExpr a
iMkValid t e =
  let a = take1tmpVarIds
      ic_ty = ITForAll a IKStar $ (ITVar a) `itFun` (itMaybe (ITVar a))
      cti = ConTagInfo { conNo = 1, numCon = 2, conTag = 1, tagSize = 1 }
      ic = ICon idValid (ICCon { iConType = ic_ty, conTagInfo = cti })
  in  IAps ic [t] [e]

iMkNil :: IType -> IExpr a
iMkNil t = IAps icPrimChr [mkNumConT 1, itList t] [iMkLitSize 1 0]

iMkCons :: IType -> IExpr a -> IExpr a -> IExpr a
iMkCons t e_hd e_tl =
  let a = take1tmpVarIds
      ic_ty = ITForAll a IKStar $
              (ITVar a) `itFun` (itList (ITVar a)) `itFun` (itList (ITVar a))
      cti = ConTagInfo { conNo = 1, numCon = 2, conTag = 1, tagSize = 1 }
      ic = ICon (idCons noPosition)
                (ICCon { iConType = ic_ty, conTagInfo = cti })
      -- multiple arguments become a single struct argument
      e = iMkPairAt noPosition t (itList t) e_hd e_tl
  in  IAps ic [t] [e]

iMkList :: IType -> [IExpr a] -> IExpr a
iMkList t xs = foldr (iMkCons t) (iMkNil t) xs

iMkBool :: Bool -> IExpr a
iMkBool True  = iTrue
iMkBool False = iFalse

iMkBoolAt :: Position -> Bool -> IExpr a
iMkBoolAt pos True  = iTrueAt pos
iMkBoolAt pos False = iFalseAt pos

iMkRealBool :: Bool -> IExpr a
iMkRealBool b = IAps (ICon i (ICPrim t PrimChr)) [] [iMkBool b]
  where i = if b then idTrue else idFalse
        t = itBit1 `itFun` itBool

iTrue :: IExpr a
iTrue = iMkLitSize 1 1

iTrueAt :: Position -> IExpr a
iTrueAt pos = iMkLitSizeAt pos 1 1

iFalse :: IExpr a
iFalse = iMkLitSize 1 0

iFalseAt :: Position -> IExpr a
iFalseAt pos = iMkLitSizeAt pos 1 0

-- conversions between Bit#(1) and Bool

toBit :: IExpr a -> IExpr a
toBit e = IAps icPrimOrd [itBool, it1] [e]

toBool :: IExpr a -> IExpr a
toBool e = IAps icPrimChr [it1, itBool] [e]

-- Functions
ieAnd :: IExpr a -> IExpr a -> IExpr a
--ieAnd e1 e2@(IAps (ICon _ (ICPrim _ PrimBAnd)) _ [a,b]) | e1 == a || e1 == b = e2
ieAnd e1 e2 | isTrue e1      = e2
ieAnd e1 e2 | isTrue e2      = e1
ieAnd e1 e2 | isFalse e1     = iFalse
ieAnd e1 e2 | isFalse e2     = iFalse
ieAnd e1 e2                  = IAps iAnd [] [e1, e2]

-- Versions of ieAnd with some optimization -- more expensive call
ieAndOpt :: IExpr a -> IExpr a -> IExpr a
ieAndOpt e1 e2 | e1 == e2       = e1
ieAndOpt e1 e2 | e1 == ieNot e2 = iFalse
ieAndOpt e1 e2 = ieAnd e1 e2


ieOr :: IExpr a -> IExpr a -> IExpr a
--ieOr e1 e2@(IAps (ICon _ (ICPrim _ PrimBAnd)) _ [a,b]) | e1 == a || e1 == b = e1
ieOr e1 e2 | isFalse e1     = e2
ieOr e1 e2 | isFalse e2     = e1
ieOr e1 e2 | isTrue e1      = iTrue
ieOr e1 e2 | isTrue e2      = iTrue
ieOr e1 e2                  = IAps iOr [] [e1, e2]

ieOrOpt :: IExpr a -> IExpr a -> IExpr a
-- a || (a && b) == a
ieOrOpt e1 e2@(IAps (ICon _ (ICPrim _ PrimBAnd)) _ [a,b]) | e1 == a || e1 == b = e1
-- a || (~a && b ) == a || b
ieOrOpt e1 e2@(IAps (ICon _ (ICPrim _ PrimBAnd)) _ [a,b]) | e1 == ieNot a = ieOrOpt e1 b
ieOrOpt e1 e2@(IAps (ICon _ (ICPrim _ PrimBAnd)) _ [a,b]) | e1 == ieNot b = ieOrOpt e1 a
ieOrOpt e1 e2 | e1 == e2       = e1
ieOrOpt e1 e2 | e1 == ieNot e2 = iTrue
ieOrOpt e1 e2 = ieOr e1 e2


ieNot :: IExpr a -> IExpr a
ieNot (IAps (ICon _ (ICPrim _ PrimBNot)) _ [e]) = e
ieNot (IAps p@(ICon _ (ICPrim _ PrimIf)) ts [c,t,e]) = IAps p ts [c, ieNot t, ieNot e]
ieNot e | isFalse e = iTrue
ieNot e | isTrue e  = iFalse
ieNot e = IAps iNot [] [e]

ieIf :: IType -> IExpr a -> IExpr a -> IExpr a -> IExpr a
--ieIf ty (IAps (ICon _ (ICPrim _ PrimBNot)) _ [c]) t e = ieIf ty c e t
ieIf ty c t e | isTrue c  = t
ieIf ty c t e | isFalse c = e
--ieIf ty c t e | t == e    = t
ieIf ty c t e               = IAps icIf [ty] [c, t, e]

ieIfx :: IType -> IExpr a -> IExpr a -> IExpr a -> IExpr a
ieIfx ty c t e | t == e                                = t
               | ty == itBit1 && isTrue t && isFalse e = c
               | otherwise                             = ieIf ty c t e

ieArraySel :: IType -> Integer -> IExpr a -> [IExpr a] -> IExpr a
-- XXX check if the index is constant and return that element?
ieArraySel elem_ty idx_sz idx es =
  let n = length es
      arr = IAps (icPrimBuildArray n) [elem_ty] es
  in  IAps icPrimArrayDynSelect [elem_ty, ITNum idx_sz] [arr, idx]

-- This is like ieArraySel, except that it takes a default value
ieCase :: IType -> Integer -> IExpr a -> [IExpr a] -> IExpr a -> IExpr a
ieCase elem_ty idx_sz idx es dflt =
  let idx_ty = itBitN idx_sz
      max_idx = (2 ^ idx_sz) - 1
      mkArm c e = (iMkLit idx_ty c, e)
      arms = zipWith mkArm [0..max_idx] es
      n = length arms
      ces = flattenPairs arms
  in  IAps (icPrimCase n) [ITNum idx_sz, elem_ty] (idx:dflt:ces)

isTrue :: IExpr a -> Bool
isTrue (ICon _ (ICInt { iVal = IntLit { ilValue = 1 } })) = True
isTrue _ = False

isFalse :: IExpr a -> Bool
isFalse (ICon _ (ICInt { iVal = IntLit { ilValue = 0 } })) = True
isFalse _ = False

iePrimWhen :: IType -> IExpr a -> IExpr a -> IExpr a
iePrimWhen t p e =
    if isTrue p then
        e
    else
        IAps icPrimWhen [t] [p, e]

pTrue :: Pred a
pTrue = PConj S.empty

iePrimWhenPred :: IType -> Pred a -> IExpr a -> IExpr a
iePrimWhenPred t p e =
  if p == pTrue then
      e
  else IAps icPrimWhenPred [t] [icPred p, e]

ieJoinR :: IExpr a -> IExpr a -> IExpr a
ieJoinR e1 e2 | e1 == icNoRules = e2
ieJoinR e1 e2 | e2 == icNoRules = e1
ieJoinR e1 e2 = IAps icJoinRules [] [e1, e2]

ieJoinA :: IExpr a -> IExpr a -> IExpr a
ieJoinA e1 e2 | e1 == icNoActions = e2
ieJoinA e1 e2 | e2 == icNoActions = e1
ieJoinA e1 e2 = IAps icJoinActions [] [e1, e2]

-- utility method to check for type action
isTAction :: IType -> Bool
isTAction (ITCon a _ _) = a == idPrimAction
isTAction _ = False

-- Constants
iAnd, iOr, iNot :: IExpr a
iAnd = ICon idPrimBAnd (ICPrim (itBit1 `itFun` itBit1 `itFun` itBit1) PrimBAnd)
iOr  = ICon idPrimBOr  (ICPrim (itBit1 `itFun` itBit1 `itFun` itBit1) PrimBOr)
iNot = ICon idPrimBNot (ICPrim (itBit1 `itFun` itBit1) PrimBNot)

icJoinRules, icNoRules, icRule, icAddSchedPragmas, icJoinActions, icNoActions ::  IExpr a
icJoinRules = ICon idPrimJoinRules (ICPrim (itRules `itFun` itRules `itFun` itRules) PrimJoinRules)
icNoRules = ICon idPrimNoRules (ICPrim itRules PrimNoRules)
icRule = ICon idPrimRule (ICPrim (itString `itFun` itBit0 `itFun` itBit1 `itFun` itAction `itFun` itRules) PrimRule)
icAddSchedPragmas = ICon idPrimAddSchedPragmas (ICPrim (itSchedPragma `itFun` itRules `itFun` itRules) PrimAddSchedPragmas)
icJoinActions = ICon idPrimJoinActions (ICPrim (itAction `itFun` itAction `itFun` itAction) PrimJoinActions)
icNoActions = ICon idPrimNoActions (ICPrim itAction PrimNoActions)

icIf :: IExpr a
icIf = ICon idPrimIf (ICPrim (ITForAll i IKStar (itBit1 `itFun` ty `itFun` ty `itFun` ty)) PrimIf)
  where i = take1tmpVarIds
        ty = ITVar i

icPrimArrayDynSelect :: IExpr a
icPrimArrayDynSelect = ICon idPrimArrayDynSelect (ICPrim t PrimArrayDynSelect)
  where elem_ty = ITVar a
        arr_ty = ITAp itPrimArray elem_ty
        idx_ty = aitBit (ITVar n)
        t = ITForAll a IKStar $
              ITForAll n IKNum $
                arr_ty `itFun` idx_ty `itFun` elem_ty
        (a, n) = take2tmpVarIds

icPrimBuildArray ::  (Num a, Enum a) => a -> IExpr b
icPrimBuildArray sz = ICon idPrimBuildArray (ICPrim t PrimBuildArray)
  where elem_ty = ITVar i
        arr_ty = ITAp itPrimArray elem_ty
        t = ITForAll i IKStar $ foldr (\ e f -> elem_ty `itFun` f) arr_ty [1..sz]
        i = take1tmpVarIds

-- n is the number of explicit arms, not counting the default arm
icPrimCase :: (Num a, Enum a) => a -> IExpr b
icPrimCase sz = ICon idPrimCase (ICPrim t PrimCase)
  where elem_ty = ITVar a
        idx_ty = aitBit (ITVar n)
        t = ITForAll n IKNum $
              ITForAll a IKStar $
                idx_ty `itFun` elem_ty `itFun`
                  (foldr (\ e f -> idx_ty `itFun` elem_ty `itFun` f)
                         elem_ty [1..sz])
        (n, a) = take2tmpVarIds

icPrimOrd :: IExpr a
icPrimOrd = ICon idPrimOrd (ICPrim t PrimOrd)
  where t = ITForAll a IKStar (ITForAll n IKNum (ITVar a `itFun` aitBit (ITVar n)))
        (a, n) = take2tmpVarIds

icPrimChr :: IExpr a
icPrimChr = ICon idPrimChr (ICPrim t PrimChr)
  where t = ITForAll n IKNum (ITForAll a IKStar (aitBit (ITVar n) `itFun` ITVar a))
        (n, a) = take2tmpVarIds

icSelect :: Position -> IExpr a
icSelect pos = ICon (idPrimSelectAt pos) (ICPrim t PrimSelect)
  where t = ITForAll k IKNum (ITForAll m IKNum (ITForAll n IKNum rt))
        rt = aitBit (ITVar n) `itFun` aitBit (ITVar k)
        (k, m, n) = take3tmpVarIds

icPrimConcat :: IExpr a
icPrimConcat = ICon idPrimConcat (ICPrim t PrimConcat)
  where t = ITForAll k IKNum (ITForAll m IKNum (ITForAll n IKNum rt))
        rt = aitBit (ITVar k) `itFun` aitBit (ITVar m) `itFun` aitBit (ITVar n)
        (k, m, n) = take3tmpVarIds

icPrimMul :: IExpr a
icPrimMul = ICon idPrimMul (ICPrim t PrimMul)
  where t = ITForAll k IKNum (ITForAll m IKNum (ITForAll n IKNum rt))
        rt = aitBit (ITVar k) `itFun` aitBit (ITVar m) `itFun` aitBit (ITVar n)
        (k, m, n) = take3tmpVarIds

icPrimQuot :: IExpr a
icPrimQuot = ICon idPrimQuot (ICPrim t PrimQuot)
  where t = ITForAll k IKNum (ITForAll n IKNum rt)
        rt = aitBit (ITVar k) `itFun` aitBit (ITVar n) `itFun` aitBit (ITVar k)
        (k, n) = take2tmpVarIds

icPrimRem :: IExpr a
icPrimRem = ICon idPrimRem (ICPrim t PrimRem)
  where t = ITForAll k IKNum (ITForAll n IKNum rt)
        rt = aitBit (ITVar k) `itFun` aitBit (ITVar n) `itFun` aitBit (ITVar n)
        (k, n) = take2tmpVarIds

icPrimZeroExt :: IExpr a
icPrimZeroExt = ICon idPrimZeroExt (ICPrim t PrimZeroExt)
  where t = ITForAll m IKNum (ITForAll k IKNum (ITForAll n IKNum rt))
        rt = aitBit (ITVar k) `itFun` aitBit (ITVar n)
        (k, m, n) = take3tmpVarIds

icPrimSignExt :: IExpr a
icPrimSignExt = ICon idPrimSignExt (ICPrim t PrimSignExt)
  where t = ITForAll m IKNum (ITForAll k IKNum (ITForAll n IKNum rt))
        rt = aitBit (ITVar k) `itFun` aitBit (ITVar n)
        (k, m, n) = take3tmpVarIds

icPrimTrunc :: IExpr a
icPrimTrunc = ICon idPrimTrunc (ICPrim t PrimTrunc)
  where t = ITForAll k IKNum (ITForAll m IKNum (ITForAll n IKNum rt))
        rt = aitBit (ITVar n) `itFun` aitBit (ITVar m)
        (k, m, n) = take3tmpVarIds

icPrimRel :: Id -> PrimOp -> IExpr a
icPrimRel id p = ICon id (ICPrim (ITForAll i IKNum (ty `itFun` ty `itFun` itBit1)) p)
  where i = take1tmpVarIds
        ty = itBit `ITAp` ITVar i

icPrimWhen :: IExpr a
icPrimWhen = ICon idPrimWhen (ICPrim t PrimWhen)
  where t = ITForAll i IKStar (itBit1 `itFun` ITVar i `itFun` ITVar i)
        i = take1tmpVarIds

icPrimWhenPred :: IExpr a
icPrimWhenPred = ICon idPrimWhen (ICPrim t PrimWhenPred)
  where t = ITForAll i IKStar (itPred `itFun` ITVar i `itFun` ITVar i)
        i = take1tmpVarIds

itUninitialized :: IType
itUninitialized = ITForAll i IKStar (itPosition `itFun` itString `itFun` ITVar i)
  where i = take1tmpVarIds

icPrimRawUninitialized, icPrimUninitialized :: IExpr a
icPrimRawUninitialized = ICon idPrimRawUninitialized (ICPrim itUninitialized PrimRawUninitialized)
icPrimUninitialized = ICon idPrimUninitialized (ICPrim itUninitialized PrimUninitialized)

icPrimSetSelPosition :: IExpr a
icPrimSetSelPosition = ICon idPrimSetSelPosition (ICPrim t PrimSetSelPosition)
  where t = ITForAll i IKStar (itPosition `itFun` ITVar i `itFun` ITVar i)
        i = take1tmpVarIds

icPrimSL :: IExpr a
icPrimSL = ICon idPrimSL (ICPrim t PrimSL)
  where t = ITForAll i IKNum (ty `itFun` itNat `itFun` ty)
        ty = itBit `ITAp` ITVar i
        i = take1tmpVarIds

icPrimSRL :: IExpr a
icPrimSRL = ICon idPrimSRL (ICPrim t PrimSRL)
  where t = ITForAll i IKNum (ty `itFun` itNat `itFun` ty)
        ty = itBit `ITAp` ITVar i
        i = take1tmpVarIds

icPrimEQ, icPrimULE, icPrimULT, icPrimSLE, icPrimSLT :: IExpr a
icPrimEQ = icPrimRel idPrimEQ PrimEQ
icPrimULE = icPrimRel idPrimULE PrimULE
icPrimULT = icPrimRel idPrimULT PrimULT
icPrimSLE = icPrimRel idPrimSLE PrimSLE
icPrimSLT = icPrimRel idPrimSLT PrimSLT

-- For primitive functions of type (Bit n -> Bit n -> Bit n)
icPrimBinVecOp :: Id -> PrimOp -> IExpr a
icPrimBinVecOp id p = ICon id (ICPrim t p)
  where t = ITForAll i IKNum (ty `itFun` ty `itFun` ty)
        i = take1tmpVarIds
        ty = itBit `ITAp` ITVar i

icPrimAdd, icPrimSub :: IExpr a
icPrimAdd = icPrimBinVecOp idPrimAdd PrimAdd
icPrimSub = icPrimBinVecOp idPrimSub PrimSub

icPrimInv :: IExpr a
icPrimInv = ICon idPrimSL (ICPrim t PrimInv)
  where t = ITForAll i IKNum (ty `itFun` ty)
        i = take1tmpVarIds
        ty = itBit `ITAp` ITVar i

icPrimIntegerToBit :: IExpr a
icPrimIntegerToBit = ICon (idFromInteger noPosition) (ICPrim t PrimIntegerToBit)
  where t  = ITForAll i IKNum (itInteger `itFun` (aitBit ty))
        ty = ITVar i
        i  = take1tmpVarIds

icClock :: Id -> IClock a -> IExpr a
icClock i c = ICon i (ICClock {iConType = itClock, iClock = c})

icReset :: Id -> IReset a -> IExpr a
icReset i r = ICon i (ICReset {iConType = itReset, iReset = r})

icInout :: Id -> Integer -> IInout a -> IExpr a
icInout i sz iot = ICon i (ICInout {iConType = itInout_N sz, iInout = iot})

icSelClockOsc :: Id -> IClock a -> IExpr a
icSelClockOsc i c =
    IAps (ICon idClockOsc (ICSel { iConType = itClock `itFun` itBit1,
                                    selNo = 0,
                                    numSel = 2 }))
         []
         [icClock i c]

icSelClockGate :: Id -> IClock a -> IExpr a
icSelClockGate i c =
    IAps (ICon idClockGate (ICSel { iConType = itClock `itFun` itBit1,
                                    selNo = 1,
                                    numSel = 2 }))
         []
         [icClock i c]

icNoClock, icNoReset, icNoPosition :: IExpr a
icNoClock = icClock idNoClock noClock
icNoReset = icReset idNoReset noReset
icNoPosition = ICon idNoPosition (ICPosition { iConType = itPosition, iPosition = [noPosition] })

-- turn an oscillator and gate expression into a clock wires tuple
makeClockWires :: IExpr a -> IExpr a -> IExpr a
makeClockWires osc gate = iAps (ICon idClock (ICTuple {iConType = itClockCons, fieldIds = [idClockOsc, idClockGate]})) [] [osc, gate]

noClock :: IClock a
noClock = makeClock noClockId noClockDomain (makeClockWires (iMkLit itBit1 0) (iMkLit itBit1 0))

missingDefaultClock :: IClock a
-- XXX should the wires evaluate to error?
missingDefaultClock = makeClock noDefaultClockId noClockDomain (makeClockWires (iMkLit itBit1 0) (iMkLit itBit1 0))

noReset :: IReset a
noReset = makeReset noResetId noClock (ICon idNoReset (ICPrim itBit1 PrimResetUnassertedVal))

-- XXX should the reset wire be an error?
missingDefaultReset :: IReset a
missingDefaultReset = makeReset noDefaultResetId noClock (iMkLit itBit1 1)

-- clock extraction utilities
-- required here because they need noClock which needs itClockCons
-- (via makeClockWires)
getNamedClock :: Id -> IStateVar a -> IClock a
getNamedClock i v =
    -- XXX unQualId VModInfo
    case (lookup (unQualId i) (getClockMap v)) of
        Just c -> c
        Nothing -> internalError
                     ("ISyntaxUtil.getNamedClockFromMap: unknown clock " ++
                      (ppReadable i) ++ (ppReadable v) ++
                      (ppReadable (getClockMap v)))

getMethodClock :: Id -> IStateVar a -> IClock a
getMethodClock i v@(IStateVar { isv_vmi = vmi }) =
    case mclock_name of
        Nothing -> noClock
        Just n  -> getNamedClock n v
  -- XXX unQualId VModInfo
  where mclock_names =
            [ c | Method { vf_name = n, vf_clock = c } <- vFields vmi,
                  n == unQualId i]
        mclock_name =
            case mclock_names of
                [n] -> n
                _   -> internalError ("ISyntaxUtil.getMethodClock: " ++
                                      (ppReadable vmi) ++ (ppReadable i))

getIfcInoutClock :: Id -> IStateVar a -> IClock a
getIfcInoutClock i v@(IStateVar { isv_vmi = vmi }) =
    case mclock_name of
        Nothing -> noClock
        Just n  -> getNamedClock n v
  -- XXX unQualId VModInfo
  where mclock_names =
            [ c | Inout { vf_name = n, vf_clock = c } <- vFields vmi,
                  n == unQualId i]
        mclock_name =
            case mclock_names of
                [n] -> n
                _   -> internalError ("ISyntaxUtil.getIfcInoutClock: " ++
                                      (ppReadable vmi) ++ (ppReadable i))

-- reset extraction utilities (like the clock extraction utilities)
-- they also need noReset
getNamedReset :: Id -> IStateVar a -> IReset a
getNamedReset i v =
    -- XXX unQualId VModInfo
    case (lookup (unQualId i) (getResetMap v)) of
        Just r -> r
        Nothing -> internalError
                     ("ISyntaxUtil.getNamedResetFromMap: unknown reset " ++
                      (ppReadable i) ++ (ppReadable v) ++
                      (ppReadable (getResetMap v)))

getMethodReset :: Id -> IStateVar a -> IReset a
getMethodReset i v@(IStateVar { isv_vmi = vmi }) =
    case mreset_name of
        Nothing -> noReset
        Just n  -> getNamedReset n v
  -- XXX unQualId VModInfo
  where mreset_names =
            [ r | Method { vf_name = n, vf_reset = r } <- vFields vmi,
                  n == unQualId i]
        mreset_name =
            case mreset_names of
                [n] -> n
                _   -> internalError ("ISyntaxUtil.getMethodReset: " ++
                                      (ppReadable vmi) ++ (ppReadable i))

getIfcInoutReset :: Id -> IStateVar a -> IReset a
getIfcInoutReset i v@(IStateVar { isv_vmi = vmi }) =
    case mreset_name of
        Nothing -> noReset
        Just n  -> getNamedReset n v
  -- XXX unQualId VModInfo
  where mreset_names =
            [ r | Inout { vf_name = n, vf_reset = r } <- vFields vmi,
                  n == unQualId i]
        mreset_name =
            case mreset_names of
                [n] -> n
                _   -> internalError ("ISyntaxUtil.getIfcInoutReset: " ++
                                      (ppReadable vmi) ++ (ppReadable i))

getClockGate :: IClock a -> IExpr a
getClockGate c =
   case (getClockWires c) of
     IAps (ICon i (ICTuple {fieldIds = [i_osc, i_gate]})) [] [osc, gate] |
        i == idClock && i_osc == idClockOsc && i_gate == idClockGate -> gate
     IAps (ICon i (ICSel { iConType = itClock })) _ [(ICon vid (ICStateVar {iVar = sv}))] ->
        case (lookupOutputClockWires i (getVModInfo sv)) of
          (_, Nothing) -> iTrue
          (_, Just _)  -> icSelClockGate i c
     _ -> internalError "ISyntaxUtil.getClockGate"

-- Print a user-readable string for a clock expression
-- (displays the source-level name, using the interface name not the
-- Verilog port)
-- XXX This could be achieved by defining PVPrint on IExpr and adding
-- XXX a case-arm for oscillator/gate selection applied to a clock,
-- XXX to print just that field of the clock.  Then you could just call
-- XXX pvPrint on "getClockOsc" (which could be defined as above).
getClockOscString :: IClock a -> String
getClockOscString clk =
   let
       handleExpr :: IExpr a -> String
       handleExpr (IAps (ICon m (ICSel { })) _
                        [(ICon i (ICClock { iClock = c }))]) = handleClk c
       handleExpr (ICon v (ICModPort { })) =
           -- This does not display the user-level name for a port.
           -- We currently expect the caller to handle that.
           getIdString v
       handleExpr (IAps (ICon m (ICSel { })) _
                        (ICon vid (ICStateVar { }) : es )) =
           getIdString vid ++ "." ++ getIdString m
       handleExpr e = internalError ("getClockOscString: unexpected expr: " ++
                                     ppReadable e)

       handleClk :: IClock a -> String
       handleClk c =
           case (getClockWires c) of
               IAps (ICon i (ICTuple {fieldIds = [i_osc, i_gate]})) []
                    [osc, gate] | i == idClock &&
                                  i_osc == idClockOsc && i_gate == idClockGate
                 -> handleExpr osc
               IAps (ICon i (ICSel { iConType = itClock })) _
                    [(ICon vid (ICStateVar {iVar = sv}))]
                 -> -- display the BSV name, not the Verilog port
                    getIdString vid ++ "." ++ getIdString i
                    --let port = fst $
                    --           lookupOutputClockPorts i (getVModInfo sv)
                    --in  getIdString (mkOutputWireId vid port)
               e -> internalError ("getClockOscString: " ++ ppReadable e)
   in
       handleClk clk

getResetString :: IReset a -> String
getResetString rst =
   let
       handleExpr :: IExpr a -> String
       handleExpr (ICon _ (ICReset { iReset = r })) = handleRst r
       handleExpr (ICon v (ICModPort { })) =
           -- This does not display the user-level name for a port.
           -- We currently expect the caller to handle that.
           getIdString v
       handleExpr (IAps (ICon m (ICSel { })) _
                        [ICon vid (ICStateVar { })]) =
           getIdString vid ++ "." ++ getIdString m
       handleExpr e = internalError ("getResetString: unexpected expr: " ++
                                     ppReadable e)

       handleRst :: IReset a -> String
       handleRst r = handleExpr (getResetWire r)
   in
       handleRst rst


-- Utils
iAps :: IExpr a -> [IType] -> [IExpr a] -> IExpr a
iAps e [] [] = e
iAps (IAps e ts es) [] es' = IAps e ts (es ++ es')
iAps e ts es = IAps e ts es

iAPs :: IExpr a -> [IType] -> IExpr a
iAPs e ts = iAps e ts []

iLet :: Id -> IType -> IExpr a -> IExpr a -> IExpr a
iLet i _ e (IVar i') | i == i' && not (isKeepId i) && not (isKeepId i') = e
iLet i t e e' = iAp (ILam i t e') e

iePrimEQ, iePrimULE :: IType -> IExpr a -> IExpr a -> IExpr a
iePrimEQ t e1 e2 = IAps icPrimEQ [t] [e1, e2]
iePrimULE t e1 e2 = IAps icPrimULE [t] [e1, e2]

-- Misc
idIntLit, idRealLit, idPositionLit, idPredLit, idStringLit, idCharLit, idHandleLit :: Id
idIntLit       = dummyId noPosition
idRealLit      = dummyId noPosition
idPositionLit  = dummyId noPosition
idPredLit      = dummyId noPosition
idStringLit    = dummyId noPosition
idCharLit      = dummyId noPosition
idHandleLit    = dummyId noPosition

itInst :: IType -> [IType] -> IType
itInst (ITForAll i _ t) (a:as) = itInst (tSubst i a t) as
itInst t                []     = t
itInst t                as     = internalError ("itInst: " ++ ppReadable (t, as))

leftmost :: IType -> IType
leftmost (ITAp t _) = leftmost t
leftmost t = t

dropForAll :: IType -> IType
dropForAll (ITForAll _ _ t) = dropForAll t
dropForAll t = t

dropArrows :: Int -> IType -> IType
dropArrows 0 t = t
dropArrows n (ITAp (ITAp arr _) r) | arr == itArrow = dropArrows (n-1) r
dropArrows n t = internalError ("dropArrows: " ++ ppReadable (n, t))

itGetArrows :: IType -> ([IType], IType)
itGetArrows it = itGetArrows' [] it
  where itGetArrows' ts (ITAp (ITAp arr a) r) | arr == itArrow = itGetArrows' (a:ts) r
        itGetArrows' ts r = (reverse ts, r)

-- #############################################################################
-- #
-- #############################################################################

-- Apply an ISyntax substitution to the predicate and action of a set of rules
irulesMap :: (IExpr a -> IExpr a) -> IRules a -> IRules a
irulesMap f (IRules sps rs) = IRules sps (map (iruleMap f) rs)
  where iruleMap f r = r { irule_pred = f (irule_pred r),
                           irule_body = f (irule_body r) }

irulesMapM :: (Monad m) => (IExpr a -> m (IExpr a)) -> IRules a -> m (IRules a)
irulesMapM f (IRules sps rs) = do
  let iruleMapM f r = do
        p' <- f $ irule_pred r
        a' <- f $ irule_body r
        return r { irule_pred = p' , irule_body = a' }
  rs' <- mapM (iruleMapM f) rs
  return (IRules sps rs')

-------------------

-- Similar to the routine in ISyntaxCheck, but with shortcuts to make
-- it faster.

iGetType :: IExpr a -> IType
iGetType e0 =
    let iGetTypePrim _ PrimIf [t] [_,_,_] = t
        iGetTypePrim _ PrimConcat [_,_,ITNum n] [_,_] = itBitN n
        iGetTypePrim _ PrimMul [_,_,ITNum n] [_,_] = itBitN n
        iGetTypePrim _ PrimQuot [_,_,ITNum n] [_,_] = itBitN n
        iGetTypePrim _ PrimRem [_,_,ITNum n] [_,_] = itBitN n
        iGetTypePrim _ PrimSelect [ITNum n,_,_] [_] = itBitN n
        iGetTypePrim _ PrimJoinActions [] [_,_] = itAction
        iGetTypePrim _ p          _  [_,_] | isBoolRes p = itBit1
          where isBoolRes PrimEQ  = True
                isBoolRes PrimULE  = True
                isBoolRes PrimULT  = True
                isBoolRes PrimSLE  = True
                isBoolRes PrimSLT  = True
                isBoolRes PrimBAnd = True
                isBoolRes PrimBOr  = True
                isBoolRes PrimBNot = True
                isBoolRes _        = False
        iGetTypePrim _ p       [ITNum n]  [_,_] | isNRes p = itBitN n
          where isNRes PrimAdd = True
                isNRes PrimSub = True
                isNRes PrimAnd = True
                isNRes PrimOr  = True
                isNRes PrimXor = True
                isNRes PrimSL  = True
                isNRes PrimSRL = True
                isNRes PrimSRA = True
                isNRes _       = False
        iGetTypePrim e _ _ _ = tCheck emptyEnv e

        tCheck r (ILam i t e) =
                itFun t (tCheck (addT i t r) e)
        tCheck r (IAps f [] []) = tCheck r f
        tCheck r (IAps e [t] []) =
                case tCheck r e of
                ITForAll i _ rt -> tSubst i t rt
                tt -> internalError ("iGetType.tCheck: " ++ ppString (e0, e, tt, t))
        tCheck r (IAps f (t:ts) []) = tCheck r (IAps (IAps f [t] []) ts [])
        tCheck r (IAps f ts es) = dropArrows (length es) (tCheck r (IAps f ts []))
        tCheck r (IVar i) = findT i r
        tCheck r (ILAM i k e) = ITForAll i k (tCheck r e)
        tCheck r (ICon c ic) = iConType ic
        tCheck r (IRefT t _ _) = t
--        tCheck _ e = internalError ("no match in ISyntaxUtil.tCheck: " ++ ppReadable e)

        emptyEnv = M.empty

        addT i t tm = M.insert i t tm

        findT i tm =
                case M.lookup i tm of
                Just t -> t
                Nothing -> internalError ("ISyntaxUtil.findT " ++ ppString i ++ "\n" ++ ppReadable (M.toList tm))

    in  case e0 of
        -- First some fast special cases:
        (ICon c ic) -> iConType ic
        e@(IAps (ICon _ (ICPrim _ p)) ts es) -> iGetTypePrim e p ts es
        -- General
        e -> tCheck emptyEnv e

-- input must be an interface type
iGetIfcName :: IType -> Id
iGetIfcName t = fromMaybe err (iMGetIfcName t)
  where err = internalError ("ISyntaxUtil.iGetIfcName: " ++ ppReadable t)

iMGetIfcName :: IType -> Maybe Id
iMGetIfcName (ITCon i _ (TIstruct (SInterface _) _)) = Just i
iMGetIfcName (ITAp t _) = iMGetIfcName t
iMGetIfcName t = Nothing

-- get the interface type from a Module def type
iGetModIfcType :: IType -> IType
iGetModIfcType t =
    let (_, modTy) = itGetArrows t
    in  case modTy of
          ITAp _ ifcTy -> ifcTy
          _ -> internalError ("iGetModIfcType: " ++ ppReadable modTy)

getITypeSort :: IType -> Maybe TISort
getITypeSort (ITCon i _ tisort) = Just tisort
getITypeSort (ITAp t _) = getITypeSort t
getITypeSort _ = Nothing

isIfcType :: IType -> Bool
isIfcType t = case (getITypeSort t) of
                Just (TIstruct (SInterface _) _) -> True
                _ -> False

isPolyWrapType :: IType -> Bool
isPolyWrapType t = case (getITypeSort t) of
                Just (TIstruct (SPolyWrap _ _ _) _) -> True
                _ -> False

isAbstractType :: IType -> Bool
isAbstractType t = getITypeSort t == Just TIabstract


-- utility method to check if an expression is an if or not
notIf :: IExpr a -> Bool
notIf (IAps (ICon _ (ICPrim { primOp = PrimIf })) _ _) = False
notIf _ = True

-- note that ISplitIf.push assumes that PrimIf is FALSE for this function
isIfWrapper :: PrimOp -> Bool
isIfWrapper PrimExpIf = True
isIfWrapper PrimNoExpIf = True
isIfWrapper PrimNosplitDeep = True
isIfWrapper PrimSplitDeep = True
isIfWrapper _ = False

-- utilities for flattening and joining up action lists
-- flatAction: flattens (IAps joinactions a1 (IAps joinactions a2 a3 ...) into [a1, a2, a3 ...]

flattensToNothing :: IExpr a -> Bool
flattensToNothing (ICon _ (ICPrim { primOp = PrimNoActions })) = True
flattensToNothing (ICon i (ICUndet { })) = True
flattensToNothing (IAps (ICon i (ICUndet { })) _ _) = True
flattensToNothing _ = False

flatAction :: IExpr a -> [IExpr a]
flatAction x | flattensToNothing x = []
flatAction (IAps (ICon _ (ICPrim { primOp = PrimJoinActions })) _ [a1, a2]) = flatAction a1 ++ flatAction a2
--flatAction (IAps f ts es) = [IAps f ts (map (joinActions . flatAction) es)]
flatAction a = [a]

joinActions :: [IExpr a] -> IExpr a
joinActions [] = icNoActions
joinActions as = foldr1 ja as
  where ja a1 a2 = IAps icJoinActions [] [a1, a2]

-- perhaps the position information should be transferred over XXX
actionValue_BitN :: IType -> IType
actionValue_BitN t = itBitN (getAV_Size t)

iStrToInt :: String -> Position -> IExpr a
iStrToInt s pos = iMkLitAt pos itInteger i
  where i = foldl sumString 0 s
        sumString :: Integer -> Char -> Integer
        sumString t c = 256 * t + c'
          where c' = toInteger (fromEnum c)

iuDontCareExpr :: IExpr a
iuDontCareExpr = iMkLit itInteger uDontCareInteger

iuNoMatchExpr :: IExpr a
iuNoMatchExpr = iMkLit itInteger uNoMatchInteger

iuKindToExpr :: UndefKind -> IExpr a
iuKindToExpr = (iMkLit itInteger) . undefKindToInteger

getStateVarNames :: IExpr a -> [Id]
getStateVarNames (ILam _ _ e) = getStateVarNames e
getStateVarNames (ILAM _ _ e) = getStateVarNames e
getStateVarNames (ICon i (ICStateVar {})) = [i]
getStateVarNames (IAps f _ es) = concatMap getStateVarNames (f:es)
getStateVarNames _ = []

iTSizeOf :: IType
iTSizeOf = ITCon idSizeOf (IKStar `IKFun` IKNum) tiSizeOf

iTLog, iTAdd, iTMax, iTMin, iTMul, iTDiv :: IType
iTLog = ITCon idTLog (IKNum `IKFun` IKNum) TIabstract
iTAdd = ITCon idTAdd (IKNum `IKFun` IKNum `IKFun` IKNum) TIabstract
iTMax = ITCon idTMax (IKNum `IKFun` IKNum `IKFun` IKNum) TIabstract
iTMin = ITCon idTMin (IKNum `IKFun` IKNum `IKFun` IKNum) TIabstract
iTMul = ITCon idTMul (IKNum `IKFun` IKNum `IKFun` IKNum) TIabstract
iTDiv = ITCon idTDiv (IKNum `IKFun` IKNum `IKFun` IKNum) TIabstract

iDefMap :: (IExpr a -> IExpr a) -> IDef a -> IDef a
iDefMap f (IDef i t e p) = IDef i t (f e) p

iDefsMap :: (Functor f) => (IExpr a -> IExpr a) -> f (IDef a) -> f (IDef a)
iDefsMap f defs = fmap (iDefMap f) defs

iDefMapM :: (Monad m) => (IExpr a -> m (IExpr a)) -> IDef a -> m (IDef a)
iDefMapM f (IDef i t e p) = do
  e' <- f e
  return $ IDef i t e' p

emptyFmt :: (IExpr a)
emptyFmt = (IAps (ICon idFormat (ICForeign {fName    = getIdString(unQualId(idFormat)),
                                            foports  = Nothing,
                                            fcallNo  = (Just 0),
                                            iConType = tt,
                                            isC = False -- unsure what this should be?
                                            })) [] [e])
   where e = iMkString ""
         t = iGetType e
         tt = (t `itFun` itFmt)
