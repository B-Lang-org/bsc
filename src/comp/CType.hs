{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, PatternGuards, DeriveDataTypeable #-}
-- | The CType package defines the concrete representation of types and kinds.
module CType(
  -- * Types
  Type(..), CType, TyVar(..), TyCon(..), TISort(..), StructSubType(..),

  -- ** Examining Types
  getTyVarId, getTypeKind,
  isTNum, getTNum,
  isTStr, getTStr,
  isTVar, isTCon, isIfc, isInterface, isUpdateable,
  leftCon, leftTyCon, allTyCons, allTConNames, tyConArgs,
  splitTAp, normTAp,
  isTypeBit, isTypeString,
  isTypePrimAction, isTypeAction,
  isTypeActionValue, isTypeActionValue_,
  isTypePolyBit, bitWidth,
  isTypeUnit,
  noTyVarNo, isGeneratedTVar,
  getArrows,  getRes,
  seqCType,
  -- if the above are not sufficient, use these:
  isTypeTConNoArgs, isTypeTConArgs,
  getActionValueArg,
  isTConArrow, isTConPair,

  -- ** Constructing Types
  noType, tVar, tVarKind, cTVar, cTVarKind, cTVarNum, cTCon, cTNum, cTStr,
  cTApplys, setTypePosition,

  -- * Kinds
  Kind(..), PartialKind(..),


  -- ** Examining Kinds
  isKVar, getArgKinds, getResKind,

  -- ** Constructing Kinds
  baseKVar,

  -- * Type Classes
  CTypeclass(..),

  -- ** Examining Type Classes
  typeclassId,

  -- * Type class constraints
  CQType(..), CPred(..),
  getCQArrows,

        ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Data.Char(isDigit, chr)
import Data.List(union)
import Data.Maybe
import qualified Data.Generics as Generic

import Eval
import PPrint
import Position
import Id
import IdPrint
import PreIds(idArrow, idPrimPair, idPrimUnit, idBit, idString,
              idPrimAction, idAction, idActionValue_, idActionValue,
              idTNumToStr
              {-, idSizeOf -})
import Util(itos)
import ErrorUtil
import Pragma(IfcPragma)
import TypeOps
import PVPrint(PVPrint(..))
import FStringCompat

-- Data structures

-- | Representation of types
data Type = TVar TyVar         -- ^ type variable
          | TCon TyCon         -- ^ type constructor
          | TAp Type Type      -- ^ type-level application
          | TGen Position Int  -- ^ quantified type variable used in type schemes
          | TDefMonad Position -- ^ not used after CVParserImperative
    deriving (Show, Generic.Data, Generic.Typeable)

-- | Representation of a type variable
data TyVar = TyVar { tv_name :: Id    -- ^ name of the type variable
                   , tv_num  :: Int   -- ^ number for a generated type variable
                   , tv_kind :: Kind  -- ^ kind of the type variable
                   }
    deriving (Show, Generic.Data, Generic.Typeable)


-- | Representation of a type constructor
data TyCon = -- | A constructor for a type of value kind
             TyCon { tcon_name :: Id           -- ^ name of the type constructor
                   , tcon_kind :: (Maybe Kind) -- ^ kind of the type constructor
                   , tcon_sort :: TISort       -- ^ purpose of the type constructor
                   }
             -- | A constructor for a type of numeric kind
           | TyNum { tynum_value :: Integer  -- ^ type-level numeric value
                   , tynum_pos   :: Position -- ^ position of introduction
                   }
             -- | A constructor for a type of string kind
           | TyStr { tystr_value :: FString  -- ^ type-level string value
                   , tystr_pos   :: Position -- ^ position of introduction
                   }
    deriving (Show, Generic.Data, Generic.Typeable)

data TISort
        = -- type synonym
          TItype Integer Type
        | TIdata { tidata_cons :: [Id]
                 , tidata_enum :: Bool
                 }
        | TIstruct StructSubType [Id]
          -- primitive abstract type
          -- e.g. Integer, Bit, Module, etc.
        | TIabstract
        deriving (Eq, Ord, Show, Generic.Data, Generic.Typeable)


data StructSubType
        = SStruct
        | SClass
        | SDataCon { sdatacon_id :: Id
                   , sdatacon_named_fields :: Bool
                   }
        | SInterface [IfcPragma]
        | SPolyWrap { spolywrap_id :: Id         -- ^ name of the type with the wrapped field
                    , spolywrap_ctor :: Maybe Id -- ^ name of the data constructor
                    , spolywrap_field :: Id      -- ^ name of the wrapped field
                    }
        deriving (Eq, Ord, Show, Generic.Data, Generic.Typeable)

type CType = Type

-- | Representation of kinds
data Kind = KStar           -- ^ kind of a simple value type
          | KNum            -- ^ kind of a simple numeric type
          | KStr            -- ^ kind of a simple string type
          | Kfun Kind Kind  -- ^ kind of type constructors (type-level function)
          | KVar Int        -- ^ generated kind variable (used only during kind inference)
    deriving (Eq, Ord, Show, Generic.Data, Generic.Typeable)

-- Used for providing partial Kind information
data PartialKind
        = PKNoInfo -- this is what makes it partial
        | PKStar
        | PKNum
        | PKStr
        | PKfun PartialKind PartialKind
        deriving (Eq, Ord, Show)

-- | A named typeclass
newtype CTypeclass = CTypeclass Id
    deriving (Eq, Ord, Show, PPrint, HasPosition, NFData)

-- | Representation of the provisos and other class constraints
data CPred = CPred { cpred_tc   :: CTypeclass  -- ^ constraint class, e.g., "Eq"
                   , cpred_args :: [CType]     -- ^ argument types
                   }
        deriving (Eq, Ord, Show)

-- Eq instances

-- | used to do the sorting of instances
-- so that overlapping matches go to the most specific
-- TAp first because it brings forward instances with larger structure
-- see the Has_tpl_n instances in the Prelude
cmp :: Type -> Type -> Ordering
cmp (TAp f1 a1) (TAp f2 a2) = compare (f1, a1) (f2, a2)
cmp (TAp _  _)  _           = LT
cmp (TCon c1) (TCon c2) = compare c1 c2
cmp (TCon _)  (TAp _ _) = GT
cmp (TCon _)  _         = LT
cmp (TVar _) (TCon _)   = GT
cmp (TVar _) (TAp _ _)  = GT
cmp (TVar v1) (TVar v2) = compare v1 v2
cmp (TVar _)  _         = LT
cmp (TGen _ i1) (TGen _ i2) = compare i1 i2
cmp (TGen _ _) (TDefMonad _) = LT
cmp (TGen _ _) _        = GT
cmp (TDefMonad _) (TDefMonad _) = EQ
cmp (TDefMonad _) _  = GT

instance Eq Type where
    x == y  =  cmp x y == EQ

instance Eq TyVar where
    TyVar i n _ == TyVar i' n' _  =  (n, i) == (n', i')

instance Eq TyCon where
    TyCon i k _ == TyCon i' k' _  =  qualEq i i' && k == k'
    TyNum i _   == TyNum i' _     =  i == i'
    TyStr s _   == TyStr s' _     =  s == s'
    _           == _              =  False

-- Ord instances

instance Ord Type where
    compare x y = cmp x y

instance Ord TyVar where
    TyVar i n _ <= TyVar i' n' _  =  (n, i) <= (n', i')
    TyVar i n _ <  TyVar i' n' _  =  (n, i) <  (n', i')
    TyVar i n _ >= TyVar i' n' _  =  (n, i) >= (n', i')
    TyVar i n _ >  TyVar i' n' _  =  (n, i) >  (n', i')
    TyVar i n _ `compare` TyVar i' n' _  =  (n, i) `compare` (n', i')

instance Ord TyCon where
    TyCon i k _ `compare` TyCon i' k' _   =  (getIdBase i, getIdQual i, k) `compare` (getIdBase i', getIdQual i', k')
    TyCon _ _ _ `compare` TyNum _  _      =  LT
    TyCon _ _ _ `compare` TyStr _  _      =  LT
    TyNum _ _   `compare` TyCon _  _  _   =  GT
    TyNum i _   `compare` TyNum i' _      =  i `compare` i'
    TyNum _ _   `compare` TyStr _  _      =  LT
    TyStr _ _   `compare` TyCon _  _  _   =  GT
    TyStr _ _   `compare` TyNum _  _      =  GT
    TyStr s _   `compare` TyStr s' _      =  s `compare` s'





instance PPrint Type where
    pPrint d p (TCon (TyCon unit _ _)) | unit == idPrimUnit = text "()"
    pPrint d p (TCon c) = pPrint d 0 c
    pPrint d p (TVar i) = pPrint d 0 i
    pPrint d p (TAp (TAp (TCon pair) a) b) | isTConPair pair =
        pparen (p >= 0) (sep [pPrint d 0 a <> text ",", pPrint d (-1) b])
    pPrint d p (TAp (TAp (TCon arr) a) r) | isTConArrow arr =
        pparen (p > 8) (sep [pPrint d 9 a <+> text "->", pPrint d 8 r])
    pPrint d p (TAp e e') = pparen (p>9) $
        sep [pPrint d 9 e, pPrint d 10 e']
    pPrint d p (TDefMonad _) = text ("TDefMonad")
    pPrint d p (TGen _ n) = pparen True (text "TGen" <+> pPrint d p n)

instance NFData Type where
    rnf (TVar v) = rnf v
    rnf (TCon c) = rnf c
    rnf (TAp t1 t2) = rnf2 t1 t2
    rnf (TGen p i) = rnf2 p i
    rnf (TDefMonad _) = ()

instance HasPosition Type where
    getPosition (TVar var) = getPosition var
    getPosition (TCon con) = getPosition con
    getPosition (TAp f a) = getPosition f `bestPosition` getPosition a
    getPosition (TGen pos _) = pos
    getPosition (TDefMonad pos) = pos

instance NFData TyVar where
    rnf (TyVar i n k) = rnf3 i n k

instance HasPosition TyVar where
    getPosition (TyVar name _ _) = getPosition name

getTyVarId :: TyVar -> Id
getTyVarId = tv_name

instance PPrint TyVar where
    pPrint d _ (TyVar i _ _) = ppVarId d i

instance PPrint TyCon where
    pPrint d _ (TyCon i _ _) = ppConId d i
    pPrint d _ (TyNum i _) = text (itos i)
    pPrint d _ (TyStr s _) = text (show s)

instance NFData TyCon where
    rnf (TyCon i k s) = rnf3 i k s
    rnf (TyNum i p) = rnf2 i p
    rnf (TyStr s p) = rnf2 s p

instance HasPosition TyCon where
    getPosition (TyCon name k _) = getPosition name
    getPosition (TyNum _ pos) = pos
    getPosition (TyStr _ pos) = pos

instance HasPosition CQType where
    -- prefer t to ps, since that is a better position for BSV
    getPosition (CQType ps t) = getPosition t `bestPosition` getPosition ps

instance HasPosition CPred where
    getPosition (CPred c ts) = getPosition (c, ts)

data CQType = CQType [CPred] CType
    deriving (Eq, Ord, Show)

instance NFData CQType where
    rnf (CQType ps t) = rnf2 ps t


{-
-- should typeclass ids be equal if they are qualEq?
instance Eq CTypeclass where
  (==) (CTypeclass i) (Ctypeclass i') = qualEq i i'

instance Ord CTypeclass where
  compare (CTypeclass i) (CTypeclass i') | qualEq i i' = EQ
                                         | otherwise  = compare i i'
-}

-- This function is dangerous, it allows a CTypeclass to be "coerced" in type to a
-- bare Id, which in turn might be interpreted as something else.
typeclassId :: CTypeclass -> Id
typeclassId (CTypeclass i) = i

instance PVPrint CTypeclass where
   pvPrint d p (CTypeclass i) = pvPrint d p i

instance NFData CPred where
    rnf (CPred c ts) = rnf2 c ts

instance PPrint CQType where
    pPrint d p (CQType [] ct) = pPrint d p ct
    pPrint d p (CQType preds ct) = sep [text "(" <> sepList (map (pPrint d 0) preds) (text ",") <> text ")" <+> text "=>", pPrint d 0 ct]

instance PPrint CPred where
    pPrint d p (CPred (CTypeclass c) []) = ppConId d c
    pPrint d p (CPred (CTypeclass c) ts) = ppConId d c <+> sep (map (pPrint d (maxPrec+1)) ts)

noTyVarNo :: Int
noTyVarNo = -1

tVarKind :: Id -> Kind -> TyVar
tVarKind i k = TyVar i noTyVarNo k

tVar :: Id -> TyVar
-- XXX KVar (-42) below is a hack so that undefined is not visible
-- XXX when deriving Show
tVar i = tVarKind i (KVar (-42))

cTVar :: Id -> CType
cTVar i = TVar (tVar i)

cTVarKind :: Id -> Kind -> CType
cTVarKind name kind = TVar (tVarKind name kind)

cTVarNum :: Id -> CType
cTVarNum name = cTVarKind name KNum

cTCon :: Id -> CType
cTCon i | all isDigit s = cTNum (read s) (getIdPosition i)
        | head s == '"' = cTStr (mkFString $ read s) (getIdPosition i)
  where s = getIdString i
cTCon i = TCon (TyCon i Nothing TIabstract)

cTNum :: Integer -> Position -> CType
cTNum n pos = TCon (TyNum n pos)

isTNum :: CType -> Bool
isTNum (TCon (TyNum _ _)) = True
isTNum _ = False

getTNum :: CType -> Integer
getTNum (TCon (TyNum n _)) = n
getTNum t = internalError $ "getTNum: not a type-level integer -- " ++ (show t)

cTStr :: FString -> Position -> CType
cTStr s pos = TCon (TyStr s pos)

isTStr :: CType -> Bool
isTStr (TCon (TyStr _ _)) = True
isTStr _ = False

getTStr :: CType -> FString
getTStr (TCon (TyStr s _)) = s
getTStr t = internalError $ "getTNum: not a type-level string -- " ++ (show t)

isTVar :: Type -> Bool
isTVar (TVar _) = True
isTVar _ = False

isTCon :: Type -> Bool
isTCon (TCon _) = True
isTCon _ = False

isGeneratedTVar :: TyVar -> Bool
isGeneratedTVar (TyVar _ n _) = n /= noTyVarNo

isIfc :: StructSubType -> Bool
isIfc SInterface {} = True
--isIfc SStruct = True -- XXX why??
isIfc _ = False

isInterface :: CType -> Bool
isInterface t | Just (TyCon _ _ (TIstruct s _)) <- leftTyCon t = isIfc s
isInterface _ = False

isUpdateable :: StructSubType -> Bool
isUpdateable SStruct = True
isUpdateable SInterface {} = True
isUpdateable _ = False

noType :: Type
noType = TGen noPosition (-1)

getCQArrows :: CQType -> ([CQType], CQType)
getCQArrows (CQType preds ctype) =
    let (args, result) = getArrows ctype
    in  (map (CQType preds) args, CQType preds result)

getArrows :: Type -> ([Type], Type)
getArrows t = getArrowsAccum [] t
    where getArrowsAccum ts (TAp (TAp (TCon arr) a) r) | isTConArrow arr
                              = getArrowsAccum (a:ts) r
          getArrowsAccum ts r = (reverse ts, r)

getRes :: Type -> Type
getRes t = snd (getArrows t)

isTConArrow :: TyCon -> Bool
isTConArrow (TyCon i _ _) =  i == idArrow noPosition
isTConArrow t = internalError("isTConArrow: not TCon " ++ show t)

isTConPair :: TyCon -> Bool
isTConPair (TyCon i _ _) =  i == idPrimPair
isTConPair t = internalError("isTConPair: not TCon " ++ show t)

-- is a type a specific TCon with no arguments
isTypeTConNoArgs :: Id -> Type -> Bool
isTypeTConNoArgs cid (TCon (TyCon i _ _)) | (i == cid) = True
isTypeTConNoArgs _ _ = False

-- is a type a specific TCon with arguments
isTypeTConArgs :: Id -> Type -> Bool
isTypeTConArgs cid (TAp (TCon (TyCon i _ _)) _) | (i == cid) = True
isTypeTConArgs _ _ = False

isTypeBit, isTypeString, isTypePrimAction, isTypeAction :: Type -> Bool
isTypeBit          = isTypeTConArgs   idBit
isTypeString       = isTypeTConNoArgs idString
isTypePrimAction   = isTypeTConNoArgs idPrimAction
isTypeAction       = isTypeTConNoArgs idAction

isTypeActionValue, isTypeActionValue_, isTypeUnit :: Type -> Bool
isTypeActionValue  = isTypeTConArgs   idActionValue
isTypeActionValue_ = isTypeTConArgs   idActionValue_
isTypeUnit         = isTypeTConNoArgs  idPrimUnit

getActionValueArg :: Type -> Type
getActionValueArg (TAp (TCon (TyCon i _ _)) arg) | (i == idActionValue) = arg
getActionValueArg t = internalError ("getActionValueArg: " ++ ppReadable t)

-- These are used during foreign function processing to determine if arguments
-- and return values are polymorphic or of a known size.
isTypePolyBit :: Type -> Bool
isTypePolyBit (TAp (TCon (TyCon i _ _)) arg)
  | (i == idBit) || (i == idActionValue) || (i == idActionValue_) = isTVar arg
isTypePolyBit _ = False

bitWidth :: Type -> Integer
bitWidth (TAp (TCon (TyCon i _ _)) arg)
  | ((i == idBit) || (i == idActionValue) || (i == idActionValue_)) &&
     (isTNum arg) = getTNum arg
bitWidth t =
  internalError $ "bitWidth: not a Bit type of known width -- " ++ (show t)


cTApplys :: CType -> [CType] -> CType
cTApplys t ts = foldl TAp t ts

leftCon :: CType -> Maybe Id
leftCon (TAp f _) = leftCon f
leftCon (TCon (TyCon i _ _)) = Just i
leftCon _ = Nothing

leftTyCon :: CType -> Maybe TyCon
leftTyCon (TAp f _) = leftTyCon f
leftTyCon (TCon tc) = Just tc
leftTyCon _ = Nothing

tyConArgs :: CType -> [CType]
tyConArgs (TAp f a) = tyConArgs f ++ [a]
tyConArgs (TCon _) = []
tyConArgs t = internalError("tyConArgs: " ++ show t)

allTyCons :: CType -> [TyCon]
allTyCons (TCon c) = [c]
allTyCons (TAp f a) = allTyCons f `union` allTyCons a
allTyCons _ = []

getTConName :: TyCon -> Maybe Id
getTConName (TyCon i _ _) = Just i
getTConName (TyNum {}) = Nothing
getTConName (TyStr {}) = Nothing

allTConNames :: CType -> [Id]
allTConNames = mapMaybe getTConName . allTyCons

-- like the above functions, but works even if the left-most is not a tycon
splitTAp :: CType -> (CType, [CType])
splitTAp (TAp f a) = let (l,as) = splitTAp f
                     in  (l,as ++ [a])
splitTAp t = (t,[])

-- Copied from normITAp
normTAp :: Type -> Type -> Type
normTAp (TAp (TCon (TyCon op _ _)) (TCon (TyNum x xpos))) (TCon (TyNum y ypos))
        | isJust (res) = cTNum (fromJust res) (getPosition op)
  where res = opNumT op [x, y]

normTAp (TCon (TyCon op _ _)) (TCon (TyNum x xpos))
        | isJust (res) = cTNum (fromJust res) (getPosition op)
  where res = opNumT op [x]

normTAp (TAp (TCon (TyCon op _ _)) (TCon (TyStr x xpos))) (TCon (TyStr y ypos))
        | isJust (res) = cTStr (fromJust res) (getPosition op)
  where res = opStrT op [x, y]

normTAp (TCon (TyCon op _ _)) (TCon (TyNum x xpos))
        | op == idTNumToStr = cTStr (mkNumFString x) (getPosition op)

normTAp f a = TAp f a

getTypeKind :: Type -> Maybe Kind
getTypeKind (TVar (TyVar _ _ k))  = Just k
getTypeKind (TCon (TyCon _ mk _)) = mk
getTypeKind (TCon (TyNum _ _)) = Just KNum
getTypeKind (TCon (TyStr _ _)) = Just KStr
getTypeKind (TAp t1 t2) = case (getTypeKind t1) of
                            Just (Kfun k1 k2) -> Just k2
                            _ -> Nothing -- don't know or isn't Kfun
getTypeKind _ = Nothing

----

-- KIMisc.newKVar starts at this number
baseKVar :: Int
baseKVar = 1000

isKVar :: Kind -> Bool
isKVar (KVar _) = True
isKVar _ = False

-- Display the kind variable with letters
showKVar :: Int -> String
showKVar v =
    let
        makeDigit x = chr (x + 97)  -- 97 = ASCII a

        showDigits :: Int -> String
        showDigits x | (x < 26) = [makeDigit x]
        showDigits x = (showDigits (x `div` 26)) ++ [makeDigit (x `mod` 26)]
    in
        if (v < baseKVar)
        then (itos v)
        else (showDigits (v - baseKVar))

-- this differs from the version in KIMisc because it does not include the kind of the result
getArgKinds :: Kind -> [Kind]
getArgKinds (Kfun a b) = a : getArgKinds b
getArgKinds _ = []

getResKind :: Kind -> Kind
getResKind (Kfun a b) = getResKind b
getResKind k = k

instance PPrint Kind where
    pPrint _ _ KStar = text "*"
    pPrint _ _ KNum = text "#"
    pPrint _ _ KStr = text "$"
    pPrint d p (Kfun l r) = pparen (p>9) $ pPrint d 10 l <+> text "->" <+> pPrint d 9 r
    pPrint _ _ (KVar i) = text (showKVar i)

instance NFData Kind where
    rnf KStar = ()
    rnf KNum = ()
    rnf KStr = ()
    rnf (Kfun k1 k2) = rnf2 k1 k2
    rnf (KVar n) = rnf n

----

instance PPrint PartialKind where
    pPrint _ _ PKNoInfo = text "?"
    pPrint _ _ PKStar = text "*"
    pPrint _ _ PKNum = text "#"
    pPrint _ _ PKStr = text "$"
    pPrint d p (PKfun l r) =
        pparen (p>9) $ pPrint d 10 l <+> text "->" <+> pPrint d 9 r

instance NFData PartialKind where
    rnf PKNoInfo = ()
    rnf PKStar = ()
    rnf PKNum = ()
    rnf PKStr = ()
    rnf (PKfun k1 k2) = rnf2 k1 k2

----

instance PPrint TISort where
    pPrint d p (TItype n t) = pparen (p>0) $ text "TItype" <+> pPrint d 0 n <+> pPrint d 1 t
    pPrint d p (TIdata is enum) = pparen (p>0) $ text (if enum then "TIdata (enum)" else "TIdata") <+> pPrint d 1 is
    pPrint d p (TIstruct ss is) = pparen (p>0) $ text "TIstruct" <+> pPrint d 1 ss <+> pPrint d 1 is
    pPrint d p (TIabstract) = text "TIabstract"

instance NFData TISort where
    rnf (TItype i t) = rnf2 i t
    rnf (TIdata is enum) = rnf2 is enum
    rnf (TIstruct ss is) = rnf2 ss is
    rnf (TIabstract) = ()

instance PPrint StructSubType where
    pPrint _ _ ss = text (show ss)

instance NFData StructSubType where
    rnf (SDataCon i nm) = rnf2 i nm
    rnf x = x `seq` ()

-- Force evaluation of a Ctype
seqCType :: CType -> CType
seqCType t@(TVar v) = seq v t
seqCType t@(TCon c) = t
seqCType t@(TAp t1 t2) = seq (seqCType t1) (seq (seqCType t2) t)
seqCType t@(TGen _ _) = t
seqCType t@(TDefMonad _) = t

----
setTypePosition :: Position -> Type -> Type
setTypePosition pos (TVar (TyVar id n k)) = (TVar (TyVar (setIdPosition pos id) n k))
setTypePosition pos (TCon (TyCon id k s)) = (TCon (TyCon (setIdPosition pos id) k s))
setTypePosition pos (TCon (TyNum n _)) = (TCon (TyNum n pos))
setTypePosition pos (TCon (TyStr s _)) = (TCon (TyStr s pos))
setTypePosition pos (TAp f a) = (TAp (setTypePosition pos f) (setTypePosition pos a))
setTypePosition pos (TGen _ n)    = (TGen pos n)
setTypePosition pos (TDefMonad _) = (TDefMonad pos)
