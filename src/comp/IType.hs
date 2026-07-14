{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternSynonyms #-}

module IType(
  IType(ITVar, ITCon, ITNum, ITStr, ITAp, ITForAll)
  ,IKind(..)
  ,itArrow
  ,mkNumConT
  ,iToCT
  ,iToCK
   )
    where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import qualified Data.Map.Strict as M
import Data.IORef(IORef, newIORef, readIORef, atomicModifyIORef')
import Data.Maybe(isJust, fromJust)
import System.Environment(lookupEnv)
import System.IO.Unsafe(unsafePerformIO)

import ErrorUtil(internalError)
import Id(Id, IdProp(..), getIdBase, getIdQual, getIdPosition, getIdProps)
import PreIds(idArrow, idId, idTNumToStr)
import TypeOps(opNumT, opStrT)
import CType(Type(..), CType, TyCon(..), TyVar(..), Kind(..),
             TISort(..), StructSubType(..),
             cTApplys, cTVar, cTCon, cTNum, cTStr)
import Pragma(IfcPragma(..))
import StdPrel(tiArrow)
import Eval(NFData(..), rnf3, rnf2, rnf)
import PPrint
import PFPrint
import Position(noPosition)
import Util(itos)
import FStringCompat(FString, mkNumFString)

-- ==============================
-- IKind, IType

-- Arrow kinds nest to the right (matching Kind's Kfun and IConv.iConvK),
-- so backticked IKFun chains must associate to the right.  Without this
-- declaration the default infixl 9 silently built left-nested (wrong)
-- kinds; tconcheck caught exactly that in itPrimPair.
infixr 8 `IKFun`

data IKind
        = IKStar
        | IKNum
        | IKStr
        | IKFun IKind IKind
        deriving (Eq, Ord, Show)

-- ITypes are hash-consed: the two interior constructors carry a unique
-- assigned by a global intern table, so structurally equal interior
-- nodes are one shared heap object.  The real constructors ITForAll_
-- and ITAp_ are private to this module; construction goes through the
-- smart constructors behind the bidirectional pattern synonyms below,
-- so every other module reads and writes the six historical
-- constructor names unchanged.
--
-- The uniques are arrival-order identifiers.  They must never influence
-- anything observable (ordering, printing, serialization); they may
-- only be used for pointer-style equality (same unique => same node).
data IType
        = ITForAll_ {-# UNPACK #-} !Int !Id !IKind IType
        | ITAp_ {-# UNPACK #-} !Int IType IType
        | ITVar !Id
        | ITCon !Id !IKind !TISort
        | ITNum !Integer
        | ITStr !FString

pattern ITForAll :: Id -> IKind -> IType -> IType
pattern ITForAll i k t <- ITForAll_ _ i k t
  where ITForAll i k t = mkITForAll i k t

pattern ITAp :: IType -> IType -> IType
pattern ITAp f a <- ITAp_ _ f a
  where ITAp f a = mkITAp f a

{-# COMPLETE ITForAll, ITAp, ITVar, ITCon, ITNum, ITStr #-}

-- --------------------------------
-- The intern table

-- Intern keys compare at full serialization granularity: everything
-- that BinData writes for a leaf participates in the comparison --
-- Id base and qual (FString unique indices), Id position and props,
-- and the complete ITCon payload (kind and sort, including the Ids
-- embedded in TIdata/TIstruct/TIatf sorts and the CTypes inside
-- TItype, all with their own positions, qualifiers and props).
--
-- Anything coarser measurably drifts .bo bytes, because interning
-- substitutes the first-CONSTRUCTED representative for all key-equal
-- requests while the base compiler's .bo writer picks the first
-- occurrence in WRITE order.  Two incidents from developing this
-- change: keying Ids without positions/props conflated position-
-- variant types and shrank every library .bo; keying ITCon by Id
-- alone (per the one-tycon-per-qualified-name invariant, which does
-- hold at Id granularity) leaked import-qualification variants of the
-- Ids inside the sort payload, changing .bo contents.  A deliberate
-- relaxation to coarser keys (more sharing) is possible later, but it
-- must come with its own golden accounting.
--
-- The single knowing exception: Position comparison ignores
-- pos_is_stdlib (matching Position's Eq/Ord and the .bo writer's own
-- sharing keys); a source location determines its stdlib-ness, so
-- key-equal values cannot differ in serialized bytes.

thenCmp :: Ordering -> Ordering -> Ordering
thenCmp EQ o = o
thenCmp o  _ = o

exactCmpList :: (a -> a -> Ordering) -> [a] -> [a] -> Ordering
exactCmpList _ []     []     = EQ
exactCmpList _ []     (_:_)  = LT
exactCmpList _ (_:_)  []     = GT
exactCmpList c (x:xs) (y:ys) = c x y `thenCmp` exactCmpList c xs ys

exactCmpId :: Id -> Id -> Ordering
exactCmpId i1 i2 =
    compare (getIdBase i1) (getIdBase i2) `thenCmp`
    compare (getIdQual i1) (getIdQual i2) `thenCmp`
    compare (getIdPosition i1) (getIdPosition i2) `thenCmp`
    exactCmpList exactCmpIdProp (getIdProps i1) (getIdProps i2)

-- IdP_TypeJoin embeds Ids, which the derived IdProp Ord compares
-- without their positions and props; everything else in IdProp is
-- exact under the derived Ord.
exactCmpIdProp :: IdProp -> IdProp -> Ordering
exactCmpIdProp (IdP_TypeJoin a1 b1) (IdP_TypeJoin a2 b2) =
    exactCmpId a1 a2 `thenCmp` exactCmpId b1 b2
exactCmpIdProp p1 p2 = compare p1 p2

exactCmpMaybe :: (a -> a -> Ordering) -> Maybe a -> Maybe a -> Ordering
exactCmpMaybe _ Nothing   Nothing   = EQ
exactCmpMaybe _ Nothing   (Just _)  = LT
exactCmpMaybe _ (Just _)  Nothing   = GT
exactCmpMaybe c (Just x)  (Just y)  = c x y

exactCmpSort :: TISort -> TISort -> Ordering
exactCmpSort (TItype n1 t1) (TItype n2 t2) =
    compare n1 n2 `thenCmp` exactCmpCT t1 t2
exactCmpSort (TItype _ _)      _                  = LT
exactCmpSort _                 (TItype _ _)       = GT
exactCmpSort (TIdata cs1 e1)   (TIdata cs2 e2)    =
    exactCmpList exactCmpId cs1 cs2 `thenCmp` compare e1 e2
exactCmpSort (TIdata _ _)      _                  = LT
exactCmpSort _                 (TIdata _ _)       = GT
exactCmpSort (TIstruct s1 f1)  (TIstruct s2 f2)   =
    exactCmpSST s1 s2 `thenCmp` exactCmpList exactCmpId f1 f2
exactCmpSort (TIstruct _ _)    _                  = LT
exactCmpSort _                 (TIstruct _ _)     = GT
exactCmpSort TIabstract        TIabstract         = EQ
exactCmpSort TIabstract        _                  = LT
exactCmpSort _                 TIabstract         = GT
exactCmpSort (TIatf c1 p1 t1)  (TIatf c2 p2 t2)   =
    exactCmpId c1 c2 `thenCmp` compare p1 p2 `thenCmp` compare t1 t2

exactCmpSST :: StructSubType -> StructSubType -> Ordering
exactCmpSST SStruct            SStruct            = EQ
exactCmpSST SStruct            _                  = LT
exactCmpSST _                  SStruct            = GT
exactCmpSST SClass             SClass             = EQ
exactCmpSST SClass             _                  = LT
exactCmpSST _                  SClass             = GT
exactCmpSST (SDataCon i1 b1)   (SDataCon i2 b2)   =
    exactCmpId i1 i2 `thenCmp` compare b1 b2
exactCmpSST (SDataCon _ _)     _                  = LT
exactCmpSST _                  (SDataCon _ _)     = GT
exactCmpSST (SInterface ps1)   (SInterface ps2)   =
    exactCmpList exactCmpIfcP ps1 ps2
exactCmpSST (SInterface _)     _                  = LT
exactCmpSST _                  (SInterface _)     = GT
exactCmpSST (SPolyWrap a1 b1 c1) (SPolyWrap a2 b2 c2) =
    exactCmpId a1 a2 `thenCmp` exactCmpMaybe exactCmpId b1 b2 `thenCmp`
    exactCmpId c1 c2

exactCmpIfcP :: IfcPragma -> IfcPragma -> Ordering
exactCmpIfcP (PIArgNames is1) (PIArgNames is2) = exactCmpList exactCmpId is1 is2
exactCmpIfcP p1 p2 = compare p1 p2  -- no Ids in the other constructors

exactCmpCT :: Type -> Type -> Ordering
exactCmpCT (TVar (TyVar i1 n1 k1)) (TVar (TyVar i2 n2 k2)) =
    exactCmpId i1 i2 `thenCmp` compare n1 n2 `thenCmp` compare k1 k2
exactCmpCT (TVar _)        _                 = LT
exactCmpCT _               (TVar _)          = GT
exactCmpCT (TCon c1)       (TCon c2)         = exactCmpTyCon c1 c2
exactCmpCT (TCon _)        _                 = LT
exactCmpCT _               (TCon _)          = GT
exactCmpCT (TAp f1 a1)     (TAp f2 a2)       =
    exactCmpCT f1 f2 `thenCmp` exactCmpCT a1 a2
exactCmpCT (TAp _ _)       _                 = LT
exactCmpCT _               (TAp _ _)         = GT
exactCmpCT (TGen p1 n1)    (TGen p2 n2)      =
    compare p1 p2 `thenCmp` compare n1 n2
exactCmpCT (TGen _ _)      _                 = LT
exactCmpCT _               (TGen _ _)        = GT
exactCmpCT (TDefMonad p1)  (TDefMonad p2)    = compare p1 p2

exactCmpTyCon :: TyCon -> TyCon -> Ordering
exactCmpTyCon (TyCon i1 mk1 s1) (TyCon i2 mk2 s2) =
    exactCmpId i1 i2 `thenCmp` compare mk1 mk2 `thenCmp` exactCmpSort s1 s2
exactCmpTyCon (TyCon _ _ _)  _                = LT
exactCmpTyCon _              (TyCon _ _ _)    = GT
exactCmpTyCon (TyNum n1 p1)  (TyNum n2 p2)    =
    compare n1 n2 `thenCmp` compare p1 p2
exactCmpTyCon (TyNum _ _)    _                = LT
exactCmpTyCon _              (TyNum _ _)      = GT
exactCmpTyCon (TyStr s1 p1)  (TyStr s2 p2)    =
    compare s1 s2 `thenCmp` compare p1 p2

-- Exact comparison of leaf ITypes (interior nodes never appear here:
-- inside keys they are identified by their unique).
exactCmpLeaf :: IType -> IType -> Ordering
exactCmpLeaf (ITVar i1)       (ITVar i2)       = exactCmpId i1 i2
exactCmpLeaf (ITVar _)        _                = LT
exactCmpLeaf _                (ITVar _)        = GT
exactCmpLeaf (ITCon i1 k1 s1) (ITCon i2 k2 s2) =
    exactCmpId i1 i2 `thenCmp` compare k1 k2 `thenCmp` exactCmpSort s1 s2
exactCmpLeaf (ITCon _ _ _)    _                = LT
exactCmpLeaf _                (ITCon _ _ _)    = GT
exactCmpLeaf (ITNum n1)       (ITNum n2)       = compare n1 n2
exactCmpLeaf (ITNum _)        _                = LT
exactCmpLeaf _                (ITNum _)        = GT
exactCmpLeaf (ITStr s1)       (ITStr s2)       = compare s1 s2
exactCmpLeaf t1 t2 =
    internalError ("IType.exactCmpLeaf: interior node: " ++ show (t1, t2))

-- The identity of a child inside an intern key: interned interior
-- nodes are identified by their unique; leaves by their exact content
-- (compared with exactCmpLeaf).
data TKey
        = TKNode {-# UNPACK #-} !Int
        | TKLeaf !IType

instance Eq TKey where
    k1 == k2  =  cmpTKey k1 k2 == EQ

instance Ord TKey where
    compare = cmpTKey

cmpTKey :: TKey -> TKey -> Ordering
cmpTKey (TKNode u1) (TKNode u2) = compare u1 u2
cmpTKey (TKNode _)  (TKLeaf _)  = LT
cmpTKey (TKLeaf _)  (TKNode _)  = GT
cmpTKey (TKLeaf l1) (TKLeaf l2) = exactCmpLeaf l1 l2

-- Exact structural key of an interior node.  NKForAll includes the
-- binder kind even though cmpT skips it: interning must never change
-- what a pattern match observes.
data NodeKey
        = NKAp !TKey !TKey
        | NKForAll !Id !IKind !TKey

instance Eq NodeKey where
    k1 == k2  =  cmpNodeKey k1 k2 == EQ

instance Ord NodeKey where
    compare = cmpNodeKey

cmpNodeKey :: NodeKey -> NodeKey -> Ordering
cmpNodeKey (NKAp f1 a1) (NKAp f2 a2) =
    cmpTKey f1 f2 `thenCmp` cmpTKey a1 a2
cmpNodeKey (NKAp _ _) (NKForAll _ _ _) = LT
cmpNodeKey (NKForAll _ _ _) (NKAp _ _) = GT
cmpNodeKey (NKForAll i1 k1 t1) (NKForAll i2 k2 t2) =
    exactCmpId i1 i2 `thenCmp` compare k1 k2 `thenCmp` cmpTKey t1 t2

tKey :: IType -> TKey
tKey (ITForAll_ u _ _ _) = TKNode u
tKey (ITAp_ u _ _)       = TKNode u
tKey t                   = TKLeaf t

data InternTable = InternTable !(M.Map NodeKey IType) {-# UNPACK #-} !Int

{-# NOINLINE internTable #-}
internTable :: IORef InternTable
internTable = unsafePerformIO $ newIORef (InternTable M.empty 0)

-- When BSC_INTERN_SANITY is set in the environment, every intern hit
-- verifies full structural equality of the requested children against
-- the canonical node's children.  This catches key collisions and any
-- leaf whose payload drifts from its key (e.g. two ITCons with the
-- same Id but different kind/sort, which the tconcheck-verified
-- invariant forbids).
{-# NOINLINE internSanityOn #-}
internSanityOn :: Bool
internSanityOn = unsafePerformIO $ do
    mv <- lookupEnv "BSC_INTERN_SANITY"
    return (isJust mv)

-- Structural equality at the granularity interning promises (the
-- exactCmp* granularity: full leaf payloads, everything but heap
-- identity).  Only used by the sanity check.
structEqT :: IType -> IType -> Bool
structEqT (ITForAll_ u1 i1 k1 t1) (ITForAll_ u2 i2 k2 t2) =
    exactCmpId i1 i2 == EQ && k1 == k2 && (u1 == u2 || structEqT t1 t2)
structEqT (ITAp_ u1 f1 a1) (ITAp_ u2 f2 a2) =
    u1 == u2 || (structEqT f1 f2 && structEqT a1 a2)
structEqT t1@(ITForAll_ _ _ _ _) t2 = False
structEqT t1 t2@(ITForAll_ _ _ _ _) = False
structEqT t1@(ITAp_ _ _ _) t2 = False
structEqT t1 t2@(ITAp_ _ _ _) = False
structEqT t1 t2 = exactCmpLeaf t1 t2 == EQ

{-# NOINLINE internAp #-}
internAp :: IType -> IType -> IType
internAp f a = unsafePerformIO $ do
    let key = NKAp (tKey f) (tKey a)
    InternTable m0 _ <- readIORef internTable
    case M.lookup key m0 of
      Just t  -> return (checkHit t)
      Nothing -> atomicModifyIORef' internTable (go key)
  where
    go key st@(InternTable m n) =
        case M.lookup key m of
          Just t  -> (st, checkHit t)
          Nothing -> let t = ITAp_ n f a
                     in  (InternTable (M.insert key t m) (n+1), t)
    checkHit t@(ITAp_ _ f' a')
        | not internSanityOn || (structEqT f f' && structEqT a a') = t
    checkHit t =
        internalError ("IType.internAp: intern table mismatch\n" ++
                       "requested: " ++ show (ITAp_ (-1) f a) ++ "\n" ++
                       "canonical: " ++ show t)

{-# NOINLINE mkITForAll #-}
mkITForAll :: Id -> IKind -> IType -> IType
mkITForAll i k t = unsafePerformIO $ do
    let key = NKForAll i k (tKey t)
    InternTable m0 _ <- readIORef internTable
    case M.lookup key m0 of
      Just t' -> return (checkHit t')
      Nothing -> atomicModifyIORef' internTable (go key)
  where
    go key st@(InternTable m n) =
        case M.lookup key m of
          Just t' -> (st, checkHit t')
          Nothing -> let t' = ITForAll_ n i k t
                     in  (InternTable (M.insert key t' m) (n+1), t')
    checkHit t'@(ITForAll_ _ i' k' b')
        | not internSanityOn ||
          (exactCmpId i i' == EQ && k == k' && structEqT t b') = t'
    checkHit t' =
        internalError ("IType.mkITForAll: intern table mismatch\n" ++
                       "requested: " ++ show (ITForAll_ (-1) i k t) ++ "\n" ++
                       "canonical: " ++ show t')

-- The smart constructor behind the ITAp pattern synonym.  It first
-- performs the single-step type-function reduction that
-- ISyntax.normITAp used to do (same rules, same semantics), then
-- interns.  Since every ITAp is now built here, reducible
-- applications like TAdd#(2,3) can no longer be constructed at all.
--
-- These cases just handle special built-in type functions like TAdd
-- and Id__; it would be nice to get rid of this if we can make those
-- work via preds, as with user-defined type functions, but that seems
-- hard because we still need to permit them in instance heads.
--
-- NB: everything inside this module must match and build with the
-- real constructors (ITAp_): the ITAp synonym's builder is this very
-- function.
mkITAp :: IType -> IType -> IType
mkITAp (ITAp_ _ (ITCon op _ _) (ITNum x)) (ITNum y) | isJust (res) =
    mkNumConT (fromJust res)
  where res = opNumT op [x, y]
mkITAp (ITCon op _ _) (ITNum x) | isJust (res) =
    mkNumConT (fromJust res)
  where res = opNumT op [x]
mkITAp (ITAp_ _ (ITCon op _ _) (ITStr x)) (ITStr y) | isJust (res) =
    ITStr (fromJust res)
  where res = opStrT op [x, y]
mkITAp (ITCon op _ _) (ITNum x) | op == idTNumToStr =
    ITStr (mkNumFString x)

mkITAp (ITCon op _ _) a | op == idId = a

mkITAp f a = internAp f a

mkNumConT :: Integer -> IType
mkNumConT i =
    if i < 0 then
        internalError ("mkNumCon: " ++ show i)
    else
        ITNum i

-- --------------------------------
-- Show instance
--
-- Hand-written to print the historical constructor names without the
-- intern uniques, matching what the derived instance printed before
-- hash-consing (so debug dumps are unchanged).
instance Show IType where
    showsPrec d (ITForAll_ _ i k t) = showParen (d > 10) $
        showString "ITForAll " . showsPrec 11 i . showString " " .
        showsPrec 11 k . showString " " . showsPrec 11 t
    showsPrec d (ITAp_ _ f a) = showParen (d > 10) $
        showString "ITAp " . showsPrec 11 f . showString " " .
        showsPrec 11 a
    showsPrec d (ITVar i) = showParen (d > 10) $
        showString "ITVar " . showsPrec 11 i
    showsPrec d (ITCon i k s) = showParen (d > 10) $
        showString "ITCon " . showsPrec 11 i . showString " " .
        showsPrec 11 k . showString " " . showsPrec 11 s
    showsPrec d (ITNum n) = showParen (d > 10) $
        showString "ITNum " . showsPrec 11 n
    showsPrec d (ITStr s) = showParen (d > 10) $
        showString "ITStr " . showsPrec 11 s

-- --------------------------------
-- NFData Instances
instance NFData IType where
    rnf (ITForAll i k t) = rnf3 i k t
    rnf (ITAp a b) = rnf2 a b
    rnf (ITVar i) = rnf i
    rnf (ITCon i k s) = rnf3 i k s
    rnf (ITNum i) = rnf i
    rnf (ITStr s) = rnf s

instance NFData IKind where
    rnf IKStar = ()
    rnf IKNum = ()
    rnf IKStr = ()
    rnf (IKFun a b) = rnf2 a b

-- --------------------------------
-- Eq Instances
instance Eq IType where
    x == y  =  cmpT x y == EQ
    x /= y  =  cmpT x y /= EQ

instance Ord IType where
    compare x y = cmpT x y

-- ITCon is compared by Id alone.  This is justified by the
-- one-tycon-per-qualified-name invariant: BSC's front end enforces one
-- type constructor per qualified name, so a qualified Id determines its
-- (kind, sort) payload -- and all ITCon Ids are qualified, because IType
-- is born post-resolution at IConv.  The handwritten payload copies this
-- relies on are verified against the compiled Prelude by the tconcheck
-- build step (src/comp/tconcheck.hs).
--
-- The ITForAll case skips the binder kinds; that is a separate,
-- alpha-structural assumption (same binder Id in the same position implies
-- the same kind), unchanged and unrelated to the tycon invariant.
--
-- Interned interior nodes short-circuit on equal uniques (same unique
-- means the same node, hence EQ).  Uniques are never used for LT/GT.
cmpT :: IType -> IType -> Ordering
cmpT (ITForAll_ u1 i1 _ t1) (ITForAll_ u2 i2 _ t2)  -- binder kind comparison skipped (see above)
        | u1 == u2  = EQ
        | otherwise =
            case compare i1 i2 of
            EQ -> cmpT t1 t2
            o  -> o
cmpT (ITForAll _  _  _ ) _                   = LT

cmpT (ITAp _ _)          (ITForAll _  _  _)  = GT
cmpT (ITAp_ u1 f1 a1)    (ITAp_ u2 f2 a2)
        | u1 == u2  = EQ
        | otherwise =
            case cmpT f1 f2 of
            EQ -> cmpT a1 a2
            o  -> o
cmpT (ITAp _  _)         _                   = LT

cmpT (ITVar _)           (ITForAll _  _  _)  = GT
cmpT (ITVar _)           (ITAp _  _)         = GT
cmpT (ITVar i1)          (ITVar i2)          = compare i1 i2
cmpT (ITVar _)           _                   = LT

cmpT (ITCon _  _ _)      (ITForAll _  _  _)  = GT
cmpT (ITCon _  _ _)      (ITAp _ _)          = GT
cmpT (ITCon _  _ _)      (ITVar _)           = GT
cmpT (ITCon i1 _ _)      (ITCon i2 _ _)      = compare i1 i2
cmpT (ITCon _  _ _)      _                   = LT

cmpT (ITNum _)           (ITForAll _  _  _)  = GT
cmpT (ITNum _)           (ITAp _ _)          = GT
cmpT (ITNum _)           (ITVar _)           = GT
cmpT (ITNum _)           (ITCon _ _ _)       = GT
cmpT (ITNum n1)          (ITNum n2)          = compare n1 n2
cmpT (ITNum _)           _                   = LT

cmpT (ITStr s1)          (ITStr s2)          = compare s1 s2
cmpT (ITStr _)           _                   = GT

-- -----------------------------------------
-- Pretty Print instances PPrint and PVPrint

instance PPrint IKind where
    pPrint _ _ IKStar = text "*"
    pPrint _ _ IKNum = text "#"
    pPrint _ _ IKStr = text "$"
    pPrint d p (IKFun l r) = pparen (p>9) $ pPrint d 9 l <+> text "->" <+> pPrint d 10 r

instance PPrint IType where
    pPrint d p (ITForAll i k t) = ppQuant "\\/" d p i k t
    pPrint d p (ITAp (ITAp arr a) r) | arr == itArrow =
        pparen (p > 8) (sep [pPrint d 9 a <+> text "->", pPrint d 8 r])
    pPrint d p (ITAp e e') = pparen (p>9) $
        sep [pPrint d 9 e, pPrint d 10 e']
    pPrint d p (ITVar i) = pPrint d 0 i
    pPrint d p (ITCon c _ _) = pPrint d 0 c
    pPrint d p (ITNum n) = text (itos n)
    pPrint d p (ITStr s) = text (show s)

instance PVPrint IType where
    -- convert to CType and use the PVPrint instance for that
    pvPrint d p ity =
        let convITyToCTy (ITForAll _ _ t) = convITyToCTy t
            convITyToCTy (ITAp t1 t2)  = cTApplys (convITyToCTy t1)
                                                  [convITyToCTy t2]
            convITyToCTy (ITVar i)     = cTVar i
            convITyToCTy (ITCon i _ _) = cTCon i
            convITyToCTy (ITNum n)     = cTNum n noPosition
            convITyToCTy (ITStr s)     = cTStr s noPosition
        in  pvPrint d p (convITyToCTy ity)

-- ---------------------------------------------------
-- Other utility functions

-- Function type (a -> b)
itArrow :: IType
itArrow = ITCon (idArrow noPosition) (IKFun IKStar (IKFun IKStar IKStar)) tiArrow

-- Pretty print ITForAll
ppQuant :: String -> PDetail -> Int -> Id -> IKind -> IType -> Doc
ppQuant s d p i t e =
    pparen (p>0) (sep [text s <> pparen True (pPrint d 0 i <>text" ::" <+> pPrint d 0 t) <+> text ".", pPrint d 0 e])

-- ---------------------------------------------------
-- Convert ISyntax kinds/types to CType

iToCT :: IType -> CType
iToCT (ITForAll _ _ _) = internalError "IConv.iToCT: ITForAll"
iToCT (ITAp t1 t2) = TAp (iToCT t1) (iToCT t2)
iToCT (ITVar i) = internalError "IConv.iToCT: ITVar"
iToCT (ITCon i k s) = TCon (TyCon i (Just (iToCK k)) s)
iToCT (ITNum n) = TCon (TyNum n noPosition)
iToCT (ITStr s) = TCon (TyStr s noPosition)

iToCK :: IKind -> Kind
iToCK (IKStar) = KStar
iToCK (IKNum) = KNum
iToCK (IKStr) = KStr
iToCK (IKFun k1 k2) = Kfun (iToCK k1) (iToCK k2)
