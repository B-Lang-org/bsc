{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, PatternGuards, DeriveDataTypeable #-}
{-# LANGUAGE PatternSynonyms #-}
-- | The CType package defines the concrete representation of types and kinds.
module CType(
  -- * Types
  -- TAp and TCon are bidirectional pattern synonyms over the hidden
  -- real constructors (the IType idiom); see the consing note below.
  Type(TVar, TCon, TAp, TGen, TDefMonad),
  CType, TyVar(..), TyCon(..), TISort(..), StructSubType(..),
  isCanonType, typeCanonId, consCTypeEnabled, cTypeConsStats,

  -- ** Examining Types
  getTyVarId, getTypeKind,
  isTNum, getTNum,
  isTStr, getTStr,
  isTVar, isTCon, isIfc, isInterface, isDictType, isDictFun, isUpdateable,
  leftCon, leftTyCon, allTyCons, allTConNames, tyConArgs,
  splitTAp, normTAp,
  isATFAp,
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
  baseKVar, mkKFun,

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
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import Data.IORef(IORef, newIORef, readIORef, modifyIORef', atomicModifyIORef')
import Control.Exception(SomeException, SomeAsyncException(..),
                         fromException, throwIO, try, evaluate)
import System.Exit(ExitCode)
import Control.Monad(when)
import Data.Bits(finiteBitSize)
import System.IO.Unsafe(unsafePerformIO, unsafeDupablePerformIO)
import IOUtil(progArgs)

import Eval
import PPrint
import Position
import Id
import IdPrint
import PreIds(idArrow, idPrimPair, idPrimUnit, idBit, idString,
              idPrimAction, idAction, idActionValue_, idActionValue,
              idTNumToStr, idId)
import Util(itos)
import ErrorUtil
import Pragma(IfcPragma)
import TypeOps
import PVPrint(PVPrint(..))
import FStringCompat

-- Data structures

-- | Representation of types
--
-- TCon_ and TAp_ carry a canonical-node id slot (the IType idiom).
-- An id of -1 means the node is raw and claims nothing.  A
-- non-negative id means this object is the intern table's
-- representative for its structure, and that every child is
-- transitively canonical and therefore ground.  Only the intern
-- machinery below assigns ids; every other construction site must use
-- -1.  The slot makes the groundness test a field read.  Equal ids
-- mean equal values under Eq Type: an interior node with a given id
-- is a single object, and a leaf with a given id is a single value
-- that carries the caller's position (see ccAtCaller).
data Type = TVar TyVar          -- ^ type variable
          | TCon_ {-# UNPACK #-} !Int TyCon
                                -- ^ type constructor (build via 'TCon')
          | TAp_ {-# UNPACK #-} !Int Type Type
                                -- ^ type-level application (build via 'TAp')
          | TGen Position Int   -- ^ quantified type variable used in type schemes
          | TDefMonad Position  -- ^ not used after CVParserImperative
    deriving (Generic.Typeable)

-- Every TCon and TAp, inside this module and out, goes through the
-- smart constructors, which hash-cons ground nodes at construction.
pattern TCon :: TyCon -> Type
pattern TCon c <- TCon_ _ c
  where TCon c = mkTCon c

pattern TAp :: Type -> Type -> Type
pattern TAp f a <- TAp_ _ f a
  where TAp f a = mkTAp f a

{-# COMPLETE TVar, TCon, TAp, TGen, TDefMonad #-}

-- | The canonical-node id of a type: -1 unless this object is the
-- unique canonical (hence ground) intern-table node for its structure.
typeCanonId :: Type -> Int
typeCanonId (TAp_ i _ _) = i
typeCanonId (TCon_ i _)  = i
typeCanonId _            = -1

-- | Canonical implies ground: no TVar/TGen/TDefMonad anywhere inside,
-- so substitution is the identity and tv is empty.
isCanonType :: Type -> Bool
isCanonType t = typeCanonId t >= 0

-- Show is written out rather than derived, so that it prints the
-- public constructors and not the id slots or the underscored names.
instance Show Type where
    showsPrec d (TVar v) = showParen (d > 10) $
        showString "TVar " . showsPrec 11 v
    showsPrec d (TCon c) = showParen (d > 10) $
        showString "TCon " . showsPrec 11 c
    showsPrec d (TAp f a) = showParen (d > 10) $
        showString "TAp " . showsPrec 11 f . showString " " . showsPrec 11 a
    showsPrec d (TGen p i) = showParen (d > 10) $
        showString "TGen " . showsPrec 11 p . showString " " . showsPrec 11 i
    showsPrec d (TDefMonad p) = showParen (d > 10) $
        showString "TDefMonad " . showsPrec 11 p

-- No Data instance for Type: nothing in the compiler needs one, and a
-- generic rebuild could fabricate an id slot.  The syb traversals are
-- confined to the Verilog AST, and no Data-deriving container embeds
-- a Type.  TISort and TyCon drop their Data derivings too, since they
-- embed Type.

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
    deriving (Show, Generic.Typeable)

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
          -- Associated type function: resolved by looking up the corresponding
          -- typeclass instance.  Stores the class that defines this type function,
          -- and the indices of the ATF params and the target param within the class's
          -- parameter list.
        | TIatf { atf_class_id   :: Id     -- the class this type function belongs to
                , atf_param_idxs :: [Int]  -- index of each ATF param in the class param list
                , atf_target_idx :: Int    -- index of the result param in the class param list
                }
        deriving (Eq, Ord, Show, Generic.Typeable)


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

-- =====
-- Construction-time consing of ground type nodes, behind the TAp and
-- TCon pattern synonyms.
--
-- A node is consed only when both of its children already carry
-- canonical ids, so groundness is inductive and costs one field read:
-- a raw child leaves the parent raw, with no table traffic at all.
-- TVar, TGen and TDefMonad never carry ids, and canonical leaves are
-- where the induction starts.  On a platform whose Int is narrower
-- than 64 bits the fused application key does not fit, consing is
-- disabled, and the smart constructors build raw nodes.
--
-- Unlike GroundCType, this table is purely structural: it performs no
-- synonym expansion and no type-function evaluation, because
-- construction must preserve the structure that the caller wrote.
-- That is why the two tables are separate.
--
-- Leaf policy: a TyCon leaf is keyed on its qualifier and base name,
-- as Eq TyCon compares them, and only when the name is qualified.
-- The key also covers the kind and a tag that identifies the sort.
-- Kind and tag are needed because consing runs from the parser
-- onward, where a TyCon of the same name can still carry an
-- unresolved payload -- no kind, or the TIabstract sort -- which must
-- not be conflated with the resolved one.  The sort payload itself is
-- excluded from the key, because covering it would force synonym
-- bodies during symbol-table construction.  Positions are excluded
-- too, because covering them would leave no sharing.  A TyNum or
-- TyStr leaf is keyed on its value alone.  Soundness rests on the
-- same one-tycon-per-qualified-name invariant as Eq TyCon.
--
-- Lifetime: the tables are process-global and never reset, so in a
-- multi-package process a shared leaf carries a position that depends
-- on compile order.  Output is semantically identical either way, but
-- .bo bytes are not reproducible per input.  A per-session reset would
-- fix that, and would also be needed before reloading a redefined
-- package in one process, where a name-keyed memo goes stale in
-- semantics and not just positions.  It would have to cover ccState,
-- ctRnfSeen, GroundCType's gctState and ptrTable, and any later memo
-- that is keyed on type names or intern ids.

-- A fused ap key holds two ids as base-2^31 digits, so consing needs
-- a 64-bit Int.  All of bsc's supported platforms have one.
{-# NOINLINE consCTypeEnabled #-}
consCTypeEnabled :: Bool
consCTypeEnabled = finiteBitSize (0 :: Int) >= 64

-- recorded only under -trace-ctype-stats, so the construction path
-- carries no IORef traffic by default
{-# NOINLINE ctypeStatsEnabled #-}
ctypeStatsEnabled :: Bool
ctypeStatsEnabled = "-trace-ctype-stats" `elem` progArgs

-- construction counters; approximate, since GHC may share a
-- construction
{-# NOINLINE cnTApBuild #-}
cnTApBuild :: IORef Int
cnTApBuild = unsafePerformIO $ newIORef 0

{-# NOINLINE cnTConBuild #-}
cnTConBuild :: IORef Int
cnTConBuild = unsafePerformIO $ newIORef 0

{-# NOINLINE cnConsApHit #-}
cnConsApHit :: IORef Int
cnConsApHit = unsafePerformIO $ newIORef 0

{-# NOINLINE cnConsApNew #-}
cnConsApNew :: IORef Int
cnConsApNew = unsafePerformIO $ newIORef 0

{-# NOINLINE cnConsConHit #-}
cnConsConHit :: IORef Int
cnConsConHit = unsafePerformIO $ newIORef 0

{-# NOINLINE cnConsConNew #-}
cnConsConNew :: IORef Int
cnConsConNew = unsafePerformIO $ newIORef 0

{-# NOINLINE cnRefuseChild #-}
cnRefuseChild :: IORef Int
cnRefuseChild = unsafePerformIO $ newIORef 0

{-# NOINLINE cnRefuseLeaf #-}
cnRefuseLeaf :: IORef Int
cnRefuseLeaf = unsafePerformIO $ newIORef 0

{-# NOINLINE cnRefuseKeyErr #-}
cnRefuseKeyErr :: IORef Int
cnRefuseKeyErr = unsafePerformIO $ newIORef 0

{-# NOINLINE cnRefuseRedex #-}
cnRefuseRedex :: IORef Int
cnRefuseRedex = unsafePerformIO $ newIORef 0

bump :: IORef Int -> IO ()
bump r = when ctypeStatsEnabled (modifyIORef' r (+1))

-- count a construction on the pure (non-consing) path; the IO result
-- depends on both arguments, so it cannot be floated or shared
{-# NOINLINE bumpRet #-}
bumpRet :: IORef Int -> a -> a
bumpRet r x
  | ctypeStatsEnabled = unsafeDupablePerformIO (modifyIORef' r (+1) >> return x)
  | otherwise = x

-- The identity of a leaf inside the table key: its normalized name or
-- value, plus its kind and sort tag (see the leaf policy above).  An
-- interior node is keyed on its two children's ids, which are fused
-- into one Int.
data CCKey
        = CCCon !FString !FString !(Maybe Kind) {-# UNPACK #-} !Int
        | CCNum !Integer
        | CCStr !FString
        deriving (Eq, Ord)

ccSortTag :: TISort -> Int
ccSortTag (TItype {})    = 0
ccSortTag (TIdata {})    = 1
ccSortTag (TIstruct {})  = 2
ccSortTag (TIabstract)   = 3
ccSortTag (TIatf {})     = 4

-- Canonicalize a leaf's sort payload before consing, as
-- IType.tidySort does for an ITCon payload: the payload's entity Ids
-- (constructors, fields, wrapper names) are re-qualified to the
-- owning tycon and lose positions and props.
--
-- The key excludes the payload, so without this normalization the
-- table would treat two spellings of one payload as distinct, and the
-- first TyCon to arrive would impose its spelling on later callers.
-- A .bo carries constructors as the source package wrote them,
-- unqualified, while MakeSymTab and IType.ownedId re-qualify them to
-- the owner.
--
-- Local names (PIArgNames dummies) and references to other packages'
-- entities keep their own qualification.  TItype and TIatf never
-- reach here, since ccConKey refuses both, so no synonym body is
-- forced.
ccTidySort :: FString -> TISort -> TISort
ccTidySort q (TIdata cs enc)  = TIdata (map (ccOwnedId q) cs) enc
ccTidySort q (TIstruct ss fs) = TIstruct (ccTidySST q ss) (map (ccOwnedId q) fs)
ccTidySort _ s                = s

ccTidySST :: FString -> StructSubType -> StructSubType
ccTidySST q (SDataCon i nf)     = SDataCon (ccOwnedId q i) nf
ccTidySST q (SPolyWrap a mc f)  = SPolyWrap (ccOwnedId q a) (fmap (ccOwnedId q) mc)
                                            (ccOwnedId q f)
ccTidySST _ ss                  = ss

-- the owner is always qualified (ccConKey refuses unqualified tycons)
ccOwnedId :: FString -> Id -> Id
ccOwnedId q i = setIdQual (setIdPosition noPosition (setIdProps i [])) q

ccTidyTyCon :: TyCon -> TyCon
ccTidyTyCon (TyCon i mk sort) = TyCon i mk (ccTidySort (getIdQual i) sort)
ccTidyTyCon tc                = tc

-- an ap-node key fuses the two child ids into one Int; ccFusable
-- refuses to cons rather than overflow the fusion
ccFuse :: Int -> Int -> Int
ccFuse fi ai = fi * 0x80000000 + ai

ccFusable :: Int -> Bool
ccFusable i = i < 0x80000000

-- the intern state: canonical ap nodes by fused child ids, canonical
-- leaves by CCKey, and the next id.  Ids are arrival-order, so
-- nothing observable may depend on them beyond identity (see
-- ccAtCaller).
data CCState = CCState !(IM.IntMap Type) !(M.Map CCKey Type)
                       {-# UNPACK #-} !Int

{-# NOINLINE ccState #-}
ccState :: IORef CCState
ccState = unsafePerformIO $ newIORef (CCState IM.empty M.empty 0)

-- normTAp's redex shapes: a primitive type-function head over literal
-- children.  These must never cons.  apSub rebuilds interior nodes
-- through normTAp, which reduces such a redex, so treating apSub as
-- the identity on a canonical node is sound only if canonical implies
-- normTAp-normal.  Refusing here keeps that inductive: a refused redex
-- is raw, so no node above it is consed either.
ccIsRedex :: Type -> Type -> Bool
ccIsRedex (TAp_ _ (TCon_ _ (TyCon op _ _)) (TCon_ _ (TyNum x _))) (TCon_ _ (TyNum y _))
    = isJust (opNumT op [x, y])
ccIsRedex (TCon_ _ (TyCon op _ _)) (TCon_ _ (TyNum x _))
    = isJust (opNumT op [x]) || op == idTNumToStr
ccIsRedex (TAp_ _ (TCon_ _ (TyCon op _ _)) (TCon_ _ (TyStr x _))) (TCon_ _ (TyStr y _))
    = isJust (opStrT op [x, y])
ccIsRedex _ _ = False

-- | The smart constructor behind the TAp pattern synonym.  The
-- children's slots decide membership: a raw child (id -1) refuses for
-- the cost of a field read.
{-# NOINLINE mkTAp #-}
mkTAp :: Type -> Type -> Type
mkTAp f a
  | not consCTypeEnabled = bumpRet cnTApBuild (TAp_ (-1) f a)
  | otherwise = unsafeDupablePerformIO $ do
      bump cnTApBuild
      let fi = typeCanonId f
          ai = typeCanonId a
      if fi < 0 || ai < 0 || not (ccFusable fi) || not (ccFusable ai)
        then do bump cnRefuseChild; return (TAp_ (-1) f a)
      else if ccIsRedex f a
        then do bump cnRefuseRedex; return (TAp_ (-1) f a)
        else do
          let key = ccFuse fi ai
          CCState apm _ _ <- readIORef ccState
          case IM.lookup key apm of
            Just canon -> do bump cnConsApHit; return canon
            Nothing -> do
              (canon, isNew) <- atomicModifyIORef' ccState (insAp key)
              bump (if isNew then cnConsApNew else cnConsApHit)
              return canon
  where
    -- f and a carry ids, so they are the canonical table nodes
    insAp key st@(CCState apm lm n) =
        case IM.lookup key apm of
          Just c  -> (st, (c, False))
          Nothing -> let c = TAp_ n f a
                     in  (CCState (IM.insert key c apm) lm (n+1), (c, True))

-- Exceptions that must reach the top rather than demote the leaf to a
-- raw node.  Asynchronous ones are not ours to swallow, and
-- internalError prints its banner and then calls exitWith, which
-- throws a synchronous ExitCode: catching that would leave the banner
-- on stderr and let the compile carry on to a zero exit.
rethrowsPastCons :: SomeException -> Bool
rethrowsPastCons e =
    case fromException e of
      Just (SomeAsyncException _) -> True
      Nothing -> case (fromException e :: Maybe ExitCode) of
                   Just _  -> True
                   Nothing -> False

-- deep-force a leaf key via its own Ord (kind and sort tag included)
ccForceKey :: Maybe CCKey -> Maybe CCKey
ccForceKey Nothing = Nothing
ccForceKey (Just k) = (k `compare` k) `seq` Just k

-- | The smart constructor behind the TCon pattern synonym.
{-# NOINLINE mkTCon #-}
mkTCon :: TyCon -> Type
mkTCon tc
  | not consCTypeEnabled = bumpRet cnTConBuild (TCon_ (-1) tc)
  | otherwise = unsafeDupablePerformIO $ do
      bump cnTConBuild
      -- The whole key computation runs inside the guard, because
      -- building the key forces the TyCon, its Id, its kind and its
      -- sort tag, any of which could be an error thunk that would
      -- otherwise never be forced.  Refuse the leaf on a synchronous
      -- exception, and rethrow anything that must reach the top (see
      -- rethrowsPastCons).  internalError prints its banner before it
      -- throws, so if a stored kind or sort held one, that output
      -- leaks even though the exit is honoured.
      mkey <- try (evaluate (ccForceKey (ccConKey tc)))
      case (mkey :: Either SomeException (Maybe CCKey)) of
        Left e
          | rethrowsPastCons e -> throwIO e
          | otherwise -> do bump cnRefuseKeyErr; return (TCon_ (-1) tc)
        Right Nothing -> do bump cnRefuseLeaf; return (TCon_ (-1) tc)
        Right (Just key) -> do
          CCState _ lm _ <- readIORef ccState
          case M.lookup key lm of
            Just canon -> do bump cnConsConHit; return (ccAtCaller canon tc)
            Nothing -> do
              (canon, isNew) <- atomicModifyIORef' ccState (insLeaf key)
              bump (if isNew then cnConsConNew else cnConsConHit)
              return (ccAtCaller canon tc)
  where
    insLeaf key st@(CCState apm lm n) =
        case M.lookup key lm of
          Just c  -> (st, (c, False))
          -- the canonical node carries the normalized payload, so the
          -- two spellings of one payload become the same value and
          -- the payload-free key has nothing left to conflate
          Nothing -> let c = TCon_ n (ccTidyTyCon tc)
                     in  (CCState apm (M.insert key c lm) (n+1), (c, True))

-- Share by id, but hand back the caller's position.  A canonical leaf
-- is one value, not one occurrence: the key covers the value, kind and
-- sort tag because Eq TyCon does, and Eq ignores positions.
-- Diagnostics do not.  So if a leaf kept the position of whichever
-- occurrence arrived first, it would report a kind error or an unused
-- import against the wrong line, or against the wrong file.
--
-- The id and the normalized sort survive, so cmp's shortcut, the
-- groundness induction and the payload canonicalization above are all
-- unaffected.  Only one claim weakens: equal ids now mean equal
-- values rather than a single heap object, and equal values is all
-- that any consumer of an id relies on.
ccAtCaller :: Type -> TyCon -> Type
ccAtCaller (TCon_ n c) tc = TCon_ n (ccSetTyConPos c (getPosition tc))
ccAtCaller t _ = t

ccSetTyConPos :: TyCon -> Position -> TyCon
ccSetTyConPos (TyCon i k s) p = TyCon (setIdPosition p i) k s
ccSetTyConPos (TyNum v _)   p = TyNum v p
ccSetTyConPos (TyStr v _)   p = TyStr v p

ccConKey :: TyCon -> Maybe CCKey
ccConKey (TyNum n _) = Just (CCNum n)
ccConKey (TyStr s _) = Just (CCStr s)
ccConKey (TyCon i mk sort)
  | isUnqualId i = Nothing
  -- expTFun eliminates the identity type constructor like a redex, so
  -- refusing it keeps the rule that a canonical node has nothing left
  -- to reduce
  | i == idId = Nothing
  | otherwise = case sort of
      -- synonyms and associated type functions are refused, like
      -- normTAp redexes, so that canonical means ground normal form:
      -- expandSyn is then the identity on a canonical node and no
      -- walker finds anything to reduce inside one
      TItype {} -> Nothing
      TIatf {}  -> Nothing
      _ -> Just (CCCon (getIdQual i) (getIdBase i) mk (ccSortTag sort))

-- | Counter/table snapshot for the -trace-ctype-stats dump.
cTypeConsStats :: IO [(String, Int)]
cTypeConsStats = do
    tap <- readIORef cnTApBuild
    tcon <- readIORef cnTConBuild
    aphit <- readIORef cnConsApHit
    apnew <- readIORef cnConsApNew
    chit <- readIORef cnConsConHit
    cnew <- readIORef cnConsConNew
    rchild <- readIORef cnRefuseChild
    rleaf <- readIORef cnRefuseLeaf
    rkey <- readIORef cnRefuseKeyErr
    rredex <- readIORef cnRefuseRedex
    CCState _ _ n <- readIORef ccState
    return [ ("ctype.tap_built", tap)
           , ("ctype.tcon_built", tcon)
           , ("ctype.cons_ap_hit", aphit)
           , ("ctype.cons_ap_new", apnew)
           , ("ctype.cons_con_hit", chit)
           , ("ctype.cons_con_new", cnew)
           , ("ctype.refuse_child_not_canon", rchild)
           , ("ctype.refuse_leaf", rleaf)
           , ("ctype.refuse_key_err", rkey)
           , ("ctype.refuse_redex", rredex)
           , ("ctype.cons_table_nodes", n)
           ]

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
-- equal canonical ids = equal values under Eq Type (see ccAtCaller):
-- answer EQ without descending.  (Only an EQ shortcut -- the order
-- stays structural, so container iteration order is unchanged.)  On
-- unequal canonical trees the recursion below prunes to the differing
-- paths, so comparisons over exponentially shared ground types stay
-- polynomial.
cmp x y | i >= 0, i == typeCanonId y = EQ
  where i = typeCanonId x
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

-- TyCon comparison and the one-tycon-per-qualified-name invariant
--
-- BSC's front end enforces one type constructor per qualified name, so a
-- qualified Id determines its (kind, sort) payload.  The invariant holds
-- ONLY for qualified names: unqualified TyCons exist during scope
-- resolution, where the same base name may denote different constructors.
-- The tconcheck build step (src/comp/tconcheck.hs) verifies the compiler's
-- handwritten copies of Prelude tycon payloads against the compiled
-- Prelude, keeping the invariant checkable.
--
-- Eq is therefore scoped by qualification:
--  * both ids qualified: the invariant's regime.  Comparison is by Id;
--    the payloads are determined by the name (checker-verified), so a
--    payload comparison would be a dead tail.
--  * either id unqualified: resolution-era fuzz, where the invariant is
--    undefined; the kind comparison is kept as a hedge.
--
-- Two pre-existing quirks, both deliberate and unchanged:
--  * Eq is non-transitive: qualEq compares by base name alone when either
--    side is unqualified, so P.T == T and T == Q.T but P.T /= Q.T.
--  * Eq and Ord disagree: Ord compares the full qualifier on both sides
--    (a lawful total order), while Eq admits the qualEq fuzz.  Containers
--    key on Ord.
instance Eq TyCon where
    TyCon i k _ == TyCon i' k' _  =  qualEq i i' && (bothQualified i i' || k == k')
    TyNum i _   == TyNum i' _     =  i == i'
    TyStr s _   == TyStr s' _     =  s == s'
    _           == _              =  False

-- both ids carry a package qualifier (see the invariant note above)
bothQualified :: Id -> Id -> Bool
bothQualified i i' = not (isUnqualId i) && not (isUnqualId i')

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
    -- lexicographic on (base, qual); within a (base, qual) bucket either
    -- both ids are qualified -- unique by the invariant documented at Eq,
    -- so EQ without consulting the kinds -- or both are unqualified, where
    -- the kind comparison is kept, as in Eq.  This remains a lawful total
    -- order.
    TyCon i k _ `compare` TyCon i' k' _   =
        case (getIdBase i, getIdQual i) `compare` (getIdBase i', getIdQual i') of
          EQ -> if bothQualified i i' then EQ else compare k k'
          o  -> o
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

-- Canonical nodes deep-force once per cons id (cf. itRnfOnce in
-- IType.hs).  Everything still gets forced exactly once per node, but
-- the walk is linear rather than per-path on a shared DAG.  Raw nodes
-- have no id, so they take the plain walk.
{-# NOINLINE ctRnfSeen #-}
ctRnfSeen :: IORef IS.IntSet
ctRnfSeen = unsafePerformIO $ newIORef IS.empty

ctRnfOnce :: Int -> () -> ()
ctRnfOnce i force = unsafeDupablePerformIO $ do
    s <- readIORef ctRnfSeen
    if IS.member i s
      then return ()
      else do -- force BEFORE marking (cf. itRnfOnce)
              _ <- return $! force
              atomicModifyIORef' ctRnfSeen (\ ss -> (IS.insert i ss, ()))
              return ()

instance NFData Type where
    rnf (TCon_ i c) | i >= 0 = ctRnfOnce i (rnf c)
    rnf (TAp_ i t1 t2) | i >= 0 = ctRnfOnce i (rnf2 t1 t2)
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

isDictType :: CType -> Bool
isDictType t | Just (TyCon _ _ (TIstruct SClass _)) <- leftTyCon t = True
isDictType _ = False

isDictFun :: CType -> Bool
isDictFun t = all isDictType (res:args)
  where (args, res) = getArrows t

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
isTypePolyBit (TAp (TCon (TyCon i _ _)) (TAp (TCon (TyCon i' _ _)) arg))
  | (i == idActionValue) || (i == idActionValue_), (i' == idBit) = isTVar arg
isTypePolyBit (TAp (TCon (TyCon i _ _)) arg)
  | (i == idBit) || (i == idActionValue) || (i == idActionValue_) = isTVar arg
isTypePolyBit _ = False

-- Note that this is only used for foreign functions, so it does not currently handle tuples of Bits
bitWidth :: Type -> Integer
bitWidth (TAp (TCon (TyCon i _ _)) (TAp (TCon (TyCon i' _ _)) arg))
  | ((i == idActionValue) || (i == idActionValue_)) &&
    (i' == idBit) &&
    (isTNum arg) = getTNum arg
bitWidth (TAp (TCon (TyCon i _ _)) arg)
  | (i == idBit) && (isTNum arg) = getTNum arg
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

-- Copied from the IType reduction rules (now IType.mkITAp)
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

isATFAp :: Type -> Bool
isATFAp t0 =
    let (f, as) = splitTAp t0
    in case f of
        TCon (TyCon _ _ (TIatf { atf_param_idxs = pIdxs })) -> length as == length pIdxs
        _ -> False

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

mkKFun :: [Kind] -> Kind -> Kind
mkKFun []     k = k
mkKFun (a:as) k = Kfun a (mkKFun as k)

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
    pPrint d p (TIatf { atf_param_idxs = pIdxs, atf_class_id = cls }) =
        pparen (p>0) $ text "TIatf" <+> pPrint d 0 (length pIdxs) <+> pPrint d 0 cls

instance NFData TISort where
    rnf (TItype i t) = rnf2 i t
    rnf (TIdata is enum) = rnf2 is enum
    rnf (TIstruct ss is) = rnf2 ss is
    rnf (TIabstract) = ()
    rnf (TIatf { atf_class_id = c, atf_param_idxs = ps, atf_target_idx = t }) =
        rnf3 c ps t

instance PPrint StructSubType where
    pPrint _ _ ss = text (show ss)

instance NFData StructSubType where
    rnf SStruct = ()
    rnf SClass = ()
    rnf (SDataCon i nm) = rnf2 i nm
    rnf (SInterface ps) = rnf ps
    rnf (SPolyWrap i con field) = rnf3 i con field

-- Force evaluation of a Ctype
seqCType :: CType -> CType
-- a canonical node and its children were forced when interned
seqCType t | isCanonType t = t
seqCType t@(TVar v) = seq v t
seqCType t@(TCon c) = t
seqCType t@(TAp t1 t2) = seq (seqCType t1) (seq (seqCType t2) t)
seqCType t@(TGen _ _) = t
seqCType t@(TDefMonad _) = t

----
-- Stamps raw nodes and returns canonical ones unchanged, at every
-- level.  A canonical node's positions are shared representatives, so
-- stamping one would either mutate a node other callers hold or copy
-- it raw and lose the sharing.  The nodes it does build are raw,
-- since it writes positions that consing would otherwise replace.
setTypePosition :: Position -> Type -> Type
setTypePosition _ t | isCanonType t = t
setTypePosition pos (TVar (TyVar id n k)) = (TVar (TyVar (setIdPosition pos id) n k))
setTypePosition pos (TCon (TyCon id k s)) = (TCon_ (-1) (TyCon (setIdPosition pos id) k s))
setTypePosition pos (TCon (TyNum n _)) = (TCon_ (-1) (TyNum n pos))
setTypePosition pos (TCon (TyStr s _)) = (TCon_ (-1) (TyStr s pos))
setTypePosition pos (TAp f a) =
    (TAp_ (-1) (setTypePosition pos f) (setTypePosition pos a))
setTypePosition pos (TGen _ n)    = (TGen pos n)
setTypePosition pos (TDefMonad _) = (TDefMonad pos)
