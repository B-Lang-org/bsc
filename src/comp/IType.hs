{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternSynonyms #-}

module IType(
  IType(ITVar, ITCon, ITNum, ITStr, ITAp, ITForAll)
  ,IKind(..)
  ,itArrow
  ,mkNumConT
  ,iTypeNodeId
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
import System.IO.Unsafe(unsafePerformIO)

import ErrorUtil(internalError)
import IOUtil(progArgs)
import Id(Id, getIdBase, getIdQual, setIdPosition, setIdProps, setIdQual)
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
import PreStrings(fsEmpty)

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
        | ITVar_ !Id
        | ITCon_ !Id !IKind !TISort
        | ITNum !Integer
        | ITStr !FString

pattern ITForAll :: Id -> IKind -> IType -> IType
pattern ITForAll i k t <- ITForAll_ _ i k t
  where ITForAll i k t = mkITForAll i k t

pattern ITAp :: IType -> IType -> IType
pattern ITAp f a <- ITAp_ _ f a
  where ITAp f a = mkITAp f a

-- The Id-carrying leaves are sealed the same way: construction goes
-- through normalizing smart constructors (Ids embedded in types carry
-- no positions and no props -- see the normalization section below),
-- so "stripped on entry" is enforced by the module boundary, not by
-- convention.
pattern ITVar :: Id -> IType
pattern ITVar i <- ITVar_ i
  where ITVar i = mkITVar i

pattern ITCon :: Id -> IKind -> TISort -> IType
pattern ITCon i k s <- ITCon_ i k s
  where ITCon i k s = mkITCon i k s

{-# COMPLETE ITForAll, ITAp, ITVar, ITCon, ITNum, ITStr #-}

-- --------------------------------
-- The intern unique of an interior node (ITAp / ITForAll).  Uniques
-- are process-local, arrival-order identifiers: two types carry the
-- same unique exactly when they are the same interned node.  They are
-- valid only as in-process identity -- notably as writer-local
-- sharing-map keys in BinData -- and must never be serialized or
-- otherwise influence anything observable.
iTypeNodeId :: IType -> Int
iTypeNodeId (ITForAll_ u _ _ _) = u
iTypeNodeId (ITAp_ u _ _) = u
iTypeNodeId t =
    internalError ("IType.iTypeNodeId: not an interior node: " ++ show t)

-- --------------------------------
-- Id normalization for type embedding
--
-- Ids embedded in ITypes are identity, not provenance: positions and
-- props are stripped on entry through the smart constructors behind
-- the pattern synonyms, so key-equal is byte-equal by construction,
-- representative choice cannot drift .bo output, and no consumer can
-- smuggle per-type data through the Id side-channel.  Per-type data
-- belongs in IType/TISort.  The consumer audit behind this (which
-- reads survive, which regold) is in ITYPE-INTERNING-DESIGN.md.

tidyTypeId :: Id -> Id
tidyTypeId i = setIdPosition noPosition (setIdProps i [])

-- Deep normalization of an ITCon payload: every embedded Id loses
-- positions and props, every Position inside a TItype synonym body
-- becomes noPosition, and the payload's ENTITY Ids (constructors,
-- fields, wrapper names -- entities of the tycon's own package) are
-- canonicalized to the owning tycon's qualification.  The first
-- checked library build caught exactly this variance: handwritten
-- constants carry unqualified field Ids ([fst,snd]) where compiled
-- source carries qualified ones ([Prelude::fst,Prelude::snd]) -- the
-- same entity either way.  Local names (PIArgNames dummies) and
-- references to OTHER packages' entities (the TIatf class, tycons
-- inside a synonym body) keep their own qualification.
-- Paid once per distinct tycon (tconTable).
tidySort :: FString -> TISort -> TISort
tidySort _ (TItype n t) = TItype n (tidyCT t)
tidySort q (TIdata cs enc) = TIdata (map (ownedId q) cs) enc
tidySort q (TIstruct ss fs) = TIstruct (tidySST q ss) (map (ownedId q) fs)
tidySort _ TIabstract = TIabstract
tidySort _ (TIatf c ps r) = TIatf (tidyTypeId c) ps r

-- an entity of the owning tycon's package: tidied and re-qualified.
-- The owner is always qualified (mkITCon rejects unqualified tycons),
-- so an empty qualifier here is a broken caller.
ownedId :: FString -> Id -> Id
ownedId q i | q == fsEmpty =
                internalError ("IType.ownedId: unqualified owner for " ++
                               show i)
            | otherwise    = setIdQual (tidyTypeId i) q

tidySST :: FString -> StructSubType -> StructSubType
tidySST _ SStruct = SStruct
tidySST _ SClass = SClass
tidySST q (SDataCon i nf) = SDataCon (ownedId q i) nf
tidySST _ (SInterface ps) = SInterface (map tidyIfcP ps)
tidySST q (SPolyWrap a mc f) =
    SPolyWrap (ownedId q a) (fmap (ownedId q) mc) (ownedId q f)

-- Only PIArgNames embeds Ids; the other constructors carry strings.
tidyIfcP :: IfcPragma -> IfcPragma
tidyIfcP (PIArgNames is) = PIArgNames (map tidyTypeId is)
tidyIfcP p = p

tidyCT :: CType -> CType
tidyCT (TVar (TyVar i n k)) = TVar (TyVar (tidyTypeId i) n k)
tidyCT (TCon (TyCon i mk s)) =
    -- a reference to another tycon: its payload entities belong to
    -- ITS package, so canonicalize against its own qualification
    TCon (TyCon (tidyTypeId i) mk (tidySort (getIdQual i) s))
tidyCT (TCon (TyNum n _)) = TCon (TyNum n noPosition)
tidyCT (TCon (TyStr s _)) = TCon (TyStr s noPosition)
tidyCT (TAp f a) = TAp (tidyCT f) (tidyCT a)
tidyCT (TGen _ n) = TGen noPosition n
tidyCT (TDefMonad _) = TDefMonad noPosition

-- The smart constructor behind the ITVar pattern synonym: type
-- variables are local names -- normalized, never qualified, never
-- interned (no payload to amortize).
mkITVar :: Id -> IType
mkITVar i = ITVar_ (tidyTypeId i)

-- ITCon leaves are interned by qualified name.  Soundness rests on
-- the one-tycon-per-qualified-name invariant (front-end enforced,
-- tconcheck-verified): the qualified Id determines the kind and sort,
-- so a by-name hit may return the canonical node without normalizing
-- the requested payload -- that walk is paid once, at first intern.
-- -trace-itype-intern verifies every hit against the invariant.
data TConTable = TConTable !(M.Map (FString, FString) IType)

{-# NOINLINE tconTable #-}
tconTable :: IORef TConTable
tconTable = unsafePerformIO $ newIORef (TConTable M.empty)

{-# NOINLINE mkITCon #-}
mkITCon :: Id -> IKind -> TISort -> IType
mkITCon i k s
    | getIdQual i == fsEmpty =
        -- Invariant: every ITCon arrives with a qualified Id.  The
        -- front end canonicalizes tycon references against the symbol
        -- table (MakeSymTab.trCType' substitutes ti_qual_id, which is
        -- qualified even for the current package's own decls), so any
        -- unqualified arrival is a synthesis site bypassing that layer
        -- and must be fixed at its origin.  The one such site found --
        -- ISyntaxCheck.atfEqsFromDict building associated-type-function
        -- tycons (e.g. Prelude's Rep) from raw symtab alias keys --
        -- now uses ti_qual_id.  Locating others: temporarily add
        -- HasCallStack to mkITCon and the ITCon pattern signature and
        -- render callStack here.
        internalError ("IType.mkITCon: unqualified tycon " ++
                       show (ITCon_ i k s))
    | otherwise = unsafePerformIO $ do
        let key = (getIdQual i, getIdBase i)
        TConTable m0 <- readIORef tconTable
        case M.lookup key m0 of
          Just t  -> return (checkHit t)
          Nothing -> atomicModifyIORef' tconTable (go (getIdQual i, getIdBase i))
  where
    go key st@(TConTable m) =
        case M.lookup key m of
          Just t  -> (st, checkHit t)
          Nothing -> let t = ITCon_ (tidyTypeId i) k (tidySort (getIdQual i) s)
                     in  (TConTable (M.insert key t m), t)
    -- The hit check verifies the full payload: the kind, and the sort
    -- with built-in (==).  That equality is exactly serialization
    -- granularity here: Id's Eq is base+qual, and both sides are
    -- normalized (positions and props stripped, entity Ids
    -- canonicalized), so the compared fields are precisely the bytes
    -- BinData would write.
    checkHit t@(ITCon_ _ k' s')
        | not internSanityOn ||
          (k == k' && tidySort (getIdQual i) s == s') = t
    checkHit t =
        internalError ("IType.mkITCon: one-tycon invariant violated\n" ++
                       "requested: " ++
                       show (ITCon_ (tidyTypeId i) k (tidySort (getIdQual i) s)) ++ "\n" ++
                       "canonical: " ++ show t)

-- --------------------------------
-- The intern table

-- Intern keys are names and values.  Normalization makes key-equal
-- byte-equal: every Id embedded in an IType is stripped to base and
-- qualifier on entry (no positions, no props -- see the normalization
-- section above), so a leaf's name IS its serialized content.  An
-- ITCon is keyed by its qualified name alone: under the one-tycon-
-- per-qualified-name invariant (front-end enforced, tconcheck-
-- verified) the name determines the kind and sort payload.  An ITVar
-- is keyed by its base name (type variables are local names, never
-- qualified -- see mkITVar); ITNum and ITStr by their values.
--
-- Payload exactness is established once, at first intern: the first
-- construction of a node stores its normalized payload, and every
-- later key-equal request receives that representative.  The guards
-- are tconcheck (handwritten Prelude tycon payloads match the
-- compiled Prelude) and -trace-itype-intern (every intern hit
-- re-verifies the requested structure against the canonical node).

-- The identity of a child inside an intern key: interned interior
-- nodes are identified by their unique; leaves by their normalized
-- name or value.
data TKey
        = TKNode {-# UNPACK #-} !Int
        | TKCon !FString !FString   -- qualifier, base
        | TKVar !FString            -- base
        | TKNum !Integer
        | TKStr !FString
        deriving (Eq, Ord)

-- Structural key of an interior node.  NKForAll includes the binder
-- kind even though cmpT skips it: interning must never change what a
-- pattern match observes.  The binder Id is normalized before key
-- construction (mkITForAll), so Id's built-in base+qual Eq/Ord
-- compares its full content.
data NodeKey
        = NKAp !TKey !TKey
        | NKForAll !Id !IKind !TKey
        deriving (Eq, Ord)

tKey :: IType -> TKey
tKey (ITForAll_ u _ _ _) = TKNode u
tKey (ITAp_ u _ _)       = TKNode u
tKey (ITCon_ i _ _)      = TKCon (getIdQual i) (getIdBase i)
tKey (ITVar_ i)          = TKVar (getIdBase i)
tKey (ITNum n)           = TKNum n
tKey (ITStr s)           = TKStr s

data InternTable = InternTable !(M.Map NodeKey IType) {-# UNPACK #-} !Int

{-# NOINLINE internTable #-}
internTable :: IORef InternTable
internTable = unsafePerformIO $ newIORef (InternTable M.empty 0)

-- When -trace-itype-intern is given (a hidden trace flag, so it
-- reaches every invocation via BSC_OPTIONS), every intern hit
-- verifies full structural equality of the requested children against
-- the canonical node's children.  This catches key collisions and any
-- leaf whose payload drifts from its key (e.g. two ITCons with the
-- same Id but different kind/sort, which the tconcheck-verified
-- invariant forbids).  Intended for the library build and a dedicated
-- checked testsuite leg while the intern key is under change; costs a
-- structural walk per hit, so it is never on by default.
{-# NOINLINE internSanityOn #-}
internSanityOn :: Bool
internSanityOn = "-trace-itype-intern" `elem` progArgs

-- Structural equality at the granularity interning promises: full
-- leaf payloads, everything but heap identity.  Fields compare with
-- built-in (==); on normalized values that is full granularity --
-- Id's Eq is base+qual, and type-embedded Ids carry nothing else
-- (positions and props are stripped by the smart constructors).
-- Only used by the sanity check.
structEqT :: IType -> IType -> Bool
structEqT (ITForAll_ u1 i1 k1 t1) (ITForAll_ u2 i2 k2 t2) =
    i1 == i2 && k1 == k2 && (u1 == u2 || structEqT t1 t2)
structEqT (ITAp_ u1 f1 a1) (ITAp_ u2 f2 a2) =
    u1 == u2 || (structEqT f1 f2 && structEqT a1 a2)
structEqT (ITVar_ i1)       (ITVar_ i2)       = i1 == i2
structEqT (ITCon_ i1 k1 s1) (ITCon_ i2 k2 s2) =
    i1 == i2 && k1 == k2 && s1 == s2
structEqT (ITNum n1)        (ITNum n2)        = n1 == n2
structEqT (ITStr s1)        (ITStr s2)        = s1 == s2
structEqT _ _ = False

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
    let key = NKForAll ti k (tKey t)
    InternTable m0 _ <- readIORef internTable
    case M.lookup key m0 of
      Just t' -> return (checkHit t')
      Nothing -> atomicModifyIORef' internTable (go key)
  where
    -- binder Ids are type-embedded Ids like any other: normalized
    ti = tidyTypeId i
    go key st@(InternTable m n) =
        case M.lookup key m of
          Just t' -> (st, checkHit t')
          Nothing -> let t' = ITForAll_ n ti k t
                     in  (InternTable (M.insert key t' m) (n+1), t')
    checkHit t'@(ITForAll_ _ i' k' b')
        | not internSanityOn ||
          (ti == i' && k == k' && structEqT t b') = t'
    checkHit t' =
        internalError ("IType.mkITForAll: intern table mismatch\n" ++
                       "requested: " ++ show (ITForAll_ (-1) ti k t) ++ "\n" ++
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
