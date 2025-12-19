{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables, BangPatterns #-}
{-# LANGUAGE PatternSynonyms, OverloadedLists, TypeFamilies #-}
{-# OPTIONS_GHC -Werror -fwarn-incomplete-patterns #-}
module BinData ( Byte
               , putBs, putB, putI
               , getN, getB, getI -- , getBytesRead
               , Bin(..)
               , section
               , encode, decode, decodeWithHash
               ) where

{- Routines for converting structures to/from byte strings.

   These routines are carefully crafted to avoid three problem scenarios:
   stack overflows due to thunks within a monad, requiring the
   entire binary stream to be built in memory before it can begin to be
   consumed, and losing structure sharing in the generated binary stream.

   Because of these requirements, this module is designed for
   full laziness and includes a facility for tracking shared structures.
   This allows the conversion to run in bounded space because the byte
   stream is generated lazily and the portion of it
   which has been consumed can be reclaimed by the garbage collector
   before the remainder of the stream has been generated.

   When reconstructing a data structure from its byte stream, we do
   not yet meet the goal of bounded space.  Care must be taken to make
   all of the reader routines sufficiently strict to avoid building
   large trees of thunks that are never evaluated.
-}

import ErrorUtil(internalError)

import FStringCompat
import PreIds(idDefaultClock)
import Id
import Position
import VModInfo
import SchedInfo(SchedInfo(..), MethodConflictInfo(..),
                 extractFromMethodConflictInfo)
import Pragma
import ASyntax
import ISyntax
import Wires
import CType
import IntLit
import Undefined
import Prim hiding(PrimArg(..))

import Util(Hash, hashInit, nextHash, showHash)

import Data.List(sort, intercalate)
import Control.Monad(replicateM, liftM, ap)
import Data.Array.IArray()
import Data.Array.Unboxed
import Data.Bits
import Data.Word
import GHC.IsList(IsList(..))
import qualified Data.ByteString.Lazy as B
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.Encoding as TE
import qualified Data.Map as M
import qualified Data.Set as S
import Numeric(showHex)

import Debug.Trace

type Byte = Word8

{- To reduce the size of the binary stream and preserve shared
   structures, we want to avoid repeatedly emitting identical
   structures into the binary stream.  But we need to do it in
   a way that still allows full laziness.  So examining the entire
   structure to identify all shared structures before writing out
   the data is not a viable option.  Instead, we take the approach
   of converting (lazily) into this intermediate structure which
   distinguishes shared values from the other converted data.  This
   structure has the advantage of being compositional and easy to
   generate in a fully lazy monad with constant stack usage.

   When the final result is extracted from the monad, the shared
   elements are replaced with the binary representation of
   either a tagged value if it is the first time the value
   has been encountered or a tagged index which identifies the
   number of the value if it has been seen before.

   This process can be done piecewise and lazily, which is what we
   want.
 -}

-- -------------------------------------------------------------
-- Intermediate structure with distinguished shared structures

{- HOW TO ADD A NEW TYPE TO THE SET OF STRUCTURES THAT GET SHARED

   1. Add a constructor for it to the BinElem definition
      (Don't forget to add it to the Show instance)
   2. Add a cache for it to the BinCache record along with
      a set function to update the field of the record
      (Don't forget to update unknownCache)
   3. Add a table for it to the BinTable record along with
      a set function to update the field of the record
      (Don't forget to update unknownTable)
   4. Add a Shared instance to provide access to the cache and table
      added in steps 2 & 3
   5. In the Bin instance, define toBin and fromBin functions
      These will typically be simply:
        toBin a = Out [Constructor a] ()
        fromBin = readShared
   6. Add a case to the share function to handle the constructor
      added in Step 1
-}

data BinElem = B [Byte]
             -- shared types
             | S FString
             | I Id
             | P Position
             | T Type
             -- | ASL AStateLocPathComponent
             | IT IType
             -- | AExp AExpr
             -- accounting markers
             | Start String
             | End

instance Show BinElem where
  show (B bs)    = "[" ++
                   (intercalate "," [showHex b "" | b <- bs]) ++
                   "]"
  show (S s)     = getFString s
  show (I i)     = show i
  show (P p)     = show p
  show (T t)     = show t
  show (IT t)    = show t
  -- show (ASL l)   = show l
  -- show (AExp e)  = show e
  show (Start s) = "<BEGIN " ++ s ++ ">"
  show End       = "<END>"

-- Simple difference list implementation for O(1) append.
newtype DList a = DL ([a] -> [a])

instance IsList (DList a) where
  type Item (DList a) = a

  {-# INLINE toList #-}
  toList (DL f) = f []

  {-# INLINE fromList #-}
  fromList = DL . (++)

instance Semigroup (DList a) where
  {-# INLINE (<>) #-}
  (DL a) <> (DL b) = DL (a . b)

type BinData = DList BinElem

-- -------------------------------------------------------------
-- Structures used to track shared values during writing and reading

data Known k v = Known Int (M.Map k v)
  deriving Show

unknown :: Known k v
unknown = Known 0 M.empty

-- Cache of known keys and the index assigned to them
type Cache k = Known k Int

data BinCache = BinCache { string_cache   :: Cache FString
                         , id_cache       :: Cache IdKey
                         , position_cache :: Cache Position
                         , type_cache     :: Cache TypeKey
                         , itype_cache    :: Cache ITypeKey
                         }

-- Set functions
set_string_cache :: BinCache -> Cache FString -> BinCache
set_string_cache   bc c = bc { string_cache = c }

set_id_cache :: BinCache -> Cache IdKey -> BinCache
set_id_cache       bc c = bc { id_cache = c }

set_position_cache :: BinCache -> Cache Position -> BinCache
set_position_cache bc c = bc { position_cache = c }

set_type_cache :: BinCache -> Cache TypeKey -> BinCache
set_type_cache     bc c = bc { type_cache = c }

set_itype_cache :: BinCache -> Cache ITypeKey -> BinCache
set_itype_cache    bc c = bc { itype_cache = c }

unknownCache :: BinCache
unknownCache = BinCache unknown unknown unknown unknown unknown

-- Table of known indexes and the values they map to
type Table v = Known Int v

data BinTable = BinTable { string_table   :: Table FString
                         , id_table       :: Table Id
                         , position_table :: Table Position
                         , type_table     :: Table Type
                         -- , loc_table      :: Table AStateLocPathComponent
                         , itype_table    :: Table IType
                         -- , aexpr_table    :: Table AExpr
                         }

-- Set functions
set_string_table :: BinTable -> Table FString -> BinTable
set_string_table   bt t = bt { string_table = t }

set_id_table :: BinTable -> Table Id -> BinTable
set_id_table       bt t = bt { id_table = t }

set_position_table :: BinTable -> Table Position -> BinTable
set_position_table bt t = bt { position_table = t }

set_type_table :: BinTable -> Table Type -> BinTable
set_type_table     bt t = bt { type_table = t }

set_itype_table :: BinTable -> Table IType -> BinTable
set_itype_table    bt t = bt { itype_table = t }

unknownTable :: BinTable
unknownTable = BinTable unknown unknown unknown unknown unknown

-- We don't use Id as a key since the Eq instance for Id only
-- compares the strings, but we want to distinguish Ids with
-- different properties, positions, etc.
data IdKey = IK FString FString Position [IdProp]
  deriving (Eq, Ord, Show)

id_key :: Id -> IdKey
id_key i = IK (getIdBase i) (getIdQual i) (getIdPosition i) (getIdProps i)

-- We don't use the Type as a key since the Eq instance for some
-- elements of Type (like TyVar) ignore Kinds in the equaliy test.
data TypeKey = TKV IdKey Int Kind
             | TKC IdKey (Maybe Kind) TISort
             | TKN Integer Position
             | TKS FString Position
             | TKA TypeKey TypeKey
             | TKG Position Int
  deriving (Eq, Ord, Show)

type_key :: Type -> TypeKey
type_key (TVar (TyVar i n k))  = TKV (id_key i) n k
type_key (TCon (TyCon i mk s)) = TKC (id_key i) mk s
type_key (TCon (TyNum n p))    = TKN n p
type_key (TCon (TyStr s p))    = TKS s p
type_key (TAp t1 t2)           = TKA (type_key t1) (type_key t2)
type_key (TGen p n)            = TKG p n
type_key (TDefMonad _) = internalError $ "BinData.type_key: TDefMonad"

-- We don't use the IType as a key since the Eq instance for some
-- variants (like ITForAll) ignore Kinds in the equality test.
data ITypeKey = ITKF IdKey IKind ITypeKey
              | ITKA ITypeKey ITypeKey
              | ITKV IdKey
              | ITKC IdKey IKind TISort
              | ITKN Integer
              | ITKS FString
  deriving (Eq, Ord, Show)

itype_key :: IType -> ITypeKey
itype_key (ITForAll i k t) = ITKF (id_key i) k (itype_key t)
itype_key (ITAp t1 t2)     = ITKA (itype_key t1) (itype_key t2)
itype_key (ITVar i)        = ITKV (id_key i)
itype_key (ITCon i k s)    = ITKC (id_key i) k s
itype_key (ITNum n)        = ITKN n
itype_key (ITStr s)        = ITKS s

-- -------------------------------------------------------------
-- The Out monad makes it easy to generate composite BinData

data Out a = Out BinData a

out_data :: Out a -> [BinElem]
out_data (Out bd _) = toList bd

instance Monad Out where
  return = pure
  (Out bs x) >>= f = let (Out bs' x') = f x in Out (bs <> bs') x'

instance Functor Out where
  fmap = liftM

instance Applicative Out where
  pure x = Out [] x
  (<*>) = ap

-- Insert some bytes into the byte stream
putBs :: [Byte] -> Out ()
putBs bs = Out [B bs] ()

-- Insert one byte into the byte stream
putB :: Byte -> Out ()
putB b = putBs [b]

-- Insert an Int value (between 0 and 255) into the byte stream
putI :: Int -> Out ()
putI n = if (n >= 0) && (n < 256)
         then putB $ toEnum n
         else internalError $ "BinData.putI value out of range: " ++ (show n)

-- Insert accounting marks into the byte stream

beginSection :: String -> Out ()
beginSection s = Out [Start s] ()

endSection :: Out ()
endSection = Out [End] ()

section :: String -> Out () -> Out ()
section s action = do { beginSection s; action; endSection }

-- -------------------------------------------------------------
-- The In monad makes it easy to parse a byte stream

-- The In monad state keeps tables for shared structures
-- in addition to unconsumed bytes and an optional hash of
-- consumed bytes.

data IS = IS BinTable [Byte] !(Maybe Hash) -- Integer

-- In monad is a state transformer type monad
newtype In a = In (IS -> (a,IS))

instance Monad In where
  return = pure
  (In v) >>= f = In $ \is -> let !(x,is') = v is
                                 (In fn) = f x
                             in fn is'

instance Functor In where
  fmap = liftM

instance Applicative In where
  pure x = In $ \is -> (x,is)
  (<*>) = ap

getN :: Int -> In [Byte]
getN n = replicateM n getB

getB :: In Byte
getB = In $ \is -> consume_byte is
  where consume_byte (IS _ [] _) =
          internalError "BinData.getB: unexpected end of byte stream"
        consume_byte (IS bc (b:bs) (Just h)) =
            -- trace ((show n) ++ ": " ++ (showHex (ord b) "")) $
            let h' = nextHash h [b]
            in seq h' $ (b,(IS bc bs (Just h')))
        consume_byte (IS bc (b:bs) Nothing) =
          -- trace ((show n) ++ ": " ++ (showHex (ord b) "")) $
          (b,(IS bc bs Nothing))

-- get an Int value (between 0 and 255)
getI :: In Int
getI = do { b <- getB; return (fromEnum b) }

{-
getBytesRead :: In Integer
getBytesRead = In $ \is@(IS _ _ _ n) -> (n,is)
-}
-- ------------------------------------------------------------------
-- The Shared typeclass simplifies the process of creating shared
-- structures in the output byte stream.

class Shared k v | v -> k where
  -- query if a key is already known (value is used only for its type)
  knownAs   :: k -> v -> BinCache -> Maybe Int
  -- add a (key,value) association
  addKey    :: k -> v -> BinCache -> BinCache
  -- reserve an index for a new value (value is used only for its type)
  newVal    :: In (Int,v)
  -- record a value for its index once it is fully constructed
  recordVal :: Int -> v -> In ()
  -- get the value associated with a given index
  lookupIdx :: Int -> In v

-- Templates for instances. These take get/set functions for the
-- particular cache and table fields in a BinCache/BinTable and
-- generate a function appropriate for defining an instance of
-- Shared for the correct key and value type.

-- get the right cache, lookup the key and return the result
mkKnownAs :: (Ord k) =>
             (BinCache -> (Cache k)) ->
             (k -> v -> BinCache -> Maybe Int)
mkKnownAs get k _ bc = let (Known _ m) = get bc
                       in M.lookup k m

-- get the right cache, add an mapping from key to the next index, and
-- put back the updated cache
mkAddKey :: (Ord k) =>
            (BinCache -> (Cache k)) ->
            (BinCache -> (Cache k) -> BinCache) ->
            (k -> v -> BinCache -> BinCache)
mkAddKey get set k v bc = let (Known n m) = get bc
                          in set bc (Known (n+1) (M.insert k n m))

-- get the right table, increment its index count and
-- put back the updated table while returning the fresh index
mkNewVal :: (BinTable -> (Table v)) ->
            (BinTable -> (Table v) -> BinTable) ->
            In (Int,v)
mkNewVal get set =
  In $ \(IS bt bs h) ->
          let (Known n m) = get bt
              bt' = set bt (Known (n+1) m)
          in ((n, undefined), (IS bt' bs h))

-- get the right table, add a mapping from the index to the value,
-- and put back the updated table while returning ()
mkRecordVal ::(BinTable -> (Table v)) ->
              (BinTable -> (Table v) -> BinTable) ->
              (Int -> v -> In ())
mkRecordVal get set idx v =
  In $ \(IS bt bs h) ->
          let (Known n m) = get bt
              bt' = v `seq` set bt (Known n (M.insert idx v m))
          in ((), (IS bt' bs h))


-- get the right table and look up the value for the given index
mkLookupIdx ::(BinTable -> (Table v)) ->
              (Int -> In v)
mkLookupIdx get idx =
  In $ \is@(IS bt _ _) ->
          let (Known _ m) = get bt
          in case (M.lookup idx m) of
               (Just v) -> (v, is)
               Nothing  -> internalError $ "BinData.lookupIdx: invalid index " ++ (show idx)


-- This is a convenience function that groups the sequence of operations
-- required to read a shared value.  It also hides the type trickery so
-- that no one will notice.  What is happening is that we need a way to
-- force the typechecker to infer the correct Shared instance for newVal,
-- which we do by having newVal return (in addition to the fresh index
-- we actually want) a dummy value of the type which uniquely determines
-- the Shared instance.  Then we use asTypeOf to force the typechecker
-- to unify the dummy value's type with the type of the return value.
--
-- Also note: the index is created before reading the value so that
-- indexes are assigned in the same top-down order as they are assigned
-- during writing.  This particularly affects recursive types.
readShared :: (Bin a, Shared k a) => In a
readShared = do tag <- getI
                case tag of
                  0 -> do (idx, dummy) <- newVal
                          v <- readBytes
                          recordVal idx (v `asTypeOf` dummy)
                          return v
                  1 -> do idx <- readBytes
                          lookupIdx idx
                  n -> internalError $ "BinData.readShared: invalid tag " ++ (show tag)

-- actual Shared instance definitions

instance Shared FString FString where
  knownAs   = mkKnownAs string_cache
  addKey    = mkAddKey string_cache set_string_cache
  newVal    = mkNewVal string_table set_string_table
  recordVal = mkRecordVal string_table set_string_table
  lookupIdx = mkLookupIdx string_table

instance Shared IdKey Id where
  knownAs   = mkKnownAs id_cache
  addKey    = mkAddKey id_cache set_id_cache
  newVal    = mkNewVal id_table set_id_table
  recordVal = mkRecordVal id_table set_id_table
  lookupIdx = mkLookupIdx id_table

instance Shared Position Position where
  knownAs   = mkKnownAs position_cache
  addKey    = mkAddKey position_cache set_position_cache
  newVal    = mkNewVal position_table set_position_table
  recordVal = mkRecordVal position_table set_position_table
  lookupIdx = mkLookupIdx position_table

instance Shared TypeKey Type where
  knownAs   = mkKnownAs type_cache
  addKey    = mkAddKey type_cache set_type_cache
  newVal    = mkNewVal type_table set_type_table
  recordVal = mkRecordVal type_table set_type_table
  lookupIdx = mkLookupIdx type_table

instance Shared ITypeKey IType where
  knownAs   = mkKnownAs itype_cache
  addKey    = mkAddKey itype_cache set_itype_cache
  newVal    = mkNewVal itype_table set_itype_table
  recordVal = mkRecordVal itype_table set_itype_table
  lookupIdx = mkLookupIdx itype_table

-- ------------------------------------------------------------------
-- The Bin typeclass defines automatic conversions to/from a
-- byte stream.  We include instances for common types.

class Bin a where
  -- these support sharing for some data types
  toBin :: a -> Out ()
  fromBin :: In a

  -- these are direct binary write/read with no sharing
  -- (although sub-structures may be shared)
  writeBytes :: a -> Out ()
  readBytes :: In a

  -- default definitions for toBin & fromBin provide no sharing
  toBin   = writeBytes
  fromBin = readBytes


instance Bin Word8 where
  writeBytes c = putB c
  readBytes    = getB

instance Bin Bool where
  writeBytes False = putI 0
  writeBytes True  = putI 1
  readBytes = do i <- getI
                 case i of
                   0 -> return False
                   1 -> return True
                   n -> internalError $ "BinData.Bin(Bool).readBytes: " ++ show n

instance Bin Double where
  writeBytes i = do let (m,n) = decodeFloat i
                    toBin m; toBin n
  readBytes = do m <- fromBin; n <- fromBin; return (encodeFloat m n)

instance Bin Int where
  writeBytes i = toBin (toInteger i)
  readBytes = do i <- fromBin
                 return (fromInteger i)

instance Bin Integer where
  writeBytes i = if i < 0
                 then putBs (emit (-i) [endNeg])
                 else putBs (emit   i  [endPos])
    where emit 0 bs = bs
          emit n bs = emit (n `div` baseI) (fromInteger (n `mod` baseI) : bs)
  readBytes = loop 0
    where loop n = do b <- getB
                      if b == endNeg
                       then return (-n)
                       else if b == endPos
                             then return n
                             else loop (n * baseI + toInteger b)

endNeg, endPos :: Word8
endNeg = 255
endPos = 254
baseI :: Integer
baseI = 254

-- Write a Word32 value as 4 bytes with LSB first
instance Bin Word32 where
  writeBytes x = putBs $ [ toEnum (fromEnum ((shiftR x sh) .&. 255))
                         | sh <- [0,8..31]
                         ]
  readBytes  = do bs <- getN 4
                  return $ foldl1 (.|.) [ shiftL (toEnum (fromEnum x)) sh
                                        | (sh,x) <- zip [0,8..31] bs
                                        ]

-- For list types, we use a representation
-- where each non-nil element is given a 1 prefix and the
-- nil element is represented by 0.  This is not as
-- space-efficient as a length + bytes representation, but
-- it has better laziness properties.
instance {-# OVERLAPPABLE #-} (Bin a) => Bin [a] where
  writeBytes []     = putI 0
  writeBytes (x:xs) = do { putI 1; toBin x; toBin xs }
  readBytes = do i <- getI
                 case i of
                   0 -> return []
                   1 -> do x <- fromBin
                           rest <- fromBin
                           return (x:rest)
                   n -> internalError $ "BinData.Bin([a]).readBytes: " ++ show n

-- For array types, we use a length + values representation
instance {-# OVERLAPPABLE #-} (IArray arr a, Ix i, Num i, Integral i, Bin a) => Bin (arr i a) where
  writeBytes x = let (lo,hi) = bounds x
                 in if (lo /= 0)
                    then internalError $ "BinData.Bin(Array).writeBytes: not 0-indexed"
                    else do toBin (toInteger (hi+1))
                            mapM_ toBin (elems x)
  readBytes = do len <- fromBin
                 xs <- replicateM (fromInteger len) fromBin
                 return $ listArray (0,fromInteger (len-1)) xs

instance {-# OVERLAPPING #-} (Bin a, Bin b) => Bin (a,b) where
  writeBytes (x,y) = do { toBin x; toBin y }
  readBytes = do x <- fromBin
                 y <- fromBin
                 return (x,y)

instance (Bin a, Bin b, Bin c) => Bin (a,b,c) where
  writeBytes (x,y,z) = do { toBin x; toBin y; toBin z }
  readBytes = do x <- fromBin
                 y <- fromBin
                 z <- fromBin
                 return (x,y,z)

instance (Bin a, Bin b, Bin c, Bin d) => Bin (a,b,c,d) where
  writeBytes (w,x,y,z) = do { toBin w; toBin x; toBin y; toBin z }
  readBytes = do w <- fromBin
                 x <- fromBin
                 y <- fromBin
                 z <- fromBin
                 return (w,x,y,z)

instance {-# OVERLAPPABLE #-} (Bin a) => Bin (Maybe a) where
  writeBytes Nothing  = putI 0
  writeBytes (Just x) = do { putI 1; toBin x }
  readBytes = do i <- getI
                 case i of
                   0 -> return Nothing
                   1 -> do { x <- fromBin; return (Just x) }
                   n -> internalError $ "BinData.Bin(Maybe a).readBytes: " ++ show n
instance Bin () where
  writeBytes () = return ()
  readBytes     = return ()

instance (Bin a, Bin b) => Bin (Either a b) where
  writeBytes (Left x)  = do { putI 0; toBin x }
  writeBytes (Right y) = do { putI 1; toBin y }
  readBytes = do i <- getI
                 case i of
                   0 -> do { x <- fromBin; return (Left x) }
                   1 -> do { y <- fromBin; return (Right y) }
                   n -> internalError $ "BinData.Bin(Either a b).readBytes: " ++ show n

instance (Ord a, Bin a, Bin b) => Bin (M.Map a b) where
    writeBytes omap = toBin (M.toList omap)
    readBytes       = do { ms <- fromBin; return (M.fromList ms) }

instance (Ord a, Bin a) => Bin (S.Set a) where
    writeBytes set = toBin (S.toList set)
    readBytes      = do { ss <- fromBin; return (S.fromList ss) }

-- ---------
-- Bin Ids, Positions, etc.

instance Bin FString where
  writeBytes = writeBytes . getFString
  readBytes = mkFString <$> readBytes
  -- FStrings are shared
  toBin s = Out [S s] ()
  fromBin = readShared

instance {-# OVERLAPPABLE #-} Bin String where
    writeBytes fs = do let bs = TE.encodeUtf8 $ T.pack fs
                       toBin $ toInteger $ B.length bs
                       putBs $ B.unpack bs
    readBytes     = do len <- fromBin
                       bs <- getN len
                       return (T.unpack $ TE.decodeUtf8 $ B.pack bs)

instance Bin Position where
    writeBytes (Position fs l c is_stdlib) = section "Position" $ do
        toBin fs
        toBin l
        toBin c
        toBin is_stdlib
    readBytes = do
        fs <- fromBin
        l <- fromBin
        c <- fromBin
        is_stdlib <- fromBin
        return (mkPositionFull fs l c is_stdlib)

    -- Positions are shared
    toBin p = Out [P p] ()
    fromBin = readShared

instance Bin Id where
    writeBytes i = section "Id" $
                   do let (mfs,fs) = getIdFStrings i
                      toBin (getIdPosition i)
                      toBin mfs
                      toBin fs
                      toBin (getIdProps i)
    readBytes = do pos <- fromBin
                   mfs <- fromBin
                   fs <- fromBin
                   props <- fromBin
                   return (setIdProps (mkQId pos mfs fs) props)

    -- Ids are shared
    toBin i = Out [I i] ()
    fromBin = readShared

instance Bin IdProp where
    writeBytes IdPCanFire         = putI 0
    writeBytes IdPWillFire        = putI 1
    writeBytes IdPProbe           = putI 2
    writeBytes IdPInternal        = putI 4
    writeBytes IdPReady           = putI 5
    writeBytes IdPGeneratedIfc    = putI 7
    writeBytes IdPMeth            = putI 9
    writeBytes IdPCommutativeTCon = putI 14
    writeBytes IdP_enable         = putI 15
    writeBytes IdP_keep           = putI 17
    writeBytes IdPRule            = putI 18
    writeBytes IdPSplitRule       = putI 19
    writeBytes IdPDict            = putI 20
    writeBytes IdPRenaming        = putI 21
    writeBytes IdP_hide           = putI 22
    writeBytes IdP_hide_all       = putI 23
    writeBytes IdP_suffixed       = putI 24
    writeBytes (IdP_SuffixCount count)
                                  = do putI 25 ; toBin count
    writeBytes IdP_bad_name       = putI 26
    writeBytes IdP_from_rhs       = putI 27
    writeBytes IdP_signed         = putI 28
    writeBytes IdP_NakedInst      = putI 30
    writeBytes (IdPDisplayName name)
                                  = do putI 31 ; toBin name
    writeBytes (IdP_TypeJoin a b) = do putI 32 ; toBin a ; toBin b
    writeBytes IdP_keepEvenUnused = putI 33
    writeBytes IdPMethodPredicate = putI 34
    writeBytes (IdPInlinedPositions poss)
                                  = do putI 35 ; toBin poss
    writeBytes IdPParserGenerated = putI 36
    readBytes = do
        i <- getI
        case i of
          0  -> return IdPCanFire
          1  -> return IdPWillFire
          2  -> return IdPProbe
          4  -> return IdPInternal
          5  -> return IdPReady
          7  -> return IdPGeneratedIfc
          9  -> return IdPMeth
          14 -> return IdPCommutativeTCon
          15 -> return IdP_enable
          17 -> return IdP_keep
          18 -> return IdPRule
          19 -> return IdPSplitRule
          20 -> return IdPDict
          21 -> return IdPRenaming
          22 -> return IdP_hide
          23 -> return IdP_hide_all
          24 -> return IdP_suffixed
          25 -> do k <- fromBin; return (IdP_SuffixCount k)
          26 -> return IdP_bad_name
          27 -> return IdP_from_rhs
          28 -> return IdP_signed
          30 -> return IdP_NakedInst
          31 -> do k <- fromBin; return (IdPDisplayName k)
          32 -> do a <- fromBin; b <- fromBin; return $ IdP_TypeJoin a b
          33 -> return IdP_keepEvenUnused
          34 -> return IdPMethodPredicate
          35 -> do poss <- fromBin; return (IdPInlinedPositions poss)
          36 -> return IdPParserGenerated
          n  -> internalError $ "BinData.Bin(IdProp).readBytes: " ++ show n


-- ---------
-- Bin PProp, Pragmas, etc.

instance Bin PProp where
    writeBytes (PPverilog)              = putI 0
    writeBytes (PPalwaysReady ms)       = do putI 1; toBin ms
    writeBytes (PPalwaysEnabled ms)     = do putI 2; toBin ms
    writeBytes (PPscanInsert i)         = do putI 4; toBin i
    writeBytes (PPbitBlast)             = putI 5
    writeBytes (PPCLK s)                = do putI 6; toBin s
    writeBytes (PPRSTN s)               = do putI 7; toBin s
    writeBytes (PPoptions os)           = do putI 8; toBin os
    writeBytes (PPmethod_scheduling si) = do putI  9; toBin si
    -- 11 is obsolete (used to be PPgate_default_clock)
    writeBytes (PPgate_input_clocks cs) = do putI 12; toBin cs
    writeBytes (PPdoc txt)              = do putI 13; toBin txt
    writeBytes (PPperf_spec ranks)      = do putI 14; toBin ranks
    writeBytes (PPenabledWhenReady ms)  = do putI 15; toBin ms
    writeBytes (PPparam is)             = do putI 16; toBin is
    writeBytes (PPforeignImport i)      = do putI 17; toBin i
    writeBytes (PPinst_name i)          = do putI 18; toBin i
    writeBytes (PPclock_family is)      = do putI 19; toBin is
    writeBytes (PPclock_ancestors ils)  = do putI 20; toBin ils
    writeBytes (PPGATE s)               = do putI 21; toBin s
    writeBytes (PPclock_osc ps)         = do putI 22; toBin ps
    writeBytes (PPclock_gate ps)        = do putI 23; toBin ps
    writeBytes (PPgate_inhigh is)       = do putI 24; toBin is
    writeBytes (PPgate_unused is)       = do putI 25; toBin is
    writeBytes (PPreset_port ps)        = do putI 26; toBin ps
    writeBytes (PParg_param ps)         = do putI 27; toBin ps
    writeBytes (PParg_port ps)          = do putI 28; toBin ps
    writeBytes (PParg_clocked_by ps)    = do putI 29; toBin ps
    writeBytes (PParg_reset_by ps)      = do putI 30; toBin ps
    writeBytes (PPdeprecate txt)        = do putI 31; toBin txt
    writeBytes (PPinst_hide)            = putI 32
    writeBytes (PPinst_hide_all)        = putI 33
    readBytes = do
        i <- getI
        case i of
          0  -> return PPverilog
          1  -> do ms <- fromBin; return (PPalwaysReady ms)
          2  -> do ms <- fromBin; return (PPalwaysEnabled ms)
          4  -> do i <- fromBin; return (PPscanInsert i)
          5  -> return PPbitBlast
          6  -> do i <- fromBin; return (PPCLK i)
          7  -> do i <- fromBin; return (PPRSTN i)
          8  -> do os <- fromBin; return (PPoptions os)
          9  -> do si <- fromBin; return (PPmethod_scheduling si)
          -- for backward compatibility (used to be PPgate_default_clock)
          11 -> return (PPgate_input_clocks [idDefaultClock])
          12 -> do cs <- fromBin; return (PPgate_input_clocks cs)
          13 -> do txt <- fromBin; return (PPdoc txt)
          14 -> do ranks <- fromBin; return (PPperf_spec ranks)
          15 -> do ms <- fromBin; return (PPenabledWhenReady ms)
          16 -> do is <- fromBin; return (PPparam is)
          17 -> do i <- fromBin; return (PPforeignImport i)
          18 -> do i <- fromBin; return (PPinst_name i)
          19 -> do is <- fromBin; return (PPclock_family is)
          20 -> do ils <- fromBin; return (PPclock_ancestors ils)
          21 -> do i <- fromBin; return (PPGATE i)
          22 -> do ps <- fromBin; return (PPclock_osc ps)
          23 -> do ps <- fromBin; return (PPclock_gate ps)
          24 -> do is <- fromBin; return (PPgate_inhigh is)
          25 -> do is <- fromBin; return (PPgate_unused is)
          26 -> do ps <- fromBin; return (PPreset_port ps)
          27 -> do ps <- fromBin; return (PParg_param ps)
          28 -> do ps <- fromBin; return (PParg_port ps)
          29 -> do ps <- fromBin; return (PParg_clocked_by ps)
          30 -> do ps <- fromBin; return (PParg_reset_by ps)
          31 -> do txt <- fromBin; return (PPdeprecate txt)
          32 -> return PPinst_hide
          33 -> return PPinst_hide_all
          n  -> internalError $ "BinData.Bin(PProp).readBytes: " ++ show n

instance Bin PPnm where
    writeBytes (PPnmOne i) = do putI 0; toBin i
    writeBytes (PPnmArray i h l) = do putI 1; toBin i; toBin h; toBin l
    readBytes = do
        i <- getI
        case i of
          0 -> do i <- fromBin; return (PPnmOne i)
          1 -> do i <- fromBin; h <- fromBin; l <- fromBin; return (PPnmArray i h l)
          n -> internalError $ "BinData.Bin(PPnm).readBytes: " ++ show n

instance Bin IfcPragma where
    writeBytes (PIArgNames ids)     = do putI 0 ; toBin ids
    writeBytes (PIPrefixStr fs)     = do putI 1 ; toBin fs
    writeBytes (PIRdySignalName fs) = do putI 2 ; toBin fs
    writeBytes (PIEnSignalName fs)  = do putI 3 ; toBin fs
    writeBytes (PIResultName fs)    = do putI 4 ; toBin fs
    writeBytes (PIAlwaysRdy )       = putI 5
    writeBytes (PIAlwaysEnabled )   = putI 6
    readBytes = do
        i <- getI
        case i of
          0 -> do ids <- fromBin; return (PIArgNames ids )
          1 -> do fs <- fromBin;  return (PIPrefixStr fs)
          2 -> do fs <- fromBin;  return (PIRdySignalName fs)
          3 -> do fs <- fromBin;  return (PIEnSignalName fs)
          4 -> do fs <- fromBin;  return (PIResultName fs)
          5 -> do                 return (PIAlwaysRdy )
          6 -> do                 return (PIAlwaysEnabled)
          n -> internalError $ "BinData.Bin(IfcPragms).readBytes: " ++ show n

instance Bin RulePragma where
    writeBytes RPfireWhenEnabled                = putI 0
    writeBytes RPnoImplicitConditions           = putI 1
    writeBytes RPaggressiveImplicitConditions   = putI 2
    writeBytes RPconservativeImplicitConditions = putI 3
    writeBytes RPnoWarn                         = putI 4
    writeBytes RPwarnAllConflicts                  = putI 5
    writeBytes RPcanScheduleFirst               = putI 6
    writeBytes RPclockCrossingRule              = putI 7
    writeBytes (RPdoc txt)                      = do putI 8; toBin txt
    writeBytes RPhide                           = putI 9
    readBytes = do tag <- getI
                   case tag of
                     0 -> return RPfireWhenEnabled
                     1 -> return RPnoImplicitConditions
                     2 -> return RPaggressiveImplicitConditions
                     3 -> return RPconservativeImplicitConditions
                     4 -> return RPnoWarn
                     5 -> return RPwarnAllConflicts
                     6 -> return RPcanScheduleFirst
                     7 -> return RPclockCrossingRule
                     8 -> do txt <- fromBin; return (RPdoc txt)
                     9 -> return RPhide
                     n -> internalError $ "BinData.Bin(RulePragma).readBytes: " ++ show n

instance (Bin t, Ord t) => Bin (SchedulePragma t) where
    writeBytes (SPUrgency i)           = do putI 0; toBin i
    writeBytes (SPExecutionOrder i)    = do putI 1; toBin i
    writeBytes (SPPreempt ids1 ids2)   = do putI 2; toBin ids1; toBin ids2
    writeBytes (SPSchedule si)         = do putI 3; toBin si
    writeBytes (SPMutuallyExclusive i) = do putI 4; toBin i
    writeBytes (SPConflictFree i)      = do putI 5; toBin i
    readBytes = do tag <- getI
                   case tag of
                     0 -> do i <- fromBin; return (SPUrgency i)
                     1 -> do i <- fromBin; return (SPExecutionOrder i)
                     2 -> do ids1 <- fromBin; ids2 <- fromBin
                             return (SPPreempt ids1 ids2)
                     3 -> do si <- fromBin; return (SPSchedule si)
                     4 -> do i <- fromBin; return (SPMutuallyExclusive i)
                     5 -> do i <- fromBin; return (SPConflictFree i)
                     n -> internalError $ "BinData.Bin(SchedulePragma).readBytes: " ++ show n

-- ----------
-- Bin AClockDomain

instance Bin ClockDomain where
    writeBytes cd = toBin (writeClockDomain cd)
    readBytes     = do { i <- fromBin; return (readClockDomain i) }

instance Bin AClock where
    writeBytes (AClock osc gate) = do toBin osc; toBin gate
    readBytes = do osc <- fromBin
                   gate <- fromBin
                   return (AClock osc gate)

-- ----------
-- Bin AReset

instance Bin ResetId where
    writeBytes cd = toBin (writeResetId cd)
    readBytes = do { i <- fromBin; return (readResetId i) }

instance Bin AReset where
    writeBytes (AReset wire) = toBin wire
    readBytes = do { wire <- fromBin; return (AReset wire) }

-- ----------
-- Bin AInout

instance Bin AInout where
    writeBytes (AInout wire) = toBin wire
    readBytes = do { wire <- fromBin; return (AInout wire) }

-- ----------
-- Bin VWireInfo

instance Bin VWireInfo where
    writeBytes (WireInfo clk rst args) = do toBin clk; toBin rst; toBin args
    readBytes = do clk <- fromBin
                   rst <- fromBin
                   args <- fromBin
                   return (WireInfo clk rst args)

instance Bin VClockInfo where
    writeBytes (ClockInfo in_cs out_cs as ss) =
        do toBin in_cs; toBin out_cs; toBin as; toBin ss
    readBytes = do in_cs <- fromBin
                   out_cs <- fromBin
                   as <- fromBin
                   ss <- fromBin;
                   return (ClockInfo in_cs out_cs as ss)

instance Bin VResetInfo where
    writeBytes (ResetInfo in_rs out_rs) = do toBin in_rs; toBin out_rs
    readBytes = do in_rs <- fromBin
                   out_rs <- fromBin
                   return (ResetInfo in_rs out_rs)

instance Bin VArgInfo where
    writeBytes (Param a)    = do putI 0; toBin a
    writeBytes (Port a b c) = do putI 1; toBin a; toBin b; toBin c
    writeBytes (ClockArg a) = do putI 2; toBin a
    writeBytes (ResetArg a) = do putI 3; toBin a
    writeBytes (InoutArg a b c) = do putI 4; toBin a; toBin b; toBin c
    readBytes = do
        i <- getI
        case i of
          0 -> do a <- fromBin; return (Param a)
          1 -> do a <- fromBin; b <- fromBin; c <- fromBin; return (Port a b c)
          2 -> do a <- fromBin; return (ClockArg a)
          3 -> do a <- fromBin; return (ResetArg a)
          4 -> do a <- fromBin; b <- fromBin; c <- fromBin;
                  return (InoutArg a b c)
          n -> internalError $ "BinData.Bin(VArgInfo).readBytes: " ++ show n

instance Bin VName where
    writeBytes (VName s) = toBin s
    readBytes = do { s <- fromBin; return (VName s) }

-- ----------
-- Bin AType

instance Bin AType where
    writeBytes (ATBit sz)         = do putI 0; toBin sz
    writeBytes (ATString sz)      = do putI 1; toBin sz
    writeBytes (ATReal)           = do putI 2;
    writeBytes (ATArray sz t)     = do putI 3; toBin sz; toBin t
    writeBytes (ATAbstract i szs) = do putI 4; toBin i; toBin szs
    readBytes = do
        i <- getI
        case i of
          0 -> do sz <- fromBin; return (ATBit sz)
          1 -> do sz <- fromBin; return (ATString sz)
          2 -> do return ATReal
          3 -> do sz <- fromBin; t <- fromBin; return (ATArray sz t)
          4 -> do i <- fromBin; szs <- fromBin; return (ATAbstract i szs)
          n -> internalError $ "GenABin.Bin(AType).readBytes: " ++ show n

-- ----------
-- Bin AExpr

instance Bin AExpr where
    writeBytes (APrim i t op args) = section "AExpr" $
        do putI 0; toBin i; toBin t; toBin op; toBin args
    writeBytes (AMethCall t obj meth args) = section "AExpr" $
        do putI 1; toBin t; toBin obj; toBin meth; toBin args
    writeBytes (AMethValue t obj meth) = section "AExpr" $
        do putI 2; toBin t; toBin obj; toBin meth
    writeBytes (ANoInlineFunCall t obj fun args) = section "AExpr" $
        do putI 3; toBin t; toBin obj; toBin fun; toBin args
    writeBytes (AFunCall t obj fun isC args) = section "AExpr" $
        do putI 4; toBin t; toBin obj; toBin fun; toBin isC; toBin args
    writeBytes (ATaskValue t obj fun isC cookie) = section "AExpr" $
        do putI 5; toBin t; toBin obj; toBin fun; toBin isC; toBin cookie
    writeBytes (ASPort t i)    = section "AExpr" $ do putI  6; toBin t; toBin i
    writeBytes (ASParam t i)   = section "AExpr" $ do putI  7; toBin t; toBin i
    writeBytes (ASDef t i)     = section "AExpr" $ do putI  8; toBin t; toBin i
    writeBytes (ASInt i t val) = section "AExpr" $ do putI  9; toBin i; toBin t; toBin val
    writeBytes (ASStr i t str) = section "AExpr" $ do putI 10; toBin i; toBin t; toBin str
    writeBytes (ASAny t me)       = section "AExpr" $ do putI 11; toBin t; toBin me
    writeBytes (ASClock t clk) = section "AExpr" $ do putI 12; toBin t; toBin clk
    writeBytes (ASReset t rst) = section "AExpr" $ do putI 13; toBin t; toBin rst
    writeBytes (AMGate t obj clk) = section "AExpr" $ do putI 14; toBin t; toBin obj; toBin clk
    writeBytes (ASInout t iot) = section "AExpr" $ do putI 15; toBin t; toBin iot
    writeBytes (ASReal i t val) = section "AExpr" $ do putI 16; toBin i; toBin t; toBin val
    readBytes = do
        i <- getI
        case i of
          0  -> do { i <- fromBin; t <- fromBin; op <- fromBin;
                     args <- fromBin; return (APrim i t op args); }
          1  -> do { t <- fromBin; obj <- fromBin; meth <- fromBin;
                     args <- fromBin; return (AMethCall t obj meth args); }
          2  -> do { t <- fromBin; obj <- fromBin; meth <- fromBin;
                     return (AMethValue t obj meth); }
          3  -> do { t <- fromBin; obj <- fromBin; fun <- fromBin;
                     args <- fromBin;
                     return (ANoInlineFunCall t obj fun args); }
          4  -> do { t <- fromBin; obj <- fromBin; fun <- fromBin;
                     isC <- fromBin; args <- fromBin;
                     return (AFunCall t obj fun isC args); }
          5  -> do { t <- fromBin; obj <- fromBin; fun <- fromBin;
                     isC <- fromBin; cookie <- fromBin;
                     return (ATaskValue t obj fun isC cookie); }
          6  -> do t <- fromBin; i <- fromBin; return (ASPort t i)
          7  -> do t <- fromBin; i <- fromBin; return (ASParam t i)
          8  -> do t <- fromBin; i <- fromBin; return (ASDef t i)
          9  -> do { i <- fromBin; t <- fromBin; val <- fromBin;
                     return (ASInt i t val) }
          10 -> do { i <- fromBin; t <- fromBin; str <- fromBin;
                     return (ASStr i t str) }
          11 -> do t <- fromBin; me <- fromBin; return (ASAny t me)
          12 -> do t <- fromBin; clk <- fromBin; return (ASClock t clk)
          13 -> do t <- fromBin; rst <- fromBin; return (ASReset t rst)
          14 -> do { t <- fromBin; obj <- fromBin; clk <- fromBin;
                     return (AMGate t obj clk); }
          15 -> do t <- fromBin; iot <- fromBin; return (ASInout t iot)
          16 -> do { i <- fromBin; t <- fromBin; val <- fromBin;
                     return (ASReal i t val) }
          n  -> internalError $ "GenABin.Bin(IExpr).readBytes: " ++ show n
    -- toBin e = Out [AExp e] ()
    -- fromBin = readShared

instance Bin IntLit where
    writeBytes (IntLit w b i) = do toBin w; toBin b; toBin i
    readBytes = do w <- fromBin
                   b <- fromBin
                   i <- fromBin
                   return (IntLit w b i)

instance Bin ANoInlineFun where
    writeBytes (ANoInlineFun s ts ps mi) = do toBin s; toBin ts; toBin ps; toBin mi
    readBytes = do s <- fromBin
                   ts <- fromBin
                   ps <- fromBin
                   mi <- fromBin
                   return (ANoInlineFun s ts ps mi)

instance Bin PrimOp where
    writeBytes p = toBin (writePrimOp p)
    readBytes = do n <- fromBin; return (readPrimOp n)

-- ----------
-- Bin ADef

instance Bin ADef where
    writeBytes (ADef i t e p) = do toBin i; toBin t; toBin e; toBin p
    readBytes = do i <- fromBin
                   t <- fromBin
                   e <- fromBin
                   p <- fromBin
                   return (ADef i t e p)

instance Bin DefProp where
    writeBytes (DefP_Rule i) = do putI 0 ; toBin i
    writeBytes (DefP_Method i) = do putI 1 ; toBin i
    writeBytes (DefP_Instance i) = do putI 2 ; toBin i
    writeBytes DefP_NoCSE = putI 3
    readBytes = do
      select <- getI
      case select of
        0 -> do i <- fromBin ; return $ DefP_Rule i
        1 -> do i <- fromBin ; return $ DefP_Method i
        2 -> do i <- fromBin ; return $ DefP_Instance i
        3 -> return DefP_NoCSE
        n -> internalError $ "BinData.Bin(DefProp).readBytes: " ++ show n

-- ------------
-- Bin VModInfo

instance Bin VModInfo where
    writeBytes x = section "VModInfo" $
                   do { toBin (vName x); toBin (vClk x); toBin (vRst x);
                        toBin (vArgs x); toBin (vFields x); toBin (vSched x);
                        toBin (vPath x); }
    readBytes = do { name <- fromBin; clk <- fromBin; rst <- fromBin;
                     args <- fromBin; meths <- fromBin; sch <- fromBin;
                     p <- fromBin;
                     return (mkVModInfo name clk rst args meths sch p); }

instance Bin VFieldInfo where
    writeBytes (Method a b c d e f g) =
        do { putI 0; toBin a; toBin b; toBin c; toBin d; toBin e; toBin f;
             toBin g; }
    writeBytes (Clock i) = do putI 1; toBin i
    writeBytes (Reset i) = do putI 2; toBin i
    writeBytes (Inout i p c r) = do putI 3; toBin i; toBin p; toBin c; toBin r
    readBytes = do
        i <- getI
        case i of
          0 -> do a <- fromBin; b <- fromBin; c <- fromBin; d <- fromBin;
                  e <- fromBin; f <- fromBin; g <- fromBin;
                  return (Method a b c d e f g)
          1 -> do a <- fromBin; return (Clock a)
          2 -> do a <- fromBin; return (Reset a)
          3 -> do i <- fromBin; p <- fromBin; c <- fromBin; r <- fromBin;
                  return (Inout i p c r)
          n -> internalError $ "GenABin.Bin(VFieldInfo).readBytes: " ++ show n

instance (Bin a, Ord a) => Bin (SchedInfo a) where
    writeBytes (SchedInfo mci rms rbm ccm) = do toBin mci
                                                toBin rms
                                                toBin rbm
                                                toBin ccm
    readBytes = do mci <- fromBin
                   rms <- fromBin
                   rbm <- fromBin
                   ccm <- fromBin
                   return (SchedInfo mci rms rbm ccm)

instance (Bin a, Ord a) => Bin (MethodConflictInfo a) where
    writeBytes mci@(MethodConflictInfo cfs sbs mes ps sbrs cs exts) =
        section "MethodConflictInfo" $
        do let meths = extractFromMethodConflictInfo mci
               arr :: Array Int a
               arr = listArray (0,length(meths)-1) meths
               arr_map = M.fromList (zip meths [0..])
           toBin arr -- write array of methods
           -- write list of pairs using compact bit matrix representations
           toBin (toBitMatrix arr_map cfs)
           toBin (toBitMatrix arr_map sbs)
           toBin mes
           toBin (toBitMatrix arr_map ps)
           toBin (toBitMatrix arr_map sbrs)
           toBin (toBitMatrix arr_map cs)
           toBin exts
    readBytes =
        do -- read method array
           arr <- (fromBin :: In (Array Int a))
           -- read lists of pairs from bit-matrix representations
           cfs0  <- fromBin
           let cfs = fromBitMatrix arr cfs0
           sbs0  <- fromBin
           let sbs = fromBitMatrix arr sbs0
           mes   <- fromBin
           ps0   <- fromBin
           let ps = fromBitMatrix arr ps0
           sbrs0 <- fromBin
           let sbrs = fromBitMatrix arr sbrs0
           cs0   <- fromBin
           let cs = fromBitMatrix arr cs0
           exts  <- fromBin;
           return (MethodConflictInfo cfs sbs mes ps sbrs cs exts)

type BitMatrix = UArray Int Word32

toBitMatrix :: (Ord a) => (M.Map a Int) -> [(a,a)] -> BitMatrix
toBitMatrix m ps =
    let n           = M.size m
        total_bits  = n * n
        total_words = (total_bits + 31) `quot` 32
        getIndex i = M.findWithDefault (internalError $ "toBitMatrix: bad index") i m
        idxs = [(getIndex a) * n + (getIndex b) | (a,b) <- ps]
    in accumArray (.|.) 0 (0,total_words-1) [ (i `quot` 32, bit (i `rem` 32))
                                            | i <- idxs
                                            ]

fromBitMatrix :: (Array Int a) -> BitMatrix -> [(a,a)]
fromBitMatrix marr mtx =
    let (_,n) = bounds marr
        len = n+1
        bits_of x = filter (testBit x) [0..31]
        ps = concat [ zip (repeat i) (bits_of w)
                    | (i,w) <- assocs mtx
                    , w /= 0
                    ]
    in [ (marr!row, marr!col)
       | (wi,bi) <- ps
       , let idx = wi*32 + bi
       , let row = idx `quot` len
       , let col = idx `rem` len
       ]

instance Bin VPathInfo where
    writeBytes (VPathInfo v) = section "VPathInfo" $ do toBin v
    readBytes = do v <- fromBin; return (VPathInfo v)

instance Bin VeriPortProp where
    writeBytes VPreg = putI 0
    writeBytes VPclock = putI 1
    writeBytes VPconst = putI 2
    writeBytes VPunused = putI 3
    writeBytes VPinhigh = putI 4
    writeBytes VPouthigh = putI 5
    writeBytes VPreset = putI 6
    writeBytes VPclockgate = putI 7
    writeBytes VPinout = putI 8
    readBytes = do
        i <- getI
        case i of
          0 -> return VPreg
          1 -> return VPclock
          2 -> return VPconst
          3 -> return VPunused
          4 -> return VPinhigh
          5 -> return VPouthigh
          6 -> return VPreset
          7 -> return VPclockgate
          8 -> return VPinout
          n -> internalError $ "GenABin.Bin(VeriPortProp).readBytes: " ++ show n

{-
instance Bin AStateLocPathComponent where
    writeBytes loc@(AStateLocPathComponent id1 id2 t) =
        section "AStateLocPathComponent" $
        do toBin id1; toBin id2; (section "CType" (toBin t))
    readBytes = do id1 <- fromBin; id2 <- fromBin; t <- fromBin;
                   return (AStateLocPathComponent id1 id2 t)

    -- AStateLocPathComponent is shared
    toBin l = Out [ASL l] ()
    fromBin = readShared
-}

-- ------------
-- Bin CType / CQType

-- AStateLocPathComponent contains CType
-- ABinModInfo also contains a CQType

instance Bin Type where
    writeBytes (TVar tvar) = do putI 0; toBin tvar
    writeBytes (TCon tcon) = do putI 1; toBin tcon
    writeBytes (TAp t1 t2) = do putI 2; toBin t1; toBin t2;
    writeBytes (TGen pos i) = do putI 3; toBin pos; toBin i
    writeBytes (TDefMonad pos) = internalError $ "BinData.write: TDefMonad"
    readBytes =
        do i <- getI
           case i of
             0 -> do tvar <- fromBin; return (TVar tvar)
             1 -> do tcon <- fromBin; return (TCon tcon)
             2 -> do t1 <- fromBin; t2 <- fromBin; return (TAp t1 t2)
             3 -> do pos <- fromBin; i <- fromBin; return (TGen pos i)
             n -> internalError $ "BinData.Bin(Type).readBytes: " ++ show n

    -- Type is shared
    toBin t = Out [T t] ()
    fromBin = readShared

instance Bin TyVar where
    writeBytes (TyVar i n k) = do toBin i; toBin n; toBin k
    readBytes = do i <- fromBin; n <- fromBin; k <- fromBin;
                   return (TyVar i n k)

instance Bin TyCon where
    writeBytes (TyCon i mk s) = do putI 0; toBin i; toBin mk; toBin s
    writeBytes (TyNum i pos) = do putI 1; toBin i; toBin pos
    writeBytes (TyStr s pos) = do putI 2; toBin s; toBin pos
    readBytes =
        do i <- getI
           case i of
             0 -> do i <- fromBin; mk <- fromBin; s <- fromBin;
                     return (TyCon i mk s)
             1 -> do i <- fromBin; pos <- fromBin; return (TyNum i pos)
             2 -> do s <- fromBin; pos <- fromBin; return (TyStr s pos)
             n -> internalError $ "BinData.Bin(TyCon).readBytes: " ++ show n

instance Bin TISort where
    writeBytes (TItype i t)     = do putI 0; toBin i; toBin t
    writeBytes (TIdata is enum) = do putI 1; toBin is; toBin enum
    writeBytes (TIstruct su is) = do putI 2; toBin su; toBin is
    writeBytes (TIabstract)     = do putI 3
    readBytes = do
        i <- getI
        case i of
          0 -> do i <- fromBin; t <- fromBin; return (TItype i t)
          1 -> do is <- fromBin; enum <- fromBin; return (TIdata is enum)
          2 -> do su <- fromBin; is <- fromBin; return (TIstruct su is)
          3 -> return TIabstract
          n -> internalError $ "BinData.Bin(TISort).readBytes: " ++ show n

instance Bin StructSubType where
    writeBytes SStruct           = putI 0
    writeBytes SClass            = putI 1
    writeBytes (SDataCon i nm)   = do putI 2 ; toBin i; toBin nm
    writeBytes (SInterface ps)   = do putI 3 ; toBin ps
    writeBytes (SPolyWrap i c f) = do putI 4; toBin i; toBin c; toBin f
    readBytes = do
        i <- getI
        case i of
          0 -> return SStruct
          1 -> return SClass
          2 -> do i  <- fromBin ; nm <- fromBin; return (SDataCon i nm)
          3 -> do ps <- fromBin ; return (SInterface ps)
          4 -> do i <- fromBin; c <- fromBin; f <- fromBin; return (SPolyWrap i c f)
          n -> internalError $ "BinData.Bin(StructSubType).readBytes: " ++ show n

instance Bin Kind where
  writeBytes KStar = putI 0
  writeBytes KNum = putI 1
  writeBytes (Kfun k1 k2) = do putI 2; toBin k1; toBin k2
  writeBytes (KVar i) = do putI 3; toBin i
  writeBytes KStr = putI 4
  readBytes =
      do i <- getI
         case i of
           0 -> return KStar
           1 -> return KNum
           2 -> do k1 <- fromBin; k2 <- fromBin; return (Kfun k1 k2)
           3 -> do i <- fromBin; return (KVar i)
           4 -> return KStr
           n -> internalError $ "BinData.Bin(Kind).readBytes: " ++ show n

instance Bin CQType where
    writeBytes (CQType ps t) = do toBin ps; toBin t
    readBytes = do ps <- fromBin; t <- fromBin; return (CQType ps t)

instance Bin CPred where
    writeBytes (CPred c ts) = do toBin c; toBin ts
    readBytes = do c <- fromBin; ts <- fromBin; return (CPred c ts)

instance Bin CTypeclass where
    writeBytes (CTypeclass i) = toBin i
    readBytes = do i <- fromBin; return (CTypeclass i)


-- ------------
-- Bin IType, IKind, etc.

instance Bin IType where
    writeBytes (ITForAll i k t) = do putI 0; toBin i; toBin k; toBin t
    writeBytes (ITAp t1 t2)     = do putI 1; toBin t1; toBin t2
    writeBytes (ITVar i)        = do putI 2; toBin i
    writeBytes (ITCon i k s)    = do putI 3; toBin i; toBin k; toBin s
    writeBytes (ITNum n)        = do putI 4; toBin n
    writeBytes (ITStr s)        = do putI 5; toBin s
    readBytes = do tag <- getI
                   case tag of
                     0 -> do i <- fromBin; k <- fromBin; t <- fromBin
                             return $ ITForAll i k t
                     1 -> do t1 <- fromBin; t2 <- fromBin
                             return $ ITAp t1 t2
                     2 -> do i <- fromBin; return $ ITVar i
                     3 -> do i <- fromBin; k <- fromBin; s <- fromBin
                             return $ ITCon i k s
                     4 -> do n <- fromBin; return $ ITNum n
                     5 -> do s <- fromBin; return $ ITStr s
                     n -> internalError $ "BinData.Bin(IType).readBytes: " ++ show n

    -- IType is shared
    toBin t = Out [IT t] ()
    fromBin = readShared

instance Bin IKind where
    writeBytes IKStar        = do putI 0
    writeBytes IKNum         = do putI 1
    writeBytes (IKFun k1 k2) = do putI 2; toBin k1; toBin k2
    writeBytes IKStr         = do putI 3
    readBytes = do tag <- getI
                   case tag of
                     0 -> return IKStar
                     1 -> return IKNum
                     2 -> do k1 <- fromBin; k2 <- fromBin; return (IKFun k1 k2)
                     3 -> return IKStr
                     n -> internalError $ "BinData.Bin(IKind).readBytes: " ++ show n

instance Bin UndefKind where
    writeBytes UNotUsed  = putI 0
    writeBytes UDontCare = putI 1
    writeBytes UNoMatch  = putI 2
    readBytes = do tag <- getI
                   case tag of
                     0 -> return UNotUsed
                     1 -> return UDontCare
                     2 -> return UNoMatch
                     n -> internalError $ "BinData.Bin(UndefKind).readBytes: " ++ show n

-- ------------------------------------------------------------------
-- This is a debugging facility to help in determining what structures
-- contribute the most bytes to the output byte stream.

-- XXX This should be a trace flag, but tracing can overflow the stack
-- when the data is too large, so I am leaving it as a compile-time
-- setting for now.
trace_bindata :: Bool
trace_bindata = False

type Histogram = M.Map String (Integer, Integer, Integer)

incr :: (Integer, Integer, Integer ) -> (Integer, Integer, Integer)
     -> (Integer, Integer, Integer)
incr (x1,y1,z1) (x2,y2,z2) = (x1+x2, y1+y2, z1+z2)

updateBytes :: [String] -> Integer -> Histogram -> Histogram
updateBytes [] _ h = h
-- updateBytes (s:ss) n h = let upds = (s, (n,0,n)):[(p, (0,0,n)) | p <- ss]
--                          in map_insertManyWith incr upds h
updateBytes (s:_) n h = M.insertWith incr s (n,0,n) h

incrSection :: String -> Histogram -> Histogram
incrSection s h = M.insertWith incr s (0,1,0) h

showHist :: Histogram -> String
showHist hist = let buckets = sort [ (n1,n2,n3,s)
                                   | (s,(n1,n2,n3)) <- (M.toList hist) ]
                    ls = [ (show n1) ++ " (" ++ (show n3) ++ ") count = " ++
                           (show n2) ++ " : " ++ s
                         | (n1,n2,n3,s) <- buckets ]
                    total = [ "----------------------------"
                            , (show (sum [ n | (n,_,_,_) <- buckets]))
                            ]
                in unlines (ls ++ total)

buildHistogram :: [BinElem] -> Histogram
buildHistogram bes = snd (foldl build (["<UNCLAIMED>"], M.empty) bes)
  where build ([], _) _ = internalError "unbalanced accounting marks"
        build (sec, hist) (B b) =
          (sec, updateBytes sec (toInteger (length b)) hist)
        build (sec, hist) (Start s) = ((s:sec), incrSection s hist)
        build ((_:sec), hist) End   = (sec, hist)
        build _ x = internalError $ "unexpected BinElem: " ++ (show x)

-- ------------------------------------------------------------------

-- Convert BinData containing shared elements to BinData containing
-- only B elements, where the shared elements are put in the binary
-- stream the first time they occur and referenced by index thereafter.

-- This converts a BinElem for a shared value into BinData
-- matching (Left value) the first time it is encountered
-- and (Right idx) each time afterward, updating the cache
-- to track known values.
share :: BinElem -> BinCache -> ([BinElem], BinCache)
share (S s)   bc = share' s s bc
share (I i)   bc = share' (id_key i) i bc
share (P p)   bc = share' p p bc
share (T t)   bc = share' (type_key t) t bc
share (IT t)  bc = share' (itype_key t) t bc
-- share (ASL l) bc = share' l l bc
share be      bc = ([be], bc)

share' :: (Bin v, Shared k v) => k -> v -> BinCache -> ([BinElem], BinCache)
share' k x bc =
          case (knownAs k x bc) of
            (Just idx) -> (out_data $ do { putI 1; writeBytes idx }, bc)
            Nothing    -> (out_data $ do { putI 0; writeBytes x },
                           addKey k x bc)


compress :: [BinElem] -> [BinElem]
compress bes = compress' (bes, unknownCache)
  where compress' ((x@(B _):xs), cache) = x:(compress' (xs, cache))
        compress' ((x@(Start _):xs), cache) = x:(compress' (xs, cache))
        compress' ((x@(End):xs), cache) = x:(compress' (xs, cache))
        compress' ((x:xs), cache) =
          let (bes, cache') = share x cache
          in -- trace ((show x) ++ " -> " ++ (show bes)) $
             compress' (bes ++ xs, cache')
        compress' ([], _) = []

-- Run the Out monad and extract a byte stream.  The resulting
-- byte stream is generated lazily through the monad and preserves
-- sharing.

runOut :: Out () -> [Byte]
runOut (Out xs _) = let bes   = compress $ toList xs
                        bytes = concat [ bs | B bs <- bes ]
                    in -- trace ("xs = " ++ (show xs)) $
                       -- trace ("bytes = " ++ (show bytes)) $
                       if trace_bindata
                       then trace (showHist (buildHistogram bes)) $ bytes
                       else bytes

-- Convenience function for encoding structures in the Bin typeclass
encode :: (Bin a) => a -> [Byte]
encode x = runOut (toBin x)

runIn :: In a -> [Byte] -> Bool -> (a, [Byte], String)
runIn (In f) bs do_hash =
  let h0 = if do_hash then (Just hashInit) else Nothing
      (x,(IS _ bs' h)) = f (IS unknownTable bs h0)
      hstr = maybe "" showHash h
  in (x, bs', hstr)

decode :: (Bin a) => [Byte] -> a
decode s = let (x, bs, _) = runIn fromBin s False
           in if (null bs)
              then x
              else internalError "BinData.decode: unused trailing bytes"

decodeWithHash :: (Bin a) => [Byte] -> (a,String)
decodeWithHash s = let (x, bs, hstr) = runIn fromBin s True
                   in if (null bs)
                      then (x, hstr)
                      else internalError "BinData.decodeWithHash: unused trailing bytes"
