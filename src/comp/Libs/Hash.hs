-- Copyright (c) 1982-1999 Lennart Augustsson, Thomas Johnsson
-- See LICENSE for the full license.
--
module Hash(Hash(..), combineHash, emptyHash, hashToInt, hashToMax, Hashable(..)) where

--
-- Hash a value.  Hashing produces an Int of
-- unspecified range.
--
import Data.Array
import Data.Complex
import Data.Ratio

-- #define HASH(x) (case hash (x) of H h -> h)
hASH x = case hash (x) of H h -> h

newtype Hash = H Int deriving (Eq)

instance Show Hash where
    --showsType _ = showString "Hash"
    show _ = "<<Hash>>"

combineHash :: Hash -> Hash -> Hash
combineHash (H x) (H y) = H (x+y)

emptyHash :: Hash
emptyHash = H 0

class Hashable a where
    hash :: a -> Hash

instance Hashable Char where
    hash x = H $ fromEnum x

instance Hashable Int where
    hash x = H $ x

instance Hashable Integer where
    hash x = H $ fromInteger x

instance Hashable Float where
    hash x = H $ truncate x

instance Hashable Double where
    hash x = H $ truncate x

instance Hashable (IO a) where
    hash x = H 0

instance Hashable () where
    hash x = H 0

instance Hashable (a -> b) where
    hash x = H 0

instance (Hashable a) => Hashable (Maybe a) where
    hash Nothing = H 0
    hash (Just x) = hash x

instance (Hashable a, Hashable b) => Hashable (Either a b) where
    hash (Left x) = hash x
    hash (Right y) = hash y

instance Hashable a => Hashable [a] where
    hash l = H $ f l 0
        where f :: (Hashable a') => [a'] -> Int -> Int
              f [] r = r
              f (c:cs) r = f cs (3*r + hASH(c))

{-
#ifndef __HBCC__
instance Hashable [Char] where
    hash l = H $ f l 0
        where f :: String -> Int -> Int
              f [] r = r
              f (c:cs) r = f cs (3*r + fromEnum c)
#endif
-}

instance (Hashable a, Hashable b) => Hashable (a,b) where
    hash (a,b) = H $ hASH(a) + 3 * hASH(b)

instance (Hashable a, Hashable b, Hashable c) => Hashable (a,b,c) where
    hash (a,b,c) = H $ hASH(a) + 3 * hASH(b) + 5 * hASH(c)

instance (Hashable a, Hashable b, Hashable c, Hashable d) => Hashable (a,b,c,d) where
    hash (a,b,c,d) = H $ hASH(a) + 3 * hASH(b) + 5 * hASH(c) + 7 * hASH(d)

instance (Hashable a, Hashable b, Hashable c, Hashable d, Hashable e) => Hashable (a,b,c,d,e) where
    hash (a,b,c,d,e) = H $ hASH(a) + 3 * hASH(b) + 5 * hASH(c) + 7 * hASH(d) + 9 * hASH(e)

instance Hashable Bool where
    hash False = H 0
    hash True = H 1

instance (Integral a, Hashable a) => Hashable (Ratio a) where
    hash x = H $ hASH (denominator x) + hASH (numerator x)

instance (RealFloat a, Hashable a) => Hashable (Complex a) where
    hash (x :+ y) = H $ hASH(x) + hASH(y)

instance (Ix a) => Hashable (Array a b) where
    hash x = H $ 0 -- !!!

hashToInt :: Int -> Hash -> Int
hashToInt maxhash x =
    case x of
    H h ->
        if h < 0 then
            if -h < 0 then 0
            else (-h) `rem` maxhash
        else h `rem` maxhash

hashToMax maxhash x =
    case hash x of
    H h ->
        if h < 0 then
            if -h < 0 then 0
            else (-h) `rem` maxhash
        else h `rem` maxhash
