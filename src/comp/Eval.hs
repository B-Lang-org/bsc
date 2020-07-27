module Eval(Hyper(..),
            hyper2, hyper3, hyper4, hyper5, hyper6, hyper7, hyper8, hyper9,
            hyper10, hyper11, hyper12, hyper13, hyper14, hyper15, hyper16,
            hyper17,
            hyperId) where

import System.IO(Handle)
import Data.IntMap as IM
import Data.IntSet as IS
import Data.Set as DS
import Data.Map as DM
import FStringCompat(FString)

-- Hyperstrict identity function
class Hyper a where
    hyper :: a -> b -> b

instance Hyper Int where
    hyper x y = seq x y

instance Hyper Bool where
    hyper x y = seq x y

instance Hyper Integer where
    hyper x y = seq x y

instance Hyper Handle where
    hyper x y = seq x y

instance Hyper Char where
    hyper x y = seq x y

instance Hyper FString where
    hyper x y = seq x y

instance Hyper Double where
    hyper x y = seq x y

instance Hyper () where
    hyper x y = seq x y

instance (Hyper a, Hyper b) => Hyper (a, b) where
    hyper (a, b) y = hyper2 a b y

instance (Hyper a, Hyper b, Hyper c) => Hyper (a, b, c) where
    hyper (a, b, c) y = hyper3 a b c y

instance (Hyper a, Hyper b, Hyper c, Hyper d) => Hyper (a, b, c, d) where
    hyper (a, b, c, d) y = hyper4 a b c d y

instance (Hyper a, Hyper b, Hyper c, Hyper d, Hyper e) => Hyper (a, b, c, d, e) where
    hyper (a, b, c, d, e) y = hyper5 a b c d e y

instance (Hyper a, Hyper b, Hyper c, Hyper d, Hyper e, Hyper f) => Hyper (a, b, c, d, e, f) where
    hyper (a, b, c, d, e, f) y = hyper6 a b c d e f y

instance (Hyper a) => Hyper [a] where
    hyper [] y = y
    hyper (x:xs) y = hyper2 x xs y

instance (Hyper a) => Hyper (Maybe a) where
    hyper Nothing y = y
    hyper (Just x) y = hyper x y

instance (Hyper a, Hyper b) => Hyper (Either a b) where
    hyper (Left a)  y = hyper a y
    hyper (Right b) y = hyper b y

hyper2 :: (Hyper a1, Hyper a2) => a1 -> a2 -> b -> b
hyper2 x1 x2 y = x1 `hyper` x2 `hyper` y

hyper3 :: (Hyper a1, Hyper a2, Hyper a3) => a1 -> a2 -> a3 -> b -> b
hyper3 x1 x2 x3 y = x1 `hyper` x2 `hyper` x3 `hyper` y

hyper4 :: (Hyper a1, Hyper a2, Hyper a3, Hyper a4)
       => a1 -> a2 -> a3 -> a4 -> b -> b
hyper4 x1 x2 x3 x4 y = x1 `hyper` x2 `hyper` x3 `hyper` x4 `hyper` y

hyper5 :: (Hyper a1, Hyper a2, Hyper a3, Hyper a4, Hyper a5)
       => a1 -> a2 -> a3 -> a4 -> a5 -> b -> b
hyper5 x1 x2 x3 x4 x5 y =
   x1 `hyper` x2 `hyper` x3 `hyper` x4 `hyper` x5 `hyper` y

hyper6 :: (Hyper a1, Hyper a2, Hyper a3, Hyper a4, Hyper a5, Hyper a6)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> b -> b
hyper6 x1 x2 x3 x4 x5 x6 y =
    x1 `hyper` x2 `hyper` x3 `hyper` x4 `hyper` x5 `hyper` x6 `hyper` y

hyper7 :: (Hyper a1, Hyper a2, Hyper a3, Hyper a4, Hyper a5, Hyper a6, Hyper a7)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> b -> b
hyper7 x1 x2 x3 x4 x5 x6 x7 y =
    x1 `hyper` x2 `hyper` x3 `hyper` x4 `hyper` x5 `hyper` x6 `hyper` x7
       `hyper` y

hyper8 :: (Hyper a1, Hyper a2, Hyper a3, Hyper a4, Hyper a5, Hyper a6, Hyper a7
          ,Hyper a8) => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> b -> b
hyper8 x1 x2 x3 x4 x5 x6 x7 x8 y =
    x1 `hyper` x2 `hyper` x3 `hyper` x4 `hyper` x5 `hyper` x6 `hyper` x7
       `hyper` x8 `hyper` y

hyper9 :: (Hyper a1, Hyper a2, Hyper a3, Hyper a4, Hyper a5, Hyper a6, Hyper a7
          ,Hyper a8, Hyper a9)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> b -> b
hyper9 x1 x2 x3 x4 x5 x6 x7 x8 x9 y =
    x1 `hyper` x2 `hyper` x3 `hyper` x4 `hyper` x5 `hyper` x6 `hyper` x7
       `hyper` x8 `hyper` x9 `hyper` y

hyper10 :: (Hyper a1, Hyper a2, Hyper a3, Hyper a4, Hyper a5, Hyper a6, Hyper a7
           ,Hyper a8, Hyper a9, Hyper a10)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> a10 -> b -> b
hyper10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 y =
    x1 `hyper` x2 `hyper` x3 `hyper` x4 `hyper` x5 `hyper` x6 `hyper` x7
       `hyper` x8 `hyper` x9 `hyper` x10 `hyper` y

hyper11 :: (Hyper a1, Hyper a2, Hyper a3, Hyper a4, Hyper a5, Hyper a6, Hyper a7
           ,Hyper a8, Hyper a9, Hyper a10, Hyper a11)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> a10 -> a11
       -> b -> b
hyper11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 y =
    x1 `hyper` x2 `hyper` x3 `hyper` x4 `hyper` x5 `hyper` x6 `hyper` x7
       `hyper` x8 `hyper` x9 `hyper` x10 `hyper` x11 `hyper` y

hyper12 :: (Hyper a1, Hyper a2, Hyper a3, Hyper a4, Hyper a5, Hyper a6, Hyper a7
           ,Hyper a8, Hyper a9, Hyper a10, Hyper a11, Hyper a12)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> a10 -> a11
       -> a12 -> b -> b
hyper12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 y =
    x1 `hyper` x2 `hyper` x3 `hyper` x4 `hyper` x5 `hyper` x6 `hyper` x7
       `hyper` x8 `hyper` x9 `hyper` x10 `hyper` x11 `hyper` x12 `hyper` y

hyper13 :: (Hyper a1, Hyper a2, Hyper a3, Hyper a4, Hyper a5, Hyper a6, Hyper a7
           ,Hyper a8, Hyper a9, Hyper a10, Hyper a11, Hyper a12, Hyper a13)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> a10 -> a11
       -> a12 -> a13 -> b -> b
hyper13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 y =
    x1 `hyper` x2 `hyper` x3 `hyper` x4 `hyper` x5 `hyper` x6 `hyper` x7
       `hyper` x8 `hyper` x9 `hyper` x10 `hyper` x11 `hyper` x12 `hyper` x13
       `hyper` y

hyper14 :: (Hyper a1, Hyper a2, Hyper a3, Hyper a4, Hyper a5, Hyper a6, Hyper a7
           ,Hyper a8, Hyper a9, Hyper a10, Hyper a11, Hyper a12, Hyper a13
           ,Hyper a14)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> a10 -> a11
       -> a12 -> a13 -> a14 -> b -> b
hyper14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 y =
    x1 `hyper` x2 `hyper` x3 `hyper` x4 `hyper` x5 `hyper` x6 `hyper` x7
       `hyper` x8 `hyper` x9 `hyper` x10 `hyper` x11 `hyper` x12 `hyper` x13
       `hyper` x14 `hyper` y

hyper15 :: (Hyper a1, Hyper a2, Hyper a3, Hyper a4, Hyper a5, Hyper a6, Hyper a7
           ,Hyper a8, Hyper a9, Hyper a10, Hyper a11, Hyper a12, Hyper a13
           ,Hyper a14, Hyper a15)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> a10 -> a11
       -> a12 -> a13 -> a14 -> a15 -> b -> b
hyper15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y =
    x1 `hyper` x2 `hyper` x3 `hyper` x4 `hyper` x5 `hyper` x6 `hyper` x7
       `hyper` x8 `hyper` x9 `hyper` x10 `hyper` x11 `hyper` x12 `hyper` x13
       `hyper` x14 `hyper` x15 `hyper` y

hyper16 :: (Hyper a1, Hyper a2, Hyper a3, Hyper a4, Hyper a5, Hyper a6, Hyper a7
           ,Hyper a8, Hyper a9, Hyper a10, Hyper a11, Hyper a12, Hyper a13
           ,Hyper a14, Hyper a15, Hyper a16)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> a10 -> a11
       -> a12 -> a13 -> a14 -> a15 -> a16 -> b -> b
hyper16 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 y =
    x1 `hyper` x2 `hyper` x3 `hyper` x4 `hyper` x5 `hyper` x6 `hyper` x7
       `hyper` x8 `hyper` x9 `hyper` x10 `hyper` x11 `hyper` x12 `hyper` x13
       `hyper` x14 `hyper` x15 `hyper` x16 `hyper` y

hyper17 :: (Hyper a1, Hyper a2, Hyper a3, Hyper a4, Hyper a5, Hyper a6, Hyper a7
           ,Hyper a8, Hyper a9, Hyper a10, Hyper a11, Hyper a12, Hyper a13
           ,Hyper a14, Hyper a15, Hyper a16, Hyper a17)
       => a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7 -> a8 -> a9 -> a10 -> a11
       -> a12 -> a13 -> a14 -> a15 -> a16 -> a17 ->  b -> b
hyper17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 y =
    x1 `hyper` x2 `hyper` x3 `hyper` x4 `hyper` x5 `hyper` x6 `hyper` x7
       `hyper` x8 `hyper` x9 `hyper` x10 `hyper` x11 `hyper` x12 `hyper` x13
       `hyper` x14 `hyper` x15 `hyper` x16 `hyper` x17 `hyper` y

hyperId :: Hyper a => a -> a
hyperId x = hyper x x

instance (Eq a) => Hyper (IM.IntMap a) where
  hyper m y = (m == m) `seq` y

instance Hyper (IS.IntSet) where
  hyper s y = (s == s) `seq` y

instance (Hyper a) => Hyper (DS.Set a) where
  hyper s y = hyper (DS.toList s) y

instance (Hyper a, Hyper b) => Hyper (DM.Map a b) where
  hyper m y = hyper (DM.toList m) y
