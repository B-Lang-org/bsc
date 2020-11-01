{-# LANGUAGE MagicHash, CPP, BangPatterns #-}
-- |This module provides an optimized version of log2 for Integral
-- types that is efficient even for very large integers.
module Log2(log2,log10) where

-- GHC 9.0 has an entirely new ghc-bignum package.
-- See https://iohk.io/en/blog/posts/2020/07/28/improving-haskells-big-numbers-support/
#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 900)
import GHC.Num.Integer (Integer(IS, IP, IN))
import GHC.Num.BigNat
#else
import GHC.Integer.GMP.Internals
#endif
import GHC.Exts
import Data.Bits

-- In GHC 7.8, internal primops return Int# instead of Bool
eqInt, neqInt :: Int# -> Int# -> Bool
{-# INLINE eqInt #-}
{-# INLINE neqInt #-}
eqInt a b = isTrue# (a ==# b)
neqInt a b = isTrue# (a /=# b)

-- |Number of bits in an Int (or Int#) on this machine
wordSize :: Int
wordSize = finiteBitSize (0 :: Int)

-- |Compute the logarithm base 2, rounded up, for Integral types.
-- One interpretation of this log2 function is that it tells you
-- the minimum number of bits required to represent a given number
-- of distinct values.
log2 :: (Integral a, Integral b) => a -> b
log2 0 = 0
log2 x = case (toInteger x) of
           -- for values which fit in a single word, we
           -- find the index of the most significant non-zero
           -- bit.  if all other bits are zero, then this is
           -- the value of the base 2 log, otherwise we must
           -- add one to the value to get the base 2 log.
           -- 'small' integer that fits in a single word
#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 900)
           IS n  -> let !(top_one,any_other_ones) = analyze (I# n)
                    in toEnum (top_one + (if any_other_ones then 1 else 0))
#else
           S# n  -> let !(top_one,any_other_ones) = analyze (I# n)
                    in toEnum (top_one + (if any_other_ones then 1 else 0))
#endif
           -- for values which exceed the word size, we use the
           -- log2large function to examine the values in the array.
           -- positive and negative multiword integers respectively
#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 900)
           IP bn -> let sz = bigNatSize# bn
                    in  log2large (sz -# 1#) bn
           IN bn -> let sz = bigNatSize# bn
                    in  log2large (sz -# 1#) bn
#else
           Jp# bn@(BN# arr) -> let sz = sizeofBigNat# bn
                               in  log2large (sz -# 1#) arr
           Jn# bn@(BN# arr) -> let sz = sizeofBigNat# bn
                               in  log2large (sz -# 1#) arr
#endif

-- |Utility function to find the index of the most significant
-- non-zero bit in a single-word Int and also report if any
-- other bits are non-zero.  Note: this assumes n /= 0.
analyze :: Int -> (Int,Bool)
analyze n = helper n (wordSize - 1)
    where helper v idx = if (testBit v idx)
                         then (idx, (clearBit v idx) /= 0)
                         else helper n (idx - 1)

-- |Utility function to determine if any words in a ByteArray#
-- up to a given index are non-zero.
anyNonZero :: ByteArray# -> Int# -> Bool
anyNonZero arr idx = if (indexIntArray# arr idx) `neqInt` 0#
                     then True
                     else (idx `neqInt` 0#) && (anyNonZero arr (idx -# 1#))

-- |Compute the log2 for Integers which span multiple words.  This
-- first scans the memory for the most significant word that is not 0.
-- Then it analyzes that word to determine, along with the word's
-- index, the provisional logarithm value, If that word had any
-- additional non-zero bits, or if any other words in the ByteArray#
-- are non-zero, then the actual logarithm will be one more than the
-- provisional value.
log2large :: (Integral b) => Int# -> ByteArray# -> b
log2large i arr =
    let !w = indexIntArray# arr i
    in if w `eqInt` 0#
       then if i `eqInt` 0# then 0 else log2large (i -# 1#) arr
       else let !(top_one,any_other_ones) = analyze (I# w)
                base = (wordSize * (I# i) + top_one)
            in if any_other_ones || ((i `neqInt` 0#) && (anyNonZero arr (i -# 1#)))
               then toEnum (base + 1)
               else toEnum base

-- | This is a quick-and-dirty log10 implementation.  It will not
-- be fast for large numbers.
log10 :: (Integral a, Integral b) => a -> b
log10 n = if (n < 10)
          then 0
          else 1 + (log10 (quot n 10))
