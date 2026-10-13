{-# LANGUAGE ForeignFunctionInterface #-}
module RealUtil( log2, log10
               , doubleToWord64, word64ToDouble
               , isPosInfinite, isNegInfinite
               ) where

import Data.Word (Word64)
import GHC.Float (castDoubleToWord64, castWord64ToDouble)
import Foreign.C.Types

-- ---------------

foreign import ccall unsafe "math.h log2"
    c_log2 :: CDouble -> CDouble

log2 :: Double -> Double
log2 x = realToFrac (c_log2 (realToFrac x))

-- -----

foreign import ccall unsafe "math.h log10"
    c_log10 :: CDouble -> CDouble

log10 :: Double -> Double
log10 x = realToFrac (c_log10 (realToFrac x))

-- -----

{-
-- XXX Can this be defined natively in Haskell with "decodeFloat" and
-- XXX "scaleFloat", or is this FFI needed?
frexp :: Double -> (Double,Int)
frexp x = unsafePerformIO $
    alloca $ \p -> do
        d <- c_frexp (realToFrac x) p
        i <- peek p
        return (realToFrac d, fromIntegral i)

foreign import ccall unsafe "math.h frexp"
     c_frexp    :: CDouble -> Ptr CInt -> IO Double
-}

-- -----

{-
-- XXX This presumably is equivalent to Haskell's "properFraction"
-- XXX so no FFI is needed
modf :: Double -> (Double,Double)
modf x = unsafePerformIO $
    alloca $ \p -> do
        d <- c_modf (realToFrac x) p
        i <- peek p
        return (realToFrac d, realToFrac i)

foreign import ccall unsafe "math.h modf"
     c_modf     :: CDouble -> Ptr CDouble -> IO CDouble
-}

-- ---------------

doubleToWord64 :: Double -> Word64
doubleToWord64 = castDoubleToWord64

word64ToDouble :: Word64 -> Double
word64ToDouble = castWord64ToDouble

-- ---------------

isPosInfinite :: Double -> Bool
isPosInfinite d = (isInfinite d) && (d > 0)

isNegInfinite :: Double -> Bool
isNegInfinite d = (isInfinite d) && (d < 0)

-- ---------------
