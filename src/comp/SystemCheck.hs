module SystemCheck (doSystemCheck) where

import Control.Monad(when)
import Foreign.Storable

import Error(ErrMsg(..), ErrorHandle, bsError)
import Position


-- Check that BSC is being called on a system which supports various
-- features assumed by parts of BSC.  Current assumptions:
--
-- * floating point arithmetic is IEEE and the radix is 2
--

doSystemCheck :: ErrorHandle -> IO ()
doSystemCheck errh = do
    let x = (0 :: Double)
    -- XXX instead of erroring, we could just disable Real support
    when (not (isIEEE x)) $
        bsError errh [(cmdPosition, EFloatingPointNotIEEE)]
    -- XXX again, we could just disable Real support
    when ((floatRadix x) /= 2) $
        bsError errh [(cmdPosition, EFloatingPointRadixNotTwo)]
    -- XXX again, we could just disable Real support
    when ((floatDigits x) /= 53) $
        bsError errh [(cmdPosition, EFloatingPointPrecisionNot53)]
    -- XXX again, we could just disable Real support
    when ((sizeOf x) /= 8) $
        bsError errh [(cmdPosition, EDoubleNot64Bit)]
    return ()
