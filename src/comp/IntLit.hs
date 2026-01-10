{-# LANGUAGE DeriveDataTypeable #-}
module IntLit (IntLit(..),
               ilDec, ilSizedDec, ilHex, ilSizedHex, ilBin, ilSizedBin,
               showVeriIntLit, showSizedVeriIntLit
              ) where

import IntegerUtil(integerFormatPref, integerToString)
import PPrint
import PVPrint
import Eval(NFData(..), rnf3)
import ErrorUtil(internalError)
import qualified Data.Generics as Generic

data IntLit = IntLit { ilWidth :: Maybe Integer,
                       ilBase  :: Integer,
                       ilValue :: Integer }
              deriving (Generic.Data, Generic.Typeable)



ilDec :: Integer -> IntLit
ilDec i = IntLit { ilWidth = Nothing, ilBase = 10, ilValue = i }

ilSizedDec :: Integer -> Integer -> IntLit
ilSizedDec w i = IntLit { ilWidth = Just w, ilBase = 10, ilValue = i }

ilHex :: Integer -> IntLit
ilHex i = IntLit { ilWidth = Nothing, ilBase = 16, ilValue = i }

ilSizedHex :: Integer -> Integer -> IntLit
ilSizedHex w i = IntLit { ilWidth = Just w, ilBase = 16, ilValue = i }

ilBin :: Integer -> IntLit
ilBin i = IntLit { ilWidth = Nothing, ilBase = 2,  ilValue = i }

ilSizedBin :: Integer -> Integer -> IntLit
ilSizedBin w i = IntLit { ilWidth = Just w, ilBase = 2, ilValue = i }


instance Eq IntLit where
     IntLit { ilValue = i1 } == IntLit { ilValue = i2 }  =  i1 == i2
     IntLit { ilValue = i1 } /= IntLit { ilValue = i2 }  =  i1 /= i2

instance Ord IntLit where
     IntLit { ilValue = i1 } <= IntLit { ilValue = i2 }  =  i1 <= i2
     IntLit { ilValue = i1 } <  IntLit { ilValue = i2 }  =  i1 <  i2
     IntLit { ilValue = i1 } >= IntLit { ilValue = i2 }  =  i1 >= i2
     IntLit { ilValue = i1 } >  IntLit { ilValue = i2 }  =  i1 >  i2
     IntLit { ilValue = i1 } `compare` IntLit { ilValue = i2 }  =  i1 `compare` i2

instance Show IntLit where
     showsPrec _ (IntLit { ilValue = i, ilWidth = mw, ilBase = b }) s =
         -- width of 0 means don't pad with leading zeros
         integerFormatPref 0 b i ++ s

instance PPrint IntLit where
     pPrint d p i = text (show i)

instance NFData IntLit where
     rnf (IntLit x1 x2 x3) = rnf3 x1 x2 x3

-- --------------------

instance PVPrint IntLit where
     pvPrint d p (IntLit { ilValue = i, ilWidth = w, ilBase = b }) =
         text $ intFormat w b i

intFormat :: Maybe Integer -> Integer -> Integer -> String
intFormat mwidth base value | value < 0 = '-' : intFormat mwidth base (-value)
intFormat mwidth  2 value = sizeFormat mwidth ++ "'b" ++ digitsFormat  2 value
intFormat mwidth  8 value = sizeFormat mwidth ++ "'o" ++ digitsFormat  8 value
intFormat mwidth 16 value = sizeFormat mwidth ++ "'h" ++ digitsFormat 16 value
intFormat Nothing 10 value = digitsFormat 10 value
intFormat mwidth 10 value = sizeFormat mwidth ++ "'d" ++ digitsFormat 10 value
intFormat mwidth base value =
    internalError ("bad radix to intFormat: " ++ show base)

sizeFormat :: Maybe Integer -> String
sizeFormat Nothing = ""
sizeFormat (Just width) = integerToString 10 width

digitsFormat :: Integer -> Integer -> String
digitsFormat base value = integerToString (fromInteger base) value

-- --------------------

showSizedVeriIntLit :: Integer -> IntLit -> String
showSizedVeriIntLit sz (IntLit { ilValue = i, ilBase = b }) =
    -- XXX we could check whether the value has a width
    -- XXX and error if it doesn't match the given width
    intFormat (Just sz) b i

showVeriIntLit :: IntLit -> String
showVeriIntLit (IntLit { ilValue = i, ilWidth = w, ilBase = b }) =
    intFormat w b i

-- --------------------
