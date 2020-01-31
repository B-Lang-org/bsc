module IntegerUtil(mask, ext, integerFormat, integerFormatPref,
		   integerInvert, integerXor, integerSelect, aaaa,
                   integerAnd, integerOr, integerToString) where

import ErrorUtil(internalError)


-- generate N bits of repeating 'aaaa' pattern
aaaa :: Integer -> Integer
aaaa 0 = 0
aaaa 1 = 0
aaaa 2 = 2
aaaa 3 = 2
aaaa sz | sz >= 4 = let higher_bits = (aaaa (sz - 4))
			lower_bits = 10
			offset = (2 :: Integer) ^ (4 :: Integer)
		    in  (offset * higher_bits) + lower_bits
aaaa _ = internalError "aaaa not defined for negative sizes"

{-
aaaa :: Integer -> Integer
aaaa 0 = 0
aaaa 1 = 0
aaaa n | n < 0     = internalError "aaaa not defined for negative sizes"
       | even n    = (2 ^ (n - 1)) + (aaaa (n - 2))
       | otherwise = aaaa (n - 1)
-}


-- mask to s bits
mask :: Integer -> Integer -> Integer
mask s i | s >= 0 = i `mod` 2^s
mask s i = internalError ("mask " ++ show (s, i))

-- sign extend to s bits
ext :: Integer -> Integer -> Integer
ext s i | s >= 1 = if i >= 2^(s-1) then i - 2^s else i
ext _ _ = internalError "ext only defined for positive input"


integerInvert :: Integer -> Integer
integerInvert x = -x - 1

integerAnd :: Integer -> Integer -> Integer
integerAnd x y = loop 1 0 x y
  where loop :: Integer -> Integer -> Integer -> Integer -> Integer
	loop bit acc x y =
	    if x == 0 || y == 0 then
	        acc
	    else if x == -1 && y == -1 then
		-bit + acc
	    else
	        let (x', xb) = divMod x 2
		    (y', yb) = divMod y 2
		in  if xb == 1 && yb == 1 then
		        loop (bit*2) (acc+bit) x' y'
		    else
		        loop (bit*2) acc       x' y'

integerOr :: Integer -> Integer -> Integer
integerOr x y = loop 1 0 x y
  where loop :: Integer -> Integer -> Integer -> Integer -> Integer
	loop bit acc x y =
	    if x == 0 && y == 0 then
	        acc
	    else if x == -1 || y == -1 then
		-bit + acc
	    else
	        let (x', xb) = divMod x 2
		    (y', yb) = divMod y 2
		in  if xb == 1 || yb == 1 then
		        loop (bit*2) (acc+bit) x' y'
		    else
		        loop (bit*2) acc       x' y'

integerXor :: Integer -> Integer -> Integer
integerXor x y = (x `integerOr` y) `integerAnd` integerInvert (x `integerAnd` y)

-- select k bits at position m
integerSelect :: Integer -> Integer -> Integer -> Integer
integerSelect k m i | k >= 0 && m >= 0 = mask k (i `div` 2^m)
integerSelect k m i = internalError ("integerSelect " ++ show (k, m, i))

integerFormat :: Integer -> Integer -> Integer -> String
integerFormat width base value =
	if value < 0 then
		'-' : integerFormat width base (-value)
	else
		let s = integerToString (fromInteger base) value
		    l = length s
		    w = fromInteger width
		    pad = if l < w then replicate (w-l) '0' else ""
		in  pad ++ s

integerFormatPref :: Integer -> Integer -> Integer -> String
integerFormatPref width  2 value = "0b" ++ integerFormat width  2 value
integerFormatPref width  8 value = "0o" ++ integerFormat width  8 value
integerFormatPref width 10 value =         integerFormat width 10 value
integerFormatPref width 16 value = "0x" ++ integerFormat width 16 value
-- otherwise, use decimal
integerFormatPref width  _ value = integerFormatPref width 10 value

integerToString :: Int -> Integer -> String
integerToString b i | b < 2      =  error "integerToString: base must be >= 2"
		    | i < 0      =  '-' : showIntBase (toInteger b) (negate i) ""
		    | otherwise  =  showIntBase (toInteger b) i ""

-- mostly duplicates the function in the Prelude from the Haskell 98 Report
showIntBase b n r | n < 0 = error "Numeric.showInt: can't show negative numbers"
		  | otherwise =
		      let (n',d) = quotRem n b
			  r'     = digit d : r
			  digit d | d < 10     =  toEnum (fromEnum '0' + fromIntegral d)
				  | otherwise  =  toEnum (fromEnum 'A' + fromIntegral d - 10)
		      in  if n' == 0 then r' else showIntBase b n' r'
