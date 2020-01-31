module NumType(opNumT, numOpNames) where
-- common routines for handling numeric types

import Id
import PreIds(idTAdd, idTSub, idTMul, idTDiv, idTLog, idTExp, idTMax, idTMin)
import Util(divC, log2)

-- do a numeric type operation on a list of arguments
-- note that we have to validate that the result is going to
-- to be >= 0 - otherwise it isn't a valid numeric type
opNumT :: Id -> [Integer] -> Maybe Integer
opNumT i [x, y] | i == idTAdd = Just (x + y)
opNumT i [x, y] | i == idTSub && x >= y = Just (x - y)
opNumT i [x, y] | i == idTMul = Just (x * y)
opNumT i [x, y] | i == idTDiv && y /= 0 = Just (divC x y)
opNumT i [x]    | i == idTExp = Just (2^x)
opNumT i [x]    | i == idTLog && x /= 0 = Just (log2 x)
opNumT i [x, y] | i == idTMax = Just (max x y)
opNumT i [x, y] | i == idTMin = Just (min x y)
opNumT _ _      = Nothing

numOpNames = [idTAdd, idTSub, idTMul, idTDiv, idTExp, idTLog, idTMax, idTMin]
