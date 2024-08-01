module TypeOps(opNumT, numOpNames, opStrT, strOpNames) where
-- common routines for handling numeric and string types

import Id
import PreIds(idTAdd, idTSub, idTMul, idTDiv, idTLog, idTExp, idTMax, idTMin, idTApp)
import Util(divC, log2)
import FStringCompat(FString, concatFString)

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

numOpNames :: [Id]
numOpNames = [idTAdd, idTSub, idTMul, idTDiv, idTExp, idTLog, idTMax, idTMin]

opStrT :: Id -> [FString] -> Maybe FString
opStrT i xs | i == idTApp = Just $ concatFString xs
opStrT _ _ = Nothing

strOpNames :: [Id]
strOpNames = [idTApp]
