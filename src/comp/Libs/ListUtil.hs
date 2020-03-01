-- Copyright (c) 1982-1999 Lennart Augustsson, Thomas Johnsson
-- See LICENSE for the full license.
--
module ListUtil where

mapFst :: (a -> c) -> [(a, b)] -> [(c, b)]
mapFst f xys = [(f x, y) | (x, y) <- xys]
mapSnd :: (b -> c) -> [(a, b)] -> [(a, c)]
mapSnd f xys = [(x, f y) | (x, y) <- xys]

-- Drop repeated (adjacent) elements according to a predicate
dropRepeatsBy :: (a -> a -> Bool) -> [a] -> [a]
dropRepeatsBy _ []  = []
dropRepeatsBy _ [x] = [x]
dropRepeatsBy fn (x:y:rest) | fn x y = dropRepeatsBy fn (x:rest)
                            | otherwise = x:(dropRepeatsBy fn (y:rest))
