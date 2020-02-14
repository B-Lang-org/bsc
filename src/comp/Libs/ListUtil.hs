-- Copyright (c) 1982-1999 Lennart Augustsson, Thomas Johnsson
-- See LICENSE for the full license.
--
module ListUtil where

-- Repeatedly extract (and transform) values until a predicate hold.  Return the list of values.
unfoldr :: (a -> (b, a)) -> (a -> Bool) -> a -> [b]
unfoldr f p x | p x       = []
	      | otherwise = y:unfoldr f p x'
			      where (y, x') = f x

chopList :: ([a] -> (b, [a])) -> [a] -> [b]
chopList f l = unfoldr f null l

mapFst :: (a -> c) -> [(a, b)] -> [(c, b)]
mapFst f xys = [(f x, y) | (x, y) <- xys]
mapSnd :: (b -> c) -> [(a, b)] -> [(a, c)]
mapSnd f xys = [(x, f y) | (x, y) <- xys]

-- Split a list up into groups separated by elements which satisfy
-- some predicate (ie., delimiters).  The delimiters are not included
-- in the result.
-- Ex: splitBy (== '.') "a.b.dir..x." gives ["a","b","dir","","x",""] 
splitBy :: (a -> Bool) -> [a] -> [[a]]
splitBy _ [] = []
splitBy p  l = helper l []
  where helper []     s             = [reverse s]
        helper (x:xs) s | p x       = [reverse s] ++ (helper xs [])
                        | otherwise = helper xs (x:s)

-- Drop repeated (adjacent) elements according to a predicate
dropRepeatsBy :: (a -> a -> Bool) -> [a] -> [a]
dropRepeatsBy _ []  = []
dropRepeatsBy _ [x] = [x]
dropRepeatsBy fn (x:y:rest) | fn x y = dropRepeatsBy fn (x:rest)
                            | otherwise = x:(dropRepeatsBy fn (y:rest))
