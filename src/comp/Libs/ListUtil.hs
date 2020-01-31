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

breakAt :: (Eq a) => a -> [a] -> ([a], [a])
breakAt _ [] = ([], [])
breakAt x (x':xs) =
	if x == x' then
	    ([], xs)
	else
	    let (ys, zs) = breakAt x xs
	    in  (x':ys, zs)

-- Read a list lazily (in contrast with reads which requires
-- to see the ']' before returning the list.
readListLazily :: (Read a) => String -> [a]
readListLazily cs = 
    case lex cs of
      [("[",cs)] -> readl' cs
      _          -> error "No leading '['"
    where readl' cs  =
                case reads cs of
                  [(x,cs)]  -> x : readl cs
                  []        -> error "No parse for list element"
                  _         -> error "Ambigous parse for list element"
          readl cs =
                case lex cs of
                  [("]",_)]  -> []
                  [(",",cs)] -> readl' cs
                  _          -> error "No ',' or ']'"

mapFst f xys = [(f x, y) | (x, y) <- xys]
mapSnd f xys = [(x, f y) | (x, y) <- xys]

-- Lookup an item in an association list.  Apply a function to it if it is found, otherwise return a default value.
assoc :: (Eq c) => (a -> b) -> b -> [(c, a)] -> c -> b
assoc f d [] x                       = d
assoc f d ((x',y):xys) x | x' == x   = f y
                         | otherwise = assoc f d xys x

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
