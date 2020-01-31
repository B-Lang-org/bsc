-- Copyright (c) 1982-1999 Lennart Augustsson, Thomas Johnsson
-- See LICENSE for the full license.
--
module ListSet where

import Data.List((\\))

-- @@ Lists as sets.

type ListSet a = [a]

empty = []

singleton x = [x]

-- Union of sets as lists.
union :: (Eq a) => [a] -> [a] -> [a]
union xs ys = xs ++ (ys \\ xs)

unionMany :: (Eq a) => [[a]] -> [a]
unionMany ss = foldr union [] ss

add :: (Eq a) => a -> [a] -> [a]
add x xs = if x `elem` xs then xs else x:xs

addMany :: (Eq a) => [a] -> [a] -> [a]
addMany xs ys = foldr add ys xs

deleteMany :: (Eq a) => [a] -> [a] -> [a]
deleteMany xs ys = foldr delete xs ys
  where delete			:: (Eq a) => a -> [a] -> [a]
        delete x []		= []
        delete x (y:ys)		= if x == y then ys else delete x ys


toList = id

fromList = id

-- Intersection of sets as lists.
intersect :: (Eq a) => [a] -> [a] -> [a]
intersect xs ys = [x | x<-xs, x `elem` ys]

minus :: (Eq a) => [a] -> [a] -> [a]
minus = (\\)

isSingleton [x] = True
isSingleton _ = False

intersecting xs ys = not (null (intersect xs ys))

isSubsetOf x y = null (x \\ y)
