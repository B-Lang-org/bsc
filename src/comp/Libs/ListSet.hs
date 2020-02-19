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

add :: (Eq a) => a -> [a] -> [a]
add x xs = if x `elem` xs then xs else x:xs

toList = id

fromList = id
