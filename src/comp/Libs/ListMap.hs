-- Copyright (c) 1982-1999 Lennart Augustsson, Thomas Johnsson
-- See LICENSE for the full license.
--
module ListMap(
	ListMap,
	toList, fromList,
	length,
	null,
	lookup, lookupWithDefault, lookupWithDefaultBy, lookupBy
	) where

--import Prelude

-- @@ Lists as finite mappings.

type ListMap a b = [(a, b)]

toList :: ListMap a b -> [(a, b)]
toList l = l

fromList :: [(a, b)] -> ListMap a b
fromList l = l

lookupWithDefault :: (Eq a) => [(a, b)] -> b -> a -> b
lookupWithDefault [] d _ = d
lookupWithDefault ((x,y):xys) d x' = if x == x' then y else lookupWithDefault xys d x'

lookupWithDefaultBy :: (a -> a -> Bool) -> [(a, b)] -> b -> a -> b
lookupWithDefaultBy _ [] d _ = d
lookupWithDefaultBy match ((x,y):xys) d x' = if (match x x') then y
                                             else lookupWithDefaultBy match xys d x'
lookupBy :: (a -> a -> Bool) -> [(a, b)] -> a -> Maybe b
lookupBy _ [] _ = Nothing
lookupBy match ((x,y):xys) x' = if (match x x') then Just y
                                else lookupBy match xys x'
