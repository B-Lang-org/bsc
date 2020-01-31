-- Copyright (c) 1982-1999 Lennart Augustsson, Thomas Johnsson
-- See LICENSE for the full license.
--
module ListMap(
	ListMap,
	empty, singleton, union, unionMany, add, addKeep,
	-- (//), union_C, unionMany_C, addMany_C, add_C,
	-- intersect, delete, deleteMany, minus, 
	amap,
	-- partition, filter, foldl, foldr
	toList, fromList,
	length,
	null, isSingleton,
	-- intersecting, subset
	elems, indices,
	-- (!!),
	lookup, lookupWithDefault, --, lookupWithContinuation
        lookupWithDefaultBy, lookupBy
	) where

--import Prelude

-- @@ Lists as finite mappings.

type ListMap a b = [(a, b)]

empty :: ListMap a b
empty = []

singleton :: (a, b) -> ListMap a b
singleton xy = [xy]

union :: (Eq a) => ListMap a b -> ListMap a b -> ListMap a b
union xs ys = foldr add ys xs

unionMany :: (Eq a) => [ListMap a b] -> ListMap a b
unionMany = foldr union empty

add :: (Eq a) => (a, b) -> ListMap a b -> ListMap a b
add xy [] = [xy]
add xy@(x, y) (xy'@(x',_):xys) =
	if x==x' then xy:xys else xy' : add xy xys

addKeep :: (Eq a) => (a, b) -> ListMap a b -> ListMap a b
addKeep xy@(x, y) xys = 
	case lookup x xys of
	Just _ -> xys
	Nothing -> xy : xys

--instance Functor (ListMap a) where
amap :: (b -> c) -> ListMap a b -> ListMap a c
amap f xys = [ (x, f y) | (x, y) <- xys ]

toList :: ListMap a b -> [(a, b)]
toList l = l

fromList :: [(a, b)] -> ListMap a b
fromList l = l

isSingleton :: ListMap a b -> Bool
isSingleton [x] = True
isSingleton _ = False

elems :: ListMap a b -> [b]
elems xys = [ y | (x, y) <- xys]

indices :: ListMap a b -> [a]
indices xys = [ x | (x, y) <- xys ]

--lookup :: (Eq a) => a -> ListMap a b -> Maybe b
--lookup x xys = Prelude.lookup x xys

{-
(!!) :: (Eq a) => ListMap a b -> a -> b
t !! x = case lookup x t of Nothing -> error "ListMap.!: index not found"; Just y -> y
-}

--null :: ListMap a b -> Bool
--null l = Prelude.null l

--length :: ListMap a b -> Int
--length l = Prelude.length l

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
