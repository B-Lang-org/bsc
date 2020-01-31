{-# LANGUAGE CPP #-}
module Intervals(VSetInteger, vEmpty, vSing, vFromTo, vGetSing,
		vCompRange, vUnion, vIntersect, vNull) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import PPrint


data IVal = IVal Integer Integer
    deriving (Show, Eq)

instance PPrint IVal where
    pPrint d _ (IVal l h) =
	if l == h then
	    text "[" <> pPrint d 0 l <> text "]"
	else
	    text "[" <> pPrint d 0 l <> text ".." <> pPrint d 0 h <> text "]"

-- A set of values is represented as a list of ordered, non-overlapping intervals
newtype VSetInteger = VSet [IVal]
    deriving (Show, Eq)

instance PPrint VSetInteger where
    pPrint d p (VSet is) = pPrint d p is

vNull :: VSetInteger -> Bool
vNull (VSet xs) = null xs -- only if no empty or [h,l] intervals

vEmpty :: VSetInteger
vEmpty = VSet []

-- Complement within a range
vCompRange :: Integer -> Integer -> VSetInteger -> VSetInteger
vCompRange lo hi (VSet [])  = VSet [IVal lo hi]
vCompRange lo hi (VSet is)  = foldr1 vIntersect (map (vCompRangeI lo hi) is)

vCompRangeI :: Integer -> Integer -> IVal -> VSetInteger
vCompRangeI lo hi (IVal l h)    = VSet [IVal lo (l-1), IVal (h+1) hi]

vSing :: Integer -> VSetInteger
vSing i = VSet [IVal i i]

vGetSing :: VSetInteger -> Maybe Integer
vGetSing (VSet [IVal i i']) | i == i' = Just i
vGetSing _ = Nothing

vFromTo ::  Integer -> Integer -> VSetInteger
vFromTo i j = VSet [IVal i j]


vUnionI :: IVal -> VSetInteger -> VSetInteger
vUnionI (IVal l h) (VSet is) = VSet (add l h is)
  where add l h [] = [IVal l h]
	add l h (i@(IVal vl vh) : is) =
		if vl <= l then
		    if vh < l then
			coal (i : add l h is)	-- (l,h) above i
		    else if vh < h then
			add vl h is		-- (l,h) overlaps i
		    else
			i : is			-- (l,h) contained in i
		else if vl > h then
			coal (IVal l h : i : is)-- (l,h) below i
		else
		    if vh <= h then
			add l h is		-- (l,h) contains i
		    else
			add l vh is		-- (l,h) overlaps i
	coal (IVal l1 h1 : IVal l2 h2 : is) | h1+1 == l2 = IVal l1 h2 : is
	coal is = is

vUnion :: VSetInteger -> VSetInteger -> VSetInteger
vUnion (VSet is) vs = foldr vUnionI vs is

vIntersectI :: IVal -> VSetInteger -> VSetInteger
vIntersectI (IVal l h) (VSet is) = VSet (sub l h is)
  where sub l h [] = []
	sub l h (i@(IVal vl vh) : is) =
		if vl <= l then
		    if vh < l then
			sub l h is		-- (l,h) above i
		    else if vh < h then
			IVal l vh : sub l h is	-- (l,h) overlaps i
		    else
			[IVal l h]		-- (l,h) contained in i
		else if vl > h then
			[]
		else
		    if vh <= h then
			i : sub l h is		-- (l,h) contains i
		    else
			[IVal vl h]		-- (l,h) overlaps i

vIntersect :: VSetInteger -> VSetInteger -> VSetInteger
vIntersect (VSet is) vs = foldr (\ i -> vUnion (vIntersectI i vs)) vEmpty is
