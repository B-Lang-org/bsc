module Bag (
            Bag,
            empty, singleton,
            insert, delete,
            fromList, toList,
            Bag.null,
            difference, union, intersection,
            removeIntersection
           ) where

import qualified Data.Map as M

type Count = Int

unity :: Count
unity = 1

data Bag k = Bag (M.Map k Count) deriving Show

empty :: Bag k
empty = Bag $ M.empty

singleton :: k -> Bag k
singleton k = Bag $ M.singleton k unity

-- insert one element
insert :: (Ord k) => k -> Bag k -> Bag k
insert k (Bag m) = Bag $ M.insertWith (+) k unity m

-- delete one element
delete :: (Ord k) => k -> Bag k -> Bag k
delete k (Bag m) =
    let updateFn 1 = Nothing
        updateFn n = Just (n-1)
    in  Bag $ M.update updateFn k m

fromList :: Ord k => [k] -> Bag k
fromList ks = Bag $ M.fromListWith (+) (zip ks (repeat unity))

toList :: Bag k -> [k]
toList (Bag m) = concatMap (\(k,c) -> replicate c k)
                 $ M.toList m

null :: Bag k -> Bool
null (Bag m) = M.null m
               -- other functions remove the node when it becomes 0
               -- so we don't need this check:
               -- || (all (== 0) (M.elems m))

difference :: Ord k => Bag k -> Bag k -> Bag k
difference (Bag big) (Bag small) =
  let
      diff :: Count -> Count -> Maybe Count
      diff x y | x > y = Just (x-y)
               | otherwise = Nothing
  in
      Bag $ M.differenceWith diff big small

union :: Ord k => Bag k -> Bag k -> Bag k
union (Bag big) (Bag small) = Bag $ M.unionWith (+) big small

intersection :: Ord k => Bag k -> Bag k -> Bag k
intersection (Bag m1) (Bag m2) =
    let intersectFn x y = min x y
        m' = M.intersectionWith intersectFn m1 m2
    in  Bag $ M.filter (> 0) m'

removeIntersection :: Ord k => Bag k -> Bag k -> (Bag k, Bag k)
removeIntersection b1 b2 =
    let i = intersection b1 b2
    in  (difference b1 i, difference b2 i)

instance (Eq k) => Eq (Bag k) where
  (Bag m1) == (Bag m2)  =  (m1 == m2)

