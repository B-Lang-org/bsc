module DynamicMap ( Map
                  , empty, singleton, insert
                  , lookup, findWithDefault
                  , union, split, fromList, toList
                  , adjust
                  ) where

import Prelude hiding (lookup)

-- temporary until findLTE, etc. are in Data.Map
import qualified Data.Map as M

-- This is a map which tracks changing values.
-- It associates keys with different values at different times
-- and supports looking up the value most-recently associated
-- with a key at any point in time.  It also allows the time
-- resolution before a particular point to be discarded to save
-- space when it is no longer required.

-- Map from each key to a map from times to the value of the key
-- at that time.
type Map t k a = M.Map k (M.Map t a)

-- Construct an empty map
empty :: Map t k a
empty = M.empty

-- Construct a map with a single initial value for a key
singleton :: t -> k -> a -> Map t k a
singleton at key val = M.singleton key (M.singleton at val)

-- Insert a value for a key at a particular point in time.
insert :: (Ord t, Ord k) => t -> k -> a -> Map t k a -> Map t k a
insert at key val m = M.insertWith (M.union) key (M.singleton at val) m

-- Return the value most recently associated with the key at or before
-- a specific time, along with the time of its association.
-- If there is no such value, returns Nothing.
lookup :: (Ord t, Ord k) => t -> k -> Map t k a -> Maybe (t,a)
lookup at key m =
    do m' <- M.lookup key m
       M.lookupLE at m'

-- Returns the value most recently associated with the key at or before
-- a specific time.  If there is no such value, returns the default.
findWithDefault :: (Ord t, Ord k) => a -> t -> k -> Map t k a -> a
findWithDefault dflt at key m =
    case (lookup at key m) of
      (Just (_,v)) -> v
      Nothing      -> dflt

-- Union two maps together, combining the changes in both maps.
-- If the two maps have a change to the same the key at the same time,
-- the value in the left map is retained and the other is discarded.
union :: (Ord t, Ord k) => Map t k a -> Map t k a -> Map t k a
union m1 m2 = M.unionWith M.union m1 m2

-- Split a map into two parts: one containing all entries before a
-- given time and one containing all entries at or after that time.
-- The value of each key at the split time is recorded in the second
-- map.  The effect of this is to retain the value of the key
-- at and beyond the given time but to throw away information
-- on the changes which led up to that value.
split :: Ord t => t -> (a -> a) -> Map t k a -> (Map t k a, Map t k a)
split at f m =
    let m' = M.map splitUp m
    in (M.map fst m', M.map snd m')
    where splitUp x = let (before,exact,after) = M.splitLookup at x
                          after' = case exact of
                                     (Just v) -> M.insert at v after
                                     Nothing  -> if (M.null before)
                                                 then after
                                                 else let (_,v) = M.findMax before
                                                      in M.insert at (f v) after
                      in (before,after')

-- Build a map from a list of (time,key,value) triples.
fromList :: (Ord t, Ord k) => [(t,k,a)] -> Map t k a
fromList xs = foldl (\m (at,key,val) -> insert at key val m) empty xs

-- Convert a map into a list of (time,key,value) triples.
toList :: Map t k a -> [(t,k,a)]
toList m = concatMap (\(key,m') -> map (addKey key) (M.toList m')) (M.toList m)
    where addKey k (t,v) = (t,k,v)

-- Adjust the time-to-value map for a given key
adjust :: (Ord k) => ((M.Map t a) -> (M.Map t a)) -> k -> Map t k a -> Map t k a
adjust f key m = M.alter f' key m
  where f' Nothing = let sm' = f M.empty
                     in if (M.null sm') then Nothing else Just sm'
        f' (Just sm) = let sm' = f sm
                       in if (M.null sm') then Nothing else Just sm'
