module EquivalenceClass
    (EquivClasses,
     empty, insert,
     equate,
     isEqual,
     classes,
     showEC
    ) where

import qualified Data.Map as M

type EquivClasses a = M.Map a (Maybe a)

empty :: EquivClasses a
empty = M.empty

insert :: (Ord a) => a -> EquivClasses a -> EquivClasses a
insert x ec = case M.lookup x ec of
             Just _  -> ec
             Nothing -> M.insert x Nothing ec

representative :: (Ord a) => EquivClasses a -> a -> a
representative ec x = case M.lookup x ec of
                        Just (Just y) -> representative ec y
                        otherwise     -> x

equate :: (Ord a) => a -> a -> EquivClasses a -> EquivClasses a
equate x y ec = let ec'    = insert x ec
                    ec''   = insert y ec'
                    x_root = representative ec'' x
                    y_root = representative ec'' y
                in if x_root == y_root
                   then ec
                   else M.insert x_root (Just y_root) ec''

classes :: (Ord a) => EquivClasses a -> [[a]]
classes ec = let pairs = [ (representative ec x, [x]) | x <- M.keys ec ]
             in M.elems (M.fromListWith (++) pairs)

isEqual :: (Ord a) => EquivClasses a -> a -> a -> Bool
isEqual ec x y = (representative ec x) == (representative ec y)

showEC :: (Ord a, Show a) => (EquivClasses a) -> String
showEC ec = "(EquivClasses " ++ show (classes ec) ++ ")"
