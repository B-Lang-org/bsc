module CondTree(
    CondTree(..),
    isNil,
    map_cond,
    enumerate,
    simplify,
) where

-- Representation of a condition tree in which conditions
-- recursively subdivide a set into a number of leaf
-- categories.  For example, this is used to capture the
-- pattern of conditions that lead the various sets of method
-- calls in a rule using the type:
--  CondTree AExpr (Set (String,MethodId))
data CondTree c a = If c [CondTree c a]
                  | Leaf a
                  | Nil
  deriving Show

isNil :: CondTree c a -> Bool
isNil Nil = True
isNil _   = False

-- Map conditions, preserving structure and leaf values
map_cond :: (c -> d) -> CondTree c a -> CondTree d a
map_cond f (If cond xs) = If (f cond) (map (map_cond f) xs)
map_cond _ (Leaf x)     = Leaf x
map_cond _ Nil          = Nil

-- Simplify a condition tree by mapping conditions onto a Bool.
-- If a condition maps to true, remove the condition but keep
-- the subtrees.  If a condition maps to false, remove the condition
-- and all subtrees.  If a condition maps to neither true, or false,
-- keep the condition and the subtrees.  This also removes conditions
-- with no subtrees.
simplify :: (c -> Maybe Bool) -> CondTree c a -> [CondTree c a]
simplify pred (If cond xs) =
    case (pred cond) of
      (Just True)  -> subs
      (Just False) -> []
      Nothing      -> if (null subs) then [] else [If cond subs]
    where subs = concatMap (simplify pred) xs
simplify _ Nil = []
simplify _ x   = [x]

-- Enumerate all paths from the root to a leaf
enumerate :: CondTree c a -> [([c],a)]
enumerate Nil = []
enumerate (Leaf x) = [([],x)]
enumerate (If cond xs) = [ ((cond:cs),x)
                         | (cs,x) <- concatMap enumerate xs
                         ]
