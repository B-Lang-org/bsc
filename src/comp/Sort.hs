module Sort(sortLe) where

import Data.List (sortBy)

-- | Sort a list using a less-than-or-equal predicate
sortLe :: (a -> a -> Bool) -> [a] -> [a]
sortLe le = sortBy (\x y -> if le x y then LT else GT) 