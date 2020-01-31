module SCC(scc, getCycles, tsort, Graph) where

-- Compute strongly connected components.
-- The graph is represented as a list of (node, neighbour list) pairs.
-- A list of list of nodes is returned, each connected.
-- Original code by John Launchbury.

import Data.List(partition, sort)
import qualified Data.Map as M
import qualified Data.Set as S
import Balanced hiding (lookup)

import ErrorUtil(internalError)


type Node v = (v, [v])
type Graph v = [Node v]

{-
type NMap node = [Node node]
mFromList xs = xs
mLookup x xys = lookup x xys
-}
type NMap node = M.Map node [node]
mFromList xs = M.fromList xs
mLookup x m = M.lookup x m

{-
type NSet node = [node]
sElem x s = elem x s
sAdd x s = x:s
sEmpty = []
-}
-- Using OrdSet seems to be slower than lists

sElem x s = S.member x s
sAdd x s = S.insert x s
sEmpty = S.empty

sccEdge :: (Ord node) => NMap node -> NMap node -> [node] -> [[node]]
sccEdge ns rns vs
  = snd (span_tree rrng sEmpty []
                   (snd (dfs erng sEmpty [] vs) )
        )
  where

    rrng w = find w rns
    erng w = find w ns

    span_tree r vs ns []   = (vs,ns)
    span_tree r vs ns (x:xs)
        | x `sElem` vs = span_tree r vs ns xs
        | otherwise    = case dfs r (sAdd x vs) [] (r x) of (vs', ns') -> span_tree r vs' ((x:ns'): ns) xs

    dfs r vs ns []   = (vs,ns)
    dfs r vs ns (x:xs) 
	| x `sElem` vs = dfs r vs ns xs
	| otherwise    = case dfs r (sAdd x vs) [] (r x) of (vs', ns') ->       dfs r vs' ((x:ns')++ns) xs

rev :: (Ord node) => [Node node] -> NMap node
rev ns = M.fromListWith (++) [ (d, [s]) | (s, ds) <- ns, d <- ds ]

find :: (Ord node) => node -> NMap node -> [node]
find x m =
    case mLookup x m of
    Just xs -> xs
    Nothing -> []

----

scc :: (Ord node) => [Node node] -> [[node]]
scc ns = sccEdge (mFromList ns) (rev ns) (map fst ns)

getCycles :: (Ord node) => [Node node] -> [[node]]
getCycles xs =
	case otsort xs of
	    Left cs -> cs
	    Right _ -> []

------

otsort :: (Ord node) => [Node node] -> Either [[node]] [node]
otsort ns =
	let es = [(x,y) | (x, ys) <- ns, y <- ys]
	    vs = map fst ns
	    sccs = sccEdge (mFromList ns) (rev ns) vs
	    isCyclic [] = internalError "otsort isCyclic []"
	    isCyclic [v] = isElem v es
	    isCyclic _ = True
	    isElem v [] = False
	    isElem v ((x,y):xys) = v == x && v == y  ||  isElem v xys
	in  case partition isCyclic sccs of
		([], noncycs) -> Right (concat noncycs)
		(cycs, _) -> Left cycs


------

-- sort a graph topologically
-- note that this is *not* a stable sort
tsort :: (Show node, Ord node) => [Node node] -> Either [[node]] [node]
tsort = ntsort
-- reverts to otsort if ntsort looks buggy (see note below)
-- tsort = otsort

-- XXX ntsort [(1, [2, 3, 4]), (5, [3, 2, 4])] = Left [[1,5]]
-- XXX fixed by falling back to otsort, but should be fixed in ntsort?
ntsort :: (Show node, Ord node) => [Node node] -> Either [[node]] [node]
ntsort g =
    let psq = fromOrdList [ n :-> length ns | (n, ns) <- sort g ]
	m = M.fromListWith (++) [ (d, [s]) | (s, ds) <- g, d <- ds ]
	get n = case M.lookup n m of Just ns -> ns; Nothing -> []
    in	{- loop get psq [] -} -- XXX: leads to buggy cycles
	case loop get psq [] of
	Right ns -> Right ns
	Left _ -> otsort g  -- revert to old version to get accurate cycles


type TSPSQ node = PSQ node Int

loop :: (Ord node) => (node -> [node]) -> TSPSQ node -> [node] -> Either [[node]] [node]
loop inputs psq ns =
    case minView psq of
    Empty -> Right (reverse ns)
    Min (n :-> 0) psq' -> loop inputs (decrList (inputs n) psq') (n:ns)
    _ -> Left [map key (toOrdList psq)]

decrList :: (Ord node) => [node] -> TSPSQ node -> TSPSQ node
decrList ns pqs = foldr decr pqs ns
  where decr n pqs = adjust (subtract 1) n pqs

------

{-
-- Consistency check
chkTsort :: (Show node, Ord node) => [Node node] -> Either [[node]] [node] -> Either [[node]] [node]
chkTsort g r@(Left _) = r
chkTsort g r@(Right ons) = cloop S.empty ons
  where cloop _ [] = r
	cloop s (n:ns) = if all (`S.member` s) xs then cloop (S.insert n s) ns else internalError ("chkTsort: " ++ show g ++ "\n" ++ show ons ++ "\n" ++ show (n, xs))
		where xs = find n m
	m = M.fromList g
-}
