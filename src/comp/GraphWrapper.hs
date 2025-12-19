module GraphWrapper (
                  Graph,
                  makeGraph, addNodes, addEdge, addEdgesWithNodes,
                  graphNodes, graphEdges, graphNeighbors,
                  findCycles, tSort, tSortInt,
                  findReachables, findReachablesIO,
                  hasPath,
                  findPath,
                  topSort,
                  toDotFormat
                  ) where

-- ==================================================
-- GraphWrapper
--
-- This package extends GHC's Data.Graph package to be more accessible.
--
-- GHC's package uses a contiguous range of Int as nodes, for fast
-- indexing into arrays.  This util package provides functions for
-- converting back and forth to this representation.
--
-- This package also defines a cycle detection function based on
-- the available graph functions, since one is not available.
--
-- ==================================================

import Data.Array
import Data.Array.IO
import System.IO.Unsafe
import Data.Maybe( mapMaybe)
import qualified Data.List as L
import qualified Data.Graph as G
import qualified Data.Map as M
import qualified Data.Set as S

import PPrint
import Eval
import Util(map_insertMany, fromJustOrErr)

-- ===============
-- Graph data type

-- A graph is:
--  * the GHC graph (a table mapping a key to the keys of neighbor nodes)
--     note that the GHC graph is mutable so addEdge can be efficient
--     we use unsafe hackery to get the immutable graph the GHC libraries expect
--  * mapping of nodes to their key
--  * mapping of keys to node
data Graph nodeT = Graph (IOArray G.Vertex [G.Vertex]) (M.Map nodeT G.Vertex) (Array G.Vertex nodeT) Int

instance (PPrint a) => PPrint (Graph a) where
    pPrint d p g =
        let ns = graphNodes g
            es = graphEdges g
        in  text "Graph" <+> text "{" $+$
            nest 2 (text "nodes" <+> text "=" <+>
                    pPrint d p ns <+> text "," $+$
                    text "edges" <+> text "=" <+>
                    pPrint d p es) $+$
            text "}"

instance (NFData a) => NFData (Graph a) where
    rnf g = rnf2 (graphNodes g) (graphEdges g)

-- ===============
-- Graph construction

vToInt :: (Ord nodeT) => Graph nodeT -> nodeT -> G.Vertex
vToInt (Graph _ ordmap _ _) x = fromJustOrErr "vToInt" (M.lookup x ordmap)

intToV :: Graph nodeT -> G.Vertex -> nodeT
intToV (Graph _ _ lookuptable _) x = lookuptable!x

makeGraph :: (Ord nodeT) => [nodeT] -> [(nodeT,nodeT)] -> IO (Graph nodeT)
makeGraph ns es = do
    let size = length ns
        pairs = zip ns [0..]
        ordmap = M.fromList pairs
        vToInt' x = fromJustOrErr "makeGraph"  (M.lookup x ordmap)
        int_es = mapPair vToInt' es
        bnds = (0, size - 1)
        graph0 = G.buildG bnds int_es
        lookuptable = listArray bnds ns
    graph <- thaw graph0
    return (Graph graph ordmap lookuptable size)

-- ===============
-- Selection functions

graphNodes :: Graph nodeT -> [nodeT]
graphNodes (Graph _ _ lookuptable _) = elems lookuptable

graphEdges :: Graph nodeT -> [(nodeT,nodeT)]
graphEdges g@(Graph graph _ lookuptable _) =
    let g_immut = unsafePerformIO (freeze graph) in
    mapPair (intToV g) (G.edges g_immut)

graphNeighbors :: (Ord nodeT) => Graph nodeT -> nodeT -> [nodeT]
graphNeighbors g@(Graph graph _ _ _) n =
  let neighborInts = unsafePerformIO (readArray graph (vToInt g n))
  in map (intToV g) neighborInts

mapPair :: (a -> b) -> [(a, a)] -> [(b, b)]
mapPair f ps = [ (f p1, f p2) | (p1, p2) <- ps ]

-- ===============
-- Graph manipulation

-- Note, this is not a fast operation, so use sparingly
addNodes :: Ord nodeT => Graph nodeT -> [nodeT] -> IO (Graph nodeT)
addNodes g@(Graph graph ordmap lookuptable size) ns = do
    let nodesSet = M.keysSet ordmap
    let new_nodes = filter (not . ((flip S.member) nodesSet)) ns
    let new_size = size + (length new_nodes)
    let new_bnds = (0, new_size - 1)
    let new_map = map_insertMany (zip new_nodes [size..]) ordmap
    let new_table = listArray new_bnds (elems lookuptable ++ new_nodes)
    old_elems <- getElems graph
    new_graph <- newListArray new_bnds (old_elems ++ map (const []) new_nodes)
    return (Graph new_graph new_map new_table new_size)

-- Note, this requires that the nodes of all the edges already be in the graph
-- Use addEdgesWithNodes if that is not the case
addEdge :: Ord nodeT => Graph nodeT -> (nodeT, nodeT) -> IO ()
addEdge g@(Graph graph _ _ _) (v1, v2) = do
  let i1 = vToInt g v1
  let i2 = vToInt g v2
  old_list <- readArray graph i1
  writeArray graph i1 (L.insert i2 old_list)

-- this could be more efficient if we coalesced the edges before adding them
addEdgesWithNodes :: Ord nodeT => Graph nodeT -> [(nodeT,nodeT)] -> IO (Graph nodeT)
addEdgesWithNodes g es = do
    let new_nodes = L.nub ((map fst es) ++ (map snd es))
    g' <- addNodes g new_nodes
    mapM_ (addEdge g') es
    return g'

-- ===============
-- Find cycles

-- This function returns sets of nodes which are strongly connected.
-- The set may include more than one loop.
findCycles :: Graph nodeT -> IO [[nodeT]]
findCycles g@(Graph graph ordmap lookuptable _) = do
    g_assocs <- getAssocs graph
    let ns = elems lookuptable
    let (keys, neighbors) = unzip g_assocs
    let graph_as_list = zip3 ns keys neighbors

    let components = G.stronglyConnComp graph_as_list

    let f (G.AcyclicSCC _) = Nothing
        f (G.CyclicSCC vs) = Just vs

    return (mapMaybe f components)

-- ===============
-- Topological sort

tSort :: (Ord nodeT) => [(nodeT, [nodeT])] -> Either [[nodeT]] [nodeT]
tSort g =
   let nodes = map fst g
       pairs = zip nodes ([0..]::[Int])
       ordmap = M.fromList pairs
       nodeToInt x = fromJustOrErr "tSort" (M.lookup x ordmap)
       convEdge (e1, e2s) = (e1, nodeToInt e1, map nodeToInt e2s)
       g' = map convEdge g
       scc = G.stronglyConnComp g'
       acyclic = [ v  | G.AcyclicSCC v <- scc ]
       cycles  = [ vs | G.CyclicSCC vs <- scc ]
   in
       case (cycles) of
         [] -> Right acyclic
         _  -> Left cycles

{-
-- For data types with an Int conversion function, using that
-- conversion preserves any order implicit in that mapping
-- XXX the default ordering appears to be the reverse of the numbering
tSortByInt :: (nodeT -> Int) -> [(nodeT, [nodeT])] -> Either [[nodeT]] [nodeT]
tSortByInt nodeToInt g =
   let convEdge (n1, n2s) = (n1, nodeToInt n1, map nodeToInt n2s)
       g' = map convEdge g
       scc = G.stronglyConnComp g'
       acyclic = [ v  | G.AcyclicSCC v <- scc ]
       cycles  = [ vs | G.CyclicSCC vs <- scc ]
   in
       case (cycles) of
         [] -> Right acyclic
         _  -> Left cycles
-}

-- For Ints, we can sort them directly
-- XXX is it inefficient to define this as "tSortByInt id" ?
tSortInt :: [(Int, [Int])] -> Either [[Int]] [Int]
tSortInt g = case cycles of
             [] -> Right acyclic
             _  -> Left cycles

  where g'  = [(v, v, es) | (v, es) <- g ]
        scc = G.stronglyConnComp g'
        acyclic = [ v  | G.AcyclicSCC v <- scc ]
        cycles  = [ vs | G.CyclicSCC vs <- scc ]


-- ===============
-- Find reachable nodes (with paths)

-- Takes a graph and a list of starting nodes, and returns a list of
-- the nodes reachable from those starting points (paired with the path).
findReachablesIO :: Ord a => Graph a -> [a] -> IO ([[ (a,[a]) ]])
findReachablesIO g@(Graph graph ordmap lookuptable _) vs = do
    let int_vs = map (vToInt g) vs
    let pairToV (a,path) = (intToV g a, map (intToV g) path)
    g_immut <- freeze graph
    return (map (map pairToV . reachable_withPath g_immut) int_vs)

findReachables :: Ord a => Graph a -> [a] -> [[ (a, [a])]]
findReachables g vs = unsafePerformIO $ findReachablesIO g vs

-- ----------

-- This is like "preorderF" from Data.Graph, except we record the path

-- the path is constructed in reverse
preorder_withPath :: [a] -> G.Tree a -> [(a,[a])]
preorder_withPath path (G.Node a ts) = (a,(a:path)) : preorderF_withPath (a:path) ts

preorderF_withPath :: [a] -> G.Forest a -> [(a,[a])]
preorderF_withPath path ts = concat (map (preorder_withPath path) ts)

-- This is like "reachable" from Data.Graph, except with path included

reachable_withPath :: G.Graph -> G.Vertex -> [(G.Vertex,[G.Vertex])]
reachable_withPath g v = preorderF_withPath [] (G.dfs g [v])

-- ----------

-- Check if a path exists, but don't return it
hasPath :: Ord a => Graph a -> a -> a -> Bool
hasPath g@(Graph graph ordmap lookuptable _) in_v out_v =
    let in_int = vToInt g in_v
        out_int = vToInt g out_v
        g_immut = unsafePerformIO (freeze graph)
    in G.path g_immut in_int out_int

-- The path list starts with in_v and ends with out_v
findPath :: Ord a => Graph a -> a -> a -> Maybe [a]
findPath g@(Graph graph ordmap lookuptable _) in_v out_v =
    let
        in_int = vToInt g in_v
        out_int = vToInt g out_v
        g_immut = unsafePerformIO (freeze graph)
    in case (lookup out_int (reachable_withPath g_immut in_int)) of
         Nothing -> Nothing
         Just path -> Just (map (intToV g) (reverse path))

-- ===============
-- Topological sort

topSort :: Graph nodeT -> [nodeT]
topSort g@(Graph graph ordmap lookuptable _) =
     map (intToV g) (G.topSort g_immut)
  where g_immut = unsafePerformIO (freeze graph)

-- ===============
-- Conversion to "dot" (GraphViz) format

toDotFormat :: String -> Graph nodeT -> (nodeT -> String) -> String
toDotFormat name g@(Graph graph _ _ _) toString =
    let g_immut = unsafePerformIO (freeze graph)
        ns = G.vertices g_immut
        es = G.edges g_immut
        label n = "[label=\"" ++ (toString (intToV g n)) ++ "\"]"
    in unlines $ [ "digraph " ++ name ++ " {"
                 , "// nodes"
                 ] ++
                 [ (show n) ++ " " ++ (label n) | n <- ns ] ++
                 [ ""
                 , "//edges"
                 ] ++
                 [ (show u) ++ " -> " ++ (show v) | (u,v) <- es ] ++
                 [ "}" ]

-- ===============
