module GraphUtil (
		  extractOneCycle,
		  extractOneCycle_gmap,
		  extractOneCycle_map,
		  findPathEdges,
		  reverseMap
		  ) where

-- ==================================================
-- GraphUtil
--
-- These are useful functions which span more than one
-- type of graph (GraphMap, Data.Graph, etc)
--
-- ==================================================

import Data.Maybe(isJust)

import Util(tailOrErr, initOrErr)
import ErrorUtil
import PPrint

import qualified GraphMap as G
import qualified GraphWrapper as GW

import qualified Data.Map as M

import System.IO.Unsafe

-- ===============

-- find one cyclic (non-repeating) path in the SCC
extractOneCycle :: (Ord nodeT, PPrint nodeT) =>
                   [(nodeT,nodeT)] -> [nodeT] -> [nodeT]
extractOneCycle edges cycle@(a:b:_) =
    let nodes = cycle
	g = unsafePerformIO (GW.makeGraph nodes edges)

	intErr s = internalError ("extractOneCyle: " ++ s)

	findPath x y =
	    case (GW.findReachables g [x]) of
		[ps] -> case (lookup y ps) of
			    Just path -> reverse path
			    Nothing -> intErr ("lookup: " ++ ppReadable ps)
		x -> intErr ("reachables: " ++ ppReadable x)

	path_a_to_b = findPath a b
	path_b_to_a = findPath b a
	-- join the two paths, but with no duplicate node b in the middle
	cycle_path =
	    path_a_to_b ++
	    tailOrErr ("extractOneCycle: path_b_to_a does not contain b:"
		       ++ ppReadable path_b_to_a)
	              path_b_to_a
    in  cycle_path
extractOneCycle _ [a] = [a] -- a cycle from a node to itself
extractOneCycle _ [] =
    internalError ("extractOneCycle: cycle has no nodes")


-- extract a cycle given a GraphMap
extractOneCycle_gmap :: (Ord nodeT, PPrint nodeT) =>
		        G.GraphMap nodeT edgeT -> [nodeT] -> [nodeT]
extractOneCycle_gmap gmap cycle =
    let edges = [ (r, r') | r <- cycle, r' <- cycle, r' /= r,
			    isJust (G.lookup (r,r') gmap) ]
    in  extractOneCycle edges cycle


-- extract a cycle given a Map
extractOneCycle_map :: (Ord nodeT, PPrint nodeT) =>
		       M.Map nodeT [nodeT] -> [nodeT] -> [nodeT]
extractOneCycle_map m cycle =
    let edges = [ (r, r') | r <- cycle,
	                    let rs = M.findWithDefault [] r m,
			    r' <- rs,
			    r' `elem` cycle ]
    in  extractOneCycle edges cycle


-- ===============

-- Given a list of nodes in a circular path (where the start and end
-- nodes in the list are the same), this returns a list of pairs of
-- nodes in the path along with the edge for that pair (from the GraphMap).
findPathEdges :: (Ord nodeT, PPrint nodeT) =>
                 G.GraphMap nodeT edgeT -> [nodeT] ->
                 [((nodeT, nodeT), edgeT)]
findPathEdges gmap path =
    let
	-- the path without the start node (which is same as the end)
	path_minus_start =
	    tailOrErr
	        ("findPathEdges: path_minus_start" ++ ppReadable path)
		path
	-- the path without the end node (which is same as the start)
	path_minus_end =
	    initOrErr
	        ("findPathEdges: path_minus_end: " ++ ppReadable path)
		path
	-- all the edges in the circular path
	path_pairs = zip path_minus_end path_minus_start
	-- lookup which shouldn't fail
	getEdge pair =
	    case (G.lookup pair gmap) of
		Nothing -> internalError ("findPathEdges: lookup failed: " ++
					  ppReadable pair)
		Just edge -> (pair,edge)
    in
	map getEdge path_pairs


-- ===============

-- takes a list of edges (of any kind) and produces a reverse map
reverseMap :: (Ord a) => M.Map a [a] -> M.Map a [a]
reverseMap m =
    let edges = M.toList m
	startEdge (e1,_) = (e1, [])
	reverseEdge (e1,es) = [(e2,[e1]) | e2 <- es]
	-- make sure that the map has "[]" for nodes with no ingoing edges
	-- XXX alternatively, users of this map could treat lookup failure
	-- XXX as meaning the empty list
	rev_edges = map startEdge edges ++
	            concatMap reverseEdge edges
    in M.fromListWith (++) rev_edges

-- ===============
