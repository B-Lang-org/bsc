{-# LANGUAGE CPP #-}
module GraphMap (GraphMap, empty, null,
                 addVertex, addEdge, addWeakEdge, addEdgeWith,
                 deleteVertex, deleteEdge, deleteVertices, filterVertices,
                 vertices, neighbors, getOutEdgeMap,
                 lookup, member, notMember, fromList, toList, toVAList,
                 ncc) where

import Prelude hiding (null, lookup
#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
                      , (<>)
#endif
                      )
import Data.Maybe (maybeToList)
import qualified Data.Map as M
import PPrint hiding(empty)


-- represent a graph of vertices of type v, with weight w
-- The graph is stored as a Map (M) indexed by Vertex, with
-- each Vertex containing another Map which represent its outbound edges.

-- edges carry weights
newtype GraphMap v w = GraphMap (M.Map v (M.Map v w))

empty :: GraphMap v w
empty = GraphMap (M.empty)

null :: GraphMap v w -> Bool
null (GraphMap m) = M.null m

-- insert empty vertex if not already there
addVertex :: (Ord v) => GraphMap v w -> v -> GraphMap v w
addVertex (GraphMap m) v = GraphMap $ M.insert v M.empty m

-- insert an edge overwriting an existing one
addEdge :: (Ord v) => GraphMap v w -> (v, v, w) -> GraphMap v w
addEdge (GraphMap m) (v1,v2,w) = --addEdgeWith const g e
    let alterFn Nothing   = Just (M.singleton v2 w)
        alterFn (Just m') = Just (M.insert v2 w m')
    in  GraphMap $ M.alter alterFn v1 m

-- insert an edge, but do NOT overwrite an existing edge, if any
addWeakEdge :: (Ord v) => GraphMap v w -> (v, v, w) -> GraphMap v w
addWeakEdge g e = addEdgeWith (flip const) g e

-- insert an edge with a combining function
addEdgeWith :: (Ord v) => (w -> w -> w) ->
                          GraphMap v w -> (v, v, w) -> GraphMap v w
addEdgeWith combFn (GraphMap m) (v1, v2, w) =
    let alterFn Nothing   = Just (M.singleton v2 w)
        alterFn (Just m') = Just (M.insertWith combFn v2 w m')
    in  GraphMap $ M.alter alterFn v1 m

deleteVertex :: (Ord v) => GraphMap v w -> v -> GraphMap v w
deleteVertex (GraphMap m) v = GraphMap $ fmap (M.delete v) (M.delete v m)

deleteVertices :: (Ord v) => GraphMap v w -> [v] -> GraphMap v w
deleteVertices = foldr (flip deleteVertex)

deleteEdge :: (Ord v) => GraphMap v w -> (v,v) -> GraphMap v w
deleteEdge g@(GraphMap m) (v1, v2) =
    let adjustFn m' = M.delete v2 m'
    in  GraphMap $ M.adjust adjustFn v1 m

filterVertices :: (Ord v) => GraphMap v w -> (v -> Bool) -> GraphMap v w
filterVertices g f = deleteVertices g vs
    where vs = filter (not . f) $ vertices g

lookup :: (Ord v) => (v,v) -> GraphMap v w -> Maybe w
lookup (v1,v2) (GraphMap m) = M.lookup v1 m >>= M.lookup v2

member :: (Ord v) => (v,v) -> GraphMap v w -> Bool
member (v1,v2) (GraphMap m) = case M.lookup v1 m of
                                  Just m2 -> M.member v2 m2
                                  Nothing -> False

notMember :: (Ord v) => (v,v) -> GraphMap v w -> Bool
notMember (v1,v2) (GraphMap m) = case M.lookup v1 m of
                                  Just m2 -> M.notMember v2 m2
                                  Nothing -> True

vertices :: GraphMap v w -> [v]
vertices (GraphMap m) = M.keys m

neighbors :: (Ord v) => GraphMap v w -> v -> [v]
neighbors (GraphMap m) v = maybeToList (M.lookup v m) >>= M.keys

getOutEdgeMap :: (Ord v) => GraphMap v w -> v -> Maybe (M.Map v w)
getOutEdgeMap (GraphMap m) v = M.lookup v m

-- vertex adjacency list with weights
fromList :: (Ord v) => [(v,[(v,w)])] -> GraphMap v w
fromList vvws = GraphMap $ foldr (flip add) M.empty vvws
    where add m (v,vws) = M.insert v (M.fromList vws) m

toList :: GraphMap v w -> [(v,[(v,w)])]
toList (GraphMap m) = [(v,M.toList m') | (v,m') <- M.toList m]

-- produces a vertex adjacency list with no weights (suitable for use with code in SCC.hs)
toVAList :: GraphMap v w -> [(v,[v])]
toVAList (GraphMap m) = [(v1,[v2 | (v2,_) <- M.toList m']) | (v1,m') <- M.toList m]

instance (PPrint v, PPrint w) => PPrint (GraphMap v w) where
    pPrint d i (GraphMap m) = vsep [pPrint d 0 v1 <>
                                    vsep [text " ->" <+> pPrint d 0 v2 <+> text ":" <+> pPrint d 0 w
                                          | (v2, w) <- M.toList m']
                                    | (v1, m') <- M.toList m]

-- non-connected components
ncc :: Ord v => GraphMap v w -> [[v]]
ncc g = case (vertices g) of
          [] -> [[]]
          (v:vs) -> let ncvs = v:[v' | v' <- vs, (v,v') `member` g]
                    in  ncvs:(ncc $ deleteVertices g ncvs)
