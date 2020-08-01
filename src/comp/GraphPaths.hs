-- |The GraphPaths module provides an efficient mechanism for
-- recording the set of paths between nodes in a directed graph.
-- The GraphPaths routines operate in the IO monad because they
-- use unboxed IO arrays internally for efficiency.
module GraphPaths ( -- *Types
                    GraphPathInfo
                    -- *Functions
                  , computeGraphPaths
                  , hasPath
                  , addPath
                  , isAcyclic
                  ) where

import Control.Monad (when,unless)

import Data.Array.IO
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Word
import Data.Bits

-- import Debug.Trace(traceM)

-- |A packed bit matrix
data BitMatrix =
    BitMatrix { rows :: Word32
              , cols :: Word32
              , words_per_row :: Word32
              , arr :: IOUArray Word32 Word32
              }

-- |Find the word index and bit within the word corresponding
-- |to the [r,c] bit of the matrix
convIdx :: BitMatrix        -- ^ the boolean matrix
        -> Word32           -- ^ row index
        -> Word32           -- ^ column index
        -> (Word32,Int)     -- ^ word index and bit offset within the array
convIdx mat r c =
    let start_of_row = r * (words_per_row mat)
        (word_idx,offset) = c `quotRem` 32
    in (start_of_row + word_idx, fromIntegral offset)

-- |Internal helper function to extract the [r,c] bit from a matrix
isBitSet :: BitMatrix -- ^the boolean matrix
         -> Word32    -- ^row of entry to test
         -> Word32    -- ^column of entry to test
         -> IO Bool   -- ^result is true if mat[r,c] is set
isBitSet mat r c =
    do let (word_idx,offset) = convIdx mat r c
       word <- readArray (arr mat) word_idx
       return $ testBit word offset

{-
-- |Internal debug function to print a matrix
print_matrix :: BitMatrix -> IO ()
print_matrix mat =
    do let w = cols mat
           h = rows mat
       putStrLn $ (show w) ++ "x" ++ (show h) ++ " matrix"
       bools <- sequence $ map sequence [ [ isBitSet mat r c | c <- [0..(w-1)] ] | r <- [0..(h-1)] ]
       let xs = map (map (\b -> if b then 'x' else ' ')) bools
       mapM_ print xs
-}

-- |Internal helper function to update the matrix with new paths
updatePaths :: BitMatrix -- ^the boolean matrix
            -> Word32    -- ^the index of the source node
            -> Word32    -- ^the index of the target node
            -> IO ()
updatePaths mat src dst =
    -- when adding a path, we must:
    -- set the dst bit and OR-in the dst row to the src row (the paths from src to dst and all nodes reachable from dst)
    -- set the dst bit and OR-in the dst row to all rows with the src bit set (the paths from nodes which reach src to dst and all nodes reachable from dst)
    do let start_of_dst_row = dst * (words_per_row mat)
           (dst_word_idx,dst_bit_offset0) = dst `quotRem` 32
           dst_bit_offset = fromIntegral dst_bit_offset0
           (src_word_idx,src_bit_offset0) = src `quotRem` 32
           src_bit_offset = fromIntegral src_bit_offset0
           the_arr = arr mat
           or_one_word :: Word32 -> Word32 -> IO ()
           or_one_word sor n = do w1 <- readArray the_arr (sor + n)
                                  w2 <- readArray the_arr (start_of_dst_row + n)
                                  writeArray the_arr (sor + n) (w1 .|. w2)
           or_one_row sor = mapM_ (or_one_word sor) [0..((words_per_row mat) - 1)]
           update_row :: Bool -> Word32 -> IO ()
           update_row force r = do let start_of_row = r * (words_per_row mat)
                                   w0 <- readArray the_arr (start_of_row + src_word_idx)
                                   when (force || (testBit w0 src_bit_offset)) $
                                        do w <- readArray the_arr (start_of_row + dst_word_idx)
                                           unless (testBit w dst_bit_offset) $
                                                  do writeArray the_arr (start_of_row + dst_word_idx) (setBit w dst_bit_offset)
                                                     or_one_row start_of_row
       update_row True src
       sequence_ [ update_row False r | r <- [0..((rows mat)-1)], r /= src ]

-- |The GraphPathInfo records a map from node values to matrix
-- indices, along with a matrix of paths between nodes.  If node "A"
-- maps to index_A and node "B" maps to index_B, then if the
-- bit[indexA,indexB] is set in the matrix it indicates there is a
-- directed path from node "A" to node "B" in the graph.
data GraphPathInfo a =
    GraphPathInfo { -- |map from nodes to matrix indices
                    node_idx_map :: M.Map a Word32
                    -- |packed boolean matrix of directed paths
                  , path_matrix  :: BitMatrix
                  }

-- |Given a directed graph in a map-of-sets representation, computes
-- all of the directed paths and returns and a GraphPathInfo
computeGraphPaths :: (Ord a) =>
                     M.Map a (S.Set a)    -- ^input graph (as a map-of-sets)
                  -> IO (GraphPathInfo a) -- ^resulting path graph summary
computeGraphPaths g =
    do -- build the node-to-index map
       let idx_map = M.fromList (zip (M.keys g) [0..])
           num_nodes = fromIntegral (M.size idx_map)
           num_words = (num_nodes + 31) `quot` 32
           arr_bound = if (num_nodes == 0) then 0 else (num_nodes*num_words-1)
       the_arr <- newArray (0,arr_bound) 0
       let edge_list = [ (i1, i2)
                       | (v,wset) <- M.toList g
                       , let i1 = (M.!) idx_map v
                       , w <- S.toList wset
                       , let i2 = (M.!) idx_map w
                       ]
           mat = BitMatrix { rows = num_nodes
                           , cols = num_nodes
                           , words_per_row = num_words
                           , arr = the_arr
                           }
       mapM_ (uncurry (updatePaths mat)) edge_list
       return $ GraphPathInfo idx_map mat

-- |Test if a directed path exists from a source node to a destination node
hasPath :: (Ord a) =>
           GraphPathInfo a -- ^the graph path summary to use for path testing
        -> a               -- ^the source node
        -> a               -- ^the destination node
        -> IO Bool         -- ^result is True when a directed path exists from source to destination
hasPath g src dst =
    -- testing for the existence of a directed path simply involves
    -- checking if the bit at [src,dst] is set in the path matrix
    isBitSet (path_matrix g) ((M.!) (node_idx_map g) src) ((M.!) (node_idx_map g) dst)

-- |Update the graph path summary information with the existence of a
-- new path, including all paths implied by the combinations of the
-- new path with existing paths.
addPath :: (Ord a) =>
           GraphPathInfo a -- ^original graph path summary
        -> a               -- ^the source node
        -> a               -- ^the destination node
        -> IO ()
addPath g src dst =
    do let src_idx = (M.!) (node_idx_map g) src
           dst_idx = (M.!) (node_idx_map g) dst
       updatePaths (path_matrix g) src_idx dst_idx

-- |Test for the absence of any cyclic paths in the graph
isAcyclic :: GraphPathInfo a -- ^graph path summary
          -> IO Bool         -- ^result is True when there are no cyclic paths in the graph
isAcyclic g =
    -- if there is a cycle in the graph, then some bit along the
    -- diagonal from (0,0) must be set, indicating a node has a
    -- directed path back to itself
    do let num_nodes = fromIntegral (M.size (node_idx_map g))
       cycles <- mapM (uncurry (isBitSet (path_matrix g))) [(idx,idx) | idx <- [0..(num_nodes - 1)]]
       return $ not (or cycles)
