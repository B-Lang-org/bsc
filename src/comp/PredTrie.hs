{-# LANGUAGE CPP #-}
module PredTrie(
    QueryElem(..),
    PredTrie,
    buildPredTrie,
    lookupPredTrie,
    allItems,
    predQuery,
    overlapProbeQuery,
) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Data.List(sortBy)

import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Error(internalError)
import CType(Type(..), TyCon(..), TyVar, leftTyCon)
import TypeOps(numOpNames, strOpNames)
import Pred(Pred(..), Class(inputPositions), expandSyn)

-- ---------------------------------------------------------------------------
-- PredTrie
--
-- A nested-map trie indexed by the head TyCon (via leftTyCon) of each
-- type argument.  Each level corresponds to one type argument position.
-- Keys in the map are Maybe TyCon:
--   Just tc  -- this instance has constructor tc at this position
--   Nothing  -- this instance has a type variable at this position
-- ---------------------------------------------------------------------------

data PredTrie a = Leaf [a]
                | Node (M.Map (Maybe TyCon) (PredTrie a))

-- ---------------------------------------------------------------------------
-- Building the trie
-- ---------------------------------------------------------------------------

-- | Build a sorted trie from items that contain predicates.  The class (and
-- hence its functional dependencies) is taken from the first item's predicate,
-- so the caller need not pass the fundep matrix separately.
-- The comparator is applied at construction time so that lookupPredTrie
-- returns items in the caller's preferred order.  The comparator should place
-- more-specific items before less-specific ones: lookupPredTrie already
-- returns items from more-specific branches (concrete constructor) before
-- less-specific branches (type variable), so the leaf ordering should be
-- consistent with that — more-specific items first.
-- The item type 'a' is unrestricted, so this works for Inst, EPred, VPred,
-- or any wrapper.
buildPredTrie :: (a -> a -> Ordering) -> (a -> Pred) -> [a] -> PredTrie a
buildPredTrie _   _      []           = Leaf []
buildPredTrie cmp toPred items@(x:_) =
    let IsIn c _ = toPred x
    in sortTrieLeaves cmp $ buildRaw (\y -> predTrieKey (inputPositions c) (toPred y)) items

buildRaw :: (a -> [Maybe TyCon]) -> [a] -> PredTrie a
buildRaw keyOf items@(x:_) =
    foldr (insertItem keyOf) (emptyForKey (keyOf x)) items
buildRaw _ [] = internalError "PredTrie.buildRaw: empty list"

-- An empty trie with the right depth for a given key.
emptyForKey :: [Maybe TyCon] -> PredTrie a
emptyForKey []    = Leaf []
emptyForKey (_:_) = Node M.empty

-- Insert one item into the trie.
insertItem :: (a -> [Maybe TyCon]) -> a -> PredTrie a -> PredTrie a
insertItem keyOf item = go (keyOf item)
  where
    go []     (Leaf ys) = Leaf (item : ys)
    go (k:ks) (Node m)  =
        let sub  = M.findWithDefault (emptyForKey ks) k m
            sub' = go ks sub
        in  Node (M.insert k sub' m)
    go key trie = internalError ("PredTrie.insertItem: key/trie depth mismatch" ++
                                 " (key remaining=" ++ show (length key) ++
                                 ", trie=" ++ trieShape trie ++ ")")

trieShape :: PredTrie a -> String
trieShape (Leaf xs) = "Leaf[" ++ show (length xs) ++ "]"
trieShape (Node _)  = "Node"

-- | Sort the items in each leaf using a comparison function.
-- Use this once at build time so that lookupPredTrie returns items in order.
sortTrieLeaves :: (a -> a -> Ordering) -> PredTrie a -> PredTrie a
sortTrieLeaves cmp (Leaf xs) = Leaf (sortBy cmp xs)
sortTrieLeaves cmp (Node m)  = Node (M.map (sortTrieLeaves cmp) m)

-- ---------------------------------------------------------------------------
-- Querying the trie
--
-- Each type argument position in the query is classified as one of:
--
--   Free  -- an unbound metavariable; could unify with any type.
--            Probe ALL branches of the trie at this level.
--
--   Bound -- a rigid/skolem type variable; cannot be unified away.
--            Only items with a variable at this position can match.
--            Probe only the Nothing branch.
--
--   Con tc -- the head constructor is tc (possibly applied to args).
--             Items with the same constructor OR a variable can match.
--             Probe the Just tc branch AND the Nothing branch.
-- ---------------------------------------------------------------------------

data QueryElem = Free | Bound | Con TyCon
    deriving (Show, Eq)

-- | Collect all items whose trie key is compatible with the given query.
-- The result is a superset of matching instances; the type checker's
-- unification will filter to the actual matches.
lookupPredTrie :: [QueryElem] -> PredTrie a -> [a]
lookupPredTrie []     (Leaf xs) = xs
lookupPredTrie []     (Node _)  = internalError "PredTrie.lookupPredTrie: query too short"
lookupPredTrie (_:_)  (Leaf []) = []   -- empty trie at any depth: no instances
lookupPredTrie (_:_)  (Leaf _)  = internalError "PredTrie.lookupPredTrie: query too long (items at leaf)"
lookupPredTrie (q:qs) (Node m)  =
    case q of
        -- Concrete constructor: check same-constructor instances first, then
        -- catch-alls (Nothing branch).
        Con tc  -> descend (Just tc) ++ descend Nothing
        -- Rigid variable: only catch-all instances can match.
        Bound   -> descend Nothing
        -- Free metavar: any instance could match.  Return concrete-constructor
        -- branches before the Nothing (catch-all) branch so that more-specific
        -- instances are encountered first by the type checker's scan.
        -- (M.elems would put Nothing first since Nothing < Just in Map order.)
        Free    -> let (_, m_nothing, justBranches) = M.splitLookup Nothing m
                   in  concatMap (lookupPredTrie qs) (M.elems justBranches)
                       ++ maybe [] (lookupPredTrie qs) m_nothing
  where
    descend k = maybe [] (lookupPredTrie qs) (M.lookup k m)

-- | Collect ALL items stored in the trie (e.g. for getInsts).
allItems :: PredTrie a -> [a]
allItems (Leaf xs) = xs
allItems (Node m)  = concatMap allItems (M.elems m)

-- ---------------------------------------------------------------------------
-- Trie key and query building for class predicates
--
-- Instances (or givens) are stored in a PredTrie keyed by the head TyCon
-- (via leftTyCon) of each type argument at the pure-input positions.
-- A position is pure-input when it is False (input) in ALL fundep directions.
-- Nothing = type variable at that position; Just tc = concrete constructor.
--
-- The btvs argument to predQuery controls whether rigid type variables in the
-- predicate produce Bound queries (probing only the Nothing branch) or Free
-- queries (probing all branches).  Pass the actual bound type variable set
-- when Bound is semantically correct (e.g. a givens pool); pass S.empty to
-- treat all type variables as Free.
-- ---------------------------------------------------------------------------

-- Trie key for a predicate at the given pre-computed positions.
-- Type synonyms are expanded so that keys are in normal form, matching the
-- post-normT predicate types used at query time.
predTrieKey :: [Int] -> Pred -> [Maybe TyCon]
predTrieKey positions (IsIn _ ts) =
    [ leftTyCon (expandSyn (ts !! i)) | i <- positions ]

-- | Probe query for overlap checking: given an instance's predicate, build a
-- query that finds all instances that might overlap with it.  Variable positions
-- in the instance key (Nothing) become Free so that cross-branch overlaps are
-- found; concrete positions (Just tc) become Con tc.
-- Unlike predQuery this does not apply isTFunTyCon: for overlap detection we
-- want to find all candidates including those with numeric-literal heads.
overlapProbeQuery :: Pred -> [QueryElem]
overlapProbeQuery p@(IsIn c _) =
    [ case k of { Just tc -> Con tc; Nothing -> Free }
    | k <- predTrieKey (inputPositions c) p ]

-- | Build a query for a predicate, using the class's pre-computed
-- inputPositions.  Output positions (in the fallback case where all positions
-- are outputs in some fundep direction) use Free; input positions use
-- mkQueryElem, which returns Con tc for concrete non-function heads, Free for
-- type variables and unevaluated type functions.  Pass S.empty for btvs to
-- suppress Bound (e.g. for instance lookup where Bound would hide
-- non-matching concrete instances needed for incoherence detection).
predQuery :: S.Set TyVar -> Pred -> [QueryElem]
predQuery btvs (IsIn c ts) =
    [ mkQueryElem btvs (ts !! i) | i <- inputPositions c ]

-- ---------------------------------------------------------------------------
-- Building queries from predicates
-- ---------------------------------------------------------------------------

-- | True when a TyCon is an unevaluated numeric or string type function
-- (TAdd, TMul, TLog, etc.).  Type-function heads cannot be resolved to a
-- concrete constructor at query time, so queries at those positions must
-- probe ALL trie branches (Free) to avoid missing instances that have a
-- concrete-number head (e.g. VectorTreeReduce 1, VectorTreeReduce 2).
isTFunTyCon :: TyCon -> Bool
isTFunTyCon (TyCon { tcon_name = i }) = i `elem` numOpNames ++ strOpNames
isTFunTyCon _                          = False

-- | Classify one type argument of the predicate being resolved.
-- A type-function head (TAdd, TLog, etc.) is treated as Free so that
-- all candidate instances are returned for unification-based filtering.
-- Pass 'S.empty' for btvs to suppress Bound (never emit Bound in queries).
mkQueryElem :: S.Set TyVar -> Type -> QueryElem
mkQueryElem btvs t =
    case leftTyCon t of
        Just tc | not (isTFunTyCon tc) -> Con tc
        Just _                         -> Free  -- unevaluated type function
        Nothing -> case headVar t of
            Just tv | tv `S.member` btvs -> Bound
            _                            -> Free
  where
    -- Walk left through TAp to find the head variable, if any.
    headVar (TVar tv)  = Just tv
    headVar (TAp f _)  = headVar f
    headVar _          = Nothing

