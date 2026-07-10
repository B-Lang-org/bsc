-- | SolvedBinds are sets of solved dictionary bindings.
-- They group recursive and non-recursive dictionary bindings separately.
-- At emission time (getRecursiveDefls/getNonRecursiveDefls) the groups are
-- normalized: non-recursive bindings that reference recursive ones are
-- promoted into the recursive group, and the remaining non-recursive
-- bindings are put in dependency order (definitions before uses), as
-- required by the positional scoping of the Cletseq they are emitted into.
module SolvedBinds(SolvedBind, mkSolvedBind, SolvedBinds, Bind,
                   markIncoherent, addBindDeps,
                   sbsEmpty, fromSB, (<++), emptySBs,
                   getRecursiveDefls, getNonRecursiveDefls) where

import Prelude hiding ((<>))

import Data.List(union, partition)
import qualified Data.Map as M
import qualified Data.Set as S

import ErrorUtil(internalError)
import Id
import CSyntax
import CSyntaxTypes()
import CFreeVars(getFVE)
import PPrint
import Subst

-- Dictionary binding representation
-- The CExpr produces the dictionary value by constructing it or referring to another dictionary
type Bind = (Id, Type, CExpr)

mkDefl :: Bind -> CDefl
mkDefl (i, t, e) = CLValueSign (CDefT i [] (CQType [] t) [CClause [] [] e]) []

data SolvedBind = SolvedBind {
  bind :: Bind,
  freeVars :: S.Set Id,
  isRecursive :: Bool
} deriving (Show)

instance PPrint SolvedBind where
  pPrint d p (SolvedBind bind fv isRec) =
    text "SolvedBind" <+> braces (
      text "bind:" <+> pPrint d p bind <> semi <+>
      text "freeVars:" <+> pPrint d p fv <> semi <+>
      text "isRecursive:" <+> pPrint d p isRec
    )

mkSolvedBind :: Bind -> Bool -> SolvedBind
mkSolvedBind b@(_,_,e) isRec =
  SolvedBind { bind = b, freeVars = snd (getFVE e), isRecursive = isRec }

markIncoherent :: SolvedBind -> SolvedBind
markIncoherent sb = sb { bind = mark (bind sb) }
  where mark (i, t, e) = (addIdProp i IdPIncoherent, t, e)

-- Record additional semantic dependencies of a binding that its
-- expression does not reference: the dictionaries of the numeric
-- equalities deferred by the fundep improvement that produced it.
-- The binding is only valid evidence if those equalities hold, so
-- they must be visible to extractClosures' completeness walk (an
-- unresolved equality forbids reuse; a solved one is walked through).
addBindDeps :: [Id] -> SolvedBind -> SolvedBind
addBindDeps is sb = sb { freeVars = foldr S.insert (freeVars sb) is }

-- Collection of bindings categorized by recursion
-- Both lists accumulate newest-first; categorization and dependency
-- order are normalized at emission time (see normalizeSBs)
data SolvedBinds = SolvedBinds {
  recursiveBinds :: [(Bind, S.Set Id)], -- binding and free variables
  nonRecursiveBinds :: [(Bind, S.Set Id)],
  recursiveIds :: S.Set Id,
  nonRecursiveIds :: S.Set Id
} deriving (Show)

instance Types SolvedBinds where
  apSub s sbs = sbs {
    recursiveBinds = [ ((i, apSub s t, apSub s e), fv) | ((i, t, e), fv) <- recursiveBinds sbs ],
    nonRecursiveBinds = [ ((i, apSub s t, apSub s e), fv) | ((i, t, e), fv) <- nonRecursiveBinds sbs ]
  }
  tv sbs = recTVs `union` nonRecTVs
    where recTVs    = tv [ (t, e) | ((_, t, e), _) <- recursiveBinds sbs ]
          nonRecTVs = tv [ (t, e) | ((_, t, e), _) <- nonRecursiveBinds sbs ]

sbsEmpty :: SolvedBinds -> Bool
sbsEmpty (SolvedBinds recs nonrecs _ _) = null recs && null nonrecs

-- Create singleton SolvedBinds from SolvedBind
-- Note: Both self-recursive and non-recursive bindings are independent of accum
-- Self-recursive bindings depend only on themselves, fresh variables, and source EPreds
fromSB :: SolvedBind -> SolvedBinds
fromSB (SolvedBind b@(i, _, _) fv isRec) =
  if isRec
    then SolvedBinds {
      recursiveBinds = [(b, fv)],
      nonRecursiveBinds = [],
      recursiveIds = S.singleton i,
      nonRecursiveIds = S.empty
    }
    else SolvedBinds {
      recursiveBinds = [],
      nonRecursiveBinds = [(b, fv)],
      recursiveIds = S.empty,
      nonRecursiveIds = S.singleton i
    }

infixl 6 <++ -- directional append new <++ old

-- Merge bindings: plain accumulation, newest first.  During solving a
-- binding's rhs references the fresh dictionary ids of its subgoals,
-- which are solved and merged later -- i.e. sit earlier in the
-- newest-first list -- so accumulation order is already close to
-- dependency order.  A binding that discharges against a previously
-- solved (committed) dictionary references an id merged before it;
-- such out-of-chronology references are repaired at emission time
-- (normalizeSBs), not here.
(<++) :: SolvedBinds -> SolvedBinds -> SolvedBinds
new <++ old = SolvedBinds {
    recursiveBinds = recursiveBinds new ++ recursiveBinds old,
    nonRecursiveBinds = nonRecursiveBinds new ++ nonRecursiveBinds old,
    recursiveIds = recursiveIds new `S.union` recursiveIds old,
    nonRecursiveIds = nonRecursiveIds new `S.union` nonRecursiveIds old
  }

-- Normalization for emission.
--
-- Non-recursive bindings are emitted as a Cletseq, whose scoping is
-- positional: a binding may only reference bindings emitted before it.
-- The accumulated newest-first order is already definition-before-use
-- except where a binding references a previously solved dictionary, so
-- emission performs a stable topological repair: bindings keep their
-- accumulated relative order except where a reference forces a
-- definition earlier.
--
-- The Cletseq scopes outside the Cletrec of the recursive bindings, so
-- a non-recursive binding that (transitively) references a recursive
-- binding cannot stay in the Cletseq; it is promoted to the recursive
-- group here.
normalizeSBs :: SolvedBinds -> ([Bind], [Bind])
normalizeSBs sbs = (map fst recs, map fst (orderBinds nonrecs))
  where
    dependsOn ids (_, fv) = not (S.disjoint fv ids)
    promote rids promoted rest =
        case partition (dependsOn rids) rest of
          ([], _) -> (promoted, rest)
          (newly, rest') ->
              let rids' = rids `S.union` S.fromList [ i | ((i, _, _), _) <- newly ]
              in  promote rids' (promoted ++ newly) rest'
    (promoted, nonrecs) = promote (recursiveIds sbs) [] (nonRecursiveBinds sbs)
    recs = recursiveBinds sbs ++ promoted

-- Stable topological order, definitions before uses: repeatedly emit
-- the earliest remaining binding all of whose references are already
-- emitted.  Input that is already dependency-ordered is returned
-- unchanged.
orderBinds :: [(Bind, S.Set Id)] -> [(Bind, S.Set Id)]
orderBinds bs =
    let n = length bs
        idx_bs = zip [(0::Int)..] bs
        bind_at = M.fromList idx_bs
        pos_of_id = M.fromList [ (i, k) | (k, ((i, _, _), _)) <- idx_bs ]
        -- positions this binding references (within the group, sans self)
        deps k fv = [ j | i <- S.toList fv,
                          Just j <- [M.lookup i pos_of_id], j /= k ]
        dep_lists = [ (k, deps k fv) | (k, (_, fv)) <- idx_bs ]
        dependents = M.fromListWith (++) [ (j, [k]) | (k, ds) <- dep_lists, j <- ds ]
        indeg0 = M.fromList [ (k, length ds) | (k, ds) <- dep_lists ]
        ready0 = S.fromList [ k | (k, 0) <- M.toList indeg0 ]
        emit d (rdy, ind) =
            let c = M.findWithDefault 1 d ind - 1
            in  (if c == 0 then S.insert d rdy else rdy, M.insert d c ind)
        go ready indeg acc
          | S.null ready =
              if length acc == n
                then reverse acc
                else internalError $
                       "SolvedBinds.orderBinds: dependency cycle among " ++
                       "non-recursive bindings:\n" ++
                       ppReadable [ b | (b, _) <- bs ]
          | otherwise =
              let (k, ready') = S.deleteFindMin ready
                  (ready'', indeg') =
                      foldr emit (ready', indeg)
                            (M.findWithDefault [] k dependents)
              in  go ready'' indeg' (bind_at M.! k : acc)
    in  go ready0 indeg0 []

emptySBs :: SolvedBinds
emptySBs = SolvedBinds {
             recursiveBinds = [],
             nonRecursiveBinds = [],
             recursiveIds = S.empty,
             nonRecursiveIds = S.empty
           }

instance PPrint SolvedBinds where
  pPrint d p (SolvedBinds recs nonrecs _ _) =
    text "SolvedBinds" <+> braces (
      text "rec:" <+> pPrint d p recs <> semi <+>
      text "nonRec:" <+> pPrint d p nonrecs
    )

getRecursiveDefls :: SolvedBinds -> [CDefl]
getRecursiveDefls = map mkDefl . fst . normalizeSBs

getNonRecursiveDefls :: SolvedBinds -> [CDefl]
getNonRecursiveDefls = map mkDefl . snd . normalizeSBs
