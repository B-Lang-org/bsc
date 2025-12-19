-- | SolvedBinds are sets of solved dictionary bindings.
-- They group recursive and non-recursive dictionary bindings separately, ensure there are
-- no references to recursive bindings from non-recursive bindings and keep non-recursive
-- bindings in topologically sorted order.
module SolvedBinds(SolvedBind(..), SolvedBinds, Bind,
                   sbsEmpty, fromSB, (<++), emptySBs,
                   getRecursiveDefls, getNonRecursiveDefls) where

import Prelude hiding ((<>))

import Data.List(union, partition)
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
  isRecursive :: Bool
} deriving (Show)

instance PPrint SolvedBind where
  pPrint d p (SolvedBind bind isRec) =
    text "SolvedBind" <+> braces (
      text "bind:" <+> pPrint d p bind <> semi <+>
      text "isRecursive:" <+> pPrint d p isRec
    )

-- Collection of bindings categorized by recursion
-- nonRecursiveBinds are maintained in topologically sorted order
data SolvedBinds = SolvedBinds {
  recursiveBinds :: [Bind],
  nonRecursiveBinds :: [Bind],
  recursiveIds :: S.Set Id,
  nonRecursiveIds :: S.Set Id
} deriving (Show)

instance Types SolvedBinds where
  apSub s sbs = sbs {
    recursiveBinds = [ (i, apSub s t, apSub s e) | (i, t, e) <- recursiveBinds sbs ],
    nonRecursiveBinds = [ (i, apSub s t, apSub s e) | (i, t, e) <- nonRecursiveBinds sbs ]
  }
  tv sbs = recTVs `union` nonRecTVs
    where recTVs    = tv [ (t, e) | (_, t, e) <- recursiveBinds sbs ]
          nonRecTVs = tv [ (t, e) | (_, t, e) <- nonRecursiveBinds sbs ]

sbsEmpty :: SolvedBinds -> Bool
sbsEmpty (SolvedBinds recs nonrecs _ _) = null recs && null nonrecs

-- Create singleton SolvedBinds from SolvedBind
-- Note: Both self-recursive and non-recursive bindings are independent of accum
-- Self-recursive bindings depend only on themselves, fresh variables, and source EPreds
fromSB :: SolvedBind -> SolvedBinds
fromSB (SolvedBind b@(i, _, _) isRec) =
  if isRec
    then SolvedBinds {
      recursiveBinds = [b],
      nonRecursiveBinds = [],
      recursiveIds = S.singleton i,
      nonRecursiveIds = S.empty
    }
    else SolvedBinds {
      recursiveBinds = [],
      nonRecursiveBinds = [b],
      recursiveIds = S.empty,
      nonRecursiveIds = S.singleton i
    }

infixl 6 <++ -- directional append new <++ old

-- Merge bindings, maintaining categorization and topological order
-- CRITICAL: Always merge as (new <++ old), never swap!
-- Invariant: new.nonRec doesn't depend on old
(<++) :: SolvedBinds -> SolvedBinds -> SolvedBinds
new <++ old
    -- Check invariant here
    | any (dependsOn oldAllIds) (nonRecursiveBinds new) =
        internalError $ "SolvedBinds invariant violated: new depends on old!\n" ++
                        "new: " ++ ppReadable new ++ "\n" ++
                        "old: " ++ ppReadable old
    | noBadDeps = result
    | otherwise = internalError $ "nonRecursive depending on recursive in result: " ++
                                  ppReadable (new, old, result)
    where dependsOn s (_,_,e) = not $ S.disjoint (snd $ getFVE e) s
          oldAllIds = recursiveIds old `S.union` nonRecursiveIds old
          promoteTransitively [] nonRecs = ([], nonRecs)
          promoteTransitively promoted nonRecs = (promoted ++ transitivePromoted, finalNonRecs)
            where promotedIds = S.fromList [ i | (i, _, _) <- promoted ]
                  (newlyPromoted, stillNonRecs) = partition (dependsOn promotedIds) nonRecs
                  (transitivePromoted, finalNonRecs) = promoteTransitively newlyPromoted stillNonRecs
          (newlyRec, stillNonRec) = uncurry promoteTransitively $
                                    partition (dependsOn $ recursiveIds new) (nonRecursiveBinds old)
          -- Updates for cached sets
          newRecIds = S.fromList [i | (i, _, _) <- recursiveBinds new ++ newlyRec]
          nowNotNonRecIds = S.fromList [ i | (i, _ , _)  <- newlyRec ]
          result = SolvedBinds {
                      recursiveBinds = newlyRec ++ recursiveBinds new ++ recursiveBinds old,
                      nonRecursiveBinds = nonRecursiveBinds new ++ stillNonRec,
                      recursiveIds = newRecIds `S.union` recursiveIds old,
                      nonRecursiveIds = nonRecursiveIds new `S.union` (nonRecursiveIds old `S.difference` nowNotNonRecIds)
                   }
          noBadDeps = all (not . dependsOn (recursiveIds result)) (nonRecursiveBinds result)

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
getRecursiveDefls = map mkDefl . recursiveBinds

getNonRecursiveDefls :: SolvedBinds -> [CDefl]
getNonRecursiveDefls = map mkDefl . nonRecursiveBinds
