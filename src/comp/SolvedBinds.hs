-- | SolvedBinds are sets of solved dictionary bindings.
-- They group recursive and non-recursive dictionary bindings separately, ensure there are
-- no references to recursive bindings from non-recursive bindings and keep non-recursive
-- bindings in topologically sorted order.
module SolvedBinds(SolvedBind, mkSolvedBind, SolvedBinds, Bind,
                   markIncoherent, isIncoherent, solvedClass,
                   DirectIncoherence(..), addDirectIncoherence,
                   sbsEmpty, fromSB, (<++), emptySBs,
                   recursiveBinds, nonRecursiveBinds,
                   bindClasses, directIncoherences,
                   getRecursiveDefls, getNonRecursiveDefls,
                   getIncoherentIds, computeTransitiveIncoherent) where

import Prelude hiding ((<>))

import Data.List(union, partition)
import Data.Maybe(listToMaybe)
import qualified Data.Set as S
import qualified Data.Map.Strict as M

import ErrorUtil(internalError)
import Id
import CSyntax
import CSyntaxTypes()
import CFreeVars(getFVE)
import PPrint
import Position
import Pred(Class, Pred)
import Subst

-- Dictionary binding representation
-- The CExpr produces the dictionary value by constructing it or referring to another dictionary
type Bind = (Id, Type, CExpr)

mkDefl :: Bind -> CDefl
mkDefl (i, t, e) = CLValueSign (CDefT i [] (CQType [] t) [CClause [] [] e]) []

-- Root cause of a direct incoherent match, for use in transitive-incoherence warnings.
data DirectIncoherence = DirectIncoherence {
  diPred :: Pred,    -- the pred being satisfied (after final substitution)
  diInst :: Pred,    -- the incoherent instance head (after final substitution)
  diPos  :: Position -- position where the direct match occurred
} deriving (Show)

data SolvedBind = SolvedBind {
  bind :: Bind,
  freeVars :: S.Set Id,
  isRecursive :: Bool,
  isIncoherent :: Bool,
  solvedClass :: Maybe Class  -- the class this bind resolves (for allowIncoherent check)
} deriving (Show)

instance PPrint SolvedBind where
  pPrint d p (SolvedBind bind fv isRec isInc _) =
    text "SolvedBind" <+> braces (
      text "bind:" <+> pPrint d p bind <> semi <+>
      text "freeVars:" <+> pPrint d p fv <> semi <+>
      text "isRecursive:" <+> pPrint d p isRec <> semi <+>
      text "isIncoherent:" <+> pPrint d p isInc
    )

mkSolvedBind :: Bind -> Bool -> SolvedBind
mkSolvedBind b@(_,_,e) isRec =
  SolvedBind { bind = b, freeVars = snd (getFVE e), isRecursive = isRec,
               isIncoherent = False, solvedClass = Nothing }

markIncoherent :: SolvedBind -> SolvedBind
markIncoherent sb = sb { bind = mark (bind sb), isIncoherent = True }
  where mark (i, t, e) = (addIdProp i IdPIncoherent, t, e)

-- Collection of bindings categorized by recursion
-- nonRecursiveBinds are maintained in topologically sorted order
data SolvedBinds = SolvedBinds {
  recursiveBinds :: [(Bind, S.Set Id)], -- binding and free variables
  nonRecursiveBinds :: [(Bind, S.Set Id)],
  recursiveIds :: S.Set Id,
  nonRecursiveIds :: S.Set Id,
  incoherentIds :: S.Set Id,
  bindClasses :: M.Map Id (Maybe Class),           -- class per bind (for allowIncoherent check)
  directIncoherences :: M.Map Id DirectIncoherence -- root cause per directly-incoherent bind
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
sbsEmpty sbs = null (recursiveBinds sbs) && null (nonRecursiveBinds sbs)

-- Create singleton SolvedBinds from SolvedBind
-- Note: Both self-recursive and non-recursive bindings are independent of accum
-- Self-recursive bindings depend only on themselves, fresh variables, and source EPreds
fromSB :: SolvedBind -> SolvedBinds
fromSB (SolvedBind b@(i, _, _) fv isRec isInc cls) =
  if isRec
    then SolvedBinds {
      recursiveBinds = [(b, fv)],
      nonRecursiveBinds = [],
      recursiveIds = S.singleton i,
      nonRecursiveIds = S.empty,
      incoherentIds = if isInc then S.singleton i else S.empty,
      bindClasses = M.singleton i cls,
      directIncoherences = M.empty
    }
    else SolvedBinds {
      recursiveBinds = [],
      nonRecursiveBinds = [(b, fv)],
      recursiveIds = S.empty,
      nonRecursiveIds = S.singleton i,
      incoherentIds = if isInc then S.singleton i else S.empty,
      bindClasses = M.singleton i cls,
      directIncoherences = M.empty
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
    where dependsOn s ((_,_,_), fv) = not $ S.disjoint fv s
          oldAllIds = recursiveIds old `S.union` nonRecursiveIds old
          promoteTransitively [] nonRecs = ([], nonRecs)
          promoteTransitively promoted nonRecs = (promoted ++ transitivePromoted, finalNonRecs)
            where promotedIds = S.fromList [ i | ((i, _, _), _) <- promoted ]
                  (newlyPromoted, stillNonRecs) = partition (dependsOn promotedIds) nonRecs
                  (transitivePromoted, finalNonRecs) = promoteTransitively newlyPromoted stillNonRecs
          (newlyRec, stillNonRec) = uncurry promoteTransitively $
                                    partition (dependsOn $ recursiveIds new) (nonRecursiveBinds old)
          -- Updates for cached sets
          newRecIds = S.fromList [i | ((i, _, _), _) <- recursiveBinds new ++ newlyRec]
          nowNotNonRecIds = S.fromList [ i | ((i, _ , _), _)  <- newlyRec ]
          result = SolvedBinds {
                      recursiveBinds = newlyRec ++ recursiveBinds new ++ recursiveBinds old,
                      nonRecursiveBinds = nonRecursiveBinds new ++ stillNonRec,
                      recursiveIds = newRecIds `S.union` recursiveIds old,
                      nonRecursiveIds = nonRecursiveIds new `S.union` (nonRecursiveIds old `S.difference` nowNotNonRecIds),
                      incoherentIds = incoherentIds new `S.union` incoherentIds old,
                      bindClasses = bindClasses new `M.union` bindClasses old,
                      directIncoherences = directIncoherences new `M.union` directIncoherences old
                   }
          noBadDeps = all (not . dependsOn (recursiveIds result)) (nonRecursiveBinds result)

-- Compute the transitive closure of incoherence across all bindings: any
-- binding whose free variables reference an incoherent Id is itself incoherent.
-- Works across both recursive and non-recursive bindings simultaneously.
-- Marks newly-incoherent binding Ids with IdPIncoherent and updates incoherentIds.
-- Also propagates DirectIncoherence root-cause info through the closure.
-- Call this once on a fully-merged SolvedBinds before consuming it.
computeTransitiveIncoherent :: SolvedBinds -> SolvedBinds
computeTransitiveIncoherent sbs = sbs {
    recursiveBinds    = map markBind (recursiveBinds sbs),
    nonRecursiveBinds = map markBind (nonRecursiveBinds sbs),
    incoherentIds     = finalIds,
    directIncoherences = propagatedSources
  }
  where
    direct = incoherentIds sbs
    allBindings = recursiveBinds sbs ++ nonRecursiveBinds sbs
    finalIds = go direct
    go known
      | S.null newIds = known
      | otherwise    = go (known `S.union` newIds)
      where newIds = S.fromList [ i | ((i, _, _), fv) <- allBindings
                                    , not (S.member i known)
                                    , not (S.disjoint fv known) ]
    markBind b@((i, t, e), fv)
      | S.member i finalIds && not (S.member i direct) =
          ((addIdProp i IdPIncoherent, t, e), fv)
      | otherwise = b
    -- Propagate root-cause DirectIncoherence through the transitive closure:
    -- for each newly-transitively-incoherent bind, inherit the source from
    -- the first free var that already has a known source.
    propagateSources known
      | M.null newEntries = known
      | otherwise = propagateSources (M.union known newEntries)
      where
        newEntries = M.fromList
          [ (i, src)
          | ((i, _, _), fv) <- allBindings
          , S.member i finalIds
          , not (M.member i known)
          , Just src <- [listToMaybe [s | j <- S.toList fv
                                        , Just s <- [M.lookup j known]]]
          ]
    propagatedSources = propagateSources (directIncoherences sbs)

-- Record the root cause of a direct incoherent match for the given dict Id.
-- Called from sat after niceTypes provides the pretty-printed pred/inst strings.
addDirectIncoherence :: Id -> DirectIncoherence -> SolvedBinds -> SolvedBinds
addDirectIncoherence i di sbs =
  sbs { directIncoherences = M.insert i di (directIncoherences sbs) }

emptySBs :: SolvedBinds
emptySBs = SolvedBinds {
             recursiveBinds = [],
             nonRecursiveBinds = [],
             recursiveIds = S.empty,
             nonRecursiveIds = S.empty,
             incoherentIds = S.empty,
             bindClasses = M.empty,
             directIncoherences = M.empty
           }

instance PPrint SolvedBinds where
  pPrint d p sbs =
    text "SolvedBinds" <+> braces (
      text "rec:" <+> pPrint d p (recursiveBinds sbs) <> semi <+>
      text "nonRec:" <+> pPrint d p (nonRecursiveBinds sbs)
    )

getRecursiveDefls :: SolvedBinds -> [CDefl]
getRecursiveDefls = map (mkDefl . fst) . recursiveBinds

getNonRecursiveDefls :: SolvedBinds -> [CDefl]
getNonRecursiveDefls = map (mkDefl . fst) . nonRecursiveBinds

getIncoherentIds :: SolvedBinds -> S.Set Id
getIncoherentIds = incoherentIds
