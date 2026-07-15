module FixupDefs(fixupDefs, updDef, DictBuckets, mkDictBuckets) where

import Data.List(nub)
import qualified Data.Map as M
import qualified Data.Set as S
import PFPrint
import ErrorUtil(internalError)
import IOUtil(progArgs)
import Id
import ISyntax
import ISyntaxXRef(updateIExprPosition)
import ISyntaxUtil(iDefsMap, itIsDictType)
import Util(tracep)
--import Debug.Trace

trace_drop_dicts :: Bool
trace_drop_dicts = "-trace-drop-dicts" `elem` progArgs

-- ===============

-- The lifted dictionaries of the imported packages, bucketed by their
-- interned type (position-insensitive cmpT order), each bucket in
-- import order.  A dictionary may be replaced by a bucket candidate
-- only when -- in addition to this type equality -- its EVIDENCE is
-- structurally equal ("eqEvidence" below).  Type equality alone is not
-- sound: packages with different visible instance sets (orphan
-- instances, T0127) can each coherently resolve the same predicate to
-- different instances, and deduplicating across that divergence
-- silently swaps the selected methods.
--
-- This map depends only on the imported packages, which are fixed for
-- the entire compilation of a package; so it is built once (in
-- "compilePackage" in bsc.hs) and passed to every call of "fixupDefs"
-- and "updDef" (which is called once per synthesized module), rather
-- than rebuilt on each call.  Within a bucket the first structurally
-- equal def in import order wins; any structurally equal candidate is
-- semantically interchangeable, and import order is fixed by the
-- source, so the choice is deterministic.
type DictBuckets a = M.Map IType [(Id, IExpr a)]

mkDictBuckets :: [(IPackage a, String)] -> DictBuckets a
mkDictBuckets ipkgs =
    M.fromListWith (\ new old -> old ++ new)
        [ (t, [(i, e)])
        | (p, _) <- ipkgs, IDef i t e _ <- ipkg_defs p,
          isLiftedDict i, itIsDictType t ]

-- This does two things:
-- (1) Insert imported packages into the current package (including their
--     pragmas and defs, and recording their signatures)
-- (2) Find references to top-level variables and insert the definitions
--     (to avoid lookups when evaluating the code).  This creates a cyclic
--     data structure when defs call each other recursively.
--
-- It also deduplicates lifted dictionaries against the imported
-- packages: every lifted dictionary that is structurally equal to an
-- earlier (import-order) one is redirected to it, and the package's
-- own dictionaries that were redirected away are dropped from the
-- package (they remain in the returned alldefs).
--
-- The first argument must be "mkDictBuckets" applied to the same
-- imported packages that are passed as the third argument.
fixupDefs :: DictBuckets a -> IPackage a -> [(IPackage a, String)] -> (IPackage a, [IDef a])
fixupDefs buckets (IPackage mi _ ps ds own_atf_cache) ipkgs =
    let
        (ms, _) = unzip ipkgs

        -- Combine the pragmas from the imported packages into this one
        -- XXX The nub is needed (at least) because we call "fixupDefs"
        -- XXX multiple times on a package and so we may be adding the ipkg
        -- XXX pragmas multiple times.
        ps' = nub $ concat $ ps : [ ps | IPackage _ _ ps _ _ <- ms ]

        -- Get all the defs from this package and the imported packages
        ads = concat (ds : map (\ (IPackage _ _ _ ds _) -> ds) ms)

        -- Pre-fixup definitions: the structural evidence comparison
        -- reads each dictionary's evidence as its package defined it,
        -- before any redirection this pass performs.
        m0 = M.fromList [ (i, e) | (IDef i _ e _) <- ads ]

        -- The canonical redirection for every lifted dictionary (local
        -- or imported): the first import-order bucket candidate of the
        -- same interned type with structurally equal evidence, when
        -- that is a different def.  Computed once per fixupDefs call
        -- over the dictionary defs only; fixUp then redirects by plain
        -- Id lookup, with no per-occurrence type work.
        redirects :: M.Map Id Id
        redirects = M.fromList
            [ (i, i')
            | IDef i t e _ <- ads, isLiftedDict i,
              Just cands@((c0, _) : _) <- [M.lookup t buckets],
              -- the head of its own bucket is canonical already
              c0 /= i,
              (i' : _) <- [[ c | (c, e') <- cands, eqEvidence m0 e e' ]],
              i' /= i ]

        -- Create a recursive data structure by populating the map "m"
        -- with defs created using the map itself
        m = M.fromList [ (i, e) | (IDef i _ e _) <- ads' ]
        ads' = iDefsMap (fixUp redirects m) ads

        -- The new package contents
        ipkg_sigs = [ (mi, s) | (m@(IPackage mi _ _ _ _), s) <- ipkgs ]
        ds' = iDefsMap (fixUp redirects m) ds
        dropDict i t = case M.lookup i redirects of
                         Just _ -> tracep trace_drop_dicts
                                       ("dropDict: " ++ ppReadable (i, t))
                                       True
                         Nothing -> False
        ds'' = [ d | d@(IDef i t _ _) <- ds', not (dropDict i t) ]
        -- Note that the package keeps only its own ATF cache entries, so
        -- that .bo files stay proportional to their own package.  The union
        -- with the imported packages' caches (for use during elaboration)
        -- is built in bsc.hs and is never stored in an IPackage.  Do not
        -- merge caches here: "fixupDefs" is re-invoked once per synthesized
        -- module (via "updDef"), so any merging added here is multiplied by
        -- the number of modules.
    in
        --trace ("fixup " ++ ppReadable (map fst (M.toList m))) $
        (IPackage mi ipkg_sigs ps' ds'' own_atf_cache, ads')


-- ===============

-- Replace the definition for a top-level variable with a new definition.
-- (This is used to replace the pre-synthesis definition for a module with
-- the post-synthesis definition.)
-- The first argument must be "mkDictBuckets" applied to the same
-- imported packages that are passed as the fourth argument.
updDef :: DictBuckets a -> IDef a -> IPackage a -> [(IPackage a, String)] -> IPackage a
updDef buckets d@(IDef i _ _ _) ipkg@(IPackage { ipkg_defs = ds }) ips =
    let
        -- replace the def in the list
        ds' = [ if i == i' then d else d' | d'@(IDef i' _ _ _) <- ds ]
        ipkg' = ipkg { ipkg_defs = ds' }

        -- The new definition is in ISyntax but it does not yet have
        -- top-level defs inlined into the variable references, so we
        -- need to call "fixup" on the def.
        --
        -- Further, any top-level def that referred to this module
        -- need to have the inlined old def replaced with the new def.
        --
        -- We use "fixupDefs" to perform both changes.
        -- XXX However, "fixupDefs" is overkill, for just one def.
        -- XXX Note that we throw away alldefs, when we could return it.
        (ipkg'', _) = fixupDefs buckets ipkg' ips
    in
        ipkg''


-- ===============

fixUp :: M.Map Id Id -> M.Map Id (IExpr a) -> IExpr a -> IExpr a
fixUp r m (ILam i t e) = ILam i t (fixUp r m e)
fixUp r m (ILAM i k e) = ILAM i k (fixUp r m e)
fixUp r m (IAps f ts es) = IAps (fixUp r m f) ts (map (fixUp r m) es)
fixUp r m (ICon i (ICDef t _)) =
    let i' = M.findWithDefault i i r
    in  ICon i' (ICDef t (get m i'))
fixUp _ _ e = e

-- Structural equality of dictionary evidence, at exactly the
-- granularity of the rest of the dictionary machinery: Ids by
-- qualified name, types by interned (position-insensitive) equality.
-- References to lifted dictionaries additionally compare by their
-- DEFINITIONS: each package lifts its own copy of shared evidence
-- under a package-local name, so equal evidence is reached by
-- recursing through the pre-fixup definitions of the two references.
-- The pair set makes that recursion well-founded should a reference
-- cycle ever arise (lifted evidence is acyclic today: recursive
-- dictionary bindings are not lifted); a revisited pair is assumed
-- equal, which is the coinductive reading of bisimulation.
-- Anything unrecognized falls back to plain equality, erring toward
-- keeping both definitions.
eqEvidence :: M.Map Id (IExpr a) -> IExpr a -> IExpr a -> Bool
eqEvidence m0 = eq S.empty
  where
    eq vs (ILam i1 t1 e1) (ILam i2 t2 e2) =
        i1 == i2 && t1 == t2 && eq vs e1 e2
    eq vs (ILAM i1 k1 e1) (ILAM i2 k2 e2) =
        i1 == i2 && k1 == k2 && eq vs e1 e2
    eq vs (IAps f1 ts1 es1) (IAps f2 ts2 es2) =
        ts1 == ts2 && length es1 == length es2 &&
        eq vs f1 f2 && and (zipWith (eq vs) es1 es2)
    eq vs (ICon i1 (ICDef t1 _)) (ICon i2 (ICDef t2 _)) =
        t1 == t2 &&
        (qualEq i1 i2 ||
         (isLiftedDict i1 && isLiftedDict i2 && eqDef vs i1 i2))
    eq _ e1 e2 = e1 == e2

    eqDef vs i1 i2
      | (i1, i2) `S.member` vs = True
      | otherwise =
          case (M.lookup i1 m0, M.lookup i2 m0) of
            (Just e1, Just e2) -> eq (S.insert (i1, i2) vs) e1 e2
            _ -> False

get :: M.Map Id (IExpr a) -> Id -> IExpr a
get m i = let value = get2 m i
              pos = (getIdPosition i)
          in -- trace("LookupX "
                -- ++ (ppReadable i) ++ " => "
                -- ++ (ppReadable (updateIExprPosition pos value))) $
             (updateIExprPosition pos value)

get2 :: M.Map Id (IExpr a) -> Id -> IExpr a
get2 m i =
    case M.lookup i m of
    Just e -> e
    Nothing -> internalError (
        "fixupDefs.get: "
        ++ pfpString i ++ "\n"
        ++ ppReadable (map fst (M.toList m)))

-- ===============
