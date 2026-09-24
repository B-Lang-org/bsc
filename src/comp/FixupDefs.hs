module FixupDefs(fixupDefs, updDef, DictBuckets, mkDictBuckets) where

import Control.Monad.State.Strict(State, evalState, gets, modify)
import Data.List(nub)
import Data.Maybe(isJust)
import qualified Data.Map as M
import qualified Data.Set as S
import PFPrint
import ErrorUtil(internalError)
import IOUtil(progArgs)
import Id
import DefProp(DefProp(..), defPropsDictEvidence)
import ISyntax
import ISyntaxXRef(updateIExprPosition)
import ISyntaxUtil(iDefsMap, itIsDictType)
import Util(tracep)
--import Debug.Trace

trace_drop_dicts :: Bool
trace_drop_dicts = "-trace-drop-dicts" `elem` progArgs

-- ===============

-- The evidence identity of a lifted dictionary, as recorded in its
-- DefProps at lift time (see "renderEvidence" in LiftDicts): the
-- slot-normalized rendering of its own evidence level, the lifted
-- dictionaries it references (in slot order), and the types it
-- references (in slot order).  A dictionary without one (incoherent,
-- or evidence outside the renderable shapes) is never merged with
-- anything but itself.
data DictEv = DictEv {
    dev_rendering :: String,
    dev_kids :: [Id],
    dev_types :: [IType]
}

getDictEv :: [DefProp] -> Maybe DictEv
getDictEv props = case defPropsDictEvidence props of
                    Just (str, ks, ts) -> Just (DictEv str ks ts)
                    Nothing -> Nothing

-- The evidence identity (and interned type) of every lifted dictionary
-- in scope -- imported or local -- keyed by name; the verification
-- procedure reads kid identities from here.
type EvMap = M.Map Id (IType, Maybe DictEv)

-- The lifted dictionaries of the imported packages that carry an
-- evidence identity, bucketed by their interned type
-- (position-insensitive cmpT order), each bucket in import order.  A
-- dictionary may be replaced by a bucket candidate only when -- in
-- addition to this type equality -- its evidence identity is verified
-- equal ("mkRedirects" below).  Type equality alone is not sound:
-- packages with different visible instance sets (orphan instances,
-- T0127) can each coherently resolve the same predicate to different
-- instances, and deduplicating across that divergence silently swaps
-- the selected methods.
--
-- This map depends only on the imported packages, which are fixed for
-- the entire compilation of a package; so it is built once (in
-- "compilePackage" in bsc.hs) and passed to every call of "fixupDefs"
-- and "updDef" (which is called once per synthesized module), rather
-- than rebuilt on each call.  Within a bucket the first verified-equal
-- def in import order wins; any verified-equal candidate is
-- semantically interchangeable, and import order is fixed by the
-- source, so the choice is deterministic.
type DictBuckets = M.Map IType [Id]

mkDictBuckets :: [(IPackage a, String)] -> DictBuckets
mkDictBuckets ipkgs =
    M.fromListWith (\ new old -> old ++ new)
        [ (t, [i])
        | (p, _) <- ipkgs, IDef i t _ props <- ipkg_defs p,
          isLiftedDict i, itIsDictType t,
          isJust (defPropsDictEvidence props) ]

-- The canonical redirection for every lifted dictionary (local or
-- imported): the first import-order bucket candidate of the same
-- interned type whose evidence identity verifies equal, when that is
-- a different def.  Computed once per fixupDefs call over the
-- dictionary defs only; fixUp then redirects by plain Id lookup, with
-- no per-occurrence type work.
--
-- Verification of a pair of dictionaries ("verifyPair"): equal names
-- are one def; otherwise both must carry evidence identities, and the
-- interned types must be equal, the renderings must be EQUAL STRINGS
-- (sound: the rendering is injective over the dictionary's own
-- evidence level), the type slots must be equal element-wise (interned
-- ITypes, so O(1) per slot), and the kid slots must verify pairwise by
-- the same procedure.  A kid without an evidence identity therefore
-- matches only itself (by name) -- exactly the never-dedup behavior
-- its own package gave it.  No digest ever commits a merge; every
-- merge decision reads the evidence identities themselves.
--
-- The kid recursion terminates because lifted evidence is acyclic
-- (letrec-bound dictionaries are never lifted); results are memoized
-- on the (Id, Id) pair across the whole computation, and a visited
-- set guards defensively against a cycle in corrupted input by
-- refusing (never trusting) a revisited pair.
mkRedirects :: DictBuckets -> EvMap -> M.Map Id Id
mkRedirects buckets evmap =
    M.fromList (concat (evalState (mapM tryRedirect dicts) M.empty))
  where
    dicts = [ (i, t) | (i, (t, Just _)) <- M.toList evmap ]

    tryRedirect :: (Id, IType) -> State (M.Map (Id, Id) Bool) [(Id, Id)]
    tryRedirect (i, t) =
        let scan [] = return []
            -- reaching itself: no earlier candidate matched, so this
            -- (imported) dict is its own canonical def
            scan (c : _) | c `qualEq` i = return []
            scan (c : rest) = do
                ok <- verifyPair S.empty i c
                if ok then return [(i, c)] else scan rest
        in  case M.lookup t buckets of
              Nothing -> return []
              Just cands -> scan cands

    verifyPair :: S.Set (Id, Id) -> Id -> Id
               -> State (M.Map (Id, Id) Bool) Bool
    verifyPair visited i1 i2
      | i1 `qualEq` i2 = return True
        -- a revisited pair means a reference cycle, which lifted
        -- evidence never has; refuse the merge rather than trust it
      | (i1, i2) `S.member` visited = return False
      | otherwise = do
          memoized <- gets (M.lookup (i1, i2))
          case memoized of
            Just r -> return r
            Nothing -> do
              r <- case (M.lookup i1 evmap, M.lookup i2 evmap) of
                     (Just (t1, Just ev1), Just (t2, Just ev2)) ->
                         verifyEv (S.insert (i1, i2) visited) t1 ev1 t2 ev2
                     _ -> return False
              modify (M.insert (i1, i2) r)
              return r

    verifyEv visited t1 ev1 t2 ev2 =
        if t1 /= t2
           || dev_rendering ev1 /= dev_rendering ev2
           || length (dev_kids ev1) /= length (dev_kids ev2)
           || dev_types ev1 /= dev_types ev2
        then return False
        else andM [ verifyPair visited k1 k2
                  | (k1, k2) <- zip (dev_kids ev1) (dev_kids ev2) ]

    andM [] = return True
    andM (mx : rest) = do x <- mx
                          if x then andM rest else return False

-- When a dictionary is dropped in favor of a canonical equivalent, the
-- kid lists of the surviving dictionaries must follow: a downstream
-- package verifies kid slots against the defs it can see, so a kid
-- entry naming a dropped local def must be rewritten to name the
-- canonical def instead.
redirectDictProps :: M.Map Id Id -> IDef a -> IDef a
redirectDictProps redirects d@(IDef i t e props)
  | M.null redirects = d
  | otherwise = IDef i t e (map upd props)
  where upd (DefP_DictKids ks) =
            DefP_DictKids [ M.findWithDefault k k redirects | k <- ks ]
        upd p = p

-- ===============

-- This does two things:
-- (1) Insert imported packages into the current package (including their
--     pragmas and defs, and recording their signatures)
-- (2) Find references to top-level variables and insert the definitions
--     (to avoid lookups when evaluating the code).  This creates a cyclic
--     data structure when defs call each other recursively.
--
-- It also deduplicates lifted dictionaries against the imported
-- packages: every lifted dictionary whose evidence identity verifies
-- equal to an earlier (import-order) one is redirected to it, and the
-- package's own dictionaries that were redirected away are dropped
-- from the package (they remain in the returned alldefs).
--
-- The first argument must be "mkDictBuckets" applied to the same
-- imported packages that are passed as the third argument.
fixupDefs :: DictBuckets -> IPackage a -> [(IPackage a, String)] -> (IPackage a, [IDef a])
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

        -- The evidence identities are read from the defs as their
        -- packages recorded them, before any redirection this pass
        -- performs.
        evmap = M.fromList [ (i, (t, getDictEv props))
                           | IDef i t _ props <- ads, isLiftedDict i ]

        redirects :: M.Map Id Id
        redirects = mkRedirects buckets evmap

        -- Create a recursive data structure by populating the map "m"
        -- with defs created using the map itself
        m = M.fromList [ (i, e) | (IDef i _ e _) <- ads' ]
        ads' = map (redirectDictProps redirects)
                   (iDefsMap (fixUp redirects m) ads)

        -- The new package contents
        ipkg_sigs = [ (mi, s) | (m@(IPackage mi _ _ _ _), s) <- ipkgs ]
        ds' = map (redirectDictProps redirects)
                  (iDefsMap (fixUp redirects m) ds)
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
updDef :: DictBuckets -> IDef a -> IPackage a -> [(IPackage a, String)] -> IPackage a
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
