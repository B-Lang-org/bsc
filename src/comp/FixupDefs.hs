module FixupDefs(fixupDefs, updDef) where

import Data.List(nub)
import qualified Data.Map as M
import PFPrint
import CType
import ISyntaxUtil
import ErrorUtil(internalError)
import IOUtil(progArgs)
import Id
import ISyntax
import ISyntaxXRef(updateIExprPosition)
import Util(tracep)

trace_drop_dicts :: Bool
trace_drop_dicts = "-trace-drop-dicts" `elem` progArgs

-- ===============


itIsDictType :: IType -> Bool
itIsDictType t
  | null $ fst $ itGetArrows t,
    ITCon _ _ (TIstruct SClass _) <- leftmost t = True
itIsDictType _ = False

-- This does two things:
-- (1) Insert imported packages into the current package (including their
--     pragmas and defs, and recording their signatures)
-- (2) Find references to top-level variables and insert the definitions
--     (to avoid lookups when evaluating the code).  This creates a cyclic
--     data structure when defs call each other recursively.
fixupDefs :: IPackage a -> [(IPackage a, String)] -> (IPackage a, [IDef a])
fixupDefs (IPackage mi _ ps ds) ipkgs =
    let
        (ms, _) = unzip ipkgs

        -- Combine the pragmas from the imported packages into this one
        -- XXX The nub is needed (at least) because we call "fixupDefs"
        -- XXX multiple times on a package and so we may be adding the ipkg
        -- XXX pragmas multiple times.
        ps' = nub $ concat $ ps : [ ps | IPackage _ _ ps _ <- ms ]

        -- Get all the defs from the imported packages
        ams = concatMap ipkg_defs ms

        coherent_dicts = [ d | d@(IDef i t _ _) <- ams, itIsDictType t, isDictId i, not $ isIncoherentDict i ]
        coherent_dict_map = M.fromList [ (t,i) | IDef i t _ _ <- coherent_dicts ]

        -- Get all the defs from this package and the imported packages
        ads = concat (ds : map (\ (IPackage _ _ _ ds) -> ds) ms)

        -- Create a recursive data structure by populating the map "m"
        -- with defs created using the map itself
        m = M.fromList [ (i, e) | (IDef i _ e _) <- ads' ]
        ads' = iDefsMap (fixUp coherent_dict_map m) ads

        -- The new package contents
        ipkg_sigs = [ (mi, s) | (m@(IPackage mi _ _ _), s) <- ipkgs ]
        ds' = iDefsMap (fixUp coherent_dict_map m) ds
        dropDict i t = tracep (trace_drop_dicts && result) ("dropDict: " ++ ppReadable (i,t)) result
          where result = itIsDictType t && isDictId i && t `M.member` coherent_dict_map && not (isIncoherentDict i)
        ds'' = [ d' | d'@(IDef i t _ _) <- ds', not (dropDict i t) ]
    in
        --trace ("fixup " ++ ppReadable (map fst (M.toList m))) $
        (IPackage mi ipkg_sigs ps' ds'', ads')


-- ===============

-- Replace the definition for a top-level variable with a new definition.
-- (This is used to replace the pre-synthesis definition for a module with
-- the post-synthesis definition.)
updDef :: IDef a -> IPackage a -> [(IPackage a, String)] -> IPackage a
updDef d@(IDef i _ _ _) ipkg@(IPackage { ipkg_defs = ds }) ips =
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
        (ipkg'', _) = fixupDefs ipkg' ips
    in
        ipkg''


-- ===============

fixUp :: M.Map IType Id -> M.Map Id (IExpr a) -> IExpr a -> IExpr a
fixUp cm m (ILam i t e) = ILam i t (fixUp cm m e)
fixUp cm m (ILAM i k e) = ILAM i k (fixUp cm m e)
fixUp cm m (IAps f ts es) = IAps (fixUp cm m f) ts (map (fixUp cm m) es)
fixUp cm m (ICon i (ICDef t _))
  | isDictId i && itIsDictType t && not (isIncoherentDict i),
    Just i' <- M.lookup t cm = ICon i' (ICDef t (get m i'))
fixUp cm m (ICon i (ICDef t _)) = ICon i (ICDef t (get m i))
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

