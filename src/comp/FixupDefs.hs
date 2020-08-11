module FixupDefs(fixupDefs, updDef) where

import Data.List(nub)
import qualified Data.Map as M
import PFPrint
import ErrorUtil(internalError)
import Id
import ISyntax
import ISyntaxXRef(updateIExprPosition)
import ISyntaxUtil(iDefsMap)
--import Debug.Trace


-- ===============

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

        -- Get all the defs from this package and the imported packages
        ads = concat (ds : map (\ (IPackage _ _ _ ds) -> ds) ms)

        -- Create a recursive data structure by populating the map "m"
        -- with defs created using the map itself
        m = M.fromList [ (i, e) | (IDef i _ e _) <- ads' ]
        ads' = iDefsMap (fixUp m) ads

        -- The new package contents
        ipkg_sigs = [ (mi, s) | (m@(IPackage mi _ _ _), s) <- ipkgs ]
        ds' = iDefsMap (fixUp m) ds
    in
        --trace ("fixup " ++ ppReadable (map fst (M.toList m))) $
        (IPackage mi ipkg_sigs ps' ds', ads')


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

fixUp :: M.Map Id (IExpr a) -> IExpr a -> IExpr a
fixUp m (ILam i t e) = ILam i t (fixUp m e)
fixUp m (ILAM i k e) = ILAM i k (fixUp m e)
fixUp m (IAps f ts es) = IAps (fixUp m f) ts (map (fixUp m) es)
fixUp m (ICon i (ICDef t _)) = ICon i (ICDef t (get m i))
fixUp m e = e

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

