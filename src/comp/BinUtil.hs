module BinUtil (
                BinMap, BinFile,
                HashMap,
                readImports,
                readBin, sortImportedSignatures,
                replaceImportedSignatures
               ) where

import Control.Monad(when, foldM)
import qualified Data.Map as M
import Flags(Flags,
             ifcPath,
             enablePoisonPills,
             usePrelude,
             verbose)
import Position(noPosition)
import Id
import PreIds
import CSyntax
import ISyntax
import Prim
import Error(internalError, ErrMsg(..), ErrorHandle, bsError, bsWarning)
import PFPrint
import SCC
import FileNameUtil(binSuffix)
import FileIOUtil(readBinFilePath)
import GenBin(readBinFile)
import Util(fromJustOrErr, fromMaybeM,
            map_insertManyWith, map_insertManyWithKeyM)


-- =========================

-- the contents of the .bo package
type BinFile a = ( String       -- filename
                 , CSignature   -- signature of user-visible defs)
                 , CSignature   -- signature of all defs
                 , IPackage a   -- the package
                 , String       -- hash
                 )

-- a map of the hashes for a package (associated with the source)
-- (more than one hash indicates a mismatch error)
type HashMap = M.Map Id (String, [Id])

-- a map containing the binfiles that have been loaded, indexed by pkg name
type BinMap a = M.Map String (BinFile a)


-- =========================

-- Read all .bo files imported by this package
readImports :: ErrorHandle -> Flags -> BinMap a -> HashMap -> CPackage ->
               IO (CPackage, BinMap a, HashMap)
readImports errh flags binmap0 hashmap0
            (CPackage pkgId exps imps [] fixs ds includes) = do
  let
      pkgName = getIdString pkgId

      -- Replace qualified importing only (True) with unqualified and
      -- qualified (False)
      qualMergeFn newQual oldQual = if (oldQual) then newQual else oldQual

      -- load files as necessary, keeping track of what has been loaded
      -- and with what qualifiers they have been imported
      -- (avoids loading packages twice and filters duplicates)
      fn (binmap, hashmap, qualmap) (CImpId q i) =
          do (binmap', hashmap', bininfo, _)
                 <- readBin errh flags (Just pkgName) binmap hashmap i
             let (_, _, _, ipkg, _) = bininfo
             let deps = map (getIdString . fst) $ ipkg_depends ipkg
                 dep_quals = map (\x -> (x,True)) deps
             -- add the dependencies as qualified-only imports
             let qualmap' = map_insertManyWith qualMergeFn dep_quals qualmap
             -- add the current package with the user-specified import
             let qualmap'' = M.insertWith qualMergeFn (getIdString i) q qualmap'
             return (binmap', hashmap', qualmap'')

  (binmap, hashmap, qualmap)
      <- foldM fn (binmap0, hashmap0, M.empty) (addPrelude flags imps)

  let mkCImp (s, q) = case (M.lookup s binmap) of
                        Just (fn, bi_sig, _, _, _) -> CImpSign fn q bi_sig
                        Nothing -> internalError ("mkCImp: " ++ ppReadable s)
  let impsigs' = map mkCImp (M.toList qualmap)

  let sortedImpsigs = sortImportedSignatures impsigs'
  let cpkg' = CPackage pkgId exps imps sortedImpsigs fixs ds includes

  return (cpkg', binmap, hashmap)

readImports errh flags binmap0 hashmap0 pkg =
  internalError $ "readImports package already has imported signatures: " ++ ppReadable pkg

-- helper function that reads in a .bo file, and any .bo files that it needs
readBin :: ErrorHandle -> Flags -> (Maybe String) ->
           BinMap a -> HashMap -> Id ->
           IO (BinMap a, HashMap, BinFile a, [Id])
readBin errh flags maybePkgName binmap0 hashmap0 p0 = do
   let
       -- if compiling a source package (that imports p0), detect when p0
       -- imports a bin-file with the same name as the source package
       checkPkgName p =
           case maybePkgName of
             Just pkgName | (getIdString p == pkgName) ->
                 bsError errh
                     [(getPosition p0,
                       ECircularImportsViaBinFile pkgName (getIdString p0))]
             _ -> return ()

       fn :: [Id] -> BinMap a -> HashMap -> [Id] ->
             IO (BinMap a, HashMap, [Id])
       fn ps_read binmap hashmap [] = return (binmap, hashmap, reverse ps_read)
       fn ps_read binmap hashmap (p:ps) =
           case (M.lookup (getIdString p) binmap) of
             Just _ -> fn ps_read binmap hashmap ps
             Nothing -> do
                 checkPkgName p
                 (fname, bi_sig, bo_sig, bo_pkg, hash, hashmap', impNames)
                     <- doImport errh flags hashmap p
                 let binmap' = M.insert (getIdBaseString p)
                                        (fname, bi_sig, bo_sig, bo_pkg, hash)
                                        binmap
                 fn (p : ps_read) binmap' hashmap' (impNames ++ ps)

   (binmap', hashmap', ps_read) <- fn [] binmap0 hashmap0 [p0]
   let p0_bininfo = fromJustOrErr "readBin" $ M.lookup (getIdString p0) binmap'
   return (binmap', hashmap', p0_bininfo, ps_read)


-- Sort signatures topologically: output signature list such that,
-- if signature s1 comes before signature s2, then s1 does not import s2
sortImportedSignatures :: [CImportedSignature] -> [CImportedSignature]
sortImportedSignatures signatures =
    let
        -- We map the signatures to strings and sort a graph of strings,
        -- so that sorting is stable (the Ord instance for the tuple includes
        -- Ids, whose Ord instance depends on when the Id was created)
        sMap = M.fromList [ (getIdString name, sign)
                            | sign@(CImpSign _ _ (CSignature name _  _ _))
                                <- signatures]
        addImplicitPreludeDependency (name, imports)
            | name == strPrelude = (name, imports)
            | name == strPreludeBSV = (name, imports)
            | otherwise = (name, strPrelude :
                           strPreludeBSV :
                           filter (\ x -> x /= strPrelude && x /= strPreludeBSV)
                                  imports)
            where strPrelude = getIdString idPrelude
                  strPreludeBSV = getIdString idPreludeBSV
        sGraph = [ addImplicitPreludeDependency (getIdString name,
                                                 map getIdString imports)
                   | (CImpSign _ _ (CSignature name imports _ _))
                       <- signatures]
        lookupFn i = case (M.lookup i sMap) of
                       Just s -> s
                       Nothing -> internalError ("sortImportedSignatures: " ++ i)
    in  case tsort sGraph of
        Left cycle -> internalError ("import cycle:\n" ++ ppString cycle)
        Right order -> map lookupFn order


-- Add the Prelude to the list of imports, unless compiling the Prelude itself
addPrelude :: Flags -> [CImport] -> [CImport]
addPrelude flags imps | usePrelude flags = CImpId False idPrelude :
                                           CImpId False idPreludeBSV :
                                           imps
                      | otherwise = imps

-- Import one .bo file
doImport :: ErrorHandle -> Flags -> HashMap -> Id ->
            IO (String, CSignature, CSignature, IPackage a, String,
                HashMap, [Id])
doImport errh flags hashmap i = do
    let binname = getIdString i ++ "." ++ binSuffix
        missingErr = (getIdPosition i,
                      EMissingBinFile binname (pfpString i))
        pillMsg = if (enablePoisonPills flags)
                  then bsWarning errh
                  else bsError errh
    (file, name) <- fromMaybeM (bsError errh [missingErr]) $
                      readBinFilePath errh (getIdPosition i)
                          (verbose flags) binname (ifcPath flags)
    (bi_sig, bo_sig, ipkg@(IPackage pi impHashes _ _), hash)
        <- readBinFile errh name file
    when (pi /= i) $
        bsError errh [(noPosition, EBinFilePkgNameMismatch name
                                       (pfpString i) (pfpString pi))]
    when (any hasPoisonPill [ e | IDef _ _ e _ <- ipkg_defs ipkg ]) $
        pillMsg [(getIdPosition pi, WPoisonedDefFile binname)]
    hashmap' <- mergeHashes errh hashmap pi hash impHashes
    let impNames = map fst impHashes
    return (name, bi_sig, bo_sig, ipkg, hash, hashmap', impNames)

hasPoisonPill :: IExpr a -> Bool
hasPoisonPill (ILam _ _ e)  = hasPoisonPill e
hasPoisonPill (ILAM _ _ e)  = hasPoisonPill e
hasPoisonPill (IAps f _ es) = any hasPoisonPill (f:es)
hasPoisonPill (ICon _ (ICPrim _ p)) = p == PrimPoisonedDef
hasPoisonPill _ = False

mergeHashes :: ErrorHandle -> HashMap -> Id -> String -> [(Id, String)] ->
               IO HashMap
mergeHashes errh hashmap binId binhash impHashes =
  let
      -- a package and its importer disagree about the hash
      mismatchErr1 pkg importer =
          let pkgfile = (pfpString pkg) ++ "." ++ binSuffix
          in  bsError errh
                  [(getIdPosition binId,
                    EBinFileSignatureMismatch pkgfile (pfpString importer))]

      -- two packages disagree about an imported file
      -- XXX we could determine which is wrong by loading the file itself
      mismatchErr2 pkg importer1 importer2 =
          let pkgfile = (pfpString pkg) ++ "." ++ binSuffix
          in  bsError errh
                  [(getIdPosition binId,
                    EBinFileSignatureMismatch2 pkgfile
                        (pfpString importer1) (pfpString importer2))]

      mergeFn :: Id -> (String, [Id]) -> (String, [Id]) ->
                 IO (String, [Id])
      mergeFn k (new_s, [new_i]) (old_s, old_is@(old_i:_))
          | new_s == old_s = return (old_s, (new_i:old_is))
          | new_i == k
              -- the "old_is" expected a different hash than the
              -- package "new_i" actually has
              = mismatchErr1 new_i old_i
          | k `elem` old_is
              -- the "new_i" is expecting different than the package
              -- actually has (and possibly other "old_is" agree)
              = mismatchErr1 k new_i
          | otherwise
              -- we don't yet know what the package's hash is,
              -- but two users disagree on its hash
              = mismatchErr2 k new_i old_i
      mergeFn _ new_val _ =
          internalError ("mergeHashes: " ++ ppReadable new_val)


      new_pairs = let mkImpPair (i,s) = (i, (s, [binId]))
                      imp_pairs = map mkImpPair impHashes
                      bin_pair = (binId, (binhash, [binId]))
                  in  (bin_pair : imp_pairs)
  in
      map_insertManyWithKeyM mergeFn new_pairs hashmap


-- =========================

-- Replace existing imports in a package with new "internal" ones
-- (where all defs are visible, not just the ones visible to the user).
-- This is used to create the full symbol table used for generating a
-- module.  (XXX can we get rid of this?)
replaceImportedSignatures :: CPackage -> [CSignature] -> CPackage
replaceImportedSignatures (CPackage i exps imps impsigs fixs defs includes) newsigs =
    CPackage i exps imps impsigs' fixs defs includes
  where sigMap = M.fromList [(i, sig) | sig@(CSignature i _ _ _) <- newsigs]
        impsigs' = map replaceSig impsigs
        replaceSig (CImpSign n q (CSignature i _ _ _)) =
            let errstr = "replaceImportedSignatures: missing sig: " ++ ppReadable i
            in  CImpSign n q (fromJustOrErr errstr (M.lookup i sigMap))

-- =========================
