{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StaticPointers #-}

-- | Setup hooks for the bsc package (build-type: Hooks; doc/cabal.md).
module SetupHooks (setupHooks) where

import Control.Monad (filterM, forM_)
import Control.Monad.IO.Class (liftIO)
import Data.List (isPrefixOf)
import Data.List.NonEmpty (NonEmpty ((:|)))
import Data.Maybe (fromMaybe, listToMaybe)
import qualified Data.Set as Set
import Distribution.InstalledPackageInfo (ExposedModule (..))
import qualified Distribution.InstalledPackageInfo as IPI
import Distribution.Pretty (prettyShow)
import Distribution.Simple.Configure (ccLdOptionsBuildInfo)
import Distribution.Simple.LocalBuildInfo (interpretSymbolicPathLBI)
import qualified Distribution.Simple.LocalBuildInfo as LBI
import Distribution.Simple.PackageIndex (lookupUnitId)
import Distribution.Simple.SetupHooks
import Distribution.Simple.Utils (rewriteFileEx)
import Distribution.Utils.Path (moduleNameSymbolicPath, (<.>))
import Distribution.Verbosity (normal)
import System.Directory
  ( canonicalizePath,
    createDirectoryIfMissing,
    createDirectoryLink,
    doesPathExist,
    listDirectory,
    makeAbsolute,
    pathIsSymbolicLink,
    removeDirectoryLink,
    removePathForcibly,
  )
import System.Environment (lookupEnv)
import System.FilePath (splitSearchPath, takeDirectory, (</>))
import System.IO.Error (catchIOError)
import System.Process (callProcess, readProcess)

setupHooks :: SetupHooks
setupHooks =
  noSetupHooks
    { configureHooks = noConfigureHooks {preConfComponentHook = Just preConfComponent},
      buildHooks =
        noBuildHooks
          { preBuildComponentRules = Just preBuildRules,
            postBuildComponentHook = Just postBuildComponent
          }
    }

-- | Configure hook: query platform.sh for Tcl include/link flags and defines.
preConfComponent :: PreConfComponentHook
preConfComponent inputs = do
  let c = inputs.component
  bi <- case c of
    CLib _ -> do
      let platform arg = words <$> readProcess "sh" ["platform.sh", arg] ""
      tclInc <- platform "tclinc"
      tclLibs <- platform "tcllibs"
      tclVer <- platform "tclversion"
      cflags <- case tclVer of
        ["8.5"] -> pure ["-DTCL85"]
        ["8.6"] -> pure []
        ["9.0"] -> pure ["-DTCL9"]
        _ -> ioError (userError ("unsupported Tcl version: " <> unwords tclVer))
      pure (ccLdOptionsBuildInfo (tclInc <> cflags) tclLibs []) {cppOptions = cflags}
    _ -> pure emptyBuildInfo
  pure PreConfComponentOutputs {componentDiff = buildInfoComponentDiff (componentName c) bi}

-- | Pre-build rules for the library: generate Warmup.hs and refresh BuildVersion.hs.
--
-- Warmup imports exposed modules in sorted order. Restrict it to direct
-- dependencies, which are the packages exposed to GHC; importing bsc itself
-- would create a cycle. See doc/cabal.md (Build hooks and generated files)
-- for the determinism issue
-- and GHC.Core.Rules, Note [Overall plumbing for rules], for the EPS rule cache.
--
-- The version helper also serves Bluesim and git-archive export substitutions.
-- src/comp/BuildVersion.hs is an ordinary source module and the canonical
-- version, including frozen or custom values: Make refreshes it before
-- invoking Cabal, and the call below refreshes it for a cabal build run by
-- hand. It is listed in extra-source-files so that a changed version
-- rebuilds the package even when no other source changed.
preBuildRules :: PreBuildComponentRules
preBuildRules = rules (static ()) $ \env ->
  case targetComponent env.targetInfo of
    CLib _ -> do
      let lbi = env.localBuildInfo
          clbi = env.targetInfo.targetCLBI
          mods =
            Set.toAscList . Set.fromList $
              [ prettyShow (exposedName e)
                | (uid, _) <- componentPackageDeps clbi,
                  Just ipi <- [lookupUnitId (LBI.installedPkgs lbi) uid],
                  e <- IPI.exposedModules ipi
              ]
          autogenSymDir = autogenComponentModulesDir lbi clbi
          autogenDir = interpretSymbolicPathLBI lbi autogenSymDir
          loc m = Location autogenSymDir (moduleNameSymbolicPath m <.> "hs")
      liftIO $ do
        -- A leftover src/comp/Warmup.hs from a make build would shadow the
        -- generated module (hs-source-dirs precede the autogen dir), so remove
        -- it; then refresh the version module in place.
        removePathForcibly ("src" </> "comp" </> "Warmup.hs")
        callProcess
          "bash"
          ["src" </> "comp" </> "update-build-version.sh", "--module", "src" </> "comp"]
      registerRule_ "autogen" $
        staticRule
          ( mkCommand
              (static Dict)
              (static writeAutogenModules)
              (autogenDir, mods)
          )
          []
          (loc "Warmup" :| [])
    _ -> pure ()

writeAutogenModules :: (FilePath, [String]) -> IO ()
writeAutogenModules (autogenDir, mods) = do
  createDirectoryIfMissing True autogenDir
  rewriteFileEx normal (autogenDir </> "Warmup.hs") . unlines $
    [ "-- Generated by SetupHooks.hs (preBuildRules); do not edit.",
      "module Warmup where"
    ]
      <> ["import " <> m <> " ()" | m <- mods]

-- | Post-build hook: symlink lib/SAT beside the built library and executables
-- to the solver directory from LIBRARY_PATH so binaries in dist-newstyle run
-- in place via their relative rpath ($ORIGIN/../lib/SAT).
postBuildComponent :: PostBuildComponentHook
postBuildComponent inputs = do
  let lbi = inputs.localBuildInfo
  build <- makeAbsolute (interpretSymbolicPathLBI lbi (LBI.buildDir lbi))
  case targetComponent inputs.targetInfo of
    CLib _ -> do
      path <- fromMaybe "" <$> lookupEnv "LIBRARY_PATH"
      dirs <- filterM holdsSolvers (filter (not . null) (splitSearchPath path))
      forM_ (listToMaybe dirs) $ \rawSat -> do
        sat <- canonicalizePath rawSat
        forM_ [takeDirectory build, build] $ \dir -> do
          let link = dir </> "lib" </> "SAT"
          createDirectoryIfMissing True (dir </> "lib")
          -- Replace only a link: a real directory there is not ours to delete.
          isLink <- pathIsSymbolicLink link `catchIOError` \_ -> pure False
          if isLink
            then removeDirectoryLink link
            else do
              present <- doesPathExist link
              if present
                then ioError (userError (link <> " exists and is not a symbolic link"))
                else pure ()
          createDirectoryLink sat link
    _ -> pure ()
  where
    holdsSolvers dir = do
      names <- listDirectory dir `catchIOError` \_ -> pure []
      pure (all (\p -> any (p `isPrefixOf`) names) ["libstp.", "libyices."])
