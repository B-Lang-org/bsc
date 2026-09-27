{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StaticPointers #-}

module SetupHooks (setupHooks) where

import Control.Monad (forM_, unless, when)
import Data.Char (isSpace)
import Data.List (isPrefixOf, sort)
import qualified Data.List.NonEmpty as NE
import Data.Maybe (fromMaybe)
import Distribution.Simple.LocalBuildInfo (hostPlatform)
import Distribution.Simple.SetupHooks
import Distribution.System (OS (..))
import Distribution.Utils.Path
  ( interpretSymbolicPathCWD,
    makeSymbolicPath,
    moduleNameSymbolicPath,
    (<.>),
  )
import System.Directory
  ( copyFile,
    createDirectoryIfMissing,
    doesFileExist,
    makeAbsolute,
  )
import System.Environment (getEnvironment, lookupEnv)
import System.FilePath (takeDirectory, (</>))
import System.Exit (ExitCode (..))
import System.Process
  ( CreateProcess (..),
    callProcess,
    createProcess,
    proc,
    readProcess,
    waitForProcess,
  )

setupHooks :: SetupHooks
setupHooks =
  generatedModulesSetupHooks
    <> solverSetupHooks
    <> tclSetupHooks

-- | Run a process to completion, failing if it does.
--
-- process-1.6.28 exports this as callCreateProcess, but GHC 9.6 and 9.10
-- bundle older versions, and a floor that excludes theirs makes cabal build
-- process from Hackage -- which does not compile against the filepath that
-- GHC 9.10 ships. Spelling it out keeps every supported compiler on its own
-- bundled process.
callCreateProcess :: CreateProcess -> IO ()
callCreateProcess cp = do
  (_, _, _, handle) <- createProcess cp
  code <- waitForProcess handle
  case code of
    ExitSuccess -> pure ()
    ExitFailure n -> ioError (userError ("setup command failed with " <> show n))

isMainLib :: Component -> Bool
isMainLib (CLib Library {libName = LMainLibName}) = True
isMainLib _ = False

-- | Run the action only if the target files don't already exist.
needing :: [FilePath] -> IO () -> IO ()
needing targets act = do
  exists <- and <$> mapM doesFileExist targets
  unless exists $ do
    let nub = fmap NE.head . NE.group . sort
    forM_ (nub (takeDirectory <$> targets)) (createDirectoryIfMissing True)
    act

-- | The hooks to generate the BuildSystem and BuildVersion modules.
generatedModulesSetupHooks :: SetupHooks
generatedModulesSetupHooks = noSetupHooks {configureHooks, buildHooks}
  where
    configureHooks = noConfigureHooks {preConfComponentHook}
    buildHooks = noBuildHooks {preBuildComponentRules}

    -- Declare that the modules are generated.
    preConfComponentHook :: Maybe PreConfComponentHook
    preConfComponentHook = Just $ \inputs -> do
      if isMainLib inputs.component
        then
          pure $
            PreConfComponentOutputs
              { componentDiff =
                  buildInfoComponentDiff
                    (componentName inputs.component)
                    ( emptyBuildInfo
                        { autogenModules = ["BuildSystem", "BuildVersion"]
                        }
                    )
              }
        else
          pure $ noPreConfComponentOutputs inputs

    -- Generate the module.
    preBuildComponentRules :: Maybe PreBuildComponentRules
    preBuildComponentRules = Just . rules (static ()) $ \env -> do
      let locationFor mod =
            Location
              ( autogenComponentModulesDir
                  env.localBuildInfo
                  env.targetInfo.targetCLBI
              )
              (moduleNameSymbolicPath mod <.> "hs")
          pathFor loc = interpretSymbolicPathCWD (location loc)
      let buildSystem = locationFor "BuildSystem"
          buildVersion = locationFor "BuildVersion"
      when (isMainLib (targetComponent env.targetInfo)) $ do
        registerRule_ "BuildSystem.hs" $
          staticRule
            ( mkCommand
                (static Dict)
                (static writeBuildSystemHs)
                (pathFor buildSystem, hostPlatform env.localBuildInfo)
            )
            []
            [buildSystem]
        registerRule_ "BuildVersion.hs" $
          staticRule
            ( mkCommand
                (static Dict)
                (static writeBuildVersionHs)
                (pathFor buildVersion, hostPlatform env.localBuildInfo)
            )
            []
            [buildVersion]

    writeBuildSystemHs :: (FilePath, Platform) -> IO ()
    writeBuildSystemHs (path, Platform _ os) = needing [path] $ do
      binFmtType <- case os of
        Linux -> pure "ELF"
        OSX -> pure "MachO"
        _ -> ioError (userError ("unsupported OS: " <> show os))
      writeFile path . unlines $
        [ "module BuildSystem",
          "  ( BinFmtType(..),",
          "    binFmtToString,",
          "    getBinFmtType,",
          "  )",
          "where",
          "",
          "data BinFmtType = ELF | MachO",
          "",
          "binFmtToString :: BinFmtType -> String",
          "binFmtToString ELF   = \"ELF\"",
          "binFmtToString MachO = \"Mach-O\"",
          "",
          "getBinFmtType :: BinFmtType",
          "getBinFmtType = " <> binFmtType
        ]

    writeBuildVersionHs :: (FilePath, Platform) -> IO ()
    writeBuildVersionHs (path, Platform _ os) = do
      noGit <- fromMaybe "0" <$> lookupEnv "NOGIT"
      noUpdateBuildVersion <- fromMaybe "0" <$> lookupEnv "NOUPDATEBUILDVERSION"
      let newVars =
            [ ("NOGIT", noGit),
              ("NOUPDATEBUILDVERSION", noUpdateBuildVersion)
            ]

      let cmd = proc "./update-build-version.sh" []
      env <- (newVars <>) <$> getEnvironment
      callCreateProcess $ cmd {cwd = Just "src/comp", env = Just env}
      copyFile "src/comp/BuildVersion.hs" path

-- | The hooks that make the vendored solvers available.
--
-- The solvers are shared libraries, so the Haskell library's dynamic object --
-- which is what ghci and runghc load -- carries them as recorded dependencies
-- rather than copies of their code. That is also why they cannot be
-- @extra-bundled-libraries@: cabal keeps those off the library's own link
-- line, and GHC's runtime linker cannot load a static archive on
-- aarch64-darwin at all.
--
-- Cabal is told about them the way tclSetupHooks tells it about Tcl: the
-- directory is computed here and injected into each component, because an
-- absolute path in a build tree cannot be written in the .cabal file.
solverSetupHooks :: SetupHooks
solverSetupHooks = noSetupHooks {configureHooks}
  where
    configureHooks = noConfigureHooks {preConfComponentHook}

    -- The vendored directories are named directly, so nothing has to be
    -- staged anywhere and there is no copy to go missing.
    preConfComponentHook :: Maybe PreConfComponentHook
    preConfComponentHook = Just $ \inputs -> do
      dirs <- solverLibDirs
      pure $
        PreConfComponentOutputs
          { componentDiff =
              buildInfoComponentDiff
                (componentName inputs.component)
                ( emptyBuildInfo
                    { extraLibs = ["stp", "yices"],
                      extraLibDirs = map makeSymbolicPath dirs,
                      -- The solvers record themselves as @rpath/...@, so
                      -- an rpath is the whole of what either platform needs
                      -- to resolve them, and these artifacts run where they
                      -- are built, which makes the build tree's own
                      -- directories the right answer. Naming it on the
                      -- library alone is enough: the executables that link
                      -- the library inherit its ldOptions, and injecting it
                      -- per component instead passes each -rpath twice.
                      ldOptions =
                        [ "-Wl,-rpath," <> dir
                          | isMainLib inputs.component,
                            dir <- dirs
                        ]
                    }
                )
          }

-- | Build the vendored solvers and return the directories holding them.
--
-- The make targets are no-ops once the libraries are up to date, and the
-- libraries are where the make build leaves them, so nothing is staged and
-- nothing can go missing between a configure and a build.
solverLibDirs :: IO [FilePath]
solverLibDirs = do
  scratch <- makeAbsolute ("dist-newstyle" </> "solver-prefix")
  forM_ solvers $ \(sub, _) ->
    callProcess "make" ["-C", sub, "install", "PREFIX=" <> scratch]
  mapM (makeAbsolute . snd) solvers

solvers :: [(FilePath, FilePath)]
solvers =
  [ ("src/vendor/stp", "src/vendor/stp/lib"),
    ("src/vendor/yices", "src/vendor/yices/lib")
  ]

-- | The hooks to link to Tcl.
tclSetupHooks :: SetupHooks
tclSetupHooks = noSetupHooks {configureHooks}
  where
    configureHooks = noConfigureHooks {preConfComponentHook}

    preConfComponentHook :: Maybe PreConfComponentHook
    preConfComponentHook = Just $ \inputs -> do
      let platform arg = readProcess "sh" ["platform.sh", arg] ""
      let trim = f . f where f = reverse . dropWhile isSpace
      let getArgs flag = fmap (drop (length flag)) . filter (flag `isPrefixOf`)
      if isMainLib inputs.component
        then do
          tclInc <- words <$> platform "tclinc"
          tclLibs <- words <$> platform "tcllibs"
          tclVersion <- trim <$> platform "tclversion"

          cflags <- case tclVersion of
            "8.5" -> pure ["-DTCL85"]
            "8.6" -> pure []
            "9.0" -> pure ["-DTCL9"]
            _ -> ioError (userError ("unsupported Tcl version: " <> tclVersion))
          let includeDirs = makeSymbolicPath <$> getArgs "-I" tclInc
              extraLibDirs = makeSymbolicPath <$> getArgs "-L" tclLibs
              extraLibs = getArgs "-l" tclLibs

          pure $
            PreConfComponentOutputs
              { componentDiff =
                  buildInfoComponentDiff
                    (componentName inputs.component)
                    ( emptyBuildInfo
                        { includeDirs,
                          extraLibDirs,
                          extraLibs,
                          ccOptions = cflags,
                          cppOptions = cflags
                        }
                    )
              }
        else pure $ noPreConfComponentOutputs inputs
