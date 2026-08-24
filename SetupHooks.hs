{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StaticPointers #-}

module SetupHooks (setupHooks) where

import Control.Monad (forM_, unless, when)
import Data.Char (isSpace)
import Data.Functor (void)
import Data.List (isPrefixOf, isSuffixOf, sort)
import qualified Data.List.NonEmpty as NE
import Data.Maybe (fromMaybe)
import Distribution.Simple.LocalBuildInfo (hostPlatform)
import Distribution.Simple.SetupHooks
import Distribution.System (OS (..))
import Distribution.Utils.Path
  ( interpretSymbolicPathCWD,
    makeRelativePathEx,
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
import System.Info (os)
import System.Process
  ( CreateProcess (..),
    callCreateProcess,
    callProcess,
    proc,
    readProcess,
  )

setupHooks :: SetupHooks
setupHooks =
  generatedModulesSetupHooks
    <> stpSetupHooks
    <> yicesSetupHooks
    <> tclSetupHooks

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

-- | Create a static library @out@ from other objects @objs@ and static
-- libraries @libs@.
makeStaticLib :: OS -> FilePath -> [FilePath] -> [FilePath] -> IO ()
makeStaticLib Linux out libs objs = do
  void . readProcess "ar" ["-M"] $
    unlines
      ( ["CREATE " <> out]
          <> (("ADDLIB " <>) <$> libs)
          <> (("ADDMOD " <>) <$> objs)
          <> ["SAVE", "END"]
      )
makeStaticLib OSX out libs objs = do
  callProcess "libtool" (["-static", "-o", out] <> libs <> objs)
makeStaticLib os _ _ _ = ioError (userError ("unsupported OS: " <> show os))

-- | The hooks to build STP.
stpSetupHooks :: SetupHooks
stpSetupHooks = noSetupHooks {buildHooks}
  where
    buildHooks = noBuildHooks {postBuildComponentHook}

    postBuildComponentHook :: Maybe PostBuildComponentHook
    postBuildComponentHook = Just $ \env -> do
      let out =
            Location
              (componentBuildDir env.localBuildInfo env.targetInfo.targetCLBI)
              (makeRelativePathEx "libCstp.a")
      let path = interpretSymbolicPathCWD (location out)
      let Platform _ os = hostPlatform env.localBuildInfo
      when (isMainLib (targetComponent env.targetInfo)) $ do
        needing [path] $ do
          needing (stpLibs <> stpObjs) $ do
            callProcess "make" (["-C", stpDir] <> stpLibs <> stpObjs)
          makeStaticLib
            os
            path
            ((stpDir </>) <$> stpLibs)
            ((stpDir </>) <$> stpObjs)

    stpDir :: FilePath
    stpDir = "src/vendor/stp/src"
    stpLibs :: [FilePath]
    stpLibs =
      [ "AST/libast.a",
        "STPManager/libstpmgr.a",
        "absrefine_counterexample/libabstractionrefinement.a",
        "cpp_interface/libcppinterface.a",
        "extlib-abc/libabc.a",
        "extlib-constbv/libconstantbv.a",
        "main/libmain.a",
        "parser/libparser.a",
        "printer/libprinter.a",
        "sat/libminisat.a",
        "simplifier/libsimplifier.a",
        "to-sat/libtosat.a"
      ]
    stpObjs :: [FilePath]
    stpObjs = ["c_interface/c_interface.o"]

-- | The hooks to build Yices.
yicesSetupHooks :: SetupHooks
yicesSetupHooks = noSetupHooks {buildHooks}
  where
    buildHooks = noBuildHooks {postBuildComponentHook}

    postBuildComponentHook :: Maybe PostBuildComponentHook
    postBuildComponentHook = Just $ \env -> do
      let out =
            Location
              (componentBuildDir env.localBuildInfo env.targetInfo.targetCLBI)
              (makeRelativePathEx "libCyices.a")
      let path = interpretSymbolicPathCWD (location out)
      let Platform _ os = hostPlatform env.localBuildInfo
      when (isMainLib (targetComponent env.targetInfo)) $ do
        needing [path] $ do
          needing [yicesLib] $ do
            callProcess "make" ["-C", yicesDir, "LDCONFIG=ldconfig"]
          copyFile yicesLib path

    yicesDir :: FilePath
    yicesDir = "src/vendor/yices/v2.6"
    yicesLib :: FilePath
    yicesLib = "src/vendor/yices/v2.6/yices2-inst/lib/libyices.a"

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
