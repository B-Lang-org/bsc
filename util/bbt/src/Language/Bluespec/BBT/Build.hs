-- | Invoke @bsc@ with the flags derived from @bsc.toml@.
module Language.Bluespec.BBT.Build
  ( buildTarget
  , BuildResult (..)
  , BuildError (..)
  , dryRunFlags
  ) where

import Control.Exception (IOException, try)
import Data.List (intercalate)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import System.Directory (createDirectoryIfMissing, doesFileExist)
import System.Exit (ExitCode (..))
import System.FilePath ((</>), isRelative)
import System.Process (readProcessWithExitCode)

import Language.Bluespec.BBT.Config
import Language.Bluespec.BBT.Discover

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

data BuildResult
  = BuildOk
  | BuildFailed !Int !String   -- ^ exit code, stderr
  deriving stock (Show)

data BuildError
  = NoTopFile
  | NoTopModule
  | NoTargetConfig !Text
  | TopFileNotFound !FilePath
  | ConflictsRemain ![Conflict]
  deriving stock (Show)

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

-- | Build a named target (or the first/only target if @Nothing@).
buildTarget
  :: Config
  -> Maybe Text   -- ^ target name
  -> Maybe Text   -- ^ profile name
  -> IO (Either BuildError BuildResult)
buildTarget cfg mTarget mProfile = do
  case resolveTarget cfg mTarget of
    Left err -> pure (Left err)
    Right (tname, tcfg) -> do
      srcResult <- discoverSources cfg mProfile
      case srcResult of
        Left cs   -> pure (Left (ConflictsRemain cs))
        Right srcs -> do
          case buildTopFile (cfgBuild cfg) of
            Nothing  -> pure (Left NoTopFile)
            Just top -> do
              let topAbs = absPath (cfgRoot cfg) top
              topExists <- doesFileExist topAbs
              if not topExists
                then pure (Left (TopFileNotFound topAbs))
                else do
                  let flags = assembleBscFlags cfg tcfg mProfile srcs
                  let bdir = fromMaybe "build/bdir" (targetBuildDir tcfg)
                  let absBdir = absPath (cfgRoot cfg) bdir
                  createDirectoryIfMissing True absBdir
                  case targetVerilogDir tcfg of
                    Just vdir -> do
                      let absVdir = absPath (cfgRoot cfg) vdir
                      createDirectoryIfMissing True absVdir
                    Nothing -> pure ()
                  -- When the target has a verilog_dir, generate Verilog:
                  --   bsc -verilog -g <module> ... <topfile>
                  -- Otherwise just type-check/elaborate:
                  --   bsc -elab ... <topfile>
                  -- The per-target top_module override is respected (e.g. the
                  -- verilog target might synthesise mkTop while the build target
                  -- type-checks mkSim).
                  let buildMod = buildTopModule (cfgBuild cfg)
                      modName  = maybe buildMod Just (targetTopModule tcfg)
                      genFlags = case (targetVerilogDir tcfg, modName) of
                        (Just _, Just m) -> ["-verilog", "-g", T.unpack m]
                        _                -> ["-elab"]
                      allFlags = flags ++ genFlags ++ [topAbs]
                  putStrLn $ "[bbt] Building target '" ++ T.unpack tname ++ "'"
                  putStrLn $ "[bbt] bsc " ++ unwords allFlags
                  r <- try (readProcessWithExitCode "bsc" allFlags "") :: IO (Either IOException (ExitCode, String, String))
                  case r of
                    Left ioErr -> pure (Right (BuildFailed 127
                        ("bsc not found in PATH: " ++ show ioErr
                         ++ "\nInstall bsc and ensure it is on your PATH.")))
                    Right (ec, _out, err) ->
                      case ec of
                        ExitSuccess   -> pure (Right BuildOk)
                        ExitFailure n -> pure (Right (BuildFailed n err))

-- | Return the bsc flags that would be passed, without running anything.
dryRunFlags :: Config -> Maybe Text -> Maybe Text -> IO (Either BuildError [String])
dryRunFlags cfg mTarget mProfile = do
  case resolveTarget cfg mTarget of
    Left err -> pure (Left err)
    Right (_, tcfg) -> do
      srcResult <- discoverSources cfg mProfile
      case srcResult of
        Left cs   -> pure (Left (ConflictsRemain cs))
        Right srcs ->
          let base     = assembleBscFlags cfg tcfg mProfile srcs
              buildMod = buildTopModule (cfgBuild cfg)
              modName  = maybe buildMod Just (targetTopModule tcfg)
              genFlags = case (targetVerilogDir tcfg, modName) of
                (Just _, Just m) -> ["-verilog", "-g", T.unpack m]
                _                -> ["-elab"]
          in  pure (Right (base ++ genFlags))

-- ---------------------------------------------------------------------------
-- Internal helpers
-- ---------------------------------------------------------------------------

resolveTarget :: Config -> Maybe Text -> Either BuildError (Text, TargetConfig)
resolveTarget cfg mTarget =
  let targets = cfgTargets cfg
  in case mTarget of
       Just t  -> case Map.lookup t targets of
                    Nothing  -> Left (NoTargetConfig t)
                    Just tc  -> Right (t, tc)
       Nothing ->
         case Map.toAscList targets of
           []            -> Right ("default", defaultTarget)
           ((k, tc) : _) -> Right (k, tc)

defaultTarget :: TargetConfig
defaultTarget = TargetConfig
  { targetVerilogDir = Just "build/verilog"
  , targetBuildDir   = Just "build/bdir"
  , targetInfoDir    = Nothing
  , targetSimDir     = Nothing
  , targetSimulator  = Nothing
  , targetTopModule  = Nothing
  , targetCSources   = []
  , targetCLib       = Nothing
  , targetDefines    = Map.empty
  , targetFlags      = []
  , targetPostBuild  = []
  }

assembleBscFlags :: Config -> TargetConfig -> Maybe Text -> [SourceFile] -> [String]
assembleBscFlags cfg tcfg mProfile srcs =
  let fc   = cfgFlags cfg
      root = cfgRoot cfg
      sp   = searchPath srcs

      -- -p flag: source dirs + stdlib
      pFlag = intercalate ":" (sp ++ ["+"])

      -- build dir
      bdir = fromMaybe "build/bdir" (targetBuildDir tcfg)

      -- verilog dir
      vFlags = case targetVerilogDir tcfg of
                 Just vd -> ["-vdir", absPath root vd]
                 Nothing -> []

      -- info dir
      iFlags = case targetInfoDir tcfg <|> targetBuildDir tcfg of
                 Just id_ -> ["-info-dir", absPath root id_]
                 Nothing  -> []

      -- sim dir
      sFlags = case targetSimDir tcfg of
                 Just sd -> ["-simdir", absPath root sd]
                 Nothing -> []

      -- defines: global + target + profile
      globalDefs   = cfgDefines cfg
      targetDefs   = targetDefines tcfg
      profileDefs  = maybe Map.empty profileDefines
                       (mProfile >>= \p -> Map.lookup p (cfgProfiles cfg))
      allDefs      = globalDefs `Map.union` targetDefs `Map.union` profileDefs
      defFlags     = concatMap mkDefine (Map.toList allDefs)

      -- extra target flags
      extraFlags   = map T.unpack (targetFlags tcfg)

      -- profile extra flags
      profFlags    = maybe [] (map T.unpack . profileFlags)
                       (mProfile >>= \p -> Map.lookup p (cfgProfiles cfg))

  in bscFlags fc
     ++ ["-u"]
     ++ ["-p", pFlag]
     ++ ["-bdir", absPath root bdir]
     ++ vFlags ++ iFlags ++ sFlags
     ++ defFlags
     ++ extraFlags ++ profFlags
  where
    mkDefine (k, "") = ["-D", T.unpack k]
    mkDefine (k, v)  = ["-D", T.unpack k ++ "=" ++ T.unpack v]

    (<|>) Nothing r = r
    (<|>) l _       = l

-- | Make a path absolute relative to the project root.
absPath :: FilePath -> FilePath -> FilePath
absPath root path
  | isRelative path = root </> path
  | otherwise       = path


