-- | @bbt sim@ — compile and run a Bluesim simulation.
module Language.Bluespec.BBT.Sim
  ( SimOpts (..)
  , runSim
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
import System.IO (hPutStrLn, stderr)
import System.Process (readProcessWithExitCode, createProcess, proc,
                       waitForProcess, StdStream (..))
import qualified System.Process as P

import Language.Bluespec.BBT.Config
import Language.Bluespec.BBT.Discover

-- | Options for @bbt sim@.
data SimOpts = SimOpts
  { simTarget  :: !(Maybe Text)
  , simProfile :: !(Maybe Text)
  , simArgs    :: ![String]   -- ^ extra arguments forwarded to the sim binary
  } deriving stock (Show)

-- | Build for Bluesim and execute the simulation.
runSim :: Config -> SimOpts -> IO ()
runSim cfg opts = do
  let root    = cfgRoot cfg
      mTarget = simTarget opts
      mProf   = simProfile opts
      tcfg    = resolveT cfg mTarget

  -- Validate config
  -- The target may override top_module (e.g. a sim target using mkSim while
  -- the build target uses mkTop).  Fall back to [build].top_module if not set.
  case (buildTopFile (cfgBuild cfg), buildTopModule (cfgBuild cfg)) of
    (Nothing, _) -> die "bsc.toml: [build] missing 'top_file'"
    (_, Nothing) -> die "bsc.toml: [build] missing 'top_module'"
    (Just top, Just buildMod) -> do
      let modName = maybe buildMod id (targetTopModule tcfg)
          topAbs  = mkAbs root top
      topExists <- doesFileExist topAbs
      if not topExists
        then die $ "Top file not found: " ++ topAbs
        else do
          srcResult <- discoverSources cfg mProf
          case srcResult of
            Left cs -> die $ "Package conflicts (run 'bbt check'): "
                              ++ show (length cs) ++ " conflict(s)"
            Right srcs -> doSim root tcfg modName topAbs srcs opts

doSim
  :: FilePath -> TargetConfig -> Text -> FilePath
  -> [SourceFile] -> SimOpts -> IO ()
doSim root tcfg modName topAbs srcs opts = do
  let bdir    = fromMaybe "build/bdir" (targetBuildDir tcfg)
      simdir  = fromMaybe "build/sim"  (targetSimDir   tcfg)
      absBdir = mkAbs root bdir
      absSimd = mkAbs root simdir
  createDirectoryIfMissing True absBdir
  createDirectoryIfMissing True absSimd

  let pFlag    = intercalate ":" (searchPath srcs ++ ["+"])
      modStr   = T.unpack modName
      absCsrcs = map (mkAbs root) (targetCSources tcfg)

  -- Step 1: compile + elaborate the source file.
  -- -g <module> forces BSC to elaborate (and write a .ba file for) the named
  -- top-level module even when it has no synthesis pragma.  Without this, BSC
  -- only writes .bo files and the link step (which needs a pre-built .ba) fails
  -- with S0040 "No elaboration file (.ba) was found".
  let compileFlags =
        [ "-sim", "-u"
        , "-g",        modStr
        , "-p",        pFlag
        , "-bdir",     absBdir
        , "-simdir",   absSimd
        , "-info-dir", absBdir
        , topAbs
        ]

  putStrLn $ "[bbt] Compiling for Bluesim..."
  r1 <- try (readProcessWithExitCode "bsc" compileFlags "") :: IO (Either IOException (ExitCode, String, String))
  case r1 of
    Left ioErr -> die $ "bsc not found in PATH: " ++ show ioErr
                        ++ "\nInstall bsc and ensure it is on your PATH."
    Right (ExitFailure n, _out, err) -> do
      hPutStrLn stderr err
      die $ "bsc compilation failed (exit " ++ show n ++ ")"
    Right (ExitSuccess, _out, _err) -> do

      -- Step 2: link the Bluesim binary.
      -- C sources (BDPI) must be listed here so BSC can compile and link them.
      let simBin = absSimd </> modStr
          linkFlags =
            [ "-sim"
            , "-p",      pFlag
            , "-bdir",   absBdir
            , "-simdir", absSimd
            , "-e",      modStr
            , "-o",      simBin
            ]
            ++ absCsrcs

      putStrLn $ "[bbt] Linking Bluesim binary..."
      r2 <- try (readProcessWithExitCode "bsc" linkFlags "") :: IO (Either IOException (ExitCode, String, String))
      case r2 of
        Left ioErr -> die $ "bsc not found in PATH: " ++ show ioErr
                            ++ "\nInstall bsc and ensure it is on your PATH."
        Right (ExitFailure n, _out, err) -> do
          hPutStrLn stderr err
          die $ "bsc link failed (exit " ++ show n ++ ")"
        Right (ExitSuccess, _out, _err) -> do
          binExists <- doesFileExist simBin
          if not binExists
            then die $ "Simulation binary not found: " ++ simBin
                   ++ "\n  (Check that 'top_module' in bsc.toml matches the module name)"
            else do
              putStrLn $ "[bbt] Running: " ++ simBin
              -- Inherit stdin/stdout/stderr so simulation binaries that use
              -- terminal I/O or output raw bytes work correctly.
              (_, _, _, ph) <- createProcess
                (proc simBin (simArgs opts))
                  { P.std_in  = Inherit
                  , P.std_out = Inherit
                  , P.std_err = Inherit
                  }
              ec3 <- waitForProcess ph
              case ec3 of
                ExitSuccess   -> putStrLn "[bbt] Simulation finished."
                ExitFailure n -> putStrLn $ "[bbt] Simulation exited with code " ++ show n

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

resolveT :: Config -> Maybe Text -> TargetConfig
resolveT cfg mTarget =
  case mTarget of
    Nothing ->
      case Map.elems (cfgTargets cfg) of
        (tc:_) -> tc
        []     -> simDefaultTarget
    Just t ->
      fromMaybe simDefaultTarget (Map.lookup t (cfgTargets cfg))

simDefaultTarget :: TargetConfig
simDefaultTarget = TargetConfig
  { targetVerilogDir = Just "build/verilog"
  , targetBuildDir   = Just "build/bdir"
  , targetInfoDir    = Nothing
  , targetSimDir     = Just "build/sim"
  , targetSimulator  = Nothing
  , targetTopModule  = Nothing
  , targetCSources   = []
  , targetCLib       = Nothing
  , targetDefines    = Map.empty
  , targetFlags      = []
  , targetPostBuild  = []
  }

mkAbs :: FilePath -> FilePath -> FilePath
mkAbs root path
  | isRelative path = root </> path
  | otherwise       = path

die :: String -> IO ()
die msg = hPutStrLn stderr ("[bbt] Error: " ++ msg)
