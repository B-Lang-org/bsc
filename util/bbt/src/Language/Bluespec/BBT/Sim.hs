-- | @bbt sim@ — compile and run a Bluesim simulation.
module Language.Bluespec.BBT.Sim
  ( SimOpts (..)
  , runSim
  ) where

import Data.List (intercalate)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import System.Directory (createDirectoryIfMissing, doesFileExist)
import System.Exit (ExitCode (..))
import System.FilePath ((</>), isRelative)
import System.IO (hPutStrLn, stderr)
import System.Process (readProcessWithExitCode)

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
  case (buildTopFile (cfgBuild cfg), buildTopModule (cfgBuild cfg)) of
    (Nothing, _) -> die "bsc.toml: [build] missing 'top_file'"
    (_, Nothing) -> die "bsc.toml: [build] missing 'top_module'"
    (Just top, Just modName) -> do
      let topAbs = mkAbs root top
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

  let pFlag = intercalate ":" (searchPath srcs ++ ["+"])
      flags  =
        [ "-sim", "-u"
        , "-p",       pFlag
        , "-bdir",    absBdir
        , "-simdir",  absSimd
        , "-info-dir", absBdir
        , "-e", T.unpack modName
        , topAbs
        ]

  putStrLn $ "[bbt] Compiling for Bluesim..."
  (ec, _out, err) <- readProcessWithExitCode "bsc" flags ""
  case ec of
    ExitFailure n -> do
      hPutStrLn stderr err
      die $ "bsc compilation failed (exit " ++ show n ++ ")"
    ExitSuccess -> do
      -- The sim binary bsc produces has the module name as the filename
      let simBin = absSimd </> T.unpack modName
      binExists <- doesFileExist simBin
      if not binExists
        then die $ "Simulation binary not found: " ++ simBin
               ++ "\n  (Check that 'top_module' in bsc.toml matches the module name)"
        else do
          putStrLn $ "[bbt] Running: " ++ simBin
          (ec2, out2, err2) <- readProcessWithExitCode simBin (simArgs opts) ""
          putStr out2
          putStr err2
          case ec2 of
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
