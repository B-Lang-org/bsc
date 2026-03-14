-- | @bbt@ — Bluespec Build Tool CLI
module Main (main) where

import Control.Monad (forM_)
import Data.List (intercalate, sortOn)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Options.Applicative
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

import Language.Bluespec.BBT.Build
  ( BuildResult (..), BuildError (..), buildTarget, dryRunFlags )
import Language.Bluespec.BBT.Config
  ( Config (..), BuildConfig (..), TargetConfig (..)
  , loadConfigFrom )
import Language.Bluespec.BBT.Discover
  ( SourceFile (..), Conflict (..), discoverSources )
import Language.Bluespec.BBT.Doc (DocOpts (..), runDoc)
import Language.Bluespec.BBT.LspInfo (getLspInfo, renderLspInfo)
import Language.Bluespec.BBT.Project (findBscToml)

-- ---------------------------------------------------------------------------
-- CLI types
-- ---------------------------------------------------------------------------

data Cmd
  = CmdBuild   !BuildOpts
  | CmdCheck   !CheckOpts
  | CmdClean
  | CmdDoc     !DocOpts
  | CmdShow    !ShowCmd
  | CmdLspInfo !LspInfoOpts
  | CmdNew     !Text
  deriving stock (Show)

data BuildOpts = BuildOpts
  { boTarget  :: !(Maybe Text)
  , boProfile :: !(Maybe Text)
  , boDryRun  :: !Bool
  } deriving stock (Show)

data CheckOpts = CheckOpts
  { coProfile :: !(Maybe Text)
  } deriving stock (Show)

data ShowCmd
  = ShowSources !(Maybe Text)
  | ShowConflicts !(Maybe Text)
  | ShowFlags  !(Maybe Text) !(Maybe Text)
  deriving stock (Show)

data LspInfoOpts = LspInfoOpts
  { lioToml    :: !(Maybe FilePath)
  , lioProfile :: !(Maybe Text)
  } deriving stock (Show)

data GlobalOpts = GlobalOpts
  { goToml :: !(Maybe FilePath)
  } deriving stock (Show)

-- ---------------------------------------------------------------------------
-- Parsers
-- ---------------------------------------------------------------------------

globalOpts :: Parser GlobalOpts
globalOpts = GlobalOpts
  <$> optional (strOption (long "toml" <> metavar "FILE"
        <> help "Path to bsc.toml (default: search upwards from cwd)"))

targetOpt :: Parser (Maybe Text)
targetOpt = optional (strOption (long "target" <> short 't' <> metavar "NAME"
  <> help "Build target name"))

profileOpt :: Parser (Maybe Text)
profileOpt = optional (strOption (long "profile" <> short 'p' <> metavar "NAME"
  <> help "Profile name for variant selection"))

buildOpts :: Parser BuildOpts
buildOpts = BuildOpts
  <$> targetOpt
  <*> profileOpt
  <*> switch (long "dry-run" <> help "Print bsc invocation without running it")

checkOpts :: Parser CheckOpts
checkOpts = CheckOpts <$> profileOpt

showCmd :: Parser ShowCmd
showCmd = subparser $ mconcat
  [ command "sources"   (info (ShowSources <$> profileOpt)
      (progDesc "List all source files that would be passed to bsc"))
  , command "conflicts" (info (ShowConflicts <$> profileOpt)
      (progDesc "List only conflicting package names"))
  , command "flags"     (info (ShowFlags <$> targetOpt <*> profileOpt)
      (progDesc "Print the exact bsc invocation (dry run)"))
  ]

docOpts :: Parser DocOpts
docOpts = DocOpts
  <$> strOption (long "out" <> short 'o' <> metavar "DIR"
        <> value "docs" <> showDefault
        <> help "Output directory")
  <*> switch (long "verbose" <> short 'v' <> help "Verbose output")
  <*> profileOpt

lspInfoOpts :: Parser LspInfoOpts
lspInfoOpts = LspInfoOpts
  <$> optional (strOption (long "toml" <> metavar "FILE"
        <> help "Path to bsc.toml"))
  <*> profileOpt

newCmd :: Parser Text
newCmd = strArgument (metavar "NAME" <> help "Project name")

cmdParser :: Parser (GlobalOpts, Cmd)
cmdParser = (,)
  <$> globalOpts
  <*> subparser (mconcat
        [ command "build"    (info (CmdBuild <$> buildOpts)
            (progDesc "Build the default or named target"))
        , command "check"    (info (CmdCheck <$> checkOpts)
            (progDesc "Detect conflicts and syntax-check sources"))
        , command "clean"    (info (pure CmdClean)
            (progDesc "Remove build artifacts"))
        , command "doc"      (info (CmdDoc <$> docOpts)
            (progDesc "Generate HTML documentation for the project"))
        , command "show"     (info (CmdShow <$> showCmd)
            (progDesc "Show project information"))
        , command "lsp-info" (info (CmdLspInfo <$> lspInfoOpts)
            (progDesc "Emit JSON project info for the LSP"))
        , command "new"      (info (CmdNew <$> newCmd)
            (progDesc "Create a new bbt project"))
        ])

-- ---------------------------------------------------------------------------
-- Entrypoint
-- ---------------------------------------------------------------------------

main :: IO ()
main = do
  (gopts, cmd) <- execParser (info (cmdParser <**> helper)
    (fullDesc <> progDesc "bbt — Bluespec Build Tool"
              <> header "bbt — cargo for Bluespec"))
  run gopts cmd

run :: GlobalOpts -> Cmd -> IO ()
run gopts cmd = case cmd of
  CmdNew name     -> runNew name
  CmdBuild   opts -> withBbtConfig gopts (\cfg -> runBuild cfg opts)
  CmdCheck   opts -> withBbtConfig gopts (\cfg -> runCheck cfg opts)
  CmdClean        -> withBbtConfig gopts runClean
  CmdDoc     opts -> withBbtConfig gopts (\cfg -> runDoc cfg opts)
  CmdShow    sc   -> withBbtConfig gopts (\cfg -> runShow cfg sc)
  CmdLspInfo opts -> withBbtConfig gopts (\cfg -> runLspInfo cfg opts)

withBbtConfig :: GlobalOpts -> (Config -> IO ()) -> IO ()
withBbtConfig gopts k = withConfig gopts $ \tomlPath -> do
  cfg <- loadConfigFrom tomlPath >>= either die pure
  k cfg

-- ---------------------------------------------------------------------------
-- Command implementations
-- ---------------------------------------------------------------------------

runBuild :: Config -> BuildOpts -> IO ()
runBuild cfg opts
  | boDryRun opts = do
      result <- dryRunFlags cfg (boTarget opts) (boProfile opts)
      case result of
        Left err -> die (showBuildError err)
        Right flags -> do
          topFile <- case buildTopFile (cfgBuild cfg) of
                       Nothing -> die "bsc.toml: [build] missing 'top_file'"
                       Just f  -> pure f
          putStrLn $ "bsc " ++ unwords flags ++ " -elab " ++ topFile
  | otherwise = do
      result <- buildTarget cfg (boTarget opts) (boProfile opts)
      case result of
        Left err -> die (showBuildError err)
        Right BuildOk -> putStrLn "[bbt] Build succeeded."
        Right (BuildFailed n msg) -> do
          hPutStrLn stderr ("[bbt] Build failed (exit " ++ show n ++ ")")
          hPutStrLn stderr msg
          exitFailure

runCheck :: Config -> CheckOpts -> IO ()
runCheck cfg opts = do
  result <- discoverSources cfg (coProfile opts)
  case result of
    Left conflicts -> do
      hPutStrLn stderr "[bbt] Package name conflicts detected:"
      forM_ conflicts $ \c -> do
        hPutStrLn stderr $ "  package \"" ++ T.unpack (cPackageName c) ++ "\" declared in:"
        forM_ (cFiles c) $ \f -> hPutStrLn stderr $ "    " ++ f
      hPutStrLn stderr "Add [[conflict]] entries to bsc.toml to resolve."
      exitFailure
    Right srcs -> do
      putStrLn $ "[bbt] " ++ show (length srcs) ++ " source files, no conflicts."

runClean :: Config -> IO ()
runClean cfg = do
  let root    = cfgRoot cfg
      targets = Map.elems (cfgTargets cfg)
      bdirs = [ root ++ "/" ++ d | tc <- targets, Just d <- [targetBuildDir tc] ]
      vdirs = [ root ++ "/" ++ d | tc <- targets, Just d <- [targetVerilogDir tc] ]
  forM_ (bdirs ++ vdirs) $ \dir -> do
    putStrLn $ "[bbt] Would clean: " ++ dir
  putStrLn "(Note: bbt clean not yet implemented; remove directories manually)"

runShow :: Config -> ShowCmd -> IO ()
runShow cfg (ShowSources mProfile) = do
  result <- discoverSources cfg mProfile
  case result of
    Left conflicts -> do
      hPutStrLn stderr "[bbt] Conflicts (marked with !):"
      forM_ conflicts $ \c ->
        forM_ (cFiles c) $ \f ->
          putStrLn $ "! " ++ f ++ "  [conflict: " ++ T.unpack (cPackageName c) ++ "]"
      exitFailure
    Right srcs -> do
      let sorted = sortOn sfPath srcs
      forM_ sorted $ \sf ->
        putStrLn $ sfPath sf ++ "  (" ++ T.unpack (sfPackageName sf) ++ ")"
      putStrLn $ "\n" ++ show (length srcs) ++ " files"

runShow cfg (ShowConflicts mProfile) = do
  result <- discoverSources cfg mProfile
  case result of
    Left conflicts -> forM_ conflicts $ \c -> do
      putStrLn $ T.unpack (cPackageName c) ++ ":"
      forM_ (cFiles c) $ \f -> putStrLn $ "  " ++ f
    Right _ -> putStrLn "[bbt] No conflicts."

runShow cfg (ShowFlags mTarget mProfile) = do
  result <- dryRunFlags cfg mTarget mProfile
  case result of
    Left err     -> die (showBuildError err)
    Right flags  -> putStrLn $ "bsc " ++ unwords flags

runLspInfo :: Config -> LspInfoOpts -> IO ()
runLspInfo cfg opts = do
  info_ <- getLspInfo cfg (lioProfile opts)
  TIO.putStrLn (renderLspInfo info_)

runNew :: Text -> IO ()
runNew name = do
  let toml = T.unlines
        [ "[package]"
        , "name    = \"" <> name <> "\""
        , "version = \"0.1.0\""
        , ""
        , "[build]"
        , "top_file   = \"src/Top.bsv\""
        , "top_module = \"mkTop\""
        , "src        = \"src\""
        ]
  TIO.writeFile "bsc.toml" toml
  putStrLn $ "[bbt] Created bsc.toml for project '" ++ T.unpack name ++ "'"

-- ---------------------------------------------------------------------------
-- Utilities
-- ---------------------------------------------------------------------------

withConfig :: GlobalOpts -> (FilePath -> IO ()) -> IO ()
withConfig gopts run_ =
  case goToml gopts of
    Just path -> run_ path
    Nothing   -> do
      mPath <- findBscToml
      case mPath of
        Nothing   -> die "No bsc.toml found (searched upwards from current directory)"
        Just path -> run_ path

showBuildError :: BuildError -> String
showBuildError NoTopFile           = "bsc.toml: [build] missing 'top_file'"
showBuildError NoTopModule         = "bsc.toml: [build] missing 'top_module'"
showBuildError (NoTargetConfig t)  = "bsc.toml: no [target." ++ T.unpack t ++ "] section"
showBuildError (TopFileNotFound p) = "Top file not found: " ++ p
showBuildError (ConflictsRemain cs) =
  "Package name conflicts (run 'bbt show conflicts' for details): "
  ++ intercalate ", " (map (T.unpack . cPackageName) cs)

die :: String -> IO a
die msg = hPutStrLn stderr ("[bbt] Error: " ++ msg) >> exitFailure
