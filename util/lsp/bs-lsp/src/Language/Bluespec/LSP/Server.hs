{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

-- | Main LSP server for Bluespec.
module Language.Bluespec.LSP.Server
  ( runServer,
  )
where

import Colog.Core (LogAction (..))
import Control.Concurrent (forkIO, threadDelay)
import Control.Concurrent.STM
import Control.Exception (SomeException, try)
import Control.Lens ((^.))
import Control.Monad (forM_, void)
import Control.Monad.IO.Class (liftIO)
import Data.Aeson qualified as Aeson
import Data.Aeson.Types (parseMaybe, (.:))
import Data.ByteString.Char8 qualified as BS8
import Data.Maybe (mapMaybe)
import Data.Text qualified as T
import Language.Bluespec.LSP.Handlers
import Language.Bluespec.LSP.State
import Language.Bluespec.LSP.SymbolTable (LibrarySearchResult (..), discoverLibrariesDirWithDebug, loadPreludeSymbolTable)
import Language.LSP.Protocol.Lens as Lens
import Language.LSP.Protocol.Types
import Language.LSP.Server hiding (runServer)
import System.Directory (doesDirectoryExist, doesFileExist, listDirectory)
import System.Exit (ExitCode (..), exitSuccess)
import System.FilePath (takeDirectory, (</>))
import System.IO (hPutStrLn, stderr, stdin, stdout)
import System.Process (CreateProcess (..), proc, readCreateProcessWithExitCode, readProcessWithExitCode)

-- | Run the LSP server on stdin/stdout.
runServer :: IO Int
runServer = do
  stateVar <- newTVarIO emptyServerState
  runServerWithHandles
    (LogAction $ const $ pure ())
    (LogAction $ const $ pure ())
    stdin
    stdout
    (serverDefinition stateVar)

-- | LSP server options.
lspOptions :: Options
lspOptions = defaultOptions

-- | Server definition with capabilities.
serverDefinition :: TVar ServerState -> ServerDefinition ()
serverDefinition stateVar =
  ServerDefinition
    { parseConfig = const $ const $ Right (),
      onConfigChange = const $ pure (),
      defaultConfig = (),
      configSection = "bluespec",
      doInitialize = \env req -> do
        liftIO $ hPutStrLn stderr "Bluespec LSP: Initializing..."

        -- Extract workspace roots immediately (no I/O needed).
        let initParams      = req ^. Lens.params
            workspaceRoots  = getWorkspaceRoots initParams

        -- Watch the client process: exit if VS Code is killed without sending
        -- shutdown/exit (avoids orphaned bs-lsp processes).
        case initParams ^. Lens.processId of
          InL clientPid ->
            liftIO $ void $ forkIO $ watchClientProcess (fromIntegral clientPid)
          _ -> pure ()

        liftIO $ atomically $ modifyTVar' stateVar $ \state ->
          state {ssWorkspace = workspaceRoots}

        liftIO $ hPutStrLn stderr $ "Workspace roots: " ++ show workspaceRoots

        -- All heavy work (library discovery, Prelude parsing, indexing) runs in
        -- a single background thread so the initialize response is sent instantly.
        liftIO $ void $ forkIO $ do
          -- 1. Discover standard library location.
          (libDirs, mLibDir) <- do
            libResult <- discoverLibrariesDirWithDebug
            case libResult of
              LibraryNotFound searched -> do
                hPutStrLn stderr "Bluespec LSP: Standard library not found"
                mapM_ (hPutStrLn stderr . ("  " ++)) searched
                pure ([], Nothing)
              LibraryFound libDir -> do
                hPutStrLn stderr $ "Bluespec LSP: Found standard library at: " ++ libDir
                dirs <- getLibrarySearchDirs libDir
                pure (dirs, Just libDir)

          atomically $ modifyTVar' stateVar $ \state ->
            state {ssLibraryDirs = libDirs}

          -- 2. Load Prelude symbols.
          mPrelude <- loadPreludeSymbolTable
          case mPrelude of
            Nothing -> hPutStrLn stderr "Bluespec LSP: Prelude.bs not found or failed to parse"
            Just _  -> hPutStrLn stderr "Bluespec LSP: Loaded Prelude symbols"
          atomically $ modifyTVar' stateVar (setPreludeSymbols mPrelude)

          -- 3. Index standard library.
          case mLibDir of
            Nothing    -> pure ()
            Just libDir -> do
              hPutStrLn stderr "Bluespec LSP: Indexing standard library in background..."
              scanWorkspaceForModules stateVar libDir
              hPutStrLn stderr "Bluespec LSP: Standard library indexing complete"
              runLspT env $ refreshDiagnosticsForOpenDocs stateVar

          -- 4. Scan workspace roots for modules.
          -- If a bsc.toml is found (searching upward from the root), use
          -- `bbt lsp-info` to get the exact source directories; otherwise
          -- fall back to scanning the full workspace root.
          forM_ workspaceRoots $ \root -> do
            mToml <- findBscTomlFrom root
            scanDirs <- case mToml of
              Nothing -> pure [root]
              Just tomlPath -> do
                let projectDir = takeDirectory tomlPath
                mDirs <- queryBbtSourceDirs projectDir
                case mDirs of
                  Nothing -> do
                    hPutStrLn stderr "bs-lsp: bbt lsp-info unavailable, scanning full workspace"
                    pure [root]
                  Just dirs -> do
                    hPutStrLn stderr $ "bs-lsp: bsc.toml found, scanning bbt source dirs: " ++ show dirs
                    pure dirs
            forM_ scanDirs $ \dir ->
              scanWorkspaceForModules stateVar dir
            runLspT env $ refreshDiagnosticsForOpenDocs stateVar

        pure $ Right env,
      staticHandlers = \_caps -> handlers stateVar,
      interpretHandler = \env -> Iso (runLspT env) liftIO,
      options =
        lspOptions
          { optTextDocumentSync =
              Just $
                TextDocumentSyncOptions
                  { _openClose = Just True,
                    _change = Just TextDocumentSyncKind_Full,
                    _willSave = Just False,
                    _willSaveWaitUntil = Just False,
                    _save = Just $ InR $ SaveOptions {_includeText = Just False}
                  },
            optCompletionTriggerCharacters = Just ['.'],
            optExecuteCommandCommands = Nothing
          }
    }

-- | Extract workspace root paths from initialization params.
getWorkspaceRoots :: InitializeParams -> [FilePath]
getWorkspaceRoots initParams =
  -- First try workspaceFolders, then fall back to rootUri, then rootPath
  case initParams ^. Lens.workspaceFolders of
    Just (InL folders) -> mapMaybe getFolderPath folders
    _ -> case initParams ^. Lens.rootUri of
      InL docUri -> [uriToPath docUri]
      InR _ -> case initParams ^. Lens.rootPath of
        Just (InL path) -> [T.unpack path]
        _ -> []
  where
    getFolderPath folder = Just $ uriToPath (folder ^. Lens.uri)
    uriToPath (Uri u) = T.unpack $ maybe u Prelude.id $ T.stripPrefix "file://" u

-- | Search upward from @dir@ for a @bsc.toml@ manifest file.
findBscTomlFrom :: FilePath -> IO (Maybe FilePath)
findBscTomlFrom dir = do
  let candidate = dir </> "bsc.toml"
  exists <- doesFileExist candidate
  if exists
    then pure (Just candidate)
    else do
      let parent = takeDirectory dir
      if parent == dir   -- reached filesystem root
        then pure Nothing
        else findBscTomlFrom parent

-- | Run @bbt lsp-info@ in @projectDir@ and return its @source_dirs@.
-- Returns 'Nothing' if @bbt@ is not on PATH, exits non-zero, or the output
-- cannot be parsed.
queryBbtSourceDirs :: FilePath -> IO (Maybe [FilePath])
queryBbtSourceDirs projectDir = do
  result <- try run :: IO (Either SomeException (ExitCode, String, String))
  pure $ case result of
    Left _                      -> Nothing
    Right (ExitFailure _, _, _) -> Nothing
    Right (ExitSuccess, out, _) ->
      case Aeson.decodeStrict (BS8.pack out) of
        Nothing  -> Nothing
        Just obj -> parseMaybe (.: "source_dirs") obj
  where
    run = readCreateProcessWithExitCode
            (proc "bbt" ["lsp-info"]) { cwd = Just projectDir }
            ""

-- | Poll every 5 s and exit if the client process (VS Code) is gone.
-- This prevents orphaned bs-lsp processes when VS Code is killed without
-- sending a proper LSP shutdown/exit sequence.
watchClientProcess :: Int -> IO ()
watchClientProcess clientPid = loop
  where
    loop = do
      threadDelay (5 * 1_000_000)
      killResult <- try (readProcessWithExitCode "kill" ["-0", show clientPid] "")
                      :: IO (Either SomeException (ExitCode, String, String))
      case killResult of
        Right (ExitSuccess, _, _) -> loop  -- client still alive
        _                                     -> do    -- client gone or error
          hPutStrLn stderr "bs-lsp: client process gone, exiting"
          exitSuccess

-- | Get standard library search directories (root + immediate subdirs).
getLibrarySearchDirs :: FilePath -> IO [FilePath]
getLibrarySearchDirs libDir = do
  entries <- listDirectory libDir
  let fullPaths = map (libDir </>) entries
  subdirs <- filterM doesDirectoryExist fullPaths
  pure (libDir : subdirs)
  where
    filterM p = foldr go (pure [])
      where
        go x acc = do
          flg <- p x
          if flg then (x :) <$> acc else acc
