{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

-- | Main LSP server for Bluespec.
module Language.Bluespec.LSP.Server
  ( runServer,
  )
where

import Colog.Core (LogAction (..))
import Control.Concurrent (forkIO)
import Control.Concurrent.STM
import Control.Lens ((^.))
import Control.Monad (forM_, void)
import Control.Monad.IO.Class (liftIO)
import Data.Maybe (mapMaybe)
import Data.Text qualified as T
import Language.Bluespec.LSP.Debug (withDebugLogging)
import Language.Bluespec.LSP.Handlers
import Language.Bluespec.LSP.State
import Language.Bluespec.LSP.SymbolTable (LibrarySearchResult (..), discoverLibrariesDirWithDebug, loadPreludeSymbolTable)
import Language.LSP.Protocol.Lens as Lens
import Language.LSP.Protocol.Types
import Language.LSP.Server hiding (runServer)
import System.Directory (doesDirectoryExist, listDirectory)
import System.Environment (lookupEnv)
import System.FilePath ((</>))
import System.IO (hPutStrLn, stderr, stdin, stdout)

-- | Run the LSP server on stdin/stdout.
--
-- If the environment variable @BS_LSP_DEBUG@ is set, all JSON-RPC traffic is
-- tee'd to a log file.  The variable's value is used as the log path; if it
-- is @1@ or empty, @\/tmp\/bs-lsp-debug.log@ is used instead.
runServer :: IO Int
runServer = do
  mDebug <- lookupEnv "BS_LSP_DEBUG"
  stateVar <- newTVarIO emptyServerState
  case mDebug of
    Nothing ->
      runServerWithHandles
        (LogAction $ const $ pure ())
        (LogAction $ const $ pure ())
        stdin
        stdout
        (serverDefinition stateVar)
    Just logPath -> do
      let path = case logPath of { "1" -> ""; p -> p }
      hPutStrLn stderr $ "Bluespec LSP: debug logging to " ++
        (if null path then "/tmp/bs-lsp-debug.log" else path)
      withDebugLogging path $ \teeIn teeOut ->
        runServerWithHandles
          (LogAction $ const $ pure ())
          (LogAction $ const $ pure ())
          teeIn
          teeOut
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

        liftIO $ atomically $ modifyTVar' stateVar $ \state ->
          state {ssWorkspace = workspaceRoots}

        liftIO $ hPutStrLn stderr $ "Workspace roots: " ++ show workspaceRoots

        -- All heavy work (library discovery, Prelude parsing, indexing) runs in
        -- a single background thread so the initialize response is sent instantly.
        -- The bottleneck was discoverLibrariesDirWithDebug running a Bazel query
        -- (JVM startup: ~5-6 s) before any env-var path was found.
        liftIO $ void $ forkIO $ do
          -- 1. Discover standard library location (may run Bazel query).
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
          forM_ workspaceRoots $ \root -> do
            scanWorkspaceForModules stateVar root
            runLspT env $ refreshDiagnosticsForOpenDocs stateVar
            -- Also scan bazel-bin for generated modules.
            let bazelBinPath = root </> "bazel-bin"
            scanWorkspaceForModules stateVar bazelBinPath
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
