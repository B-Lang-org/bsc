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
import Language.Bluespec.LSP.Handlers
import Language.Bluespec.LSP.State
import Language.Bluespec.LSP.SymbolTable (LibrarySearchResult (..), discoverLibrariesDirWithDebug, loadPreludeSymbolTable)
import Language.LSP.Protocol.Lens as Lens
import Language.LSP.Protocol.Types
import Language.LSP.Server hiding (runServer)
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath ((</>))
import System.IO (hPutStrLn, stderr, stdin, stdout)

-- | Run the LSP server on stdin/stdout.
runServer :: IO Int
runServer = do
  -- Create server state
  stateVar <- newTVarIO emptyServerState

  runServerWithHandles
    (LogAction $ const $ pure ()) -- IO logger (disabled)
    (LogAction $ const $ pure ()) -- LspM logger (disabled)
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

        -- Discover standard library location
        (libDirs, mLibDir) <- liftIO $ do
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

        -- Load prelude symbols
        liftIO $ do
          mPrelude <- loadPreludeSymbolTable
          case mPrelude of
            Nothing -> hPutStrLn stderr "Bluespec LSP: Prelude.bs not found or failed to parse"
            Just _ -> hPutStrLn stderr "Bluespec LSP: Loaded Prelude symbols"
          atomically $ modifyTVar' stateVar (setPreludeSymbols mPrelude)

        -- Extract workspace roots from initialization params
        let initParams = req ^. Lens.params
            workspaceRoots = getWorkspaceRoots initParams

        liftIO $ atomically $ modifyTVar' stateVar $ \state ->
          state {ssWorkspace = workspaceRoots, ssLibraryDirs = libDirs}

        liftIO $ hPutStrLn stderr $ "Workspace roots: " ++ show workspaceRoots

        -- Index standard library in background thread
        liftIO $ case mLibDir of
          Nothing -> pure ()
          Just libDir -> void $ forkIO $ do
            hPutStrLn stderr "Bluespec LSP: Indexing standard library in background..."
            scanWorkspaceForModules stateVar libDir
            hPutStrLn stderr "Bluespec LSP: Standard library indexing complete"
            runLspT env $ refreshDiagnosticsForOpenDocs stateVar

        -- Scan workspace for modules in background thread
        liftIO $ forM_ workspaceRoots $ \root -> do
          void $ forkIO $ do
            scanWorkspaceForModules stateVar root
            runLspT env $ refreshDiagnosticsForOpenDocs stateVar
          -- Also scan bazel-bin for generated modules
          let bazelBinPath = root </> "bazel-bin"
          void $ forkIO $ do
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
