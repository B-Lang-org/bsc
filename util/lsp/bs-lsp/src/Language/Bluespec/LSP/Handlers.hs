{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | LSP request handlers for Bluespec.
module Language.Bluespec.LSP.Handlers
  ( handlers,
    scanWorkspaceForModules,
  )
where

import Control.Concurrent.STM
import Control.Lens ((^.))
import Control.Monad (forM_, when)
import Control.Monad.IO.Class (liftIO)
import Data.List (isPrefixOf)
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Language.Bluespec.LSP.Completion (getCompletions)
import Language.Bluespec.LSP.Definition
import Language.Bluespec.LSP.Diagnostics
import Language.Bluespec.LSP.Hover (getHoverInfoCrossFile)
import Language.Bluespec.LSP.State
import Language.Bluespec.LSP.SymbolTable
import Language.Bluespec.LSP.Symbols
import Language.Bluespec.LSP.TypeEnv (buildTypeEnv)
import Language.Bluespec.Parser (parseAuto, parseAutoRecovering)
import Language.Bluespec.Syntax (ModuleId (..), Package)
import Language.LSP.Protocol.Lens as Lens
import Language.LSP.Protocol.Message
import Language.LSP.Protocol.Types
import Language.LSP.Server
import System.Directory (doesDirectoryExist, doesFileExist, listDirectory)
import System.FilePath (splitDirectories, takeBaseName, takeDirectory, takeExtension, (<.>), (</>))
import System.IO (hPutStrLn, stderr)

-- | All LSP handlers.
handlers :: TVar ServerState -> Handlers (LspM ())
handlers stateVar =
  mconcat
    [ -- Initialization
      notificationHandler SMethod_Initialized $ \_ -> do
        liftIO $ hPutStrLn stderr "Bluespec LSP server initialized",
      -- Document synchronization
      notificationHandler SMethod_TextDocumentDidOpen $ \msg -> do
        let doc = msg ^. Lens.params . Lens.textDocument
            docUri = doc ^. Lens.uri
            docText = doc ^. Lens.text
            docVersion = fromIntegral $ doc ^. Lens.version
        handleDocumentOpen stateVar docUri docText docVersion,
      notificationHandler SMethod_TextDocumentDidChange $ \msg -> do
        let docUri = msg ^. Lens.params . Lens.textDocument . Lens.uri
            changes = msg ^. Lens.params . Lens.contentChanges
        handleDocumentChange stateVar docUri changes,
      notificationHandler SMethod_TextDocumentDidClose $ \msg -> do
        let docUri = msg ^. Lens.params . Lens.textDocument . Lens.uri
        handleDocumentClose stateVar docUri,
      -- Hover
      requestHandler SMethod_TextDocumentHover $ \req responder -> do
        let docUri = req ^. Lens.params . Lens.textDocument . Lens.uri
            pos = req ^. Lens.params . Lens.position
        result <- handleHover stateVar docUri pos
        responder $ Right result,
      -- Go to definition
      requestHandler SMethod_TextDocumentDefinition $ \req responder -> do
        let docUri = req ^. Lens.params . Lens.textDocument . Lens.uri
            pos = req ^. Lens.params . Lens.position
        result <- handleDefinition stateVar docUri pos
        responder $ Right result,
      -- Document symbols (outline)
      requestHandler SMethod_TextDocumentDocumentSymbol $ \req responder -> do
        let docUri = req ^. Lens.params . Lens.textDocument . Lens.uri
        result <- handleDocumentSymbols stateVar docUri
        responder $ Right result,
      -- Completions
      requestHandler SMethod_TextDocumentCompletion $ \req responder -> do
        let docUri = req ^. Lens.params . Lens.textDocument . Lens.uri
            pos    = req ^. Lens.params . Lens.position
        result <- handleCompletion stateVar docUri pos
        responder $ Right result
    ]

-- | Handle document open - parse and publish diagnostics.
handleDocumentOpen :: TVar ServerState -> Uri -> Text -> Int -> LspM () ()
handleDocumentOpen stateVar docUri docText docVersion =
  parseAndUpdateDocument stateVar docUri docText docVersion

-- | Handle document change - re-parse and publish diagnostics.
handleDocumentChange :: TVar ServerState -> Uri -> [TextDocumentContentChangeEvent] -> LspM () ()
handleDocumentChange stateVar docUri changes = do
  let nuri = toNormalizedUri docUri
  state <- liftIO $ readTVarIO stateVar
  let mDoc = getDocument nuri state
      newText = case changes of
        []      -> maybe "" dsText mDoc
        (c : _) -> getChangeText c mDoc
      newVersion = maybe 0 ((+ 1) . dsVersion) mDoc
  parseAndUpdateDocument stateVar docUri newText newVersion

-- | Shared helper: parse text, update state, publish diagnostics.
parseAndUpdateDocument :: TVar ServerState -> Uri -> Text -> Int -> LspM () ()
parseAndUpdateDocument stateVar docUri docText docVersion = do
  let nuri     = toNormalizedUri docUri
      filename = uriToFilename docUri
      (pkg, merrs) = parseAutoRecovering (T.unpack filename) docText
      symbols  = buildSymbolTable pkg
      typeEnv  = buildTypeEnv pkg
      docState = DocumentState
        { dsText    = docText
        , dsParsed  = Just pkg
        , dsSymbols = symbols
        , dsTypeEnv = typeEnv
        , dsVersion = docVersion
        }
  liftIO $ atomically $ modifyTVar' stateVar $ updateDocument nuri docState
  liftIO $ updateModuleIndexFromDoc stateVar filename (Just pkg) symbols typeEnv
  state' <- liftIO $ readTVarIO stateVar
  let parseDiags  = makeDiagnostics (maybe (Right pkg) Left merrs)
      importDiags = makeImportDiagnostics (ssModuleIndex state') symbols
  sendDiagnostics docUri docVersion (parseDiags ++ importDiags)

-- | Handle document close - remove from state.
handleDocumentClose :: TVar ServerState -> Uri -> LspM () ()
handleDocumentClose stateVar docUri = do
  let nuri = toNormalizedUri docUri
  liftIO $ atomically $ modifyTVar' stateVar $ removeDocument nuri
  -- Clear diagnostics
  sendDiagnostics docUri 0 []

-- | Handle hover request.
handleHover :: TVar ServerState -> Uri -> Position -> LspM () (Hover |? Null)
handleHover stateVar docUri pos = do
  let nuri = toNormalizedUri docUri
  state <- liftIO $ readTVarIO stateVar
  case getDocument nuri state of
    Nothing -> pure $ InR Null
    Just doc -> case getHoverInfoCrossFile state (dsTypeEnv doc) (dsSymbols doc) (dsText doc) pos of
      Nothing -> pure $ InR Null
      Just hoverInfo -> pure $ InL hoverInfo

-- | Handle go-to-definition request.
handleDefinition :: TVar ServerState -> Uri -> Position -> LspM () (Definition |? ([DefinitionLink] |? Null))
handleDefinition stateVar docUri pos = do
  let nuri = toNormalizedUri docUri
  state <- liftIO $ readTVarIO stateVar
  case getDocument nuri state of
    Nothing -> pure $ InR $ InR Null
    Just doc -> case getDefinitionCrossFile state (dsTypeEnv doc) (dsSymbols doc) (dsText doc) pos of
      Just loc -> pure $ InL $ Definition $ InL loc
      Nothing -> do
        let docPath = T.unpack (uriToFilename docUri)
            imports = stImports (dsSymbols doc)
        case dsParsed doc of
          Nothing ->
            if null imports
              then liftIO $ hPutStrLn stderr $ "Bluespec LSP: Document parse failed; imports unavailable for " ++ docPath
              else pure ()
          Just _ -> pure ()
        liftIO $
          ensureImportsIndexed
            stateVar
            (ssWorkspace state)
            (ssLibraryDirs state)
            docPath
            imports
        state' <- liftIO $ readTVarIO stateVar
        case getDefinitionCrossFile state' (dsTypeEnv doc) (dsSymbols doc) (dsText doc) pos of
          Nothing -> pure $ InR $ InR Null
          Just loc -> pure $ InL $ Definition $ InL loc

-- | Handle document symbols request.
-- Returns hierarchical DocumentSymbol list (the modern format).
handleDocumentSymbols :: TVar ServerState -> Uri -> LspM () ([SymbolInformation] |? ([DocumentSymbol] |? Null))
handleDocumentSymbols stateVar docUri = do
  let nuri = toNormalizedUri docUri
  state <- liftIO $ readTVarIO stateVar
  case getDocument nuri state of
    Nothing -> pure $ InR $ InR Null
    Just doc -> pure $ InR $ InL $ getDocumentSymbols (dsSymbols doc)

-- | Handle completion request.
handleCompletion :: TVar ServerState -> Uri -> Position -> LspM () ([CompletionItem] |? (CompletionList |? Null))
handleCompletion stateVar docUri pos = do
  let nuri = toNormalizedUri docUri
  state <- liftIO $ readTVarIO stateVar
  case getDocument nuri state of
    Nothing  -> pure $ InR $ InR Null
    Just doc ->
      let items = getCompletions state doc (dsText doc) pos
      in  pure $ InL items

-- | Extract filename from URI.
uriToFilename :: Uri -> Text
uriToFilename (Uri u) = case T.stripPrefix "file://" u of
  Just path -> path
  Nothing -> u

-- | Send diagnostics to the client.
sendDiagnostics :: Uri -> Int -> [Diagnostic] -> LspM () ()
sendDiagnostics docUri docVersion diags = do
  let params =
        PublishDiagnosticsParams
          { _uri = docUri,
            _version = Just $ fromIntegral docVersion,
            _diagnostics = diags
          }
  sendNotification SMethod_TextDocumentPublishDiagnostics params

-- | Extract text from a content change event
getChangeText :: TextDocumentContentChangeEvent -> Maybe DocumentState -> Text
getChangeText (TextDocumentContentChangeEvent change) mDoc = case change of
  InR whole -> whole ^. Lens.text -- Whole document change
  InL _partial -> maybe "" dsText mDoc -- Partial changes not supported yet

-- | Ensure imported modules are indexed for cross-file lookups.
-- Uses fast path checks to avoid blocking LSP requests.
ensureImportsIndexed :: TVar ServerState -> [FilePath] -> [FilePath] -> FilePath -> [ImportInfo] -> IO ()
ensureImportsIndexed stateVar workspaceRoots libraryDirs docPath imports = do
  let docDir = takeDirectory docPath
      topLevelDirs = mapMaybe (topLevelDir docPath) workspaceRoots
      topLevelSearch =
        concatMap
          (\(root, topDir) -> [root </> topDir, root </> "bazel-bin" </> topDir])
          topLevelDirs
      searchDirs =
        docDir
          : workspaceRoots
          ++ map (</> "bazel-bin") workspaceRoots
          ++ topLevelSearch
          ++ libraryDirs
  forM_ imports $ \imp -> do
    state <- readTVarIO stateVar
    let ModuleId modName = iiModule imp
    case getModuleInfo modName state of
      Just _ -> pure ()
      Nothing -> do
        mPath <- findModuleFileInDirs searchDirs (T.unpack modName)
        mPath' <- case mPath of
          Just _ -> pure mPath
          Nothing -> findModuleFileInSubdirs topLevelSearch (T.unpack modName)
        case mPath' of
          Nothing ->
            hPutStrLn stderr $
              "Bluespec LSP: Could not locate module for import "
                ++ T.unpack modName
                ++ " (from "
                ++ docPath
                ++ ")"
          Just path -> indexModuleFile stateVar path

-- | Find a .bs file by module name in known directories.
findModuleFileInDirs :: [FilePath] -> String -> IO (Maybe FilePath)
findModuleFileInDirs dirs moduleName = go dirs
  where
    go [] = pure Nothing
    go (d : ds) = do
      let candidate = d </> moduleName <.> "bs"
      exists <- doesFileExist candidate
      if exists then pure (Just candidate) else go ds

-- | Find a .bs file by module name one level below known directories.
findModuleFileInSubdirs :: [FilePath] -> String -> IO (Maybe FilePath)
findModuleFileInSubdirs dirs moduleName = go dirs
  where
    go [] = pure Nothing
    go (d : ds) = do
      isDir <- doesDirectoryExist d
      if not isDir
        then go ds
        else do
          entries <- listDirectory d
          mFound <- findInEntries d entries
          case mFound of
            Just _ -> pure mFound
            Nothing -> go ds
    findInEntries _ [] = pure Nothing
    findInEntries base (entry : rest) = do
      let candidate = base </> entry </> moduleName <.> "bs"
      exists <- doesFileExist candidate
      if exists then pure (Just candidate) else findInEntries base rest

topLevelDir :: FilePath -> FilePath -> Maybe (FilePath, FilePath)
topLevelDir docPath root =
  let docParts = splitDirectories docPath
      rootParts = splitDirectories root
   in if rootParts `isPrefixOf` docParts
        then case drop (Prelude.length rootParts) docParts of
          ("bazel-bin" : top : _) -> Just (root, top)
          (top : _) -> Just (root, top)
          _ -> Nothing
        else Nothing

-- | Scan a directory recursively for .bs and .bsv files and add them to the module index.
scanWorkspaceForModules :: TVar ServerState -> FilePath -> IO ()
scanWorkspaceForModules stateVar rootDir = do
  hPutStrLn stderr $ "Scanning workspace for modules: " ++ rootDir
  scanDir rootDir
  where
    scanDir dir = do
      exists <- doesDirectoryExist dir
      if not exists
        then pure ()
        else do
          entries <- listDirectory dir
          forM_ entries $ \entry -> do
            let path = dir ++ "/" ++ entry
            isDir <- doesDirectoryExist path
            isFile <- doesFileExist path
            if isDir
              then scanDir path
              else
                when (isFile && takeExtension entry `elem` [".bs", ".bsv"]) $
                  indexModuleFile stateVar path

-- | Index a single .bs file into the module index.
indexModuleFile :: TVar ServerState -> FilePath -> IO ()
indexModuleFile stateVar filePath = do
  let moduleName = T.pack $ takeBaseName filePath
  -- Read and parse the file
  result <- tryReadAndParse filePath
  case result of
    Left err -> do
      hPutStrLn stderr $
        "Bluespec LSP: Failed to parse " ++ filePath ++ ": " ++ take 200 err
      pure ()
    Right (_text, pkg, symbols) -> do
      let typeEnv = buildTypeEnv pkg
          info =
            ModuleInfo
              { miFilePath = filePath,
                miSymbols = symbols,
                miTypeEnv = typeEnv,
                miParsed = Just pkg
              }
      atomically $ modifyTVar' stateVar $ updateModuleIndex moduleName info

-- | Try to read and parse a .bs or .bsv file.
tryReadAndParse :: FilePath -> IO (Either String (Text, Package, SymbolTable))
tryReadAndParse filePath = do
  text <- TIO.readFile filePath
  case parseAuto filePath text of
    Left err -> pure $ Left (show err)
    Right pkg -> pure $ Right (text, pkg, buildSymbolTable pkg)

-- | Update module index when a document is opened/changed.
updateModuleIndexFromDoc :: TVar ServerState -> Text -> Maybe Package -> SymbolTable -> TypeEnv -> IO ()
updateModuleIndexFromDoc stateVar filePath mPkg symbols typeEnv = do
  -- Extract module name from the package or use filename
  let modName = case mPkg of
        Just _pkg -> stPackageName symbols
        Nothing   -> Just $ T.pack $ takeBaseName $ T.unpack filePath
  case modName of
    Nothing -> pure ()
    Just name -> do
      let info =
            ModuleInfo
              { miFilePath = T.unpack filePath,
                miSymbols = symbols,
                miTypeEnv = typeEnv,
                miParsed = mPkg
              }
      atomically $ modifyTVar' stateVar $ updateModuleIndex name info
