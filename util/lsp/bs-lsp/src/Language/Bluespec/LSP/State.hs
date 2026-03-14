{-# LANGUAGE DuplicateRecordFields #-}

-- | Server state management for the Bluespec LSP.
module Language.Bluespec.LSP.State
  ( -- * Server State
    ServerState (..),
    emptyServerState,

    -- * Document State
    DocumentState (..),
    emptyDocumentState,

    -- * Module Index
    ModuleInfo (..),

    -- * Re-exports
    TypeEnv,

    -- * State Operations
    getDocument,
    updateDocument,
    removeDocument,
    getAllDocuments,
    getModuleInfo,
    updateModuleIndex,
    getModuleSymbols,
    setLibraryDirs,
    getLibraryDirs,

    -- * Prelude
    setPreludeSymbols,
    getPreludeSymbols,
  )
where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Language.Bluespec.LSP.SymbolTable (SymbolTable, emptySymbolTable)
import Language.Bluespec.LSP.TypeEnv (TypeEnv, emptyTypeEnv)
import Language.Bluespec.Syntax (Package)
import Language.LSP.Protocol.Types (NormalizedUri)

-- | Per-document state.
data DocumentState = DocumentState
  { -- | Current document text
    dsText :: !Text,
    -- | Parsed AST (Nothing if parse failed)
    dsParsed :: !(Maybe Package),
    -- | Symbol table for this document
    dsSymbols :: !SymbolTable,
    -- | Type environment for this document (for hover inference)
    dsTypeEnv :: !TypeEnv,
    -- | Document version
    dsVersion :: !Int
  }
  deriving stock (Show)

-- | Create empty document state.
emptyDocumentState :: Text -> Int -> DocumentState
emptyDocumentState text version =
  DocumentState
    { dsText = text,
      dsParsed = Nothing,
      dsSymbols = emptySymbolTable,
      dsTypeEnv = emptyTypeEnv,
      dsVersion = version
    }

-- | Information about a module in the workspace.
data ModuleInfo = ModuleInfo
  { -- | Path to the .bs file
    miFilePath :: !FilePath,
    -- | Symbol table (lazily populated)
    miSymbols :: !SymbolTable,
    -- | Parsed AST (if parsed)
    miParsed :: !(Maybe Package)
  }
  deriving stock (Show)

-- | Global server state.
data ServerState = ServerState
  { ssDocuments :: !(Map NormalizedUri DocumentState),
    -- | Workspace roots for import resolution
    ssWorkspace :: ![FilePath],
    -- | Module name -> info mapping
    ssModuleIndex :: !(Map Text ModuleInfo),
    -- | Prelude symbols (loaded from BLUESPECDIR)
    ssPreludeSymbols :: !(Maybe SymbolTable),
    -- | Standard library search directories
    ssLibraryDirs :: ![FilePath]
  }
  deriving stock (Show)

-- | Create empty server state.
emptyServerState :: ServerState
emptyServerState =
  ServerState
    { ssDocuments = Map.empty,
      ssWorkspace = [],
      ssModuleIndex = Map.empty,
      ssPreludeSymbols = Nothing,
      ssLibraryDirs = []
    }

-- | Set the prelude symbol table.
setPreludeSymbols :: Maybe SymbolTable -> ServerState -> ServerState
setPreludeSymbols mSt state = state {ssPreludeSymbols = mSt}

-- | Get the prelude symbol table.
getPreludeSymbols :: ServerState -> Maybe SymbolTable
getPreludeSymbols = ssPreludeSymbols

-- | Set standard library search directories.
setLibraryDirs :: [FilePath] -> ServerState -> ServerState
setLibraryDirs dirs state = state {ssLibraryDirs = dirs}

-- | Get standard library search directories.
getLibraryDirs :: ServerState -> [FilePath]
getLibraryDirs = ssLibraryDirs

-- | Get document state by URI.
getDocument :: NormalizedUri -> ServerState -> Maybe DocumentState
getDocument uri state = Map.lookup uri (ssDocuments state)

-- | Update document state.
updateDocument :: NormalizedUri -> DocumentState -> ServerState -> ServerState
updateDocument uri doc state =
  state
    { ssDocuments = Map.insert uri doc (ssDocuments state)
    }

-- | Remove document from state.
removeDocument :: NormalizedUri -> ServerState -> ServerState
removeDocument uri state =
  state
    { ssDocuments = Map.delete uri (ssDocuments state)
    }

-- | Get all document URIs.
getAllDocuments :: ServerState -> [(NormalizedUri, DocumentState)]
getAllDocuments = Map.toList . ssDocuments

-- | Get module info by module name.
getModuleInfo :: Text -> ServerState -> Maybe ModuleInfo
getModuleInfo modName state = Map.lookup modName (ssModuleIndex state)

-- | Update the module index.
updateModuleIndex :: Text -> ModuleInfo -> ServerState -> ServerState
updateModuleIndex modName info state =
  state
    { ssModuleIndex = Map.insert modName info (ssModuleIndex state)
    }

-- | Get symbols for a module by name.
getModuleSymbols :: Text -> ServerState -> Maybe SymbolTable
getModuleSymbols modName state = miSymbols <$> getModuleInfo modName state
