-- | Document symbols provider for Bluespec LSP.
module Language.Bluespec.LSP.Symbols
  ( getDocumentSymbols
  , symbolToDocumentSymbol
  ) where

import Language.LSP.Protocol.Types hiding (SymbolKind)
import qualified Language.LSP.Protocol.Types as LSP

import Language.Bluespec.Position (SrcSpan(..), Pos(..))
import Language.Bluespec.LSP.SymbolTable

-- | Get document symbols for outline view.
getDocumentSymbols :: SymbolTable -> [DocumentSymbol]
getDocumentSymbols st = map symbolToDocumentSymbol topLevelSymbols
  where
    -- Only include top-level symbols (those without a parent)
    topLevelSymbols = filter (isTopLevel . symKind) (getAllSymbols st)

    isTopLevel SKModule = True
    isTopLevel SKType = True
    isTopLevel SKData = True
    isTopLevel SKInterface = True
    isTopLevel SKClass = True
    isTopLevel SKFunction = True
    isTopLevel SKConstructor = True  -- Top-level constructors
    isTopLevel _ = False

-- | Convert a symbol to a document symbol.
symbolToDocumentSymbol :: Symbol -> DocumentSymbol
symbolToDocumentSymbol sym = DocumentSymbol
  { _name = symName sym
  , _detail = symType sym
  , _kind = symKindToLspKind (symKind sym)
  , _tags = Nothing
  , _deprecated = Nothing
  , _range = spanToRange (symSpan sym)
  , _selectionRange = spanToRange (symSpan sym)
  , _children = Nothing
  }

-- | Convert symbol kind to LSP SymbolKind.
symKindToLspKind :: SymbolKind -> LSP.SymbolKind
symKindToLspKind SKModule = LSP.SymbolKind_Module
symKindToLspKind SKType = LSP.SymbolKind_TypeParameter
symKindToLspKind SKData = LSP.SymbolKind_Struct
symKindToLspKind SKInterface = LSP.SymbolKind_Interface
symKindToLspKind SKClass = LSP.SymbolKind_Class
symKindToLspKind SKFunction = LSP.SymbolKind_Function
symKindToLspKind SKConstructor = LSP.SymbolKind_Constructor
symKindToLspKind SKField = LSP.SymbolKind_Field
symKindToLspKind SKTypeVar = LSP.SymbolKind_TypeParameter
symKindToLspKind SKVariable = LSP.SymbolKind_Variable
symKindToLspKind SKParameter = LSP.SymbolKind_Variable

-- | Convert SrcSpan to LSP Range.
spanToRange :: SrcSpan -> Range
spanToRange SrcSpan{..} = Range
  { _start = Position
      { _line = fromIntegral (posLine spanBegin - 1)
      , _character = fromIntegral (posColumn spanBegin - 1)
      }
  , _end = Position
      { _line = fromIntegral (posLine spanFinal - 1)
      , _character = fromIntegral (posColumn spanFinal - 1)
      }
  }
