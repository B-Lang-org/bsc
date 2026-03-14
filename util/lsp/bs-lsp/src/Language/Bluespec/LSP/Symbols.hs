-- | Document symbols provider for Bluespec LSP.
module Language.Bluespec.LSP.Symbols
  ( getDocumentSymbols
  , symbolToDocumentSymbol
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Language.LSP.Protocol.Types hiding (SymbolKind)
import qualified Language.LSP.Protocol.Types as LSP

import Language.Bluespec.Position (SrcSpan(..), Pos(..))
import Language.Bluespec.LSP.SymbolTable

-- | Get document symbols for outline view (hierarchical).
getDocumentSymbols :: SymbolTable -> [DocumentSymbol]
getDocumentSymbols st =
  map (buildDocSymbol childrenOf) roots
  where
    allSyms = getAllSymbols st
    -- Root symbols have no parent and are outline-worthy
    roots = filter (\s -> isOutlineSymbol s && symParent s == Nothing) allSyms
    -- Group children by their parent name
    childrenOf = buildChildrenMap allSyms

-- | Build a map from parent name to child symbols.
buildChildrenMap :: [Symbol] -> Map Text [Symbol]
buildChildrenMap = foldr insert Map.empty
  where
    insert sym m = case symParent sym of
      Nothing     -> m
      Just parent -> Map.insertWith (++) parent [sym] m

-- | Recursively build a DocumentSymbol with children.
buildDocSymbol :: Map Text [Symbol] -> Symbol -> DocumentSymbol
buildDocSymbol childrenOf sym =
  DocumentSymbol
    { _name = symName sym
    , _detail = symType sym
    , _kind = symKindToLspKind (symKind sym)
    , _tags = Nothing
    , _deprecated = Nothing
    , _range = spanToRange (symSpan sym)
    , _selectionRange = spanToRange (symSpan sym)
    , _children = childrenDocs
    }
  where
    directChildren =
      filter isOutlineSymbol $
      Map.findWithDefault [] (symName sym) childrenOf
    childrenDocs = case map (buildDocSymbol childrenOf) directChildren of
      [] -> Nothing
      cs -> Just cs

-- | Convert a symbol to a flat document symbol (no children).
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

-- | Whether a symbol should appear in the document outline.
isOutlineSymbol :: Symbol -> Bool
isOutlineSymbol sym = case symKind sym of
  SKModule      -> True
  SKType        -> True
  SKData        -> True
  SKInterface   -> True
  SKClass       -> True
  SKFunction    -> True
  SKConstructor -> True
  SKField       -> True
  _             -> False

-- | Convert symbol kind to LSP SymbolKind.
symKindToLspKind :: SymbolKind -> LSP.SymbolKind
symKindToLspKind SKModule      = LSP.SymbolKind_Module
symKindToLspKind SKType        = LSP.SymbolKind_TypeParameter
symKindToLspKind SKData        = LSP.SymbolKind_Enum
symKindToLspKind SKInterface   = LSP.SymbolKind_Interface
symKindToLspKind SKClass       = LSP.SymbolKind_Class
symKindToLspKind SKFunction    = LSP.SymbolKind_Function
symKindToLspKind SKConstructor = LSP.SymbolKind_Constructor
symKindToLspKind SKField       = LSP.SymbolKind_Field
symKindToLspKind SKTypeVar     = LSP.SymbolKind_TypeParameter
symKindToLspKind SKVariable    = LSP.SymbolKind_Variable
symKindToLspKind SKParameter   = LSP.SymbolKind_Variable

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
