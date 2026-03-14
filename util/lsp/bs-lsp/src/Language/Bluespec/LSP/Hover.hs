-- | Hover information provider for Bluespec LSP.
module Language.Bluespec.LSP.Hover
  ( getHoverInfo
  , symbolToHover
  ) where

import Data.Text (Text)
import qualified Data.Text as T

import Language.LSP.Protocol.Types hiding (SymbolKind)

import Language.Bluespec.Position ()
import Language.Bluespec.LSP.SymbolTable
import Language.Bluespec.LSP.Util (spanToRange, positionToPos)

-- | Get hover information for a symbol at a position.
getHoverInfo :: SymbolTable -> Position -> Maybe Hover
getHoverInfo st pos = do
  sym <- lookupAtPosition st (positionToPos pos)
  pure $ symbolToHover sym

-- | Convert a symbol to hover information.
symbolToHover :: Symbol -> Hover
symbolToHover sym = Hover
  { _contents = InL $ MarkupContent MarkupKind_Markdown content
  , _range = Just $ spanToRange (symSpan sym)
  }
  where
    content = T.unlines $ filter (not . T.null)
      [ "**" <> kindLabel (symKind sym) <> "** `" <> symName sym <> "`"
      , ""
      , maybe "" (\t -> "```bluespec\n" <> t <> "\n```") (symType sym)
      , maybe "" (\d -> "\n---\n" <> d) (symDoc sym)
      , maybe "" (\p -> "\n*Defined in: " <> p <> "*") (symParent sym)
      ]

-- | Get human-readable label for symbol kind.
kindLabel :: SymbolKind -> Text
kindLabel SKModule = "module"
kindLabel SKType = "type"
kindLabel SKData = "data"
kindLabel SKInterface = "interface"
kindLabel SKClass = "class"
kindLabel SKFunction = "function"
kindLabel SKConstructor = "constructor"
kindLabel SKField = "field"
kindLabel SKTypeVar = "type variable"
kindLabel SKVariable = "variable"
kindLabel SKParameter = "parameter"

