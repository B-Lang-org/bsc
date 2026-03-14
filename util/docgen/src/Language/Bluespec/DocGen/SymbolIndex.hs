-- | Build and query the global symbol index for cross-linking.
--
-- At generation time, every documented symbol is registered in the index.
-- During HTML rendering, @SymRef@ nodes are resolved against the index to
-- produce hyperlinks.
module Language.Bluespec.DocGen.SymbolIndex
  ( SymbolRef (..)
  , SymbolIndex
  , buildIndex
  , lookupSymbol
  , anchor
  , renderIndexJson
  ) where

import Data.Aeson ((.=))
import Data.Aeson qualified as Aeson
import Data.ByteString.Lazy (ByteString)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T

import Language.Bluespec.DocGen.DocAST

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

-- | A resolved symbol reference: where to find the symbol in the output.
data SymbolRef = SymbolRef
  { srPackage :: !Text   -- ^ e.g. "Prelude"
  , srSection :: !Text   -- ^ "stdlib" or "reference"
  , srAnchor  :: !Text   -- ^ e.g. "v:mkReg", "t:Reg", "c:Bits"
  } deriving stock (Show, Eq)

-- | Map from symbol name to its location.
type SymbolIndex = Map Text SymbolRef

-- ---------------------------------------------------------------------------
-- Building
-- ---------------------------------------------------------------------------

-- | Build a 'SymbolIndex' from a list of 'DocEntry' values.
buildIndex :: [DocEntry] -> SymbolIndex
buildIndex = foldr insertEntry Map.empty
  where
    insertEntry de idx =
      Map.insert (deName de) (entryToRef de) idx

    entryToRef de = SymbolRef
      { srPackage = dePackage de
      , srSection = deSection de
      , srAnchor  = anchor (deKind de) (deName de)
      }

-- ---------------------------------------------------------------------------
-- Lookup
-- ---------------------------------------------------------------------------

-- | Look up a symbol name in the index.
lookupSymbol :: Text -> SymbolIndex -> Maybe SymbolRef
lookupSymbol = Map.lookup

-- ---------------------------------------------------------------------------
-- Anchor generation
-- ---------------------------------------------------------------------------

-- | Generate an HTML anchor identifier for a symbol.
-- Uses the Haddock convention: @v:@, @t:@, @c:@, @i:@ prefix.
anchor :: DocKind -> Text -> Text
anchor kind name = prefix kind <> name
  where
    prefix DKValue       = "v:"
    prefix DKType        = "t:"
    prefix DKClass       = "c:"
    prefix DKInstance    = "i:"
    prefix DKConstructor = "v:"
    prefix DKField       = "v:"

-- | Build the URL for a symbol reference, relative to the docs root.
symbolUrl :: SymbolRef -> Text
symbolUrl sr =
  srSection sr <> "/" <> srPackage sr <> ".html#" <> srAnchor sr

-- ---------------------------------------------------------------------------
-- JSON export (for LSP and client-side search)
-- ---------------------------------------------------------------------------

-- | Serialise the index to JSON.
renderIndexJson :: SymbolIndex -> ByteString
renderIndexJson idx =
  Aeson.encode $ Aeson.object
    [ "symbols" .= Map.fromList
        [ (name, refToJson ref) | (name, ref) <- Map.toList idx ]
    ]
  where
    refToJson ref = Aeson.object
      [ "package" .= srPackage ref
      , "section" .= srSection ref
      , "anchor"  .= srAnchor  ref
      , "url"     .= symbolUrl ref
      ]
