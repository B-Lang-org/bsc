-- | Intermediate representation for documentation content.
--
-- Both LaTeX @--\@@ comments and plain-text @-- |@ comments are converted
-- to this AST before HTML rendering.  This decouples parsing from rendering
-- and lets the HTML backend remain independent of the input format.
module Language.Bluespec.DocGen.DocAST
  ( DocBlock (..)
  , DocInline (..)
  , Language (..)
  , DocEntry (..)
  , DocKind (..)
  , SrcSpan (..)
  ) where

import Data.Text (Text)

-- ---------------------------------------------------------------------------
-- Block-level nodes
-- ---------------------------------------------------------------------------

-- | A block-level documentation node.
data DocBlock
  = Para       ![DocInline]
  | Heading    !Int ![DocInline]              -- ^ heading level 1–4
  | CodeBlock  !Language !Text               -- ^ fenced code block
  | BulletList ![[DocBlock]]
  | OrderedList ![[DocBlock]]
  | Table      ![[DocInline]] ![[[DocInline]]]  -- ^ header row, data rows
  | HRule                                    -- ^ horizontal rule (\hdivider)
  | VerbBlock  !Text                         -- ^ libverbatim environment
  deriving stock (Show, Eq)

-- ---------------------------------------------------------------------------
-- Inline nodes
-- ---------------------------------------------------------------------------

-- | An inline documentation node.
data DocInline
  = Plain    !Text
  | Code     !Text                           -- ^ inline code (no highlighting)
  | Emph     ![DocInline]
  | Strong   ![DocInline]
  | SymRef   !Text                           -- ^ cross-reference to a named symbol
  | NonTerm  !Text                           -- ^ grammar non-terminal (\nterm)
  deriving stock (Show, Eq)

-- ---------------------------------------------------------------------------
-- Language tag for code blocks
-- ---------------------------------------------------------------------------

data Language
  = LangBluespec   -- ^ Classic .bs
  | LangBSV        -- ^ SystemVerilog .bsv
  | LangVerilog    -- ^ Verilog output
  | LangPlain      -- ^ plain text / unknown
  deriving stock (Show, Eq)

-- ---------------------------------------------------------------------------
-- Top-level entry
-- ---------------------------------------------------------------------------

-- | A fully-parsed documentation entry for one symbol.
data DocEntry = DocEntry
  { dePackage  :: !Text
  , deName     :: !Text
  , deSection  :: !Text      -- ^ "stdlib" or "reference"
  , deKind     :: !DocKind
  , deTypeSig  :: !(Maybe Text)   -- ^ pretty-printed type signature
  , deDoc      :: ![DocBlock]
  , deSpan     :: !SrcSpan
  } deriving stock (Show)

data DocKind
  = DKValue
  | DKType
  | DKClass
  | DKInstance
  | DKConstructor
  | DKField
  deriving stock (Show, Eq, Ord)

-- | Source location (1-indexed, inclusive).
data SrcSpan = SrcSpan
  { spanFile      :: !Text
  , spanStartLine :: !Int
  , spanEndLine   :: !Int
  } deriving stock (Show, Eq)
