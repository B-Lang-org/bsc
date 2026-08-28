{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

-- | Source position tracking for the Bluespec parser.
module Language.Bluespec.Position
  ( -- * Source Positions
    Pos (..)
  , SrcSpan (..)
  , Located (..)
  , mkPos
  , mkSpan
  , spanStart
  , spanEnd
  , mergeSpans
  , noSpan
    -- * Utilities
  , located
  , unLoc
  , getLoc
  , mapLoc
  ) where

import Data.Text (Text)
import GHC.Generics (Generic)

-- | A position in source code (1-indexed line and column).
data Pos = Pos
  { posLine   :: !Int
  , posColumn :: !Int
  }
  deriving stock (Eq, Ord, Show, Generic)

-- | Create a position from line and column (1-indexed).
mkPos :: Int -> Int -> Pos
mkPos = Pos

-- | A span in source code, from start to end position.
data SrcSpan = SrcSpan
  { spanFile  :: !Text
  , spanBegin :: !Pos
  , spanFinal :: !Pos
  }
  deriving stock (Eq, Ord, Show, Generic)

-- | Create a span from file, start, and end positions.
mkSpan :: Text -> Pos -> Pos -> SrcSpan
mkSpan = SrcSpan

-- | Get the start position of a span.
spanStart :: SrcSpan -> Pos
spanStart = spanBegin

-- | Get the end position of a span.
spanEnd :: SrcSpan -> Pos
spanEnd = spanFinal

-- | Merge two spans into one covering both.
mergeSpans :: SrcSpan -> SrcSpan -> SrcSpan
mergeSpans s1 s2 = SrcSpan
  { spanFile  = spanFile s1
  , spanBegin = min (spanBegin s1) (spanBegin s2)
  , spanFinal = max (spanFinal s1) (spanFinal s2)
  }

-- | A dummy span for generated code or when position is unknown.
noSpan :: SrcSpan
noSpan = SrcSpan "<no location>" (Pos 0 0) (Pos 0 0)

-- | A value with an attached source span.
data Located a = Located
  { locSpan :: !SrcSpan
  , locVal  :: a
  }
  deriving stock (Eq, Show, Functor, Foldable, Traversable, Generic)

-- | Attach a span to a value.
located :: SrcSpan -> a -> Located a
located = Located

-- | Extract the value from a Located wrapper.
unLoc :: Located a -> a
unLoc = locVal

-- | Get the location from a Located wrapper.
getLoc :: Located a -> SrcSpan
getLoc = locSpan

-- | Map over the value inside a Located wrapper.
mapLoc :: (a -> b) -> Located a -> Located b
mapLoc = fmap
