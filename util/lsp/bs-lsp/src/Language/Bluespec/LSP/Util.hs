-- | Shared utilities for position and range conversion.
module Language.Bluespec.LSP.Util
  ( spanToRange
  , positionToPos
  ) where

import Language.LSP.Protocol.Types (Position(..), Range(..))

import Language.Bluespec.Position (SrcSpan(..), Pos(..))

-- | Convert a Bluespec 'SrcSpan' to an LSP 'Range'.
-- Bluespec uses 1-indexed positions; LSP uses 0-indexed.
spanToRange :: SrcSpan -> Range
spanToRange SrcSpan{..} = Range
  { _start = Position
      { _line      = fromIntegral (posLine   spanBegin - 1)
      , _character = fromIntegral (posColumn spanBegin - 1)
      }
  , _end = Position
      { _line      = fromIntegral (posLine   spanFinal - 1)
      , _character = fromIntegral (posColumn spanFinal - 1)
      }
  }

-- | Convert an LSP 'Position' (0-indexed) to a Bluespec 'Pos' (1-indexed).
positionToPos :: Position -> Pos
positionToPos (Position line col) = Pos
  { posLine   = fromIntegral line + 1
  , posColumn = fromIntegral col  + 1
  }
