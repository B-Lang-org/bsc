-- | Shared utilities for position and range conversion, and identifier extraction.
module Language.Bluespec.LSP.Util
  ( spanToRange
  , positionToPos
  , getIdentifierAtPosition
  , parseQualifiedName
  , typeConstructorName
  ) where

import Data.Char (isAlphaNum, isUpper)
import Data.Text (Text)
import qualified Data.Text as T

import Language.LSP.Protocol.Types (Position(..), Range(..))

import Language.Bluespec.Position (SrcSpan(..), Pos(..), Located(..))
import Language.Bluespec.Syntax (QualIdent(..), Type(..), identText)

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

-- | Extract the identifier (possibly qualified) at a given position in source text.
-- Returns Nothing if the cursor is not on an identifier character.
-- Handles qualified names like @Module.symbol@.
getIdentifierAtPosition :: Text -> Position -> Maybe Text
getIdentifierAtPosition sourceText (Position line col) =
  let lineIdx = fromIntegral line
      colIdx  = fromIntegral col
      ls = T.lines sourceText
   in if lineIdx < 0 || lineIdx >= length ls
        then Nothing
        else extractIdentifierAt (ls !! lineIdx) colIdx

-- | Extract identifier at a column position in a line of text.
extractIdentifierAt :: Text -> Int -> Maybe Text
extractIdentifierAt lineText col =
  let chars = T.unpack lineText
      len   = length chars
   in if col < 0 || col >= len
        then Nothing
        else
          let c = chars !! col
           in if isIdentChar c
                then
                  let (start, end) = findIdentifierBounds chars col
                      ident = T.pack $ take (end - start + 1) $ drop start chars
                   in case findModuleQualifier chars start of
                        Just qual -> Just $ qual <> "." <> ident
                        Nothing   -> Just ident
                else Nothing

-- | Check if a character can be part of a Bluespec identifier.
-- Bluespec identifiers can contain alphanumeric characters, underscores, and apostrophes.
isIdentChar :: Char -> Bool
isIdentChar c = isAlphaNum c || c == '_' || c == '\''

-- | Find the full identifier at a position by expanding left and right.
findIdentifierBounds :: String -> Int -> (Int, Int)
findIdentifierBounds chars col = (findStart chars col, findEnd chars col)
  where
    findStart cs idx
      | idx <= 0              = 0
      | isIdentChar (cs !! (idx - 1)) = findStart cs (idx - 1)
      | otherwise             = idx

    findEnd cs idx
      | idx >= length cs - 1  = length cs - 1
      | isIdentChar (cs !! (idx + 1)) = findEnd cs (idx + 1)
      | otherwise             = idx

-- | Find a module qualifier immediately before an identifier (e.g., @Module@ in @Module.foo@).
findModuleQualifier :: String -> Int -> Maybe Text
findModuleQualifier chars identStart
  | identStart <= 1 = Nothing
  | otherwise =
      let dotIdx = identStart - 1
       in if chars !! dotIdx /= '.'
            then Nothing
            else
              let modEnd = dotIdx - 1
               in if modEnd < 0 || not (isIdentChar (chars !! modEnd))
                    then Nothing
                    else
                      let modStart = findQStart chars modEnd
                          modName  = take (modEnd - modStart + 1) $ drop modStart chars
                       in if null modName || not (isUpper (head modName))
                            then Nothing
                            else Just (T.pack modName)
  where
    findQStart cs idx
      | idx <= 0              = 0
      | isIdentChar (cs !! (idx - 1)) = findQStart cs (idx - 1)
      | otherwise             = idx

-- | Parse a potentially qualified name into (Maybe module, symbol).
-- E.g. @"Module.foo"@ → @(Just "Module", "foo")@, @"bar"@ → @(Nothing, "bar")@.
parseQualifiedName :: Text -> (Maybe Text, Text)
parseQualifiedName name =
  case T.breakOnEnd "." name of
    ("", n)     -> (Nothing, n)
    (modPart, n) ->
      let modName = T.dropEnd 1 modPart
      in if T.null modName || T.null n
           then (Nothing, name)
           else (Just modName, n)

-- | Extract the outermost type constructor name from a 'Type'.
-- Returns 'Nothing' for type variables, function types, etc.
-- E.g. @Reg#(UInt#(8))@ → @Just "Reg"@.
typeConstructorName :: Type -> Maybe Text
typeConstructorName (TCon qi) =
  case locVal qi of
    QualIdent _ ident -> Just (identText ident)
typeConstructorName (TApp f _) = typeConstructorName (locVal f)
typeConstructorName _          = Nothing
