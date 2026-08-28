-- | Parse @-- |@ plain-text doc comments into 'DocBlock's.
--
-- Syntax:
-- - Blank line → paragraph break
-- - 4+ leading spaces → code block
-- - \`backtick\` spans → 'Code'
-- - Single-quoted \'Foo\' → 'SymRef'
-- - \@...\@ spans → 'Code'
module Language.Bluespec.DocGen.PlainParser
  ( parsePlainComment
  ) where

import Data.Text (Text)
import Data.Text qualified as T

import Language.Bluespec.DocGen.DocAST

-- | Strip @-- | @ prefix from a block of comment lines and parse as plain text.
parsePlainComment :: [Text] -> [DocBlock]
parsePlainComment ls =
  let stripped = map stripPrefix ls
  in parseParas stripped
  where
    stripPrefix line =
      let t = T.strip line
      in if "-- | " `T.isPrefixOf` t then T.drop 5 t
         else if "-- |" `T.isPrefixOf` t then T.drop 4 t
         else t

-- ---------------------------------------------------------------------------
-- Block parsing
-- ---------------------------------------------------------------------------

parseParas :: [Text] -> [DocBlock]
parseParas []  = []
parseParas ls  =
  let (block, rest) = splitBlock ls
  in toBlock block : parseParas (dropWhile T.null rest)
  where
    -- A block ends at a blank line or a code block boundary.
    splitBlock [] = ([], [])
    splitBlock (l:ls_)
      | T.null l  = ([], ls_)
      | otherwise = let (bs, rs) = splitBlock ls_
                    in (l : bs, rs)

    toBlock [] = Para []
    toBlock (l:ls_)
      | isCodeLine l =
          let codeLines = map (T.drop 4) (l : takeWhile isCodeLine ls_)
              after     = dropWhile isCodeLine ls_
              allLines  = codeLines ++ parseIndented after
          in CodeBlock LangBluespec (T.unlines allLines)
      | otherwise =
          Para (parseInlines (T.unwords (l : ls_)))

    isCodeLine t = "    " `T.isPrefixOf` t

    parseIndented [] = []
    parseIndented (l:ls_)
      | isCodeLine l = T.drop 4 l : parseIndented ls_
      | otherwise    = []

-- ---------------------------------------------------------------------------
-- Inline parsing (simple state machine)
-- ---------------------------------------------------------------------------

parseInlines :: Text -> [DocInline]
parseInlines t
  | T.null t  = []
  | otherwise = go t
  where
    go s
      | T.null s  = []
      -- backtick code span
      | "`" `T.isPrefixOf` s =
          let (code, rest) = T.breakOn "`" (T.drop 1 s)
          in Code code : go (T.drop 1 rest)
      -- @...@ code span
      | "@" `T.isPrefixOf` s =
          let (code, rest) = T.breakOn "@" (T.drop 1 s)
          in Code code : go (T.drop 1 rest)
      -- 'Foo' symbol reference
      | "'" `T.isPrefixOf` s =
          let rest0 = T.drop 1 s
              (sym, rest1) = T.span isIdentChar rest0
          in if not (T.null sym) && "'" `T.isPrefixOf` rest1
               then SymRef sym : go (T.drop 1 rest1)
               else Plain "'" : go rest0
      | otherwise =
          let (plain, rest) = T.break (\c -> c == '`' || c == '@' || c == '\'') s
          in if T.null plain
               then Plain (T.singleton (T.head s)) : go (T.tail s)
               else Plain plain : go rest

    isIdentChar c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
                 || (c >= '0' && c <= '9') || c == '_'
