-- | Parse the LaTeX subset used in BSC library @--\@@ doc comments and the
-- reference manual.
--
-- This is not a full LaTeX parser.  It handles the specific commands and
-- environments that appear in the BSC standard library and reference manual.
-- Unknown commands are passed through as plain text with a warning.
module Language.Bluespec.DocGen.TexParser
  ( parseDocComment
  , parseTexDoc
  , expandMacros
  , MacroEnv
  , emptyMacroEnv
  , collectMacros
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char

import Language.Bluespec.DocGen.DocAST

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

type Parser = Parsec Void Text

-- | Macro environment: maps macro names to their expanded forms.
-- For parameterised macros, the Text contains @#1@, @#2@, … placeholders.
data MacroEnv = MacroEnv
  { meZeroArg :: !(Map Text Text)      -- ^ \name → expansion
  , meOneArg  :: !(Map Text Text)      -- ^ \name{arg} → expansion with #1
  } deriving stock (Show)

emptyMacroEnv :: MacroEnv
emptyMacroEnv = MacroEnv Map.empty Map.empty

-- ---------------------------------------------------------------------------
-- Macro collection (scans preamble for \newcommand)
-- ---------------------------------------------------------------------------

-- | Scan a LaTeX source for @\newcommand@ definitions and build a MacroEnv.
collectMacros :: Text -> MacroEnv
collectMacros src = foldr insert emptyMacroEnv (T.lines src)
  where
    insert line env =
      case parseNewcommand line of
        Nothing         -> env
        Just (name, 0, body) -> env { meZeroArg = Map.insert name body (meZeroArg env) }
        Just (name, _, body) -> env { meOneArg  = Map.insert name body (meOneArg env) }

    parseNewcommand line =
      let stripped = T.strip line
      in if "\\newcommand{" `T.isPrefixOf` stripped
           then Just (parseCmdDef stripped)
           else Nothing

    parseCmdDef line =
      -- \newcommand{\name}[n]{body}  or  \newcommand{\name}{body}
      let afterCmd  = T.drop (T.length "\\newcommand{\\") line
          (name, rest1) = T.breakOn "}" afterCmd
          rest2    = T.drop 1 rest1   -- drop '}'
          (nargs, rest3) = parseOptArg rest2
          body     = T.strip $ T.dropAround (\c -> c == '{' || c == '}') rest3
      in (name, nargs, body)

    parseOptArg t
      | "[" `T.isPrefixOf` t =
          let inner = T.takeWhile (/= ']') (T.drop 1 t)
              rest  = T.drop 1 $ T.dropWhile (/= ']') t
          in (read (T.unpack inner) :: Int, rest)
      | otherwise = (0, t)

-- ---------------------------------------------------------------------------
-- Macro expansion
-- ---------------------------------------------------------------------------

-- | Expand known macros in a block of text; unknown macros are left as-is.
expandMacros :: MacroEnv -> Text -> Text
expandMacros _env txt = txt   -- TODO: implement substitution

-- ---------------------------------------------------------------------------
-- Parse a sequence of @--\@@ comment lines into DocBlocks
-- ---------------------------------------------------------------------------

-- | Strip @--\@ @ prefix from a block of consecutive comment lines and parse
-- the result as LaTeX documentation.
parseDocComment :: [Text] -> [DocBlock]
parseDocComment lines_ =
  let stripped = map stripPrefix lines_
      src      = T.unlines stripped
  in parseTexDoc src

  where
    stripPrefix line =
      let t = T.strip line
      in if "--@ " `T.isPrefixOf` t then T.drop 4 t
         else if "--@" `T.isPrefixOf` t then T.drop 3 t
         else t

-- | Parse a chunk of LaTeX text into a list of DocBlocks.
parseTexDoc :: Text -> [DocBlock]
parseTexDoc src =
  case runParser docParser "<doc>" src of
    Left _   -> [Para [Plain src]]   -- fallback: treat as plain text
    Right bs -> bs

-- ---------------------------------------------------------------------------
-- LaTeX parser (megaparsec)
-- ---------------------------------------------------------------------------

type BlockParser = Parser [DocBlock]

docParser :: BlockParser
docParser = many block <* eof

block :: Parser DocBlock
block = choice
  [ sectionCmd
  , subsectionCmd
  , subsubsectionCmd
  , verbatimEnv
  , bulletList
  , para
  ]

sectionCmd :: Parser DocBlock
sectionCmd = headingCmd "\\section" 1

subsectionCmd :: Parser DocBlock
subsectionCmd = headingCmd "\\subsection" 2

subsubsectionCmd :: Parser DocBlock
subsubsectionCmd = headingCmd "\\subsubsection" 3

-- | Parse a @\cmd{...}@ heading, handling nested braces correctly.
headingCmd :: Text -> Int -> Parser DocBlock
headingCmd cmd level = do
  _ <- string (cmd <> "{")
  content <- manyTill inline (char '}')
  pure $ Heading level content

verbatimEnv :: Parser DocBlock
verbatimEnv = do
  _ <- string "\\begin{libverbatim}" <* optional newline
  content <- manyTill anySingle (string "\\end{libverbatim}")
  pure $ VerbBlock (T.pack content)

bulletList :: Parser DocBlock
bulletList = do
  _ <- string "\\begin{itemize}"
  items <- many item
  _ <- string "\\end{itemize}"
  pure $ BulletList items
  where
    item = do
      _ <- string "\\item" <* space1
      bs <- many (notFollowedBy (string "\\item" <|> string "\\end") *> block)
      pure bs

para :: Parser DocBlock
para = do
  inlines <- some inline
  _ <- many (satisfy (\c -> c == '\n' || c == ' '))
  pure $ Para inlines

-- ---------------------------------------------------------------------------
-- Brace-balanced argument parser
-- ---------------------------------------------------------------------------

-- | Consume a brace-balanced argument, assuming the opening @{@ has already
-- been consumed.  Handles any depth of nesting, so
-- @\index{Foo\@\te{Foo}|textbf}@ parses correctly.
balancedArg :: Parser Text
balancedArg = T.pack <$> go (0 :: Int)
  where
    go depth = do
      c <- anySingle
      case c of
        '}' | depth == 0 -> pure []
        '}'              -> (c :) <$> go (depth - 1)
        '{'              -> (c :) <$> go (depth + 1)
        _                -> (c :) <$> go depth

-- ---------------------------------------------------------------------------
-- Inline parser
-- ---------------------------------------------------------------------------

inline :: Parser DocInline
inline = choice
  [ teCmd          -- \te{Foo} — type/entity reference → SymRef
  , textttCmd      -- \texttt{foo} → Code
  , emphCmd        -- \emph{...} → Emph
  , textbfCmd      -- \textbf{...} → Strong
  , ntermCmd       -- \nterm{...} → NonTerm
  , indexCmd       -- \index{...} → skip (brace-balanced)
  , skipCmd        -- other known no-op commands
  , plainText
  ]

teCmd :: Parser DocInline
teCmd = do
  _ <- string "\\te{"
  name <- balancedArg
  pure $ SymRef name

textttCmd :: Parser DocInline
textttCmd = do
  _ <- string "\\texttt{"
  content <- balancedArg
  pure $ Code content

emphCmd :: Parser DocInline
emphCmd = do
  _ <- string "\\emph{"
  content <- manyTill inline (char '}')
  pure $ Emph content

textbfCmd :: Parser DocInline
textbfCmd = do
  _ <- string "\\textbf{"
  content <- manyTill inline (char '}')
  pure $ Strong content

ntermCmd :: Parser DocInline
ntermCmd = do
  _ <- string "\\nterm{"
  content <- balancedArg
  pure $ NonTerm content

indexCmd :: Parser DocInline
indexCmd = do
  _ <- string "\\index{"
  _ <- balancedArg
  pure $ Plain ""   -- strip index entries from inline text

skipCmd :: Parser DocInline
skipCmd = do
  _ <- choice
    [ string "\\BS"
    , string "\\ie"
    , string "\\eg"
    , string "\\etc"
    , string "\\hdivider"
    , string "\\\\"
    ]
  pure $ Plain " "

plainText :: Parser DocInline
plainText = do
  c <- satisfy notSpecial
  rest <- takeWhileP Nothing notSpecial
  pure $ Plain (T.cons c rest)
  where
    notSpecial ch = ch /= '\\' && ch /= '{' && ch /= '}' && ch /= '\n'
