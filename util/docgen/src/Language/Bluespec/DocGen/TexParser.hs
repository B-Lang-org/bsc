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

import Control.Monad (void)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
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

-- | Macros that have dedicated inline parsers and should NOT be expanded
-- by the macro system.  Expanding them produces complex LaTeX (e.g. \makebox,
-- \begingroup) that the parser cannot sensibly render.
skippedMacros :: Set Text
skippedMacros = Set.fromList
  [ "te", "nterm", "term", "qbs"
  , "many", "opt", "alt"
  , "gram", "grammore", "gramalt", "litem"
  , "EBS", "BBS"
  , "ttsymbol"
  ]

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
        Just (_, _, body) | not (balancedBraces body) -> env  -- unbalanced/multi-line, skip
        Just (name, _, _) | Set.member name skippedMacros -> env  -- has dedicated parser
        Just (name, 0, body) -> env { meZeroArg = Map.insert name body (meZeroArg env) }
        Just (name, _, body) -> env { meOneArg  = Map.insert name body (meOneArg env) }

    balancedBraces t = go (0 :: Int) (T.unpack t)
      where
        go d []       = d == 0
        go d ('{':cs) = go (d+1) cs
        go d ('}':cs) = if d > 0 then go (d-1) cs else False
        go d (_:cs)   = go d cs

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
          body     = T.strip $ stripOuterBraces rest3
          stripOuterBraces t
            | "{" `T.isPrefixOf` t && "}" `T.isSuffixOf` t = T.drop 1 (T.dropEnd 1 t)
            | otherwise = t
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
expandMacros env = go
  where
    go t
      | T.null t = T.empty
      -- Curly-braced macro group: {\name} or {\name extra}
      | "{" `T.isPrefixOf` t, Just ('\\', rest) <- T.uncons (T.drop 1 t) =
          let (name, after) = T.span isIdentChar rest
          in case T.uncons after of
               Just ('}', rest2) ->
                 case Map.lookup name (meZeroArg env) of
                   Just expansion -> go (expansion <> rest2)
                   Nothing        -> "{" <> "\\" <> name <> "}" <> go rest2
               Just (' ', rest2) ->
                 case Map.lookup name (meZeroArg env) of
                   Just expansion ->
                     let (extra, rest3) = T.breakOn "}" rest2
                     in go (expansion <> extra <> T.drop 1 rest3)
                   Nothing -> T.cons '{' $ go (T.drop 1 t)
               _ -> T.cons '{' $ go (T.drop 1 t)
      -- Macro call: \name or \name{arg}
      | "\\" `T.isPrefixOf` t =
          let (name, after) = T.span isIdentChar (T.drop 1 t)
          in if T.null name
               then "\\" <> go after
               else case Map.lookup name (meOneArg env) of
                 Just template ->
                   case T.uncons (T.stripStart after) of
                     Just ('{', rest2) ->
                       let arg      = consumeBalanced rest2
                           rest3    = T.drop (T.length arg + 1) rest2
                           expanded = T.replace "#1" arg template
                       in go (expanded <> rest3)
                     _ -> "\\" <> name <> go after
                 Nothing ->
                   case Map.lookup name (meZeroArg env) of
                     Just expansion -> go (expansion <> after)
                     Nothing        -> "\\" <> name <> go after
      | otherwise =
          -- Break at the next '\' or '{'.  If the very first character IS one
          -- of those (e.g. a bare '{' not part of a {\name} group), consume it
          -- literally so we always make forward progress.
          case T.break (\c -> c == '\\' || c == '{') t of
            ("", _)     -> T.cons (T.head t) (go (T.tail t))
            (plain, rest) -> plain <> go rest

    -- Consume a brace-balanced argument.  Handles \{ and \} as escaped braces
    -- (they do not change the depth counter).
    consumeBalanced :: Text -> Text
    consumeBalanced = T.pack . go' (0 :: Int) . T.unpack
      where
        go' _ []             = []
        go' 0 ('}':_)        = []
        go' d ('}':cs)       = '}' : go' (d-1) cs
        go' d ('{':cs)       = '{' : go' (d+1) cs
        go' d ('\\':c:cs)    = '\\' : c : go' d cs  -- \X: skip without depth change
        go' d (c:cs)         = c   : go' d cs

isIdentChar :: Char -> Bool
isIdentChar c = (c >= 'a' && c <= 'z')
             || (c >= 'A' && c <= 'Z')
             || (c >= '0' && c <= '9')

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
-- The parser is best-effort: it extracts all blocks it recognises and
-- silently drops content it cannot parse.  The fallback only fires if
-- the parser itself throws an unexpected exception (should never happen
-- with the current grammar).
parseTexDoc :: Text -> [DocBlock]
parseTexDoc src =
  case runParser docParser "<doc>" src of
    Left _   -> [Para [Plain src]]
    Right bs -> filter nonEmpty bs
  where
    nonEmpty (Para [])          = False
    nonEmpty (Para [Plain ""])  = False
    nonEmpty (Para [Plain " "]) = False
    nonEmpty _                  = True

-- ---------------------------------------------------------------------------
-- LaTeX parser (megaparsec)
-- ---------------------------------------------------------------------------

type BlockParser = Parser [DocBlock]

-- | Top-level document parser.  Does NOT require consuming all input — unknown
-- LaTeX constructs are absorbed by 'block's fallback alternatives.  If the
-- parser somehow stalls we return whatever blocks have been accumulated so far.
docParser :: BlockParser
docParser = skipWhitespace *> many (block <* skipWhitespace)

-- | Consume any amount of whitespace (spaces, newlines, tabs).
skipWhitespace :: Parser ()
skipWhitespace = void $ many (satisfy (\c -> c == '\n' || c == ' ' || c == '\r' || c == '\t'))

-- | All block parsers use 'try' so that if they consume input and then fail,
-- they fully backtrack to let 'para' (with its catch-all inline) absorb the text.
block :: Parser DocBlock
block = choice
  [ try sectionCmd
  , try subsectionCmd
  , try subsubsectionCmd
  , try verbatimEnv
  , try noteEnv
  , try tightlistEnv
  , try bulletList
  , try gramProductionBlock  -- \gram{name}{body} — two-arg grammar production
  , try unknownEnv    -- \begin{unknown}...\end{unknown}
  , para              -- always succeeds if any non-newline char is present
  ]

-- | Skip an unknown @\begin{name}...\end{name}@ environment entirely.
unknownEnv :: Parser DocBlock
unknownEnv = do
  _ <- string "\\begin{"
  envName <- takeWhileP (Just "env name") (\c -> c /= '}' && c /= '\n')
  _ <- char '}'
  _ <- manyTill anySingle (string ("\\end{" <> envName <> "}"))
  pure $ Para []

sectionCmd :: Parser DocBlock
sectionCmd = headingCmd "\\section" 1

subsectionCmd :: Parser DocBlock
subsectionCmd = headingCmd "\\subsection" 2

subsubsectionCmd :: Parser DocBlock
subsubsectionCmd = headingCmd "\\subsubsection" 3

-- | Parse a @\cmd{...}@ or @\cmd*{...}@ heading.
headingCmd :: Text -> Int -> Parser DocBlock
headingCmd cmd level = do
  _ <- string cmd
  _ <- optional (char '*')   -- starred variants (\section* etc.) are fine
  _ <- char '{'
  content <- manyTill inline (char '}')
  pure $ Heading level content

verbatimEnv :: Parser DocBlock
verbatimEnv = do
  envName <- choice
    [ string "\\begin{libverbatim}" *> pure "libverbatim"
    , string "\\begin{verbatim}"    *> pure "verbatim"
    , string "\\begin{BH}"          *> pure "BH"
    , string "\\begin{BSV}"         *> pure "BSV"
    ]
  _ <- optional newline
  content <- manyTill anySingle (string ("\\end{" <> envName <> "}"))
  pure $ VerbBlock (T.pack content)

noteEnv :: Parser DocBlock
noteEnv = do
  _ <- string "\\begin{NOTE}" <* optional newline
  blocks <- manyTill block (string "\\end{NOTE}")
  pure $ BulletList [blocks]   -- reuse BulletList as indented block for now

tightlistEnv :: Parser DocBlock
tightlistEnv = do
  _ <- string "\\begin{tightlist}" <* optional newline
  items <- many item
  _ <- string "\\end{tightlist}"
  pure $ BulletList items
  where
    item = do
      _ <- string "\\item" <* space1
      bs <- many (notFollowedBy (string "\\item" <|> string "\\end") *> block)
      pure bs

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

-- | Parse a @\gram{name}{body}@ grammar production (two-arg form).
-- Renders as: NonTerm name, Plain " ::= ", body_inlines...
gramProductionBlock :: Parser DocBlock
gramProductionBlock = do
  _ <- string "\\gram{"
  name <- balancedArg
  _ <- skipMany (satisfy (\c -> c == ' ' || c == '\n' || c == '\r' || c == '\t'))
  _ <- char '{'
  rawBody <- balancedArg
  let bodyBlocks  = parseTexDoc rawBody
      bodyInlines = concatMap paraInlines bodyBlocks
  pure $ Para (NonTerm name : Plain " ::= " : bodyInlines)
  where
    paraInlines (Para is) = is
    paraInlines _         = []

para :: Parser DocBlock
para = do
  inlines <- some inline
  _ <- many (satisfy (\c -> c == '\n' || c == ' '))
  pure $ Para inlines

-- ---------------------------------------------------------------------------
-- Brace-balanced argument parser
-- ---------------------------------------------------------------------------

-- | Consume a brace-balanced argument, assuming the opening @{@ has already
-- been consumed.  Handles @\{@ and @\}@ as escaped braces (they do not change
-- the depth counter and are unescaped to their literal characters).
-- Other @\X@ sequences are preserved verbatim.
balancedArg :: Parser Text
balancedArg = T.pack <$> go (0 :: Int)
  where
    go depth = do
      c <- anySingle
      case c of
        '}' | depth == 0 -> pure []
        '}'              -> (c :) <$> go (depth - 1)
        '{'              -> (c :) <$> go (depth + 1)
        '\\'             -> do
          c2 <- anySingle
          case c2 of
            '{' -> ('{' :) <$> go depth   -- \{ → literal {, don't count depth
            '}' -> ('}' :) <$> go depth   -- \} → literal }, don't count depth
            '#' -> ('#' :) <$> go depth   -- \# → literal #
            '$' -> ('$' :) <$> go depth   -- \$ → literal $
            '%' -> ('%' :) <$> go depth   -- \% → literal %
            _   -> ('\\' :) . (c2 :) <$> go depth
        _                -> (c :) <$> go depth

-- ---------------------------------------------------------------------------
-- Shared inline-to-text conversion
-- ---------------------------------------------------------------------------

-- | Convert an inline element to plain text (for contexts that need a string,
-- such as quoted content, grammar rule names, etc.).
inlineToText :: DocInline -> Text
inlineToText (Plain t)      = t
inlineToText (Code t)       = t
inlineToText (SymRef t)     = t
inlineToText (SectionRef t) = t
inlineToText (NonTerm t)    = t
inlineToText (Emph is)      = T.concat (map inlineToText is)
inlineToText (Strong is)    = T.concat (map inlineToText is)

-- ---------------------------------------------------------------------------
-- Inline parser
-- ---------------------------------------------------------------------------

-- | All inline parsers that start with a fixed prefix use 'try' so that if
-- they consume input and then fail (e.g. unbalanced brace), they fully
-- backtrack and the fallback alternatives get a chance.
inline :: Parser DocInline
inline = choice
  [ try latexQuotes       -- ``...'' → double quotes (before plainText eats backticks)
  , try mathMode          -- $...$ or $$...$$
  , try ttsymbolCmd       -- \ttsymbol{n} → Code (single char at ASCII n)
  , try teCmd             -- \te{Foo} → SymRef
  , try termCmd           -- \term{Foo} → Code
  , try qbsCmd            -- \qbs{code} → Code
  , try ebsCmd            -- \EBS{code} \BBS{code} → Code
  , try textttCmd         -- \texttt{...} → Code
  , try emphCmd           -- \emph{...} → Emph
  , try textbfCmd         -- \textbf{...} → Strong
  , try ntermCmd          -- \nterm{...} → NonTerm
  , try mboxCmd           -- \mbox{...} → render content
  , try gramCmd           -- \grammore{} \gramalt{} \litem{} → NonTerm
  , try manyOptCmd        -- \many{} \opt{} \alt → grammar operators
  , try refCmd            -- \ref{label} → section link
  , try indexCmd          -- \index{...} → stripped
  , skipCmd               -- fixed \name tokens — safe, no try needed
  , try singleNewline     -- \n not followed by \n or block-start → space
  , try unknownCmdInline  -- \unknown{...} → discarded
  , try braceGroup        -- {content} — backtrack if unbalanced
  , plainText
  , inlineCatchAll        -- last resort: any non-newline char
  ]

-- | A single newline that is NOT followed by another newline or a block-level
-- command is treated as a space (soft line break within a paragraph).
-- This prevents each source line from becoming its own @<p>@ tag.
singleNewline :: Parser DocInline
singleNewline = do
  _ <- char '\n'
  notFollowedBy (char '\n')
  notFollowedBy blockStartMarker
  pure $ Plain " "
  where
    blockStartMarker = void $ choice
      [ string "\\section"
      , string "\\subsection"
      , string "\\subsubsection"
      , string "\\begin{"
      , string "\\gram{"
      ]

-- | Consume any single non-newline character as plain text.
-- This ensures the inline parser never fails on unexpected input,
-- so 'para' always makes progress and we never fall back to the
-- whole-document-as-plain-text path.
inlineCatchAll :: Parser DocInline
inlineCatchAll = Plain . T.singleton <$> satisfy (/= '\n')

-- | Render an unknown @\cmd@ or @\cmd{arg}@ inline command.
-- This parser MUST NOT fail after consuming the initial @\@ — it either
-- returns the rendered inline or falls through via 'inlineCatchAll'.
unknownCmdInline :: Parser DocInline
unknownCmdInline = do
  _ <- char '\\'
  -- Try to consume a LaTeX identifier.  If nothing follows (e.g. \\{ \\} \\\\ \\$),
  -- fall back to returning the bare backslash.
  mName <- optional (takeWhile1P (Just "cmd name") isIdentChar)
  case mName of
    Nothing ->
      -- Bare \  followed by a special char: return the next char literally
      -- (e.g. \{ → "{", \$ → "$", \\ already handled by skipCmd)
      fmap (Plain . T.singleton) anySingle
    Just _name -> do
      -- Optional single brace-group argument
      mArg <- optional (char '{' *> balancedArg)
      pure $ case mArg of
        Just _  -> Plain ""   -- discard unknown command + arg
        Nothing -> Plain ""   -- discard unknown command

-- | A bare @{...}@ group — render its contents.
braceGroup :: Parser DocInline
braceGroup = do
  _ <- char '{'
  content <- manyTill inline (char '}')
  pure $ case content of
    []  -> Plain ""
    [x] -> x
    xs  -> Plain (T.concat (map inlineToText xs))

-- | @\ttsymbol{n}@ → Code with the character at ASCII position n.
-- This is used to typeset special characters in the tt font.
ttsymbolCmd :: Parser DocInline
ttsymbolCmd = do
  _ <- string "\\ttsymbol{"
  digits <- takeWhile1P (Just "digit") (\c -> c >= '0' && c <= '9')
  _ <- char '}'
  let n  = read (T.unpack digits) :: Int
      ch = toEnum n :: Char
  pure $ Code (T.singleton ch)

teCmd :: Parser DocInline
teCmd = do
  _ <- string "\\te{"
  content <- manyTill inline (char '}')
  pure $ SymRef (T.concat (map inlineToText content))

textttCmd :: Parser DocInline
textttCmd = do
  _ <- string "\\texttt{"
  content <- manyTill inline (char '}')
  pure $ Code (T.concat (map inlineToText content))

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
  content <- manyTill inline (char '}')
  pure $ NonTerm (T.concat (map inlineToText content))

indexCmd :: Parser DocInline
indexCmd = do
  _ <- string "\\index{"
  _ <- balancedArg
  pure $ Plain ""   -- strip index entries from inline text

-- | \term{Foo} → Code (typewriter term reference)
termCmd :: Parser DocInline
termCmd = do
  _ <- string "\\term{"
  content <- manyTill inline (char '}')
  pure $ Code (T.concat (map inlineToText content))

-- | \qbs{code} → Code (inline BH/Classic code)
qbsCmd :: Parser DocInline
qbsCmd = do
  _ <- string "\\qbs{"
  content <- manyTill inline (char '}')
  pure $ Code (T.concat (map inlineToText content))

-- | \mbox{content} → render content inline
mboxCmd :: Parser DocInline
mboxCmd = do
  _ <- string "\\mbox{"
  content <- manyTill inline (char '}')
  pure $ case content of
    []  -> Plain ""
    [x] -> x
    xs  -> Emph xs   -- wrap in emph as a neutral container

-- | \ref{label} → SectionRef node (rendered as a hyperlink by HTML backend)
refCmd :: Parser DocInline
refCmd = do
  _ <- string "\\ref{"
  lbl <- balancedArg
  pure $ SectionRef lbl

-- | \gram{text} \grammore{text} \gramalt{text} → NonTerm (grammar notation)
-- Note: \gram{name}{body} is handled by 'gramProductionBlock' (block-level).
-- This inline parser handles only the one-arg variants.
gramCmd :: Parser DocInline
gramCmd = do
  _ <- choice
    [ string "\\grammore{"
    , string "\\gramalt{"
    , string "\\litem{"
    ]
  content <- manyTill inline (char '}')
  pure $ NonTerm (T.concat (map inlineToText content))

-- | \many{x} → NonTerm "{x}*"  \opt{x} → NonTerm "[x]"
manyOptCmd :: Parser DocInline
manyOptCmd = choice
  [ do _ <- string "\\many{"
       content <- manyTill inline (char '}')
       pure $ NonTerm ("{" <> T.concat (map inlineToText content) <> "}*")
  , do _ <- string "\\opt{"
       content <- manyTill inline (char '}')
       pure $ NonTerm ("[" <> T.concat (map inlineToText content) <> "]")
  , do _ <- string "\\alt"
       pure $ Plain " | "
  ]

-- | \EBS{code} \BBS{code} → Code (example code)
ebsCmd :: Parser DocInline
ebsCmd = do
  _ <- choice [ string "\\EBS{", string "\\BBS{" ]
  content <- manyTill inline (char '}')
  pure $ Code (T.concat (map inlineToText content))

-- | LaTeX curly quotes: @``text''@ → @"text"@.
-- Content is read character-by-character so the @''@ terminator is reliably
-- detected even when the content contains apostrophes (e.g. "don't care").
-- The raw content is then post-processed through 'parseTexDoc' so that
-- any embedded LaTeX commands (e.g. @\mbox{\te{...}}@) are rendered.
latexQuotes :: Parser DocInline
latexQuotes = choice
  [ do _ <- string "``"
       rawContent <- manyTill anySingle (string "''")
       let inlines = concatMap paraInlines (parseTexDoc (T.pack rawContent))
           text    = T.concat (map inlineToText inlines)
       pure $ Plain ("\"" <> text <> "\"")
  , do _ <- string "`"
       pure $ Plain "'"
  ]
  where
    paraInlines (Para is) = is
    paraInlines _         = []

-- | Math mode.
-- * @$...$@  → @\(...\)@ (MathJax inline marker)
-- * @$$...$$@ → @\[...\]@ (MathJax display marker)
--
-- The raw LaTeX content is kept verbatim inside the MathJax delimiters so
-- that MathJax can render it in the browser.  MathJax is served as a local
-- file (@../mathjax.js@) written to the output directory by 'runDocGen'.
mathMode :: Parser DocInline
mathMode = do
  _ <- char '$'
  isDbl <- option False (True <$ char '$')
  if isDbl
    then do
      content <- manyTill anySingle (string "$$")
      pure $ Plain ("\\[\n" <> T.pack content <> "\n\\]")
    else do
      content <- manyTill (satisfy (\c -> c /= '\n' && c /= '$')) (char '$')
      pure $ Plain ("\\(" <> T.pack content <> "\\)")

skipCmd :: Parser DocInline
skipCmd = choice
  [ -- Commands with a brace argument to swallow
    do _ <- choice
         [ string "\\pageref{"
         , string "\\label{"
         , string "\\fbox{"
         , string "\\hspace{"
         , string "\\hspace*{"
         , string "\\vspace{"
         , string "\\vspace*{"
         , string "\\linewidth"
         , string "\\textwidth"
         , string "\\fontfamily{"   -- part of \ttsymbol expansion
         ]
       _ <- optional balancedArg
       pure $ Plain ""
    -- Font/grouping commands that appear in \ttsymbol expansion
  , string "\\begingroup"  *> pure (Plain "")
  , string "\\endgroup"    *> pure (Plain "")
  , string "\\selectfont"  *> pure (Plain "")
    -- Simple keyword replacements
  , string "\\BS"  *> pure (Plain " ")
  , string "\\ie"  *> pure (Plain "i.e.,")
  , string "\\eg"  *> pure (Plain "e.g.,")
  , string "\\etc" *> pure (Plain "etc.")
  , string "\\hdivider" *> pure (Plain " ")
  , string "\\\\"  *> pure (Plain " ")
  ]

plainText :: Parser DocInline
plainText = do
  c <- satisfy notSpecial
  rest <- takeWhileP Nothing notSpecial
  pure $ Plain (T.cons c rest)
  where
    -- Stop at backslash, braces, newline, dollar, and backtick.
    -- Backtick is excluded so that ``...'' quote pairs are handled by
    -- latexQuotes before plainText consumes them.
    notSpecial ch = ch /= '\\' && ch /= '{' && ch /= '}' && ch /= '\n'
                 && ch /= '$'  && ch /= '`'
