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
  , try paragraphCmd          -- \paragraph{title} → Heading 4
  , try verbatimEnv
  , try centerboxverbatimEnv  -- \begin{centerboxverbatim} → VerbBlock
  , try noteEnv
  , try tightlistEnv
  , try bulletList
  , try enumerateEnv          -- \begin{enumerate} → OrderedList
  , try listEnv               -- \begin{list}{marker}{...} → BulletList
  , try tabularEnv            -- \begin{tabular}{spec} → Table
  , try centerEnv             -- \begin{center} → pass-through (renders inner blocks)
  , try figureEnv             -- \begin{figure} → Image with optional caption
  , try quoteEnv              -- \begin{quote} → BlockQuote
  , try tabbingEnv            -- \begin{tabbing} → VerbBlock (best-effort)
  , try minipageEnv           -- \begin{minipage} → pass-through
  , try gramProductionBlock   -- \gram{name}{body} — two-arg grammar production
  , try unknownEnv            -- \begin{unknown}...\end{unknown}
  , para                      -- always succeeds if any non-newline char is present
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
  _ <- string "\\begin{NOTE}"
  skipWhitespace
  blocks <- many (notFollowedBy (string "\\end{NOTE}") *> block <* skipWhitespace)
  _ <- string "\\end{NOTE}"
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

-- | @\paragraph{title}@ → Heading level 4.
paragraphCmd :: Parser DocBlock
paragraphCmd = do
  _ <- string "\\paragraph{"
  content <- manyTill inline (char '}')
  pure $ Heading 4 content

-- | @\begin{enumerate}...\item...\end{enumerate}@ → OrderedList.
enumerateEnv :: Parser DocBlock
enumerateEnv = do
  _ <- string "\\begin{enumerate}" <* optional newline
  items <- many item
  _ <- string "\\end{enumerate}"
  pure $ OrderedList items
  where
    item = do
      _ <- string "\\item"
      _ <- optional (satisfy (\c -> c == ' ' || c == '\n'))
      bs <- many (notFollowedBy (string "\\item" <|> string "\\end") *> block)
      pure bs

-- | @\begin{list}{marker}{params}...@  → BulletList.
-- Custom list environments used for bullets/numbered lists.
listEnv :: Parser DocBlock
listEnv = do
  _ <- string "\\begin{list}{"
  _ <- balancedArg   -- marker (e.g. $\bullet$)
  _ <- char '{'
  _ <- balancedArg   -- params
  _ <- optional newline
  items <- many item
  _ <- string "\\end{list}"
  pure $ BulletList items
  where
    item = do
      _ <- string "\\item"
      _ <- optional (satisfy (\c -> c == ' ' || c == '\n'))
      bs <- many (notFollowedBy (string "\\item" <|> string "\\end") *> block)
      pure bs

-- | @\begin{centerboxverbatim}...@ → VerbBlock.
-- Also handles @\begin{codebox}@, @\begin{smcenterboxverbatim}@.
centerboxverbatimEnv :: Parser DocBlock
centerboxverbatimEnv = do
  envName <- choice
    [ string "\\begin{centerboxverbatim}" *> pure "centerboxverbatim"
    , string "\\begin{smcenterboxverbatim}" *> pure "smcenterboxverbatim"
    , string "\\begin{codebox}"  *> pure "codebox"
    , string "\\begin{smbox}"    *> pure "smbox"
    , string "\\begin{fminipage}" *> pure "fminipage"
    ]
  _ <- optional newline
  content <- manyTill anySingle (string ("\\end{" <> envName <> "}"))
  pure $ VerbBlock (T.pack content)

-- | @\begin{tabular}{spec}...@ → Table.
-- Handles @&@ column separators, @\\\\@ row terminators, @\hline@, @\multicolumn@.
tabularEnv :: Parser DocBlock
tabularEnv = do
  _ <- string "\\begin{tabular}"
  -- Consume optional column spec: {|l|c|r|p{1in}|...}
  _ <- optional (char '{' *> balancedArg)
  _ <- optional newline
  raw <- manyTill anySingle (string "\\end{tabular}")
  let rawText = T.pack raw
      rows    = parseTabularRows rawText
  case rows of
    []     -> pure $ Para []
    [r]    -> pure $ Table r []
    (r:rs) -> pure $ Table r rs

-- | Parse the body of a tabular environment into rows of cells.
-- Each row is separated by @\\\\@, each cell by @&@.
-- @\hline@ and @\cline{...}@ are stripped.
parseTabularRows :: Text -> [[[DocInline]]]
parseTabularRows raw =
  let -- Split by \\ (row terminator).  Handle both \\ and \\\\ (escaped in source).
      rawRows = splitOnRowSep raw
      -- Remove empty rows and process each
      processed = filter (not . isEmptyRow) (map processRow rawRows)
  in processed
  where
    -- Split text on \\ that are row terminators (not inside braces)
    splitOnRowSep t = case T.breakOn "\\\\" t of
      (before, rest)
        | T.null rest -> [before]
        | otherwise   -> before : splitOnRowSep (T.drop 2 rest)

    isEmptyRow cells = null cells || all null cells || all (all isBlankInline) cells

    isBlankInline (Plain t) = T.null (T.strip t)
    isBlankInline _         = False

    processRow :: Text -> [[DocInline]]
    processRow rowText =
      let -- Strip \hline, \cline{...}, \multicolumn-related whitespace
          cleaned = stripTableCmds rowText
          -- Split by & (column separator)
          cells   = T.splitOn "&" cleaned
      in map parseCell cells

    parseCell :: Text -> [DocInline]
    parseCell cellText =
      let trimmed = T.strip cellText
      in if T.null trimmed
         then []
         else concatMap paraInlines (parseTexDoc trimmed)

    paraInlines :: DocBlock -> [DocInline]
    paraInlines (Para is) = is
    paraInlines _         = []

    -- Strip table layout commands from a row.
    stripTableCmds :: Text -> Text
    stripTableCmds = go
      where
        go t
          | T.null t = t
          | "\\hline" `T.isPrefixOf` t = go (T.drop 6 t)
          | "\\cline{" `T.isPrefixOf` t =
              let rest = T.drop 7 t  -- skip \cline{
                  after = T.drop 1 (T.dropWhile (/= '}') rest)
              in go after
          | "\\multicolumn{" `T.isPrefixOf` t = handleMulticolumn t
          | otherwise = T.cons (T.head t) (go (T.tail t))

        -- \multicolumn{n}{spec}{content} → extract content
        handleMulticolumn t =
          let rest1 = T.drop (T.length "\\multicolumn{") t
              -- Skip first arg (span count)
              (_, after1) = T.breakOn "}" rest1
              rest2 = T.drop 1 after1  -- skip }
              -- Skip second arg (column spec)
          in case T.uncons rest2 of
               Just ('{', rest3) ->
                 let (_, after2) = T.breakOn "}" rest3
                     rest4 = T.drop 1 after2  -- skip }
                 in case T.uncons rest4 of
                      Just ('{', rest5) ->
                        let content = T.pack $ consumeBal (0 :: Int) (T.unpack rest5)
                            afterContent = T.drop (T.length content + 1) rest5
                        in content <> go afterContent
                      _ -> go rest4
               _ -> go rest2

        consumeBal _ []        = []
        consumeBal 0 ('}':_)   = []
        consumeBal d ('}':cs)  = '}' : consumeBal (d-1) cs
        consumeBal d ('{':cs)  = '{' : consumeBal (d+1) cs
        consumeBal d (c:cs)    = c   : consumeBal d cs

-- | @\begin{center}...@ → pass-through (renders inner blocks).
-- This is critical because most tables are wrapped in center.
centerEnv :: Parser DocBlock
centerEnv = do
  _ <- string "\\begin{center}"
  skipWhitespace
  blocks <- many (notFollowedBy (string "\\end{center}") *> block <* skipWhitespace)
  _ <- string "\\end{center}"
  -- Return the first meaningful block, or wrap in Para
  case blocks of
    [b] -> pure b
    bs  -> pure $ BulletList [bs]  -- reuse BulletList as generic container

-- | @\begin{figure}[placement]...@ → Image with optional caption.
-- Extracts \includegraphics path and \caption text.
figureEnv :: Parser DocBlock
figureEnv = do
  _ <- string "\\begin{figure}"
  _ <- optional (char '[' *> takeWhileP Nothing (/= ']') *> char ']')  -- [htbp] etc.
  _ <- optional newline
  content <- manyTill anySingle (string "\\end{figure}")
  let raw = T.pack content
      imgPath = extractIncludegraphics raw
      caption = extractCaption raw
  case imgPath of
    Just path -> pure $ Image path caption
    Nothing   -> pure $ Para (maybe [] (\c -> [Plain c]) caption)

-- | @\begin{quote}...@ → BlockQuote.
quoteEnv :: Parser DocBlock
quoteEnv = do
  _ <- string "\\begin{quote}"
  skipWhitespace
  blocks <- many (notFollowedBy (string "\\end{quote}") *> block <* skipWhitespace)
  _ <- string "\\end{quote}"
  pure $ BlockQuote blocks

-- | @\begin{tabbing}...@ → VerbBlock (best-effort: preserve as preformatted text).
-- Strips tabbing commands (\=, \>, \kill) and renders content.
tabbingEnv :: Parser DocBlock
tabbingEnv = do
  _ <- string "\\begin{tabbing}" <* optional newline
  content <- manyTill anySingle (string "\\end{tabbing}")
  let raw = T.pack content
      -- Clean up tabbing commands for a readable rendering
      cleaned = T.unlines
        [ cleanTabbingLine line
        | line <- T.lines raw
        , not (T.null (T.strip line))
        , not ("\\kill" `T.isSuffixOf` T.strip line)
        ]
  pure $ VerbBlock cleaned

-- | @\begin{minipage}...@ → pass-through (renders inner content).
minipageEnv :: Parser DocBlock
minipageEnv = do
  _ <- string "\\begin{minipage}"
  _ <- optional (char '[' *> takeWhileP Nothing (/= ']') *> char ']')
  _ <- optional (char '{' *> balancedArg)  -- width spec
  skipWhitespace
  blocks <- many (notFollowedBy (string "\\end{minipage}") *> block <* skipWhitespace)
  _ <- string "\\end{minipage}"
  case blocks of
    [b] -> pure b
    bs  -> pure $ BulletList [bs]

-- | Clean a single line from a tabbing environment: strip \=, \>, \+, \- etc.
cleanTabbingLine :: Text -> Text
cleanTabbingLine = T.replace "\\=" "  " . T.replace "\\>" "  "
                 . T.replace "\\+" "" . T.replace "\\-" ""
                 . T.replace "\\kill" "" . T.replace "\\pushtabs" ""
                 . T.replace "\\poptabs" ""

-- | Extract the path from @\includegraphics[...]{path}@ in raw text.
extractIncludegraphics :: Text -> Maybe Text
extractIncludegraphics raw =
  case T.breakOn "\\includegraphics" raw of
    (_, rest)
      | T.null rest -> Nothing
      | otherwise ->
          let after = T.drop (T.length "\\includegraphics") rest
              -- Skip optional [...] argument
              after2 = case T.uncons after of
                Just ('[', r) -> T.drop 1 (T.dropWhile (/= ']') r)
                _             -> after
              -- Extract {path}
          in case T.uncons (T.stripStart after2) of
               Just ('{', r) -> Just $ T.takeWhile (/= '}') r
               _             -> Nothing

-- | Extract caption text from @\caption{text}@ in raw text.
extractCaption :: Text -> Maybe Text
extractCaption raw =
  case T.breakOn "\\caption{" raw of
    (_, rest)
      | T.null rest -> Nothing
      | otherwise ->
          let after = T.drop (T.length "\\caption{") rest
              content = T.pack $ consumeBal (0 :: Int) (T.unpack after)
          in if T.null content then Nothing else Just (stripTexCmds content)
  where
    consumeBal _ []        = []
    consumeBal 0 ('}':_)   = []
    consumeBal d ('}':cs)  = '}' : consumeBal (d-1) cs
    consumeBal d ('{':cs)  = '{' : consumeBal (d+1) cs
    consumeBal d (c:cs)    = c   : consumeBal d cs

    -- Minimal stripping of TeX commands from caption text
    stripTexCmds t = T.replace "\\BSV" "BSV" . T.replace "\\BH" "BH"
                   . T.replace "\\bsc" "bsc" . T.replace "\\BS" "Bluespec"
                   . T.replace "\\emph{" "" . T.replace "\\texttt{" ""
                   . T.replace "\\te{" "" . T.replace "}" ""
                   $ t

-- | Parse a @\gram{name}{body}@ grammar production (two-arg form).
-- Renders as: NonTerm name, Plain " ::= ", body_inlines...
gramProductionBlock :: Parser DocBlock
gramProductionBlock = do
  _ <- string "\\gram{"
  name <- balancedArg
  _ <- skipMany (satisfy (\c -> c == ' ' || c == '\n' || c == '\r' || c == '\t'))
  _ <- char '{'
  rawBody <- balancedArg
  let bodyBlocks  = parseTexDoc (stripGramMathDollars rawBody)
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
            '{' -> ('\\' :) . ('{' :) <$> go depth   -- \{ → keep escaped, don't count depth
            '}' -> ('\\' :) . ('}' :) <$> go depth   -- \} → keep escaped, don't count depth
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
inlineToText (Footnote is)  = T.concat (map inlineToText is)
inlineToText (Link _ is)    = T.concat (map inlineToText is)

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
  , try footnoteCmd       -- \footnote{text} → Footnote
  , try textitCmd         -- \textit{...} → Emph
  , try urlCmd            -- \url{url} → Link
  , try hrefCmd           -- \href{url}{text} → Link
  , try includegraphicsInline  -- \includegraphics[...]{path} → Plain (image ref)
  , try centerlineCmd     -- \centerline{content} → render content
  , tildeSpace            -- ~ → non-breaking space (no try needed, single char)
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
  _ <- string "\\index"
  -- Handle optional type: \index[function]{...}, \index[type]{...}, etc.
  _ <- optional (char '[' *> takeWhileP Nothing (/= ']') *> char ']')
  _ <- char '{'
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

-- | @\footnote{text}@ → Footnote inline (rendered as parenthetical).
footnoteCmd :: Parser DocInline
footnoteCmd = do
  _ <- string "\\footnote{"
  content <- manyTill inline (char '}')
  pure $ Footnote content

-- | @\textit{text}@ → Emph (alias for \emph).
textitCmd :: Parser DocInline
textitCmd = do
  _ <- string "\\textit{"
  content <- manyTill inline (char '}')
  pure $ Emph content

-- | @\url{url}@ → Link with URL as display text.
urlCmd :: Parser DocInline
urlCmd = do
  _ <- string "\\url{"
  url <- balancedArg
  pure $ Link url [Plain url]

-- | @\href{url}{text}@ → Link.
hrefCmd :: Parser DocInline
hrefCmd = do
  _ <- string "\\href{"
  url <- balancedArg
  _ <- char '{'
  content <- manyTill inline (char '}')
  pure $ Link url content

-- | @\includegraphics[opts]{path}@ as inline → Plain text indicating image.
-- (Block-level figure handling is done by figureEnv.)
includegraphicsInline :: Parser DocInline
includegraphicsInline = do
  _ <- string "\\includegraphics"
  _ <- optional (char '[' *> takeWhileP Nothing (/= ']') *> char ']')
  _ <- char '{'
  path <- balancedArg
  pure $ Plain ("[Image: " <> path <> "]")

-- | @\centerline{content}@ → render content inline.
centerlineCmd :: Parser DocInline
centerlineCmd = do
  _ <- string "\\centerline{"
  content <- manyTill inline (char '}')
  case content of
    []  -> pure $ Plain ""
    [x] -> pure x
    xs  -> Plain . T.concat <$> pure (map inlineToText xs)

-- | Strip @$\term{...}$@ and @$\nterm{...}$@ dollar wrappers from grammar
-- production body text.  In BH_lang.tex these dollar signs are a LaTeX font
-- hack (switching to CM typewriter for certain Latin-1 operator characters)
-- rather than genuine math mode.  Leaving them in place would send
-- @\term{X}@ to MathJax, which doesn't know @\term@ and renders it in red.
stripGramMathDollars :: Text -> Text
stripGramMathDollars src
  | not ("$\\" `T.isInfixOf` src) = src   -- fast path: nothing to do
  | otherwise = go src
  where
    gramPrefixes = ["term{", "nterm{"]

    go t = case T.breakOn "$\\" t of
      (before, rest)
        | T.null rest -> before
        | otherwise   ->
            let afterDollarSlash = T.drop 2 rest  -- skip "$\"
            in if any (`T.isPrefixOf` afterDollarSlash) gramPrefixes
               then
                 -- Unwrap: keep the \cmd{...} but drop the surrounding $...$
                 let withSlash            = T.drop 1 rest    -- "\term{...}$..."
                     (inner, closing)     = T.break (== '$') withSlash
                 in case T.uncons closing of
                      Just ('$', after) -> before <> inner <> go after
                      _                 -> before <> "$\\" <> go afterDollarSlash
               else
                 -- Not a grammar terminal — leave unchanged, continue scanning
                 before <> "$\\" <> go afterDollarSlash

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
  rawContent <- balancedArg
  let stripped = stripGramMathDollars rawContent
      inlines  = concatMap paraInlines (parseTexDoc stripped)
  pure $ NonTerm (T.concat (map inlineToText inlines))
  where
    paraInlines (Para is) = is
    paraInlines _         = []

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
         , string "\\fontfamily{"   -- part of \ttsymbol expansion
         , string "\\caption{"      -- outside figure context
         , string "\\cite{"         -- bibliography references
         ]
       _ <- balancedArg
       pure $ Plain ""
    -- No-argument commands (do NOT consume a brace argument)
  , string "\\linewidth"   *> pure (Plain "")
  , string "\\textwidth"   *> pure (Plain "")
  , string "\\small"       *> pure (Plain "")
  , string "\\large"       *> pure (Plain "")
  , string "\\Large"       *> pure (Plain "")
  , string "\\normalsize"  *> pure (Plain "")
  , string "\\centering"   *> pure (Plain "")
  , string "\\raggedright" *> pure (Plain "")
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

-- | @~@ → non-breaking space (LaTeX tilde).
tildeSpace :: Parser DocInline
tildeSpace = char '~' *> pure (Plain "\160")   -- U+00A0 non-breaking space

plainText :: Parser DocInline
plainText = do
  c <- satisfy notSpecial
  rest <- takeWhileP Nothing notSpecial
  pure $ Plain (T.cons c rest)
  where
    -- Stop at backslash, braces, newline, dollar, backtick, and tilde.
    notSpecial ch = ch /= '\\' && ch /= '{' && ch /= '}' && ch /= '\n'
                 && ch /= '$'  && ch /= '`' && ch /= '~'
