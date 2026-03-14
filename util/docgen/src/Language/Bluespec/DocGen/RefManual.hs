-- | Convert the BSC LaTeX reference manual (@BH_lang.tex@) to HTML.
--
-- Pipeline:
-- 1. Strip everything before @\begin{document}@.
-- 2. Collect zero-arg and one-arg @\newcommand@ macros from the preamble.
-- 3. Pre-process the document body: strip TeX comments, expand macros,
--    remove layout-only commands.
-- 4. Collect @\index{...}@ entries from the preprocessed body.
-- 5. Parse with 'TexParser.parseTexDoc', which handles @\section@,
--    @\subsection@, @\te@, @\nterm@, @\begin{libverbatim}@, etc.
-- 6. Split on @Heading 1@ boundaries → one HTML file per top-level section.
-- 7. Write a table-of-contents @index.html@ and a back-of-book term index.
module Language.Bluespec.DocGen.RefManual
  ( convertRefManual
  , RefManualConfig (..)
  , defaultRefManualConfig
  ) where

import Data.Char (isAlphaNum, toLower)
import Data.List (groupBy, sortOn)
import Data.ByteString qualified as BS
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (decodeLatin1)
import Data.Text.Lazy.IO qualified as TLIO
import System.Directory (createDirectoryIfMissing)
import System.FilePath ((</>))
import Text.Blaze.Html.Renderer.Text (renderHtml)
import Text.Blaze.Html5 (Html, (!))
import Text.Blaze.Html5 qualified as H
import Text.Blaze.Html5.Attributes qualified as A

import Language.Bluespec.DocGen.DocAST
import Language.Bluespec.DocGen.HTML (renderDocBlocks, docFooter)
import Language.Bluespec.DocGen.SymbolIndex (SymbolIndex)
import Language.Bluespec.DocGen.TexParser
  ( MacroEnv, collectMacros, expandMacros, parseTexDoc )

-- ---------------------------------------------------------------------------
-- Config
-- ---------------------------------------------------------------------------

-- | Configuration for reference manual conversion.
data RefManualConfig = RefManualConfig
  { rmcTexFile  :: !FilePath       -- ^ path to BH_lang.tex
  , rmcOutDir   :: !FilePath       -- ^ output directory (files go into rmcOutDir/reference/)
  , rmcVerbose  :: !Bool
  , rmcBscSha   :: !(Maybe Text)   -- ^ BSC commit SHA for footer
  } deriving stock (Show)

-- | Sensible defaults.
defaultRefManualConfig :: RefManualConfig
defaultRefManualConfig = RefManualConfig
  { rmcTexFile = "BH_lang.tex"
  , rmcOutDir  = "docs"
  , rmcVerbose = False
  , rmcBscSha  = Nothing
  }

-- ---------------------------------------------------------------------------
-- Entry point
-- ---------------------------------------------------------------------------

-- | Convert the reference manual LaTeX file to a set of HTML pages.
convertRefManual :: RefManualConfig -> SymbolIndex -> IO ()
convertRefManual cfg idx = do
  -- BH_lang.tex uses Latin-1 (ISO 8859-1) encoding, not UTF-8.
  raw <- BS.readFile (rmcTexFile cfg)
  let src = decodeLatin1 raw

  -- 1. Split preamble from body
  let (preamble, body) = splitDocument src

  -- 2. Collect macros from preamble
  let env = collectMacros preamble

  -- 3. Pre-process body
  let processed = preprocessBody env body

  -- 4. Collect \index entries (before they are stripped by the parser)
  let indexEntries = collectIndexEntries processed

  -- 5. Parse into DocBlocks
  let blocks = parseTexDoc processed

  -- 6. Split by section
  let sections = splitSections blocks

  -- 7. Write output
  let refDir = rmcOutDir cfg </> "reference"
  createDirectoryIfMissing True refDir

  let mSha = rmcBscSha cfg
  mapM_ (writeSection refDir idx mSha) sections
  writeTocPage refDir sections mSha
  writeTermIndex refDir indexEntries mSha

  when' (rmcVerbose cfg) $ do
    putStrLn $ "[docgen] Reference manual: " ++ show (length sections) ++ " sections"
    putStrLn $ "[docgen] Term index: " ++ show (length indexEntries) ++ " entries"
    putStrLn $ "[docgen] Output: " ++ refDir

-- ---------------------------------------------------------------------------
-- Document splitting
-- ---------------------------------------------------------------------------

-- | Split LaTeX source into (preamble, body).
-- The preamble is everything before @\begin{document}@;
-- the body is everything from @\begin{document}@ onwards.
splitDocument :: Text -> (Text, Text)
splitDocument src =
  case T.breakOn "\\begin{document}" src of
    (pre, rest)
      | T.null rest -> (src, T.empty)
      | otherwise   -> (pre, T.drop (T.length "\\begin{document}") rest)

-- ---------------------------------------------------------------------------
-- Pre-processing
-- ---------------------------------------------------------------------------

-- | Pre-process the document body before parsing:
-- 1. Strip TeX line comments (@% ...@ to end of line).
-- 2. Strip @\end{document}@.
-- 3. Expand macros from the preamble.
-- 4. Remove layout-only commands (@\newpage@, @\clearpage@, @\pagestyle@, etc.).
preprocessBody :: MacroEnv -> Text -> Text
preprocessBody env =
  stripLayoutCmds
  . expandMacros env
  . stripComments
  . T.dropWhile (/= '\n')  -- drop remainder of \begin{document} line

-- | Strip TeX line comments: everything from @%@ to end of line.
-- Handles escaped @\%@.
stripComments :: Text -> Text
stripComments = T.unlines . map stripLine . T.lines
  where
    stripLine line = go line
      where
        go t
          | T.null t               = t
          | "\\" `T.isPrefixOf` t  = T.take 2 t <> go (T.drop 2 t)
          | "%" `T.isPrefixOf` t   = T.empty
          | otherwise              = T.cons (T.head t) (go (T.tail t))

-- | Remove layout-only LaTeX commands that have no semantic meaning for us.
stripLayoutCmds :: Text -> Text
stripLayoutCmds = T.unlines . map strip . T.lines
  where
    strip line =
      let t = T.stripStart line
      in if any (`T.isPrefixOf` t) layoutPrefixes
           then T.empty
           else line

    layoutPrefixes :: [Text]
    layoutPrefixes =
      [ "\\newpage", "\\clearpage", "\\vfill", "\\hm", "\\hmm"
      , "\\pagestyle", "\\lhead", "\\rhead", "\\cfoot", "\\lfoot", "\\rfoot"
      , "\\phantomsection", "\\addcontentsline", "\\tableofcontents"
      , "\\maketitle", "\\vspace", "\\hspace", "\\lineup", "\\noindent"
      , "\\setlength", "\\label", "\\cite", "\\bibliographystyle"
      , "\\bibliography", "\\printindex", "\\end{document}"
      , "\\makeindex", "\\thispagestyle", "\\markboth"
      ]

-- ---------------------------------------------------------------------------
-- \index entry collection
-- ---------------------------------------------------------------------------

-- | An entry from a @\index{...}@ command.
data IndexEntry = IndexEntry
  { ieKey     :: !Text   -- ^ normalised sort key (lowercase, stripped)
  , ieDisplay :: !Text   -- ^ display form (original, without @\te{}@ decoration)
  , ieSection :: !Text   -- ^ slug of the section this entry belongs to
  } deriving stock (Show, Eq, Ord)

-- | Scan the preprocessed body for @\index{...}@ commands and return the
-- collected entries, each tagged with the slug of the enclosing @\section@.
-- Duplicates (same key + section) are removed.
collectIndexEntries :: Text -> [IndexEntry]
collectIndexEntries src = removeDups $ go "index" src
  where
    -- go currentSectionSlug remaining
    go _    t | T.null t = []
    go slug t
      -- Update current section when we see \section{title}
      | "\\section{" `T.isPrefixOf` t =
          let content = consumeBalanced (T.drop (T.length "\\section{") t)
              rest    = T.drop (T.length "\\section{" + T.length content + 1) t
              newSlug = slugify content
          in go newSlug rest
      | "\\index{" `T.isPrefixOf` t =
          let content = consumeBalanced (T.drop (T.length "\\index{") t)
              rest    = T.drop (T.length "\\index{" + T.length content + 1) t
          in toEntry slug content : go slug rest
      | otherwise = go slug (T.drop 1 t)

    -- The \index argument may be "word@\te{word}|textbf" — take the part
    -- before the first '@' or '|'.
    toEntry slug raw =
      let stripped = T.takeWhile (\c -> c /= '@' && c /= '|') raw
          display  = stripTeCmd stripped
          key      = T.map toLower (T.strip display)
      in IndexEntry key display slug

    -- Strip \te{...} wrappers from an index entry.
    stripTeCmd t
      | "\\te{" `T.isPrefixOf` t = consumeBalanced (T.drop (T.length "\\te{") t)
      | otherwise                 = t

    consumeBalanced = T.pack . go' (0 :: Int) . T.unpack
      where
        go' _ []       = []
        go' 0 ('}':_)  = []
        go' d ('}':cs) = '}' : go' (d-1) cs
        go' d ('{':cs) = '{' : go' (d+1) cs
        go' d (c:cs)   = c   : go' d cs

    removeDups = map head . groupBy (\a b -> ieKey a == ieKey b) . sortOn ieKey

-- ---------------------------------------------------------------------------
-- Section splitting
-- ---------------------------------------------------------------------------

-- | A section extracted from the document.
data Section = Section
  { secTitle  :: !Text
  , secSlug   :: !Text     -- ^ URL-safe filename stem
  , secBlocks :: ![DocBlock]
  } deriving stock (Show)

-- | Split a list of DocBlocks into sections on every @Heading 1@.
-- Content before the first @Heading 1@ forms an "Introduction" section.
splitSections :: [DocBlock] -> [Section]
splitSections blocks = go blocks Nothing []
  where
    -- go remaining  currentTitle  accumulated-blocks-reversed
    go []     Nothing  _    = []
    go []     (Just t) acc  = [mkSection t (reverse acc)]
    go (b:bs) title    acc
      | isH1 b =
          let finished = case title of
                Nothing -> []   -- drop preamble before first section
                Just t  -> [mkSection t (reverse acc)]
          in finished ++ go bs (Just (titleText b)) [b]
      | otherwise = go bs title (b : acc)

    isH1 (Heading 1 _) = True
    isH1 _             = False

    titleText (Heading _ inlines) = inlinesToText inlines
    titleText _                   = "Untitled"

    mkSection t bs = Section t (slugify t) bs

-- | Convert heading inlines to plain text.
inlinesToText :: [DocInline] -> Text
inlinesToText = T.concat . map go
  where
    go (Plain t)     = t
    go (Code t)      = t
    go (Emph is)     = inlinesToText is
    go (Strong is)   = inlinesToText is
    go (SymRef t)    = t
    go (NonTerm t)   = t

-- | Make a URL-safe slug from a section title.
slugify :: Text -> Text
slugify = T.map slugChar . T.strip . T.toLower
  where
    slugChar c
      | isAlphaNum c = c
      | c == ' '     = '-'
      | otherwise    = '-'

-- ---------------------------------------------------------------------------
-- HTML output
-- ---------------------------------------------------------------------------

-- | Write a single section as an HTML file.
writeSection :: FilePath -> SymbolIndex -> Maybe Text -> Section -> IO ()
writeSection outDir idx mSha sec = do
  let path = outDir </> T.unpack (secSlug sec) ++ ".html"
  TLIO.writeFile path (renderHtml (sectionPage sec idx mSha))

-- | Render a section page.
sectionPage :: Section -> SymbolIndex -> Maybe Text -> Html
sectionPage sec idx mSha = H.docTypeHtml $ do
  H.head $ do
    H.meta ! A.charset "utf-8"
    H.title (H.toHtml (secTitle sec <> " — BH Reference"))
    H.link ! A.rel "stylesheet" ! A.href "../docgen.css"
  H.body $ do
    H.nav ! A.class_ "breadcrumb" $
      H.a ! A.href "index.html" $ "Reference Manual"
    H.main $
      renderDocBlocks idx (secBlocks sec)
    docFooter mSha

-- | Write the table-of-contents index page.
writeTocPage :: FilePath -> [Section] -> Maybe Text -> IO ()
writeTocPage outDir sections mSha = do
  let path = outDir </> "index.html"
  TLIO.writeFile path (renderHtml (tocPage sections mSha))

-- | Render the table-of-contents page.
tocPage :: [Section] -> Maybe Text -> Html
tocPage sections mSha = H.docTypeHtml $ do
  H.head $ do
    H.meta ! A.charset "utf-8"
    H.title "BH Language Reference"
    H.link ! A.rel "stylesheet" ! A.href "../docgen.css"
  H.body $ do
    H.main $ do
      H.h1 "BH Language Reference"
      H.p "Reference manual for the Bluespec Classic (BH) hardware description language."
      H.ul $ mapM_ tocEntry sections
      H.p $ do
        H.a ! A.href "term-index.html" $ "Term Index"
        " — alphabetical index of language terms"
    docFooter mSha
  where
    tocEntry sec =
      H.li $ H.a ! A.href (H.toValue (secSlug sec <> ".html")) $
        H.toHtml (secTitle sec)

-- | Write the back-of-book term index page.
writeTermIndex :: FilePath -> [IndexEntry] -> Maybe Text -> IO ()
writeTermIndex outDir entries mSha = do
  let path = outDir </> "term-index.html"
  TLIO.writeFile path (renderHtml (termIndexPage entries mSha))

-- | Render the alphabetical term index page.
termIndexPage :: [IndexEntry] -> Maybe Text -> Html
termIndexPage entries mSha = H.docTypeHtml $ do
  H.head $ do
    H.meta ! A.charset "utf-8"
    H.title "Term Index — BH Reference"
    H.link ! A.rel "stylesheet" ! A.href "../docgen.css"
  H.body $ do
    H.main $ do
      H.nav ! A.class_ "breadcrumb" $
        H.a ! A.href "index.html" $ "Reference Manual"
      H.h1 "Term Index"
      if null entries
        then H.p "(No index entries found.)"
        else renderAlphaGroups entries
    docFooter mSha

-- | Render entries grouped by first letter.
renderAlphaGroups :: [IndexEntry] -> Html
renderAlphaGroups entries = do
  -- Navigation bar: A B C ... links
  H.p ! A.class_ "index-nav" $
    mapM_ (\letter -> do
      H.a ! A.href (H.toValue ("#idx-" <> T.singleton letter)) $
        H.toHtml (T.singleton letter)
      " "
    ) presentLetters

  -- Groups
  mapM_ renderGroup groups
  where
    groups = groupBy (\a b -> headChar a == headChar b) entries
    presentLetters = map (headChar . head) groups

    headChar e
      | T.null (ieKey e) = '-'
      | otherwise        = T.head (ieKey e)

    renderGroup []     = pure ()
    renderGroup grp@(e:_) = do
      let letter = headChar e
      H.h2 ! A.id (H.toValue ("idx-" <> T.singleton letter)) $
        H.toHtml (T.singleton letter)
      H.ul $ mapM_ renderEntry grp

    renderEntry entry =
      H.li $ do
        let anchor = ieSection entry <> ".html"
        H.a ! A.href (H.toValue anchor) $ H.toHtml (ieDisplay entry)

-- ---------------------------------------------------------------------------
-- Utilities
-- ---------------------------------------------------------------------------

when' :: Applicative f => Bool -> f () -> f ()
when' True  action = action
when' False _      = pure ()
