-- | Convert a BSC LaTeX reference manual to HTML.
--
-- Pipeline:
-- 0. Resolve @\input{...}@ directives by inlining sub-files.
-- 1. Strip everything before @\begin{document}@.
-- 2. Collect zero-arg and one-arg @\newcommand@ macros from the preamble.
-- 3. Pre-process the document body: strip TeX comments, expand macros,
--    remove layout-only commands.
-- 4. Collect @\index{...}@ entries from the preprocessed body.
-- 5. Parse with 'TexParser.parseTexDoc', which handles @\section@,
--    @\subsection@, @\te@, @\nterm@, @\begin{libverbatim}@, etc.
-- 6. Split on heading boundaries → one HTML file per section.
-- 7. Write a table-of-contents @index.html@ and a back-of-book term index.
module Language.Bluespec.DocGen.RefManual
  ( convertRefManual
  , RefManualConfig (..)
  , defaultRefManualConfig
  ) where

import Control.Monad (forM, forM_)
import Data.Char (isAlphaNum, toLower)
import Data.List (groupBy, sortOn)
import Data.ByteString qualified as BS
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (decodeLatin1)
import Data.Text.Lazy.IO qualified as TLIO
import System.Directory (createDirectoryIfMissing, doesFileExist)
import System.FilePath ((</>), takeDirectory)
import System.IO (hPutStrLn, stderr)
import Text.Blaze.Html.Renderer.Text (renderHtml)
import Text.Blaze.Html5 (Html, (!))
import Text.Blaze.Html5 qualified as H
import Text.Blaze.Html5.Attributes qualified as A

import Language.Bluespec.DocGen.DocAST
import Language.Bluespec.DocGen.HTML (LabelMap, renderDocBlocks, docFooter, mathJaxScripts, searchHeader)
import Language.Bluespec.DocGen.SymbolIndex (SymbolIndex, SymbolRef (..))
import Language.Bluespec.DocGen.TexParser
  ( MacroEnv, collectMacros, expandMacros, parseTexDoc )

-- ---------------------------------------------------------------------------
-- Config
-- ---------------------------------------------------------------------------

-- | Configuration for reference manual conversion.
data RefManualConfig = RefManualConfig
  { rmcTexFile  :: !FilePath       -- ^ path to BH_lang.tex (or other root .tex)
  , rmcTitle    :: !Text           -- ^ human-readable manual title (e.g. "BH Language Reference")
  , rmcSubDir   :: !Text           -- ^ output sub-directory name (e.g. "bh-reference")
  , rmcOutDir   :: !FilePath       -- ^ output directory (files go into rmcOutDir/rmcSubDir/)
  , rmcVerbose  :: !Bool
  , rmcBscSha   :: !(Maybe Text)   -- ^ BSC commit SHA for footer
  } deriving stock (Show)

-- | Sensible defaults.
defaultRefManualConfig :: RefManualConfig
defaultRefManualConfig = RefManualConfig
  { rmcTexFile = "BH_lang.tex"
  , rmcTitle   = "BH Language Reference"
  , rmcSubDir  = "reference"
  , rmcOutDir  = "docs"
  , rmcVerbose = False
  , rmcBscSha  = Nothing
  }

-- ---------------------------------------------------------------------------
-- Entry point
-- ---------------------------------------------------------------------------

-- | Convert the reference manual LaTeX file to a set of HTML pages.
-- Returns additional SymbolIndex entries (one per split subsection) so they
-- can be merged into the global search index by the caller.
convertRefManual :: RefManualConfig -> SymbolIndex -> IO SymbolIndex
convertRefManual cfg idx = do
  -- LaTeX source files use Latin-1 (ISO 8859-1) encoding, not UTF-8.
  raw <- BS.readFile (rmcTexFile cfg)
  let src = decodeLatin1 raw

  -- 0. Inline \input{...} sub-files (e.g. libraries_ref_guide uses many)
  let texDir = takeDirectory (rmcTexFile cfg)
  src' <- resolveInputs texDir src

  -- 1. Split preamble from body
  let (preamble, body) = splitDocument src'

  -- 2. Collect macros from preamble
  let env = collectMacros preamble

  -- 3. Pre-process body in stages so we can collect labels before they are stripped
  let afterComments = stripAndExpand env body
      labelMap      = collectLabelMap afterComments   -- collect before \label is stripped
      processed     = stripLayoutCmds afterComments

  -- 4. Collect \index entries
  let indexEntries = collectIndexEntries processed

  -- 5. Parse into DocBlocks
  let blocks = parseTexDoc processed

  -- 6. Split by section
  let sections = splitSections blocks

  -- 7. Write output
  let refDir = rmcOutDir cfg </> T.unpack (rmcSubDir cfg)
      subDir = rmcSubDir cfg
  createDirectoryIfMissing True refDir

  let mSha  = rmcBscSha cfg
      title = rmcTitle cfg
  extraIdxs <- forM sections $ \sec ->
    writeSectionOrSplit refDir subDir idx labelMap mSha title sec
  writeTocPage refDir sections mSha title
  writeTermIndex refDir indexEntries mSha title

  when' (rmcVerbose cfg) $ do
    putStrLn $ "[docgen] " ++ T.unpack title ++ ": " ++ show (length sections) ++ " sections"
    putStrLn $ "[docgen] Term index: " ++ show (length indexEntries) ++ " entries"
    putStrLn $ "[docgen] Output: " ++ refDir

  pure (Map.unions extraIdxs)

-- ---------------------------------------------------------------------------
-- \input{} resolution
-- ---------------------------------------------------------------------------

-- | Inline all @\input{path}@ directives by reading the referenced files.
-- Paths are resolved relative to @baseDir@; if the path has no extension,
-- @.tex@ is appended (LaTeX convention).  Nested @\input@ commands in the
-- included files are resolved recursively.  Commented-out @\input@ lines
-- (where a @%@ precedes @\input@ on the same line) are left as-is.
resolveInputs :: FilePath -> Text -> IO Text
resolveInputs baseDir src = go src
  where
    go t = case T.breakOn "\\input{" t of
      (before, rest)
        | T.null rest -> pure before
        | otherwise   -> do
            let after             = T.drop (T.length "\\input{") rest
                (rawPath, closing) = T.break (== '}') after
                afterClose         = T.drop 1 closing   -- skip '}'
            if isCommented before
              -- Leave commented-out \input unchanged
              then do
                rest' <- go afterClose
                pure (before <> "\\input{" <> rawPath <> "}" <> rest')
              else do
                content <- tryReadInput (T.unpack rawPath)
                rest' <- go afterClose
                pure (before <> content <> "\n" <> rest')

    -- Check whether the fragment before the \input token is on a commented line
    -- (i.e. there is a bare % between the last newline and this point).
    isCommented before =
      let lineFragment = T.takeWhileEnd (/= '\n') before
      in "%" `T.isInfixOf` lineFragment

    -- Try to read the input file, appending .tex if needed.
    tryReadInput path = do
      let candidates = [baseDir </> path, baseDir </> (path ++ ".tex")]
      mFp <- findFirst candidates
      case mFp of
        Nothing -> do
          hPutStrLn stderr $
            "[docgen] Warning: \\input{" ++ path ++ "} not found in " ++ baseDir
          pure T.empty
        Just fp -> do
          raw <- BS.readFile fp
          let content = decodeLatin1 raw
          -- Recurse so nested \input in sub-files are also resolved
          resolveInputs (takeDirectory fp) content

    findFirst []     = pure Nothing
    findFirst (p:ps) = doesFileExist p >>= \e -> if e then pure (Just p) else findFirst ps

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
preprocessBody env = stripLayoutCmds . stripAndExpand env

-- | Steps 1–3 of pre-processing: strip comments, expand macros.
-- @\label@ commands are still present at this stage.
stripAndExpand :: MacroEnv -> Text -> Text
stripAndExpand env =
  expandMacros env
  . stripComments
  . T.dropWhile (/= '\n')  -- drop remainder of \begin{document} line

-- | Collect a map from @\label{lbl}@ keys to the slug of the enclosing
-- top-level @\section@.  Must be called on the text BEFORE 'stripLayoutCmds'
-- so that @\label@ commands are still present.
collectLabelMap :: Text -> LabelMap
collectLabelMap = go "introduction" Map.empty
  where
    go _ m t | T.null t = m
    go slug m t
      | "\\section{" `T.isPrefixOf` t =
          let rest    = T.drop (T.length "\\section{") t
              title   = T.takeWhile (/= '}') rest
              newSlug = slugify title
          in go newSlug m (T.drop 1 (T.dropWhile (/= '}') rest))
      | "\\label{" `T.isPrefixOf` t =
          let rest = T.drop (T.length "\\label{") t
              lbl  = T.takeWhile (/= '}') rest
          in go slug (Map.insert lbl slug m) (T.drop 1 (T.dropWhile (/= '}') rest))
      | otherwise = go slug m (T.drop 1 t)

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

-- | A section extracted from the document (split on H1 = \section{}).
data Section = Section
  { secTitle  :: !Text
  , secSlug   :: !Text     -- ^ URL-safe filename stem
  , secBlocks :: ![DocBlock]
  } deriving stock (Show)

-- | A subsection within a split section (split on H2 = \subsection{}).
data Subsection = Subsection
  { subTitle  :: !Text
  , subSlug   :: !Text     -- ^ URL-safe slug (combined with parent secSlug for filenames)
  , subBlocks :: ![DocBlock]
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

-- | Split a section's blocks into subsections on every @Heading 2@.
-- Returns @[]@ if the section has fewer than 2 H2 headings (no split needed).
splitSubsections :: Section -> [Subsection]
splitSubsections sec = case go (secBlocks sec) Nothing [] of
    subs | length subs >= 2 -> subs
    _                       -> []
  where
    go [] Nothing  _   = []
    go [] (Just t) acc = [mkSub t (reverse acc)]
    go (b:bs) title acc
      | isH2 b =
          let finished = case title of
                Nothing -> []
                Just t  -> [mkSub t (reverse acc)]
          in finished ++ go bs (Just (titleText b)) [b]
      | otherwise = go bs title (b : acc)

    isH2 (Heading 2 _) = True
    isH2 _             = False

    titleText (Heading _ inlines) = inlinesToText inlines
    titleText _                   = "Untitled"

    mkSub t bs = Subsection t (slugify t) bs

-- | Convert heading inlines to plain text.
inlinesToText :: [DocInline] -> Text
inlinesToText = T.concat . map go
  where
    go (Plain t)        = t
    go (Code t)         = t
    go (Emph is)        = inlinesToText is
    go (Strong is)      = inlinesToText is
    go (SymRef t)       = t
    go (SectionRef t)   = "\167" <> t
    go (NonTerm t)      = t

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

-- | Write a section, splitting into per-subsection pages if there are >= 2
-- subsections (H2 blocks).  Returns extra SymbolIndex entries for search.
writeSectionOrSplit
  :: FilePath -> Text -> SymbolIndex -> LabelMap -> Maybe Text -> Text
  -> Section -> IO SymbolIndex
writeSectionOrSplit outDir subDir idx lmap mSha title sec = do
  let subs = splitSubsections sec
  if null subs
    then do
      writeSection outDir idx lmap mSha title sec
      pure Map.empty
    else writeSectionSplit outDir subDir idx lmap mSha title sec subs

-- | Write a section that has been split into per-subsection pages.
-- Creates:
--   {secSlug}.html      — index listing all subsections
--   {secSlug}-{subSlug}.html — one page per subsection (with sidebar)
-- Returns SymbolIndex entries for all subsections (for search).
writeSectionSplit
  :: FilePath -> Text -> SymbolIndex -> LabelMap -> Maybe Text -> Text
  -> Section -> [Subsection] -> IO SymbolIndex
writeSectionSplit outDir subDir idx lmap mSha title sec subs = do
  -- Section index page
  let idxPath = outDir </> T.unpack (secSlug sec) ++ ".html"
  TLIO.writeFile idxPath (renderHtml (sectionIndexPage sec subs mSha title))
  -- Individual subsection pages
  forM_ subs $ \sub -> do
    let path = outDir </> T.unpack (secSlug sec <> "-" <> subSlug sub) ++ ".html"
    TLIO.writeFile path (renderHtml (subsectionPage sec subs sub idx lmap mSha title))
  -- Build SymbolIndex entries so subsections appear in search
  let entries = Map.fromList
        [ ( subTitle sub
          , SymbolRef
              { srPackage = secSlug sec <> "-" <> subSlug sub
              , srSection = subDir
              , srAnchor  = "top"
              , srDisplay = Just title
              }
          )
        | sub <- subs
        ]
  pure entries

-- | Write a single (non-split) section as an HTML file.
writeSection :: FilePath -> SymbolIndex -> LabelMap -> Maybe Text -> Text -> Section -> IO ()
writeSection outDir idx lmap mSha title sec = do
  let path = outDir </> T.unpack (secSlug sec) ++ ".html"
  TLIO.writeFile path (renderHtml (sectionPage sec idx lmap mSha title))

-- | Render a plain section page (no subsection sidebar).
sectionPage :: Section -> SymbolIndex -> LabelMap -> Maybe Text -> Text -> Html
sectionPage sec idx lmap mSha title = H.docTypeHtml $ do
  H.head $ do
    H.meta ! A.charset "utf-8"
    H.title (H.toHtml (secTitle sec <> " — " <> title))
    H.link ! A.rel "stylesheet" ! A.href "../docgen.css"
    mathJaxScripts "../mathjax.js"
  H.body $ do
    searchHeader "../"
    H.nav ! A.class_ "breadcrumb" $
      H.a ! A.href "index.html" $ H.toHtml title
    H.main $
      renderDocBlocks idx lmap (secBlocks sec)
    docFooter mSha
    H.script ! A.src "../search.js" $ ""

-- | Render the index page for a split section (lists all subsections).
sectionIndexPage :: Section -> [Subsection] -> Maybe Text -> Text -> Html
sectionIndexPage sec subs mSha title = H.docTypeHtml $ do
  H.head $ do
    H.meta ! A.charset "utf-8"
    H.title (H.toHtml (secTitle sec <> " — " <> title))
    H.link ! A.rel "stylesheet" ! A.href "../docgen.css"
    mathJaxScripts "../mathjax.js"
  H.body $ do
    searchHeader "../"
    H.nav ! A.class_ "breadcrumb" $
      H.a ! A.href "index.html" $ H.toHtml title
    H.div ! A.class_ "sub-layout" $ do
      H.aside ! A.class_ "sub-sidebar" $ do
        H.h3 (H.toHtml (secTitle sec))
        H.ul $ forM_ subs $ \sub ->
          H.li $ H.a
            ! A.href (H.toValue (secSlug sec <> "-" <> subSlug sub <> ".html"))
            $ H.toHtml (subTitle sub)
      H.main $ do
        H.h1 (H.toHtml (secTitle sec))
        H.ul $ forM_ subs $ \sub ->
          H.li $ H.a
            ! A.href (H.toValue (secSlug sec <> "-" <> subSlug sub <> ".html"))
            $ H.toHtml (subTitle sub)
    docFooter mSha
    H.script ! A.src "../search.js" $ ""

-- | Render a subsection page with a sidebar listing sibling subsections.
subsectionPage
  :: Section -> [Subsection] -> Subsection
  -> SymbolIndex -> LabelMap -> Maybe Text -> Text -> Html
subsectionPage sec subs sub idx lmap mSha title = H.docTypeHtml $ do
  H.head $ do
    H.meta ! A.charset "utf-8"
    H.title (H.toHtml (subTitle sub <> " — " <> title))
    H.link ! A.rel "stylesheet" ! A.href "../docgen.css"
    mathJaxScripts "../mathjax.js"
  H.body $ do
    searchHeader "../"
    H.nav ! A.class_ "breadcrumb" $ do
      H.a ! A.href "index.html" $ H.toHtml title
      " / "
      H.a ! A.href (H.toValue (secSlug sec <> ".html")) $ H.toHtml (secTitle sec)
    H.div ! A.class_ "sub-layout" $ do
      H.aside ! A.class_ "sub-sidebar" $ do
        H.h3 (H.toHtml (secTitle sec))
        H.ul $ forM_ subs $ \s -> do
          let active = subSlug s == subSlug sub
              href   = secSlug sec <> "-" <> subSlug s <> ".html"
          H.li ! (if active then A.class_ "active" else mempty) $
            H.a ! A.href (H.toValue href) $ H.toHtml (subTitle s)
      H.main $
        renderDocBlocks idx lmap (subBlocks sub)
    docFooter mSha
    H.script ! A.src "../search.js" $ ""

-- | Write the table-of-contents index page.
writeTocPage :: FilePath -> [Section] -> Maybe Text -> Text -> IO ()
writeTocPage outDir sections mSha title = do
  let path = outDir </> "index.html"
  TLIO.writeFile path (renderHtml (tocPage sections mSha title))

-- | Render the table-of-contents page.
tocPage :: [Section] -> Maybe Text -> Text -> Html
tocPage sections mSha title = H.docTypeHtml $ do
  H.head $ do
    H.meta ! A.charset "utf-8"
    H.title (H.toHtml title)
    H.link ! A.rel "stylesheet" ! A.href "../docgen.css"
    mathJaxScripts "../mathjax.js"
  H.body $ do
    searchHeader "../"
    H.main $ do
      H.h1 (H.toHtml title)
      H.ul $ mapM_ tocEntry sections
      H.p $ do
        H.a ! A.href "term-index.html" $ "Term Index"
        " — alphabetical index of terms"
    docFooter mSha
    H.script ! A.src "../search.js" $ ""
  where
    tocEntry sec =
      let subs = splitSubsections sec
      in if null subs
         then H.li $ H.a ! A.href (H.toValue (secSlug sec <> ".html")) $
                H.toHtml (secTitle sec)
         else H.li $ do
                H.a ! A.href (H.toValue (secSlug sec <> ".html")) $
                  H.toHtml (secTitle sec)
                H.ul $ forM_ subs $ \sub ->
                  H.li $ H.a
                    ! A.href (H.toValue (secSlug sec <> "-" <> subSlug sub <> ".html"))
                    $ H.toHtml (subTitle sub)

-- | Write the back-of-book term index page.
writeTermIndex :: FilePath -> [IndexEntry] -> Maybe Text -> Text -> IO ()
writeTermIndex outDir entries mSha title = do
  let path = outDir </> "term-index.html"
  TLIO.writeFile path (renderHtml (termIndexPage entries mSha title))

-- | Render the alphabetical term index page.
termIndexPage :: [IndexEntry] -> Maybe Text -> Text -> Html
termIndexPage entries mSha title = H.docTypeHtml $ do
  H.head $ do
    H.meta ! A.charset "utf-8"
    H.title (H.toHtml ("Term Index — " <> title))
    H.link ! A.rel "stylesheet" ! A.href "../docgen.css"
    mathJaxScripts "../mathjax.js"
  H.body $ do
    searchHeader "../"
    H.main $ do
      H.nav ! A.class_ "breadcrumb" $
        H.a ! A.href "index.html" $ H.toHtml title
      H.h1 "Term Index"
      if null entries
        then H.p "(No index entries found.)"
        else renderAlphaGroups entries
    docFooter mSha
    H.script ! A.src "../search.js" $ ""

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
