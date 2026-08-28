-- | Render 'DocEntry' lists to HTML documentation pages.
--
-- Each package gets one page (e.g. @stdlib/Prelude.html@) with a sidebar
-- symbol index and per-symbol sections, Hackage-style.
module Language.Bluespec.DocGen.HTML
  ( LabelMap
  , renderPackagePage
  , renderIndexPage
  , renderSitePage
  , renderDocBlocks
  , docFooter
  , mathJaxScripts
  , searchHeader
  , slugifyInlines
  ) where

import Control.Monad (when)
import Data.List (sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Lazy qualified as TL
import System.FilePath (takeFileName, takeExtension)
import Text.Blaze.Html.Renderer.Text (renderHtml)
import Text.Blaze.Html5 (Html, (!))
import Text.Blaze.Html5 qualified as H
import Text.Blaze.Html5.Attributes qualified as A

import Language.Bluespec.DocGen.DocAST
import Language.Bluespec.DocGen.SymbolIndex

-- | Map from LaTeX @\label{lbl}@ keys to the slug of the section page that
-- contains them (e.g. @"sec-type"@ → @"types"@).
-- Used to turn @\ref{lbl}@ into a proper hyperlink.
type LabelMap = Map Text Text

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

-- | Render all entries for one package to an HTML page.
renderPackagePage
  :: Text          -- ^ package name (e.g. "Prelude")
  -> [DocEntry]    -- ^ all entries for this package
  -> SymbolIndex   -- ^ global cross-reference index
  -> Text          -- ^ rendered HTML
renderPackagePage pkgName entries idx =
  TL.toStrict $ renderHtml $ page pkgName breadcrumb $ do
    H.nav ! A.class_ "sidebar" $ do
      H.h2 $ H.toHtml pkgName
      H.ul $ mapM_ sidebarItem (sortOn deName entries)
    H.main $ do
      H.h1 $ do
        H.span ! A.class_ "kw" $ "package "
        H.code $ H.toHtml pkgName
      mapM_ (renderEntry idx) (sortOn deName entries)
  where
    breadcrumb = do
      H.a ! A.href "../index.html" $ "Bluespec Docs"
      H.span ! A.class_ "sep" $ ""
      H.a ! A.href "index.html" $ "Standard Library"
      H.span ! A.class_ "sep" $ ""
      H.span $ H.toHtml pkgName

-- | Render the stdlib package index page.
renderIndexPage :: Map Text [DocEntry] -> Text
renderIndexPage pkgMap =
  TL.toStrict $ renderHtml $ page "Standard Library" breadcrumb $ do
    H.nav ! A.class_ "sidebar" $ do
      H.h2 "Packages"
      H.ul $ mapM_ (\p -> H.li $ H.a ! A.href (H.toValue (p <> ".html")) $ H.toHtml p)
                   (Map.keys pkgMap)
    H.main $ do
      H.h1 "Bluespec Standard Library"
      H.p "Auto-generated from source comments."
      H.ul $ mapM_ (\(p, es) ->
        H.li $ do
          H.a ! A.href (H.toValue (p <> ".html")) $ H.toHtml p
          H.toHtml (" — " <> T.pack (show (length es)) <> " documented symbols"))
        (Map.toAscList pkgMap)
  where
    breadcrumb = do
      H.a ! A.href "../index.html" $ "Bluespec Docs"
      H.span ! A.class_ "sep" $ ""
      H.span $ "Standard Library"

-- | Render the top-level site index.
renderSitePage :: Text
renderSitePage =
  TL.toStrict $ renderHtml $ pageRaw "Bluespec Documentation" $ do
    H.nav ! A.class_ "sidebar" $ H.ul $ do
      H.li $ H.a ! A.href "stdlib/index.html" $ "Standard Library"
      H.li $ H.a ! A.href "reference/index.html" $ "Language Reference"
    H.main $ do
      H.h1 "Bluespec Documentation"
      H.h2 $ H.a ! A.href "stdlib/index.html" $ "Standard Library"
      H.p "Auto-extracted from source comments in the BSC standard library packages."
      H.h2 $ H.a ! A.href "reference/index.html" $ "Language Reference"
      H.p "Converted from the authoritative LaTeX reference manual."

-- ---------------------------------------------------------------------------
-- Per-entry rendering
-- ---------------------------------------------------------------------------

sidebarItem :: DocEntry -> Html
sidebarItem de =
  H.li $ H.a ! A.href (H.toValue ("#" <> anchor (deKind de) (deName de))) $
    H.toHtml (deName de)

renderEntry :: SymbolIndex -> DocEntry -> Html
renderEntry idx de =
  H.section ! A.id (H.toValue (anchor (deKind de) (deName de))) $ do
    H.h3 $ do
      H.span ! A.class_ "kw" $ H.toHtml (kindLabel (deKind de) <> " ")
      H.code $ H.toHtml (deName de)
    case deTypeSig de of
      Nothing  -> pure ()
      Just sig -> H.pre ! A.class_ "type-sig" $ H.toHtml sig
    H.div ! A.class_ "doc" $ mapM_ (renderBlock idx Map.empty) (deDoc de)

kindLabel :: DocKind -> Text
kindLabel DKValue       = ""
kindLabel DKType        = "type"
kindLabel DKClass       = "typeclass"
kindLabel DKInstance    = "instance"
kindLabel DKConstructor = ""
kindLabel DKField       = "field"

-- ---------------------------------------------------------------------------
-- Block rendering
-- ---------------------------------------------------------------------------

-- | Render a list of 'DocBlock's into HTML.
-- Exported for use by 'RefManual' and other callers.
-- Pass 'Map.empty' for @lmap@ when rendering stdlib pages (no @\ref{}@ calls).
renderDocBlocks :: SymbolIndex -> LabelMap -> [DocBlock] -> Html
renderDocBlocks idx lmap = mapM_ (renderBlock idx lmap)

renderBlock :: SymbolIndex -> LabelMap -> DocBlock -> Html
renderBlock idx lmap = \case
  Para inlines       -> H.p $ mapM_ (renderInline idx lmap) inlines
  Heading n inlines  ->
    let slug = slugifyInlines inlines
        tag  = heading n
    in tag ! A.id (H.toValue slug) $ do
         mapM_ (renderInline idx lmap) inlines
         H.a ! A.class_ "anchor-link" ! A.href (H.toValue ("#" <> slug)) $ "#"
  CodeBlock _ src    -> H.pre $ H.code $ H.toHtml src
  VerbBlock src      -> H.pre $ H.code $ H.toHtml src
  BulletList items   -> H.ul $ mapM_ (\bs -> H.li $ mapM_ (renderBlock idx lmap) bs) items
  OrderedList items  -> H.ol $ mapM_ (\bs -> H.li $ mapM_ (renderBlock idx lmap) bs) items
  Table hdr rows     -> H.table ! A.class_ "doc-table" $ do
    when (any (not . null) hdr) $
      H.thead $ H.tr $ mapM_ (\cs -> H.th $ mapM_ (renderInline idx lmap) cs) hdr
    H.tbody $ mapM_ (\row -> H.tr $ mapM_ (\cs -> H.td $ mapM_ (renderInline idx lmap) cs) row) rows
  HRule              -> H.hr
  Image path mCaption -> H.figure ! A.class_ "doc-figure" $ do
    -- Normalize image path: strip directory prefix, add .png if no extension
    let filename = T.pack $ takeFileName (T.unpack path)
        imgSrc   = if T.null (T.pack (takeExtension (T.unpack filename)))
                   then filename <> ".png"
                   else filename
    H.img ! A.src (H.toValue imgSrc) ! A.alt (H.toValue (fromMaybe "" mCaption))
    case mCaption of
      Nothing -> pure ()
      Just cap -> H.figcaption $ H.toHtml cap
  BlockQuote blocks  -> H.blockquote $ mapM_ (renderBlock idx lmap) blocks

heading :: Int -> Html -> Html
heading 1 = H.h1
heading 2 = H.h2
heading 3 = H.h3
heading _ = H.h4

-- | Generate a URL-safe slug from heading inlines for use as an anchor id.
slugifyInlines :: [DocInline] -> Text
slugifyInlines = T.intercalate "-" . T.words . T.map slugChar . T.toLower . T.concat . map inlineText
  where
    slugChar c
      | c >= 'a' && c <= 'z' = c
      | c >= '0' && c <= '9' = c
      | c == ' ' = ' '
      | otherwise = ' '
    inlineText (Plain t)      = t
    inlineText (Code t)       = t
    inlineText (Emph is)      = T.concat (map inlineText is)
    inlineText (Strong is)    = T.concat (map inlineText is)
    inlineText (SymRef t)     = t
    inlineText (SectionRef t) = t
    inlineText (NonTerm t)    = t
    inlineText (Footnote is)  = T.concat (map inlineText is)
    inlineText (Link _ is)    = T.concat (map inlineText is)

-- ---------------------------------------------------------------------------
-- Inline rendering
-- ---------------------------------------------------------------------------

renderInline :: SymbolIndex -> LabelMap -> DocInline -> Html
renderInline idx lmap = \case
  Plain t    -> H.toHtml t
  Code  t    -> H.code $ H.toHtml t
  Emph  is   -> H.em $ mapM_ (renderInline idx lmap) is
  Strong is  -> H.strong $ mapM_ (renderInline idx lmap) is
  NonTerm t  -> H.em ! A.class_ "nt" $ H.toHtml t
  SymRef name ->
    case lookupSymbol name idx of
      Nothing  -> H.code $ H.toHtml name
      Just ref ->
        let url = fromMaybe name (resolveUrl ref)
        in H.a ! A.href (H.toValue url) $ H.code $ H.toHtml name
  SectionRef lbl ->
    let slug = fromMaybe lbl (Map.lookup lbl lmap)
        url  = slug <> ".html"
        -- Display the section name without the raw label prefix (e.g. "sec-").
        -- Strip a leading "sec-" and replace hyphens with spaces so that
        -- \ref{sec-overloading} renders as "overloading" rather than "§sec-overloading".
        rawDisplay = if "sec-" `T.isPrefixOf` lbl then T.drop 4 lbl else slug
        displayText = T.replace "-" " " rawDisplay
    in H.a ! A.href (H.toValue url) $ H.toHtml displayText
  Footnote is ->
    H.span ! A.class_ "footnote" $ do
      " ("
      mapM_ (renderInline idx lmap) is
      ")"
  Link url is ->
    H.a ! A.href (H.toValue url) $ mapM_ (renderInline idx lmap) is

resolveUrl :: SymbolRef -> Maybe Text
resolveUrl ref = Just $ srPackage ref <> ".html#" <> srAnchor ref

-- ---------------------------------------------------------------------------
-- Footer
-- ---------------------------------------------------------------------------

-- | Render an HTML footer with an optional BSC commit SHA.
-- Exported for use by RefManual and other callers.
docFooter :: Maybe Text -> Html
docFooter Nothing    = pure ()
docFooter (Just sha) =
  H.footer ! A.class_ "doc-footer" $ do
    "Generated by "
    H.a ! A.href "https://github.com/B-Lang-org/bsc" $ "BSC"
    " · commit "
    H.code $ H.toHtml sha

-- ---------------------------------------------------------------------------
-- Page shell
-- ---------------------------------------------------------------------------

page :: Text -> Html -> Html -> Html
page title breadcrumb body_ = H.docTypeHtml $ do
  H.head $ do
    H.meta ! A.charset "utf-8"
    H.meta ! A.name "viewport" ! A.content "width=device-width, initial-scale=1"
    H.title $ H.toHtml title
    H.link ! A.rel "stylesheet" ! A.href "../docgen.css"
    mathJaxScripts "../mathjax.js"
  H.body $ do
    searchHeader "../"
    H.nav ! A.class_ "breadcrumb" $ breadcrumb
    H.div ! A.class_ "page-layout" $ body_
    H.script ! A.src "../search.js" $ ""

pageRaw :: Text -> Html -> Html
pageRaw title body_ = H.docTypeHtml $ do
  H.head $ do
    H.meta ! A.charset "utf-8"
    H.meta ! A.name "viewport" ! A.content "width=device-width, initial-scale=1"
    H.title $ H.toHtml title
    H.link ! A.rel "stylesheet" ! A.href "docgen.css"
    mathJaxScripts "mathjax.js"
  H.body $ do
    searchHeader ""
    H.div ! A.class_ "page-layout" $ body_
    H.script ! A.src "search.js" $ ""

-- | Emit MathJax configuration + loader scripts.
-- The @src@ argument is the relative path to the local @mathjax.js@ bundle.
-- MathJax processes @\\(...\\)@ inline and @\\[...\\]@ display delimiters.
mathJaxScripts :: Text -> Html
mathJaxScripts src = do
  H.script ! A.type_ "text/javascript" $
    "MathJax={tex:{inlineMath:[['\\\\(','\\\\)']],displayMath:[['\\\\[','\\\\]']]}};"
  H.script ! A.type_ "text/javascript" ! A.src (H.toValue src) ! A.async "async" $ ""

-- | Sticky search header bar.
-- The @root@ argument is the path prefix to reach the doc root
-- (empty string @""@ for root pages, @"../"@ for pages one level deep).
searchHeader :: Text -> Html
searchHeader root =
  H.header ! A.class_ "search-header" $ do
    H.a ! A.class_ "home-btn"
        ! A.href (H.toValue (root <> "index.html")) $ "Home"
    H.div ! A.class_ "search-container" $ do
      H.input ! A.class_ "bs-search-input"
              ! A.type_ "search"
              ! A.placeholder "Search symbols\x2026"
              ! H.dataAttribute "root" (H.toValue root)
              ! A.autocomplete "off"
      H.ul ! A.class_ "bs-search-results" ! A.hidden "" $ ""
