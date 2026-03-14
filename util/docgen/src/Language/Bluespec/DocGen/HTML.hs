-- | Render 'DocEntry' lists to HTML documentation pages.
--
-- Each package gets one page (e.g. @stdlib/Prelude.html@) with a sidebar
-- symbol index and per-symbol sections, Hackage-style.
module Language.Bluespec.DocGen.HTML
  ( renderPackagePage
  , renderIndexPage
  , renderSitePage
  , renderDocBlocks
  , docFooter
  , mathJaxScripts
  ) where

import Data.List (sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Lazy qualified as TL
import Text.Blaze.Html.Renderer.Text (renderHtml)
import Text.Blaze.Html5 (Html, (!))
import Text.Blaze.Html5 qualified as H
import Text.Blaze.Html5.Attributes qualified as A

import Language.Bluespec.DocGen.DocAST
import Language.Bluespec.DocGen.SymbolIndex

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
  TL.toStrict $ renderHtml $ page pkgName $ do
    H.nav ! A.class_ "sidebar" $ do
      H.h2 $ H.toHtml pkgName
      H.ul $ mapM_ sidebarItem (sortOn deName entries)
    H.main $ do
      H.h1 $ do
        H.span ! A.class_ "kw" $ "package "
        H.code $ H.toHtml pkgName
      mapM_ (renderEntry idx) (sortOn deName entries)

-- | Render the stdlib package index page.
renderIndexPage :: Map Text [DocEntry] -> Text
renderIndexPage pkgMap =
  TL.toStrict $ renderHtml $ page "Standard Library" $ do
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
    H.div ! A.class_ "doc" $ mapM_ (renderBlock idx) (deDoc de)

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
renderDocBlocks :: SymbolIndex -> [DocBlock] -> Html
renderDocBlocks idx = mapM_ (renderBlock idx)

renderBlock :: SymbolIndex -> DocBlock -> Html
renderBlock idx = \case
  Para inlines       -> H.p $ mapM_ (renderInline idx) inlines
  Heading n inlines  -> heading n (mapM_ (renderInline idx) inlines)
  CodeBlock _ src    -> H.pre $ H.code $ H.toHtml src
  VerbBlock src      -> H.pre $ H.code $ H.toHtml src
  BulletList items   -> H.ul $ mapM_ (\bs -> H.li $ mapM_ (renderBlock idx) bs) items
  OrderedList items  -> H.ol $ mapM_ (\bs -> H.li $ mapM_ (renderBlock idx) bs) items
  Table hdr rows     -> H.table $ do
    H.thead $ H.tr $ mapM_ (\cs -> H.th $ mapM_ (renderInline idx) cs) hdr
    H.tbody $ mapM_ (\row -> H.tr $ mapM_ (\cs -> H.td $ mapM_ (renderInline idx) cs) row) rows
  HRule              -> H.hr

heading :: Int -> Html -> Html
heading 1 = H.h1
heading 2 = H.h2
heading 3 = H.h3
heading _ = H.h4

-- ---------------------------------------------------------------------------
-- Inline rendering
-- ---------------------------------------------------------------------------

renderInline :: SymbolIndex -> DocInline -> Html
renderInline idx = \case
  Plain t    -> H.toHtml t
  Code  t    -> H.code $ H.toHtml t
  Emph  is   -> H.em $ mapM_ (renderInline idx) is
  Strong is  -> H.strong $ mapM_ (renderInline idx) is
  NonTerm t  -> H.em ! A.class_ "nt" $ H.toHtml t
  SymRef name ->
    case lookupSymbol name idx of
      Nothing  -> H.code $ H.toHtml name
      Just ref ->
        let url = fromMaybe name (resolveUrl ref)
        in H.a ! A.href (H.toValue url) $ H.code $ H.toHtml name

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

page :: Text -> Html -> Html
page title body_ = H.docTypeHtml $ do
  H.head $ do
    H.meta ! A.charset "utf-8"
    H.meta ! A.name "viewport" ! A.content "width=device-width, initial-scale=1"
    H.title $ H.toHtml title
    H.link ! A.rel "stylesheet" ! A.href "../docgen.css"
    mathJaxScripts "../mathjax.js"
  H.body $ H.div ! A.class_ "page-layout" $ body_

pageRaw :: Text -> Html -> Html
pageRaw title body_ = H.docTypeHtml $ do
  H.head $ do
    H.meta ! A.charset "utf-8"
    H.meta ! A.name "viewport" ! A.content "width=device-width, initial-scale=1"
    H.title $ H.toHtml title
    H.link ! A.rel "stylesheet" ! A.href "docgen.css"
    mathJaxScripts "mathjax.js"
  H.body $ H.div ! A.class_ "page-layout" $ body_

-- | Emit MathJax configuration + loader scripts.
-- The @src@ argument is the relative path to the local @mathjax.js@ bundle.
-- MathJax processes @\\(...\\)@ inline and @\\[...\\]@ display delimiters.
mathJaxScripts :: Text -> Html
mathJaxScripts src = do
  H.script ! A.type_ "text/javascript" $
    "MathJax={tex:{inlineMath:[['\\\\(','\\\\)']],displayMath:[['\\\\[','\\\\]']]}};"
  H.script ! A.type_ "text/javascript" ! A.src (H.toValue src) ! A.async "async" $ ""
