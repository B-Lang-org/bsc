-- | Top-level documentation generation entry point.
-- Exposed as a library function so that @bbt doc@ can call it directly.
module Language.Bluespec.DocGen.Generate
  ( DocGenConfig (..)
  , defaultDocGenConfig
  , runDocGen
  ) where

import Control.Monad (filterM, forM_, when)
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Data.Text.Lazy.IO qualified as TLIO
import Data.ByteString.Lazy qualified as LBS
import System.Directory (createDirectoryIfMissing, doesDirectoryExist, doesFileExist, listDirectory)
import System.Exit (ExitCode (..))
import System.FilePath ((</>), takeDirectory, takeExtension)
import System.Process (readProcessWithExitCode)
import Text.Blaze.Html.Renderer.Text (renderHtml)
import Text.Blaze.Html5 (Html, (!))
import Text.Blaze.Html5 qualified as H
import Text.Blaze.Html5.Attributes qualified as A

import Language.Bluespec.DocGen.CSS (stylesheet)
import Language.Bluespec.DocGen.JS (searchScript)
import Language.Bluespec.DocGen.DocAST (dePackage)
import Language.Bluespec.DocGen.Extract (extractDocsFromFile)
import Language.Bluespec.DocGen.HTML
  (renderPackagePage, renderIndexPage, docFooter, mathJaxScripts, searchHeader)
import Language.Bluespec.DocGen.RefManual
  (RefManualConfig (..), defaultRefManualConfig, convertRefManual)
import Language.Bluespec.DocGen.SymbolIndex (SymbolRef (..), buildIndex, renderIndexJson)

-- | A reference manual to convert.
data ManualSpec = ManualSpec
  { msTitle       :: !Text      -- ^ display title (e.g. "BH Language Reference")
  , msTexFile     :: !FilePath  -- ^ path to the root .tex file
  , msSubDir      :: !Text      -- ^ output sub-directory name (e.g. "bh-reference")
  , msDescription :: !Text      -- ^ one-line description for the homepage
  } deriving stock (Show)

-- | Configuration for a documentation generation run.
data DocGenConfig = DocGenConfig
  { dgcLibDirs   :: ![FilePath]       -- ^ source directories to scan
  , dgcOutDir    :: !FilePath         -- ^ output directory
  , dgcRefManual :: !(Maybe FilePath) -- ^ path to BH_lang.tex (optional)
  , dgcBscDocDir :: !(Maybe FilePath) -- ^ path to BSC doc/ directory for auto-discovering all manuals
  , dgcStdlibUrl :: !(Maybe String)   -- ^ external stdlib URL for cross-linking
  , dgcVerbose   :: !Bool
  , dgcBscSha    :: !(Maybe Text)     -- ^ BSC git commit SHA for footer (auto-detected if Nothing)
  } deriving stock (Show)

-- | Sensible defaults: scan nothing, output to @docs/@.
defaultDocGenConfig :: DocGenConfig
defaultDocGenConfig = DocGenConfig
  { dgcLibDirs   = []
  , dgcOutDir    = "docs"
  , dgcRefManual = Nothing
  , dgcBscDocDir = Nothing
  , dgcStdlibUrl = Nothing
  , dgcVerbose   = False
  , dgcBscSha    = Nothing
  }

-- | Run the documentation generator.
runDocGen :: DocGenConfig -> IO ()
runDocGen cfg = do
  -- 1. Collect source files
  srcFiles <- fmap concat $ mapM collectSources (dgcLibDirs cfg)
  when (dgcVerbose cfg) $
    putStrLn $ "[docgen] Found " ++ show (length srcFiles) ++ " source files"

  -- 2. Extract documentation entries
  allEntries <- fmap concat $ mapM extractDocsFromFile srcFiles
  when (dgcVerbose cfg) $
    putStrLn $ "[docgen] Extracted " ++ show (length allEntries) ++ " doc entries"

  -- 3. Build symbol index (symbols first, then add package names for searchability)
  let symbolIdx = buildIndex allEntries

  -- 4. Group by package
  let pkgMap = foldr (\e m -> Map.insertWith (++) (dePackage e) [e] m)
                     Map.empty allEntries

  -- Add package/module names to the index so the search bar can find them.
  let pkgIdx = Map.fromList
        [ (pkg, SymbolRef { srPackage = pkg, srSection = "stdlib", srAnchor = "top", srDisplay = Nothing })
        | pkg <- Map.keys pkgMap ]
      idx = symbolIdx <> pkgIdx

  -- 5. Create output directories
  let outDir    = dgcOutDir cfg
      stdlibDir = outDir </> "stdlib"
  createDirectoryIfMissing True stdlibDir

  -- 6. Write per-package pages
  forM_ (Map.toAscList pkgMap) $ \(pkg, entries) -> do
    let html = renderPackagePage pkg entries idx
        path = stdlibDir </> T.unpack pkg ++ ".html"
    TIO.writeFile path html
    when (dgcVerbose cfg) $
      putStrLn $ "[docgen] Wrote " ++ path

  -- 7. Write stdlib index
  TIO.writeFile (stdlibDir </> "index.html") (renderIndexPage pkgMap)

  -- 8. Determine manuals to convert
  manuals <- case dgcBscDocDir cfg of
    Just docDir -> discoverManuals docDir
    Nothing     -> case dgcRefManual cfg of
      Nothing      -> pure []
      Just texPath -> pure
        [ ManualSpec "BH Language Reference" texPath "reference"
            "Reference manual for the Bluespec Classic (BH) hardware description language."
        ]

  -- 9. Convert each manual (collect extra index entries for split subsections)
  bscSha <- resolveBscSha cfg manuals
  extraIdxs <- mapM (\ms -> do
    let rmCfg = defaultRefManualConfig
                  { rmcTexFile = msTexFile ms
                  , rmcTitle   = msTitle ms
                  , rmcSubDir  = msSubDir ms
                  , rmcOutDir  = outDir
                  , rmcVerbose = dgcVerbose cfg
                  , rmcBscSha  = bscSha
                  }
    extra <- convertRefManual rmCfg idx
    when (dgcVerbose cfg) $
      putStrLn $ "[docgen] " ++ T.unpack (msTitle ms) ++ " → " ++ T.unpack (msSubDir ms) ++ "/"
    pure extra
    ) manuals

  -- 10. Write site root
  TLIO.writeFile (outDir </> "index.html") $
    renderHtml (siteRootPage manuals (dgcStdlibUrl cfg) bscSha)

  -- 11. Write stylesheet
  TIO.writeFile (outDir </> "docgen.css") stylesheet

  -- 12b. Write search script
  TIO.writeFile (outDir </> "search.js") searchScript

  -- 12. Download MathJax bundle (for local math rendering, no CDN at view time)
  downloadMathjax outDir (dgcVerbose cfg)

  -- 13. Write symbol index JSON (merging in manual section entries)
  let fullIdx = idx <> Map.unions extraIdxs
  LBS.writeFile (outDir </> "symbol-index.json") (renderIndexJson fullIdx)

  putStrLn $ "[docgen] Done. Output written to " ++ outDir ++ "/"
  putStrLn $ "[docgen] " ++ show (Map.size pkgMap) ++ " packages, "
          ++ show (length allEntries) ++ " documented symbols"
  when (not (null manuals)) $
    putStrLn $ "[docgen] " ++ show (length manuals) ++ " reference manual(s) converted"

-- ---------------------------------------------------------------------------
-- Site root page
-- ---------------------------------------------------------------------------

-- | Render the top-level index.html linking to stdlib and (optionally) the
-- reference manuals.
siteRootPage :: [ManualSpec] -> Maybe String -> Maybe Text -> Html
siteRootPage manuals mStdlibUrl mSha =
  H.docTypeHtml $ do
    H.head $ do
      H.meta ! A.charset "utf-8"
      H.title "Bluespec Documentation"
      H.link ! A.rel "stylesheet" ! A.href "docgen.css"
      mathJaxScripts "mathjax.js"
    H.body $ do
      searchHeader ""
      H.main $ do
        H.h1 "Bluespec Documentation"
        mapM_ manualSection manuals
        H.section $ do
          H.h2 $ do
            case mStdlibUrl of
              Just url -> H.a ! A.href (H.toValue url) $ "Standard Library"
              Nothing  -> H.a ! A.href "stdlib/index.html" $ "Standard Library"
          H.p $ do
            "Auto-extracted API docs from source files. "
            "Covers the Prelude, Vector, FIFOF, and other library packages. "
            when (isJust mStdlibUrl) $
              H.em "(linking to external hosted docs)"
        when (not (null manuals)) $
          H.section $ do
            H.h2 "Term Indices"
            H.ul $ mapM_ termIndexEntry manuals
      docFooter mSha
      H.script ! A.src "search.js" $ ""
  where
    manualSection ms =
      H.section $ do
        let url = msSubDir ms <> "/index.html"
        H.h2 $ H.a ! A.href (H.toValue url) $ H.toHtml (msTitle ms)
        H.p $ H.toHtml (msDescription ms)

    termIndexEntry ms =
      H.li $ H.a ! A.href (H.toValue (msSubDir ms <> "/term-index.html")) $
        H.toHtml (msTitle ms <> " Term Index")

-- ---------------------------------------------------------------------------
-- BSC SHA resolution
-- ---------------------------------------------------------------------------

-- | Determine the BSC commit SHA to embed in footers.
-- If the user provided one explicitly (via --bsc-sha), use that.
-- Otherwise, if manuals were provided, try 'git rev-parse --short HEAD'
-- in the directory of the first manual's tex file. Falls back to Nothing silently.
resolveBscSha :: DocGenConfig -> [ManualSpec] -> IO (Maybe Text)
resolveBscSha cfg manuals =
  case dgcBscSha cfg of
    Just sha -> pure (Just sha)
    Nothing  -> case manuals of
      []    -> pure Nothing
      (m:_) -> gitShortSha (takeDirectory (msTexFile m))

-- ---------------------------------------------------------------------------
-- Manual discovery
-- ---------------------------------------------------------------------------

-- | Discover the standard BSC manuals from a doc directory.
-- Checks each well-known path for existence; silently skips missing ones.
discoverManuals :: FilePath -> IO [ManualSpec]
discoverManuals docDir = do
  let candidates =
        [ ManualSpec "BH Language Reference"
            (docDir </> "BH_ref_guide" </> "BH_lang.tex")
            "bh-reference"
            "Reference manual for the Bluespec Classic (BH) hardware description language."
        , ManualSpec "BSV Language Reference"
            (docDir </> "BSV_ref_guide" </> "BSV_lang.tex")
            "bsv-reference"
            "Reference manual for Bluespec SystemVerilog (BSV)."
        , ManualSpec "BSC User Guide"
            (docDir </> "user_guide" </> "user_guide.tex")
            "user-guide"
            "User guide for the BSC compiler: flags, scheduling, synthesis, simulation."
        , ManualSpec "Libraries Reference Guide"
            (docDir </> "libraries_ref_guide" </> "libraries_ref_guide.tex")
            "libraries-reference"
            "Detailed documentation for all standard Bluespec library packages."
        ]
  filterM (\ms -> doesFileExist (msTexFile ms)) candidates

-- | Run @git rev-parse --short HEAD@ in the given directory.
gitShortSha :: FilePath -> IO (Maybe Text)
gitShortSha dir = do
  (ec, out, _) <- readProcessWithExitCode "git"
    ["-C", dir, "rev-parse", "--short", "HEAD"] ""
  case ec of
    ExitSuccess -> pure $ Just (T.strip (T.pack out))
    _           -> pure Nothing

-- ---------------------------------------------------------------------------
-- MathJax download
-- ---------------------------------------------------------------------------

-- | MathJax CDN URL for the single-file tex-svg bundle (version 3).
mathjaxUrl :: String
mathjaxUrl = "https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-svg.js"

-- | Download the MathJax bundle to @outDir/mathjax.js@ if not already present.
-- Tries @wget@ then @curl@; warns but does not fail if both are unavailable.
-- When the file already exists it is not re-downloaded.
downloadMathjax :: FilePath -> Bool -> IO ()
downloadMathjax outDir verbose = do
  let dest = outDir </> "mathjax.js"
  exists <- doesFileExist dest
  if exists
    then when verbose $ putStrLn $ "[docgen] MathJax already present: " ++ dest
    else do
      when verbose $ putStrLn $ "[docgen] Downloading MathJax from " ++ mathjaxUrl
      (ec, _, _) <- readProcessWithExitCode "wget"
        ["-q", "-O", dest, mathjaxUrl] ""
      case ec of
        ExitSuccess -> when verbose $
          putStrLn $ "[docgen] MathJax saved to " ++ dest
        _ -> do
          -- wget failed or not available; try curl
          (ec2, _, _) <- readProcessWithExitCode "curl"
            ["-sSL", "-o", dest, mathjaxUrl] ""
          case ec2 of
            ExitSuccess -> when verbose $
              putStrLn $ "[docgen] MathJax saved to " ++ dest
            _ -> putStrLn $
              "[docgen] Warning: could not download MathJax. "
              ++ "Math will not render. Run: wget -O "
              ++ dest ++ " " ++ mathjaxUrl

-- ---------------------------------------------------------------------------
-- Source file collection
-- ---------------------------------------------------------------------------

collectSources :: FilePath -> IO [FilePath]
collectSources dir = do
  exists <- doesDirectoryExist dir
  if not exists
    then do
      putStrLn $ "[docgen] Warning: directory not found: " ++ dir
      pure []
    else do
      entries <- listDirectory dir
      fmap concat $ mapM (processEntry dir) entries
  where
    processEntry parent entry = do
      let path = parent </> entry
      isDir <- doesDirectoryExist path
      if isDir
        then collectSources path
        else pure $ case takeExtension entry of
          ".bs"  -> [path]
          ".bsv" -> [path]
          _      -> []
