-- | Top-level documentation generation entry point.
-- Exposed as a library function so that @bbt doc@ can call it directly.
module Language.Bluespec.DocGen.Generate
  ( DocGenConfig (..)
  , defaultDocGenConfig
  , runDocGen
  ) where

import Control.Monad (forM_, when)
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Data.Text.Lazy.IO qualified as TLIO
import Data.ByteString.Lazy qualified as LBS
import System.Directory (createDirectoryIfMissing, doesDirectoryExist, listDirectory)
import System.Exit (ExitCode (..))
import System.FilePath ((</>), takeDirectory, takeExtension)
import System.Process (readProcessWithExitCode)
import Text.Blaze.Html.Renderer.Text (renderHtml)
import Text.Blaze.Html5 (Html, (!))
import Text.Blaze.Html5 qualified as H
import Text.Blaze.Html5.Attributes qualified as A

import Language.Bluespec.DocGen.CSS (stylesheet)
import Language.Bluespec.DocGen.DocAST (dePackage)
import Language.Bluespec.DocGen.Extract (extractDocsFromFile)
import Language.Bluespec.DocGen.HTML
  (renderPackagePage, renderIndexPage, docFooter)
import Language.Bluespec.DocGen.RefManual
  (RefManualConfig (..), defaultRefManualConfig, convertRefManual)
import Language.Bluespec.DocGen.SymbolIndex (buildIndex, renderIndexJson)

-- | Configuration for a documentation generation run.
data DocGenConfig = DocGenConfig
  { dgcLibDirs   :: ![FilePath]       -- ^ source directories to scan
  , dgcOutDir    :: !FilePath         -- ^ output directory
  , dgcRefManual :: !(Maybe FilePath) -- ^ path to BH_lang.tex (optional)
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

  -- 3. Build symbol index
  let idx = buildIndex allEntries

  -- 4. Group by package
  let pkgMap = foldr (\e m -> Map.insertWith (++) (dePackage e) [e] m)
                     Map.empty allEntries

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

  -- 8. Convert reference manual if provided
  bscSha <- resolveBscSha cfg
  hasRef <- case dgcRefManual cfg of
    Nothing -> pure False
    Just texPath -> do
      let rmCfg = defaultRefManualConfig
                    { rmcTexFile = texPath
                    , rmcOutDir  = outDir
                    , rmcVerbose = dgcVerbose cfg
                    , rmcBscSha  = bscSha
                    }
      convertRefManual rmCfg idx
      pure True

  -- 9. Write site root (links to both sections)
  TLIO.writeFile (outDir </> "index.html") $
    renderHtml (siteRootPage hasRef (dgcStdlibUrl cfg) bscSha)

  -- 10. Write stylesheet
  TIO.writeFile (outDir </> "docgen.css") stylesheet

  -- 11. Write symbol index JSON
  LBS.writeFile (outDir </> "symbol-index.json") (renderIndexJson idx)

  putStrLn $ "[docgen] Done. Output written to " ++ outDir ++ "/"
  putStrLn $ "[docgen] " ++ show (Map.size pkgMap) ++ " packages, "
          ++ show (length allEntries) ++ " documented symbols"
  when hasRef $
    putStrLn $ "[docgen] Reference manual converted to " ++ outDir ++ "/reference/"

-- ---------------------------------------------------------------------------
-- Site root page
-- ---------------------------------------------------------------------------

-- | Render the top-level index.html linking to stdlib and (optionally) the
-- reference manual.
siteRootPage :: Bool -> Maybe String -> Maybe Text -> Html
siteRootPage hasRef mStdlibUrl mSha =
  H.docTypeHtml $ do
    H.head $ do
      H.meta ! A.charset "utf-8"
      H.title "Bluespec Documentation"
      H.link ! A.rel "stylesheet" ! A.href "docgen.css"
    H.body $ do
      H.main $ do
        H.h1 "Bluespec Documentation"
        whenB hasRef $
          H.section $ do
            H.h2 $ H.a ! A.href "reference/index.html" $ "Language Reference"
            H.p $ do
              "Converted from the authoritative LaTeX reference manual. "
              "Covers syntax, semantics, and built-in constructs."
        H.section $ do
          H.h2 $ do
            case mStdlibUrl of
              Just url -> H.a ! A.href (H.toValue url) $ "Standard Library"
              Nothing  -> H.a ! A.href "stdlib/index.html" $ "Standard Library"
          H.p $ do
            "Auto-extracted from source files. "
            "Covers the Prelude, Vector, FIFOF, and other library packages. "
            whenB (isJust mStdlibUrl) $
              H.em "(linking to external hosted docs)"
        whenB hasRef $
          H.section $ do
            H.h2 $ H.a ! A.href "reference/term-index.html" $ "Term Index"
            H.p "Alphabetical index of all language terms from the reference manual."
      docFooter mSha
  where
    whenB cond action = if cond then action else pure ()

-- ---------------------------------------------------------------------------
-- BSC SHA resolution
-- ---------------------------------------------------------------------------

-- | Determine the BSC commit SHA to embed in footers.
-- If the user provided one explicitly (via --bsc-sha), use that.
-- Otherwise, if a ref-manual path was given, try 'git rev-parse --short HEAD'
-- in that directory. Falls back to Nothing silently.
resolveBscSha :: DocGenConfig -> IO (Maybe Text)
resolveBscSha cfg =
  case dgcBscSha cfg of
    Just sha -> pure (Just sha)
    Nothing  -> case dgcRefManual cfg of
      Nothing      -> pure Nothing
      Just texPath -> gitShortSha (takeDirectory texPath)

-- | Run @git rev-parse --short HEAD@ in the given directory.
gitShortSha :: FilePath -> IO (Maybe Text)
gitShortSha dir = do
  (ec, out, _) <- readProcessWithExitCode "git"
    ["-C", dir, "rev-parse", "--short", "HEAD"] ""
  case ec of
    ExitSuccess -> pure $ Just (T.strip (T.pack out))
    _           -> pure Nothing

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
