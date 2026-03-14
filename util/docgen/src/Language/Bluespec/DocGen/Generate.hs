-- | Top-level documentation generation entry point.
-- Exposed as a library function so that @bbt doc@ can call it directly.
module Language.Bluespec.DocGen.Generate
  ( DocGenConfig (..)
  , defaultDocGenConfig
  , runDocGen
  ) where

import Control.Monad (forM_, when)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Data.ByteString.Lazy qualified as LBS
import System.Directory (createDirectoryIfMissing, doesDirectoryExist, listDirectory)
import System.FilePath ((</>), takeExtension)

import Language.Bluespec.DocGen.CSS (stylesheet)
import Language.Bluespec.DocGen.DocAST (dePackage)
import Language.Bluespec.DocGen.Extract (extractDocsFromFile)
import Language.Bluespec.DocGen.HTML
  (renderPackagePage, renderIndexPage, renderSitePage)
import Language.Bluespec.DocGen.SymbolIndex (buildIndex, renderIndexJson)

-- | Configuration for a documentation generation run.
data DocGenConfig = DocGenConfig
  { dgcLibDirs  :: ![FilePath]  -- ^ source directories to scan
  , dgcOutDir   :: !FilePath    -- ^ output directory
  , dgcVerbose  :: !Bool
  } deriving stock (Show)

-- | Sensible defaults: scan nothing, output to @docs/@.
defaultDocGenConfig :: DocGenConfig
defaultDocGenConfig = DocGenConfig
  { dgcLibDirs = []
  , dgcOutDir  = "docs"
  , dgcVerbose = False
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
  let outDir   = dgcOutDir cfg
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

  -- 8. Write site root
  TIO.writeFile (outDir </> "index.html") renderSitePage

  -- 9. Write stylesheet
  TIO.writeFile (outDir </> "docgen.css") stylesheet

  -- 10. Write symbol index JSON
  LBS.writeFile (outDir </> "symbol-index.json") (renderIndexJson idx)

  putStrLn $ "[docgen] Done. Output written to " ++ outDir ++ "/"
  putStrLn $ "[docgen] " ++ show (Map.size pkgMap) ++ " packages, "
          ++ show (length allEntries) ++ " documented symbols"

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
