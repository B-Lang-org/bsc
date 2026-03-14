-- | @bs-docgen@ — documentation generator for Bluespec source files.
module Main (main) where

import Control.Monad (forM_, when)
import Data.List (sortOn)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Data.ByteString.Lazy qualified as LBS
import Options.Applicative
import System.Directory (createDirectoryIfMissing, doesDirectoryExist, listDirectory)
import System.FilePath ((</>), takeExtension, takeBaseName)

import Language.Bluespec.DocGen.CSS (stylesheet)
import Language.Bluespec.DocGen.DocAST (dePackage)
import Language.Bluespec.DocGen.Extract (extractDocsFromFile)
import Language.Bluespec.DocGen.HTML
  (renderPackagePage, renderIndexPage, renderSitePage)
import Language.Bluespec.DocGen.SymbolIndex (buildIndex, renderIndexJson)

-- ---------------------------------------------------------------------------
-- CLI
-- ---------------------------------------------------------------------------

data Opts = Opts
  { optLibDir :: ![FilePath]   -- ^ directories containing .bs/.bsv sources
  , optOut    :: !FilePath     -- ^ output directory
  , optVerbose :: !Bool
  } deriving stock (Show)

optsParser :: Parser Opts
optsParser = Opts
  <$> many (strOption (long "lib-dir" <> short 'l' <> metavar "DIR"
        <> help "Source directory to scan (can be given multiple times)"))
  <*> strOption (long "out" <> short 'o' <> metavar "DIR"
        <> value "docs" <> showDefault
        <> help "Output directory")
  <*> switch (long "verbose" <> short 'v' <> help "Verbose output")

-- ---------------------------------------------------------------------------
-- Main
-- ---------------------------------------------------------------------------

main :: IO ()
main = do
  opts <- execParser (info (optsParser <**> helper)
    (fullDesc <> progDesc "bs-docgen — Haddock for Bluespec"
              <> header "bs-docgen — generate HTML docs from Bluespec source"))
  runDocGen opts

runDocGen :: Opts -> IO ()
runDocGen opts = do
  -- 1. Collect source files
  srcFiles <- fmap concat $ mapM collectSources (optLibDir opts)
  when (optVerbose opts) $
    putStrLn $ "[docgen] Found " ++ show (length srcFiles) ++ " source files"

  -- 2. Extract documentation entries
  allEntries <- fmap concat $ mapM extractDocsFromFile srcFiles
  when (optVerbose opts) $
    putStrLn $ "[docgen] Extracted " ++ show (length allEntries) ++ " doc entries"

  -- 3. Build symbol index
  let idx = buildIndex allEntries

  -- 4. Group by package
  let pkgMap = foldr (\e m -> Map.insertWith (++) (dePackage e) [e] m)
                     Map.empty allEntries

  -- 5. Create output directories
  let outDir   = optOut opts
      stdlibDir = outDir </> "stdlib"
  createDirectoryIfMissing True stdlibDir

  -- 6. Write per-package pages
  forM_ (Map.toAscList pkgMap) $ \(pkg, entries) -> do
    let html = renderPackagePage pkg entries idx
        path = stdlibDir </> T.unpack pkg ++ ".html"
    TIO.writeFile path html
    when (optVerbose opts) $
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
