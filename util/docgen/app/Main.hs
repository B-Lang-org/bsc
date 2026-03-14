-- | @bs-docgen@ — documentation generator for Bluespec source files.
module Main (main) where

import Options.Applicative

import Language.Bluespec.DocGen.Generate (DocGenConfig (..), runDocGen)

-- ---------------------------------------------------------------------------
-- CLI
-- ---------------------------------------------------------------------------

optsParser :: Parser DocGenConfig
optsParser = DocGenConfig
  <$> many (strOption (long "lib-dir" <> short 'l' <> metavar "DIR"
        <> help "Source directory to scan (can be given multiple times)"))
  <*> strOption (long "out" <> short 'o' <> metavar "DIR"
        <> value "docs" <> showDefault
        <> help "Output directory")
  <*> optional (strOption (long "ref-manual" <> short 'r' <> metavar "FILE"
        <> help "Path to BH_lang.tex to convert to HTML reference manual"))
  <*> optional (strOption (long "stdlib-url" <> metavar "URL"
        <> help "External URL for stdlib cross-links (e.g. https://bsc-docs.example.com/stdlib/)"))
  <*> switch (long "verbose" <> short 'v' <> help "Verbose output")

-- ---------------------------------------------------------------------------
-- Main
-- ---------------------------------------------------------------------------

main :: IO ()
main = do
  cfg <- execParser (info (optsParser <**> helper)
    (fullDesc <> progDesc "bs-docgen — Haddock for Bluespec"
              <> header "bs-docgen — generate HTML docs from Bluespec source"))
  runDocGen cfg
