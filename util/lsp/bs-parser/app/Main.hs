-- | CLI for the Bluespec parser.
module Main (main) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Encoding.Error as TEE
import qualified Data.Text.IO as TIO
import qualified Data.ByteString as BS
import Options.Applicative
import Prettyprinter
import Text.Megaparsec (errorBundlePretty)
import Prettyprinter.Render.Text ()
import System.Exit (exitFailure)
import System.FilePath (takeFileName)

import Language.Bluespec.Lexer (tokenize)
import Language.Bluespec.Layout (processLayout)
import Language.Bluespec.Parser hiding (Parser)
import Language.Bluespec.Pretty

--------------------------------------------------------------------------------
-- Command Line Options
--------------------------------------------------------------------------------

data Command
  = Parse FilePath
  | Pretty FilePath
  | Check FilePath
  | Lex FilePath
  | Layout FilePath
  deriving (Eq, Show)

data Options = Options
  { optCommand :: Command
  , optWidth   :: Int
  }
  deriving (Eq, Show)

parseOptions :: Parser Options
parseOptions = Options
  <$> subparser
      ( command "parse" (info (Parse <$> fileArg) (progDesc "Parse a file and show the AST"))
     <> command "pretty" (info (Pretty <$> fileArg) (progDesc "Parse and pretty-print a file"))
     <> command "check" (info (Check <$> fileArg) (progDesc "Parse a file and report any errors"))
     <> command "lex" (info (Lex <$> fileArg) (progDesc "Lex a file and show tokens"))
     <> command "layout" (info (Layout <$> fileArg) (progDesc "Show layout-processed tokens"))
      )
  <*> option auto
      ( long "width"
     <> short 'w'
     <> metavar "WIDTH"
     <> value 80
     <> help "Line width for pretty printing (default: 80)"
      )

fileArg :: Parser FilePath
fileArg = strArgument
  ( metavar "FILE"
 <> help "Bluespec source file (.bs)"
  )

opts :: ParserInfo Options
opts = info (parseOptions <**> helper)
  ( fullDesc
 <> progDesc "Parse and analyze Bluespec Classic (.bs) files"
 <> header "bs-parser - Bluespec Classic parser"
  )

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

-- | Read a file leniently: try UTF-8 first, fall back to Latin-1 decoding.
-- Bluespec source files are typically UTF-8, but some legacy files use Latin-1.
readFileLenient :: FilePath -> IO Text
readFileLenient path = do
  bytes <- BS.readFile path
  pure $ TE.decodeUtf8With TEE.lenientDecode bytes

main :: IO ()
main = do
  options <- execParser opts
  case optCommand options of
    Parse path -> runParse path
    Pretty path -> runPretty path (optWidth options)
    Check path -> runCheck path
    Lex path -> runLex path
    Layout path -> runLayout path

runParse :: FilePath -> IO ()
runParse path = do
  content <- readFileLenient path
  case parseAuto path content of
    Left err -> do
      putStrLn $ "Parse error in " ++ path ++ ":"
      putStrLn $ errorBundlePretty err
      exitFailure
    Right pkg -> do
      putStrLn $ "Successfully parsed: " ++ takeFileName path
      putStrLn ""
      putStrLn "AST:"
      print pkg

runPretty :: FilePath -> Int -> IO ()
runPretty path width = do
  content <- readFileLenient path
  case parseAuto path content of
    Left err -> do
      putStrLn $ "Parse error in " ++ path ++ ":"
      putStrLn $ errorBundlePretty err
      exitFailure
    Right pkg -> do
      let doc = prettyPackage pkg
      TIO.putStrLn $ renderPretty width doc

runCheck :: FilePath -> IO ()
runCheck path = do
  content <- readFileLenient path
  case parseAuto path content of
    Left err -> do
      putStrLn $ "Parse error in " ++ path ++ ":"
      putStrLn $ errorBundlePretty err
      exitFailure
    Right _ -> do
      putStrLn $ "OK: " ++ takeFileName path

runLex :: FilePath -> IO ()
runLex path = do
  content <- readFileLenient path
  case tokenize (T.pack path) content of
    Left err -> do
      putStrLn $ "Lexer error in " ++ path ++ ":"
      putStrLn err
      exitFailure
    Right tokens -> do
      putStrLn $ "Tokens from " ++ takeFileName path ++ ":"
      mapM_ print tokens

runLayout :: FilePath -> IO ()
runLayout path = do
  content <- readFileLenient path
  case tokenize (T.pack path) content of
    Left err -> do
      putStrLn $ "Lexer error in " ++ path ++ ":"
      putStrLn err
      exitFailure
    Right tokens -> do
      let processed = processLayout tokens
      putStrLn $ "Layout-processed tokens from " ++ takeFileName path ++ ":"
      mapM_ print processed
