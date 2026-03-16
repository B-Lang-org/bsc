-- | @bbt new@ — scaffold a new Bluespec project.
module Language.Bluespec.BBT.New
  ( NewOpts (..)
  , BscLang (..)
  , runNew
  ) where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.Directory (createDirectoryIfMissing, doesDirectoryExist)
import System.Exit (exitFailure)
import System.FilePath ((</>))
import System.IO (hPutStrLn, stderr)

-- | Language variant for the generated project.
data BscLang = LangBS | LangBSV
  deriving stock (Show, Eq)

-- | Options for @bbt new@.
data NewOpts = NewOpts
  { noLang :: !BscLang
  , noName :: !Text
  } deriving stock (Show)

-- | Create a new scaffolded project in a new directory @noName@.
runNew :: NewOpts -> IO ()
runNew opts = do
  let name  = noName opts
      lang  = noLang opts
      dir   = T.unpack name
      srcDir = dir </> "src"

  -- Check the target directory doesn't already exist
  exists <- doesDirectoryExist dir
  if exists
    then do
      hPutStrLn stderr ("[bbt] Error: directory '" ++ dir ++ "' already exists")
      exitFailure
    else do
      createDirectoryIfMissing True srcDir

      -- Write bsc.toml
      TIO.writeFile (dir </> "bsc.toml") (toml name lang)

      -- Write top-level source file
      let (topFile, topSrc) = topSource name lang
      TIO.writeFile (srcDir </> topFile) topSrc

      -- Write .gitignore
      TIO.writeFile (dir </> ".gitignore") gitignore

      putStrLn $ "[bbt] Created project '" ++ T.unpack name ++ "'"
      putStrLn $ "[bbt]   " ++ dir </> "bsc.toml"
      putStrLn $ "[bbt]   " ++ srcDir </> topFile
      putStrLn $ "[bbt] Run: cd " ++ dir ++ " && bbt sim"

-- ---------------------------------------------------------------------------
-- File content generators
-- ---------------------------------------------------------------------------

toml :: Text -> BscLang -> Text
toml name lang = T.unlines
  [ "[package]"
  , "name    = \"" <> name <> "\""
  , "version = \"0.1.0\""
  , ""
  , "[build]"
  , "top_file   = \"src/" <> topModuleName lang <> langExt lang <> "\""
  , "top_module = \"mkTop\""
  , "src        = \"src\""
  , ""
  , "[target.default]"
  , "build_dir   = \"build/bdir\""
  , "sim_dir     = \"build/sim\""
  , "verilog_dir = \"build/verilog\""
  ]

topSource :: Text -> BscLang -> (FilePath, Text)
topSource _name LangBSV = ("Top.bsv", bsvSource)
topSource _name LangBS  = ("Top.bs",  bsSource)

topModuleName :: BscLang -> Text
topModuleName LangBSV = "Top"
topModuleName LangBS  = "Top"

langExt :: BscLang -> Text
langExt LangBSV = ".bsv"
langExt LangBS  = ".bs"

-- | A minimal BSV hello-world + counter-to-5 module.
bsvSource :: Text
bsvSource = T.unlines
  [ "package Top;"
  , ""
  , "(* synthesize *)"
  , "module mkTop(Empty);"
  , "    Reg#(UInt#(32)) counter <- mkReg(0);"
  , ""
  , "    rule run;"
  , "        $display(\"Hello, World! cycle = %0d\", counter);"
  , "        counter <= counter + 1;"
  , "        if (counter == 4) $finish(0);"
  , "    endrule"
  , "endmodule"
  , ""
  , "endpackage"
  ]

-- | A minimal Classic (BH) hello-world + counter-to-5 module.
bsSource :: Text
bsSource = T.unlines
  [ "package Top where"
  , ""
  , "{-# verilog mkTop #-}"
  , "mkTop :: Module Empty"
  , "mkTop = module"
  , "  counter :: Reg (UInt 32) <- mkReg 0"
  , "  rules"
  , "    \"run\" : when True ==>"
  , "      do"
  , "        $display \"Hello, World! cycle = %0d\" counter"
  , "        counter := counter + 1"
  , "        if counter == 4 then $finish 0 else action {}"
  ]

gitignore :: Text
gitignore = T.unlines
  [ "build/"
  , "docs/"
  , "*.bo"
  , "*.ba"
  ]
