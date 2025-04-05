import Distribution.Make
import Distribution.Simple.Utils (die)
import Distribution.Verbosity (normal)
import System.Directory (doesDirectoryExist, getCurrentDirectory)
import System.FilePath ((</>))

main :: IO ()
main = defaultMainWithHooks $ simpleUserHooks
  { buildHook = \pkg lbi hooks flags -> do
      -- Check for required tools and dependencies
      checkDependencies
      
      -- Build external dependencies
      buildExternalDeps
      
      -- Build main components
      buildMainComponents
      
      -- Call the default build hook for Haskell components
      buildHook simpleUserHooks pkg lbi hooks flags
  }

checkDependencies :: IO ()
checkDependencies = do
  -- Check for required tools
  checkTool "ghc"
  checkTool "ghc-pkg"
  checkTool "gperf"
  checkTool "autoconf"
  checkTool "flex"
  checkTool "bison"
  
  -- Check for required Haskell packages
  checkHaskellPkg "regex-compat"
  checkHaskellPkg "syb"
  checkHaskellPkg "old-time"
  checkHaskellPkg "split"
  
  -- Check for submodules
  checkSubmodule "vendor/yices/v2.6/yices2"

checkTool :: String -> IO ()
checkTool tool = do
  path <- lookupEnv "PATH"
  case path of
    Nothing -> die "Could not find PATH environment variable"
    Just p -> do
      let paths = splitOn ":" p
      exists <- anyM (doesFileExist . (</> tool)) paths
      unless exists $ die $ "Required tool " ++ tool ++ " not found in PATH"

checkHaskellPkg :: String -> IO ()
checkHaskellPkg pkg = do
  result <- readProcess "ghc-pkg" ["list", "--simple-output", pkg] ""
  when (null result) $ die $ "Required Haskell package " ++ pkg ++ " not installed"

checkSubmodule :: FilePath -> IO ()
checkSubmodule path = do
  exists <- doesDirectoryExist path
  unless exists $ do
    inGit <- isGitRepo
    if inGit
      then die $ "Submodule " ++ path ++ " missing. Initialize with:\n    git submodule update --init --recursive"
      else die $ "Submodule " ++ path ++ " missing.\nThis archive was exported from Git without the source files for submodules."

isGitRepo :: IO Bool
isGitRepo = do
  result <- try $ readProcess "git" ["rev-parse", "--is-inside-work-tree"] ""
  return $ either (const False) (const True) result

buildExternalDeps :: IO ()
buildExternalDeps = do
  -- Build STP
  buildInDir "vendor/stp"
  
  -- Build Yices
  buildInDir "vendor/yices"
  
  -- Build HTCL
  buildInDir "vendor/htcl"

buildMainComponents :: IO ()
buildMainComponents = do
  -- Build components in order
  buildInDir "comp"
  buildInDir "Libraries"
  buildInDir "exec"
  buildInDir "VPI"
  buildInDir "Verilog"
  buildInDir "Verilog.Quartus"
  buildInDir "Verilog.Vivado"
  buildInDir "bluetcl"
  buildInDir "bluesim"
  buildInDir "Verilator"

buildInDir :: FilePath -> IO ()
buildInDir dir = do
  cwd <- getCurrentDirectory
  let fullPath = cwd </> dir
  exists <- doesDirectoryExist fullPath
  when exists $ do
    setCurrentDirectory fullPath
    system "make"
    setCurrentDirectory cwd

-- Utility functions
anyM :: (a -> IO Bool) -> [a] -> IO Bool
anyM _ [] = return False
anyM p (x:xs) = do
  b <- p x
  if b then return True else anyM p xs

splitOn :: Char -> String -> [String]
splitOn _ [] = []
splitOn c s = case break (== c) s of
  (chunk, []) -> [chunk]
  (chunk, _:rest) -> chunk : splitOn c rest