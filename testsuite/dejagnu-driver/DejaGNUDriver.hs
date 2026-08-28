module DejaGNUDriver (tests) where

import Distribution.TestSuite
import Distribution.Simple.Utils (findFileWithExtension)
import System.Directory
import System.FilePath
import System.Exit
import Control.Monad
import DejaGNUTest

main :: IO ()
main = do
  -- Get test configuration from environment
  config <- configFromEnv
  
  -- Get the test directory (should be the testsuite directory)
  currentDir <- getCurrentDirectory
  let testDir = takeDirectory currentDir

  -- Run the tests
  exitCode <- runDejaGNUTests config testDir
  
  case exitCode of
    ExitSuccess -> putStrLn "All DejaGNU tests passed!"
    ExitFailure n -> do
      putStrLn $ "DejaGNU tests failed with exit code: " ++ show n
      exitWith exitCode 

tests :: IO [Test]
tests = do
  config <- configFromEnv
  currentDir <- getCurrentDirectory
  let testDir = takeDirectory currentDir
  return [Test $ TestInstance
    { run = do
        exitCode <- runDejaGNUTests config testDir
        case exitCode of
          ExitSuccess -> return $ Finished Pass
          ExitFailure n -> return $ Finished $ Fail $ "Tests failed with exit code: " ++ show n
    , name = "dejagnu"
    , tags = []
    , options = []
    , setOption = \_ _ -> Right $ error "no options supported"
    }] 