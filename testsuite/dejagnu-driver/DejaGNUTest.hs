module DejaGNUTest where

import System.Process
import System.Directory
import System.FilePath
import System.Exit
import System.Environment
import Control.Monad
import qualified Data.Text as T
import qualified Data.Text.IO as T

data DejaGNUConfig = DejaGNUConfig
  { testRelease :: FilePath      -- ^ Path to BSC installation
  , verilogSim :: String        -- ^ Verilog simulator to use
  , enableCTest :: Bool         -- ^ Whether to run Bluesim tests
  , enableVTest :: Bool         -- ^ Whether to run Verilog tests
  , enableSystemC :: Bool       -- ^ Whether to run SystemC tests
  , bscOptions :: [String]      -- ^ Additional BSC options
  , systemCInc :: Maybe String  -- ^ SystemC include path
  , systemCLib :: Maybe String  -- ^ SystemC library path
  }

defaultConfig :: DejaGNUConfig
defaultConfig = DejaGNUConfig
  { testRelease = "../inst"
  , verilogSim = "iverilog"
  , enableCTest = True
  , enableVTest = True
  , enableSystemC = True
  , bscOptions = []
  , systemCInc = Nothing
  , systemCLib = Nothing
  }

-- | Run DejaGNU tests with the given configuration
runDejaGNUTests :: DejaGNUConfig -> FilePath -> IO ExitCode
runDejaGNUTests config testDir = do
  -- Set up environment variables
  let env = [ ("TEST_RELEASE", testRelease config)
            , ("TEST_BSC_VERILOG_SIM", verilogSim config)
            , ("CTEST", if enableCTest config then "1" else "0")
            , ("VTEST", if enableVTest config then "1" else "0")
            , ("SYSTEMCTEST", if enableSystemC config then "1" else "0")
            , ("TEST_BSC_OPTIONS", unwords $ bscOptions config)
            ] ++
            maybe [] (\inc -> [("TEST_SYSTEMC_INC", inc)]) (systemCInc config) ++
            maybe [] (\lib -> [("TEST_SYSTEMC_LIB", lib)]) (systemCLib config)

  -- Create site.exp if it doesn't exist
  let siteExp = testDir </> "site.exp"
  siteExpExists <- doesFileExist siteExp
  unless siteExpExists $
    writeFile siteExp "set tool bsc\n"

  -- Run dejagnu
  (exitCode, stdout, stderr) <- readProcessWithExitCode "runtest" 
                               ["--tool", "bsc", "--srcdir", testDir] ""

  -- Print output
  putStr stdout
  putStr stderr

  return exitCode

-- | Parse environment variables to create DejaGNUConfig
configFromEnv :: IO DejaGNUConfig
configFromEnv = do
  testRelease' <- lookupEnvDef "TEST_RELEASE" (testRelease defaultConfig)
  verilogSim' <- lookupEnvDef "TEST_BSC_VERILOG_SIM" (verilogSim defaultConfig)
  enableCTest' <- lookupEnvBool "CTEST" (enableCTest defaultConfig)
  enableVTest' <- lookupEnvBool "VTEST" (enableVTest defaultConfig)
  enableSystemC' <- lookupEnvBool "SYSTEMCTEST" (enableSystemC defaultConfig)
  bscOptions' <- words <$> lookupEnvDef "TEST_BSC_OPTIONS" ""
  systemCInc' <- lookupEnv "TEST_SYSTEMC_INC"
  systemCLib' <- lookupEnv "TEST_SYSTEMC_LIB"
  
  return defaultConfig
    { testRelease = testRelease'
    , verilogSim = verilogSim'
    , enableCTest = enableCTest'
    , enableVTest = enableVTest'
    , enableSystemC = enableSystemC'
    , bscOptions = bscOptions'
    , systemCInc = systemCInc'
    , systemCLib = systemCLib'
    }
  where
    lookupEnvDef name def = maybe def id <$> lookupEnv name
    lookupEnvBool name def = maybe def (\v -> v /= "0") <$> lookupEnv name 