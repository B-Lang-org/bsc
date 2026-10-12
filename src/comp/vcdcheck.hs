module Main_vcdcheck(main) where

import Version
import FileNameUtil(hasDotSuf, vcdSuffix)
import Position
import Error(EMsg, ErrMsg(..), showErrorList)
import Util(separate)
import WaveCheck
import IOUtil(getEnvDef)
import TopUtils(dfltBluespecDir)
import VCD

import System.Environment(getArgs)
import System.Console.GetOpt
import System.IO
import System.Exit
import Control.Exception(bracket)
import Control.Monad(when, msum)
import Data.List(partition)
import Data.Maybe(fromMaybe, isJust, fromJust)

import qualified Data.ByteString.Lazy.Char8 as C
import Text.Regex
import Numeric(readDec, readSigned)

-- import Debug.Trace

-- Version string (matches main BSC version numbering)
versionString :: String
versionString = versionStr True (bluespec ++ " vcdcheck utility")

-- -------------------------------------------------------------------
-- Option processing

-- Structure which holds all option settings
data Options = Options { optShowVersion  :: Bool
                       , optShowHelp     :: Bool
                       , optVCD1         :: Maybe FilePath
                       , optVCD2         :: Maybe FilePath
                       , optCheckStrings :: [String]
                       , optLimitString  :: String
                       , optCheckCmds    :: [CheckCmd]
                       , optLimit        :: Integer
                       }
  deriving (Show)

-- Default settings
defaultOptions :: Options
defaultOptions =
    Options { optShowVersion  = False
            , optShowHelp     = False
            , optVCD1         = Nothing
            , optVCD2         = Nothing
            , optCheckStrings = []
            , optLimitString  = ""
            , optCheckCmds    = []
            , optLimit        = 1000
            }

-- Description of command-line options
options :: [OptDescr (Options -> Options)]
options =
    [ Option ['V']      ["version"]
             (NoArg (\opts -> opts { optShowVersion = True }))
             "show version information and exit"
    , Option ['c']      ["check"]
             (ReqArg (\s opts -> opts { optCheckStrings = (optCheckStrings opts) ++ [s] }) "CHECK")
             "check the given assertion"
    , Option ['h','?']  ["help"]
             (NoArg (\opts -> opts { optShowHelp = True }))
             "print usage information and exit"
    , Option ['l']      ["limit"]
             (ReqArg (\s opts -> opts { optLimitString = s }) "LIMIT")
             "limit the number of errors displayed (default = 1000)"
    , Option ['q']      ["quiet"]
             (NoArg (\opts -> opts { optLimitString = "0" }))
             "do not print errors, only set exit status"
    ]

-- Header used in usage message
usage_header :: String
usage_header = "Usage: vcdcheck [OPTIONS] <VCD>\n" ++
               "       vcdcheck [OPTIONS] <VCD1> <VCD2>"

-- Parse the command line to produce the option structure, etc.
parseOpts :: [String] -> String -> (Options, [String], [EMsg])
parseOpts argv bluespecdir =
    let (opts,args0,errs) = getOpt Permute options argv
        options0 = foldl (flip id) defaultOptions opts
        (vcds,args1) = partition (hasDotSuf vcdSuffix) args0
        emsgs0 = map toEMsg errs
        (options1,emsgs1) = checkVCDs vcds (options0,emsgs0)
        emsgs2 = if (null args1)
                 then emsgs1
                 else emsgs1 ++
                      [(noPosition, EUnrecognizedCmdLineText (unwords args1))]
        (options2,emsgs3) =
            if (null (optLimitString options1))
            then (options1,emsgs2)
            else case (readSigned readDec (optLimitString options1)) of
                   [(n,"")] | n >= 0 -> (options1 { optLimit = n }, emsgs2)
                   otherwise         -> (options1, emsgs2 ++
                                                   [(noPosition, EBadArgFlag "--limit" (optLimitString options1) ["non-negative integers"])])
        (options3,emsgs4) = parseCheckCmds (options2, emsgs3)
    in (options3, [], emsgs4)
    where checkVCDs fs (os,es) =
              case fs of
                [vcd1]      -> (os { optVCD1 = Just vcd1 }, es)
                [vcd1,vcd2] -> (os { optVCD1 = Just vcd1, optVCD2 = Just vcd2 }, es)
                [] -> (os,es ++ [(noPosition, EGeneric "no VCD files given")])
                _ -> (os,es ++ [(noPosition, EGeneric "too many VCD files given")])
          parseCheckCmds (os,es) =
              let ss = optCheckStrings os
                  fnums = (if (isJust (optVCD1 os)) then [file1] else []) ++
                          (if (isJust (optVCD2 os)) then [file2] else [])
                  (bad,cmds) = separate (concatMap (parseCheckCmd fnums) ss)
                  errs = [ (noPosition, EGeneric ("invalid check command: " ++ s))
                         | s <- bad
                         ]
              in (os { optCheckCmds = cmds }, es ++ errs)

-- Produce a standard EMsg value from an option parser error string
toEMsg :: String -> EMsg
toEMsg s = fromMaybe (noPosition, EGeneric s) $
           msum [f s | f <- [ bad_option
                            , missing_arg
                            ]]
  where bad_option_regex = mkRegex "unrecognized option `(.*)'"
        bad_option x = do [opt] <- matchRegex bad_option_regex s
                          return (noPosition, EUnknownFlag opt)
        missing_arg_regex = mkRegex "option `(.*)' requires an argument .*"
        missing_arg x = do [opt] <- matchRegex missing_arg_regex s
                           return (noPosition, EOneArgFlag opt)

-- Validate command-line and process help requests
checkCmdLine :: Options -> [String] -> [EMsg] -> IO ()
checkCmdLine opts args errs =
  do when (optShowVersion opts) $
          do hPutStrLn stdout versionString
             hPutStrLn stdout copyright
     when (optShowHelp opts) $
          hPutStrLn stdout (usageInfo usage_header options)
     when ((optShowVersion opts) || (optShowHelp opts)) $
          exitWith ExitSuccess
     when (not (null errs)) $
          do hPutStr stderr (showErrorList errs)
             hPutStrLn stderr (usageInfo usage_header options)
             exitWith (ExitFailure 1)

-- -------------------------------------------------------------------
-- Main program routine

main :: IO ()
main = do -- parse command line arguments
          argv <- getArgs
          bluespecdir <- getEnvDef "BLUESPECDIR" dfltBluespecDir
          let (opts, args, emsgs) = parseOpts argv bluespecdir

          -- handle errors and/or request for help and version info
          checkCmdLine opts args emsgs

          ok <- if (isJust (optVCD2 opts))
                then compareTwoVCDs opts
                else checkOneVCD opts

          exitWith (if ok then ExitSuccess else (ExitFailure 2))

checkOneVCD :: Options -> IO Bool
checkOneVCD opts =
    do let vcd_in = fromJust (optVCD1 opts)
       bracket (openFile vcd_in ReadMode)
               (\hIn -> do { hClose hIn; return False })
               (\hIn -> do txt <- C.hGetContents hIn
                           let msgs = checkStream (optCheckCmds opts) vcd_in (parseVCD txt)
                           when (not (null msgs)) $ mapM_ putStrLn msgs
                           return (null msgs)
               )

compareTwoVCDs :: Options -> IO Bool
compareTwoVCDs opts =
    do putStrLn $ "Checking " ++ (fromJust (optVCD1 opts)) ++ " against " ++ (fromJust (optVCD2 opts))
       return True
