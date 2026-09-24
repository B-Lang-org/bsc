module Main_fstcheck(main) where

-- Check assertions against an FST waveform file, with the same
-- checks and behavior as vcdcheck has for VCD files: the FST is read
-- into the VCD command representation (FSTRead) and the checks run
-- on the shared engine (WaveCheck).

import Version
import FileNameUtil(hasDotSuf)
import Position
import Error(EMsg, ErrMsg(..), showErrorList)
import Util(separate)
import WaveCheck
import FSTRead(readFST)
import IOUtil(getEnvDef)
import TopUtils(dfltBluespecDir)

import System.Environment(getArgs)
import System.Console.GetOpt
import System.IO
import System.Exit
import Control.Monad(when, msum)
import Data.List(partition)
import Data.Maybe(fromMaybe, isJust, fromJust)
import Text.Regex
import Numeric(readDec, readSigned)

-- Version string (matches main BSC version numbering)
versionString :: String
versionString = versionStr True (bluespec ++ " fstcheck utility")

fstSuffix :: String
fstSuffix = "fst"

-- -------------------------------------------------------------------
-- Option processing

-- Structure which holds all option settings
data Options = Options { optShowVersion  :: Bool
                       , optShowHelp     :: Bool
                       , optFST          :: Maybe FilePath
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
            , optFST          = Nothing
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
usage_header = "Usage: fstcheck [OPTIONS] <FST>"

-- Parse the command line to produce the option structure, etc.
parseOpts :: [String] -> String -> (Options, [String], [EMsg])
parseOpts argv _bluespecdir =
    let (opts,args0,errs) = getOpt Permute options argv
        options0 = foldl (flip id) defaultOptions opts
        (fsts,args1) = partition (hasDotSuf fstSuffix) args0
        emsgs0 = map toEMsg errs
        (options1,emsgs1) = checkFSTs fsts (options0,emsgs0)
        emsgs2 = if (null args1)
                 then emsgs1
                 else emsgs1 ++
                      [(noPosition, EUnrecognizedCmdLineText (unwords args1))]
        (options2,emsgs3) =
            if (null (optLimitString options1))
            then (options1,emsgs2)
            else case (readSigned readDec (optLimitString options1)) of
                   [(n,"")] | n >= 0 -> (options1 { optLimit = n }, emsgs2)
                   _                 -> (options1, emsgs2 ++
                                                   [(noPosition, EBadArgFlag "--limit" (optLimitString options1) ["non-negative integers"])])
        (options3,emsgs4) = parseCheckCmds (options2, emsgs3)
    in (options3, [], emsgs4)
    where checkFSTs fs (os,es) =
              case fs of
                [fst1] -> (os { optFST = Just fst1 }, es)
                []     -> (os,es ++ [(noPosition, EGeneric "no FST file given")])
                _      -> (os,es ++ [(noPosition, EGeneric "too many FST files given")])
          parseCheckCmds (os,es) =
              let ss = optCheckStrings os
                  fnums = if (isJust (optFST os)) then [file1] else []
                  (bad,cmds) = separate (concatMap (parseCheckCmd fnums) ss)
                  errs2 = [ (noPosition, EGeneric ("invalid check command: " ++ s))
                          | s <- bad
                          ]
              in (os { optCheckCmds = cmds }, es ++ errs2)

-- Produce a standard EMsg value from an option parser error string
toEMsg :: String -> EMsg
toEMsg s = fromMaybe (noPosition, EGeneric s) $
           msum [f s | f <- [ bad_option
                            , missing_arg
                            ]]
  where bad_option_regex = mkRegex "unrecognized option `(.*)'"
        bad_option _ = do [opt] <- matchRegex bad_option_regex s
                          return (noPosition, EUnknownFlag opt)
        missing_arg_regex = mkRegex "option `(.*)' requires an argument .*"
        missing_arg _ = do [opt] <- matchRegex missing_arg_regex s
                           return (noPosition, EOneArgFlag opt)

-- Validate command-line and process help requests
checkCmdLine :: Options -> [String] -> [EMsg] -> IO ()
checkCmdLine opts _args errs =
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

          ok <- checkOneFST opts

          exitWith (if ok then ExitSuccess else (ExitFailure 2))

checkOneFST :: Options -> IO Bool
checkOneFST opts =
    do let fst_in = fromJust (optFST opts)
       mstream <- readFST fst_in
       case mstream of
         Nothing -> do hPutStrLn stderr ("cannot open '" ++ fst_in ++ "'")
                       return False
         Just stream ->
             do let msgs = checkStream (optCheckCmds opts) fst_in stream
                when (not (null msgs)) $ mapM_ putStrLn msgs
                return (null msgs)
