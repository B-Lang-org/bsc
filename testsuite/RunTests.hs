-- Cabal test driver for the (dejagnu) BSC testsuite.
--
-- cabal provides the freshly-built executables (via build-tool-depends); we
-- point the existing testsuite harness at them with TEST_BSC/TEST_BLUETCL/etc.
-- and let it run. BLUESPECDIR defaults (in the testsuite Makefile) to
-- ./inst/lib, the already-built runtime, so that must be present.
--
-- One driver, three test-suites, dispatched on the executable name:
--   smoke          a quick SystemC-free spread (front end, scheduler/SAT, both
--                  backends, a bluetcl query)
--   bluetcl-tests  the full bsc.bluetcl tree
--   utils          the dirs exercising the utility exes (showrules, vcdcheck,
--                  dumpbo)
--
-- The smoke set deliberately avoids the to_systemc tests: SystemC isn't a hard
-- dependency here, and those tests can't pass without it (use the Makefile's
-- 'make smoke' / 'releasecheck' if you have SystemC and want full coverage).
module Main (main) where

import Control.Monad (unless, when)
import Data.List (isInfixOf, sort)
import System.Directory (doesDirectoryExist, doesFileExist, findExecutable)
import System.Environment (getExecutablePath, getProgName)
import System.Exit (die, exitWith)
import System.FilePath (dropExtension, makeRelative, takeDirectory, (</>))
import System.Process (rawSystem, readProcess)

main :: IO ()
main = do
  name <- getProgName
  bsc  <- need "bsc"

  haveRuntime <- doesDirectoryExist "inst/lib"
  unless haveRuntime $
    die "inst/lib not found - build the runtime (the Makefile 'install') first."

  (targets, toolVars) <- plan name
  ec <- rawSystem "make"
          ( [ "-C", "testsuite", "TEST_BSC=" ++ bsc ] ++ toolVars ++ targets )
  exitWith ec

-- For a suite (matched by name), the make targets to run and the extra
-- TEST_<TOOL> make vars pointing the harness at the cabal-built tools it needs.
plan :: String -> IO ([String], [String])
plan name
  | "bluetcl" `isInfixOf` name = do
      bluetcl <- need "bluetcl"
      exps <- lines <$> readProcess "find" ["testsuite/bsc.bluetcl", "-name", "*.exp"] ""
      let ts = sort [ makeRelative "testsuite" (dropExtension e) ++ ".check"
                    | e <- exps, not (null e) ]
      when (null ts) (die "no bsc.bluetcl tests found")
      return (ts, ["TEST_BLUETCL=" ++ bluetcl])
  | "utils" `isInfixOf` name = do
      bluetcl   <- need "bluetcl"
      showrules <- need "showrules"
      vcdcheck  <- need "vcdcheck"
      dumpbo    <- need "dumpbo"
      return ( utilTargets
             , [ "TEST_BLUETCL="   ++ bluetcl
               , "TEST_SHOWRULES=" ++ showrules
               , "TEST_VCDCHECK="  ++ vcdcheck
               , "TEST_DUMPBO="    ++ dumpbo ] )
  | otherwise = do  -- smoke (includes a bluetcl query)
      bluetcl <- need "bluetcl"
      return (smokeTargets, ["TEST_BLUETCL=" ++ bluetcl])

-- A small SystemC-free spread: preprocessor (front end), FloatingPoint
-- (typecheck + codegen + both sims + RTS opts), schedule (scheduler/SAT) on
-- both backends, and a bluetcl query.
smokeTargets :: [String]
smokeTargets =
  [ "bsc.preprocessor/misc/misc.check"
  , "bsc.lib/FloatingPoint/FloatTest.check"
  , "bsc.bluesim/schedule/schedule.check"
  , "bsc.verilog/schedule/schedule.check"
  , "bsc.bluetcl/commands/commands.check"
  ]

-- Dirs that exercise the utility executables: showrules + vcdcheck (dedicated
-- dirs) and dumpbo (gensign / noinline). bsc2bsv's only test is gated behind
-- do_internal_checks (off by default), and bsv2bsc/dumpba have no tests.
utilTargets :: [String]
utilTargets =
  [ "bsc.showrules/showrules.check"
  , "bsc.vcdcheck/vcdcheck.check"
  , "bsc.driver/gensign/gensign.check"
  , "bsc.verilog/noinline/noinline.check"
  ]

-- Locate a sibling cabal executable. build-tool-depends guarantees it's been
-- built, but only adds it to PATH at build time, not test-run time -- so fall
-- back to the dist-newstyle layout (build/<comp>/<comp>) relative to this test
-- binary, then finally PATH (for an installed tool).
need :: String -> IO FilePath
need exe = do
  self <- getExecutablePath
  let sibling = takeDirectory (takeDirectory self) </> exe </> exe
  here <- doesFileExist sibling
  if here
    then return sibling
    else findExecutable exe >>=
           maybe (die ("cannot find " ++ exe ++ " (looked at " ++ sibling
                       ++ " and on PATH)")) return
