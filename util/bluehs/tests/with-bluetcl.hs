-- Run against the compiled bsc package, from the source or relocated launcher.
-- This file is also loadable in GHCi; all source text is ASCII.
module Main (main) where

import Bluetcl (BluetclInterp, evalBluetcl, withBluetcl)
import Control.Concurrent
    (forkFinally, forkIO, isCurrentThreadBound, killThread, newEmptyMVar, putMVar,
     rtsSupportsBoundThreads, takeMVar, threadDelay)
import Control.Exception (SomeException, bracket, displayException, throwIO, try)
import Control.Monad (forever, replicateM_, unless, void, when)
import Data.List (isInfixOf)
import System.Environment (withArgs)
import System.Mem (performMinorGC)
import System.Timeout (timeout)

require :: String -> Bool -> IO ()
require label ok = unless ok (ioError (userError label))

expectResult :: BluetclInterp -> String -> String -> IO ()
expectResult interp script expected = do
    actual <- evalBluetcl interp script
    require ("unexpected Tcl result for " ++ show script ++ ": " ++ show actual)
        (actual == expected)

tryAny :: IO a -> IO (Either SomeException a)
tryAny = try

-- Catch outside timeout: catching its exception inside would mistake a
-- deadlock for the expected rejection.
expectFailure :: String -> String -> IO a -> IO ()
expectFailure label message action = do
    result <- tryAny (timeout 5000000 action)
    case result of
        Left err -> require (label ++ ": wrong exception: " ++ displayException err)
            (message `isInfixOf` displayException err)
        Right Nothing -> ioError (userError (label ++ ": timed out instead of rejecting"))
        Right (Just _) -> ioError (userError (label ++ ": unexpectedly succeeded"))

onOtherThread :: IO a -> IO a
onOtherThread action = do
    result <- newEmptyMVar
    bracket (forkFinally action (putMVar result)) killThread $ \_ ->
        takeMVar result >>= either throwIO pure

snapshot :: BluetclInterp -> IO (String, String)
snapshot interp = do
    packages <- evalBluetcl interp "Bluetcl::bpackage list"
    flags <- evalBluetcl interp "Bluetcl::flags show"
    pure (packages, flags)

checkFresh :: BluetclInterp -> (String, String) -> IO ()
checkFresh interp expected = do
    actual <- snapshot interp
    require "package or flag state leaked between sessions" (actual == expected)
    expectResult interp "info exists ::withBluetclProbe" "0"

main :: IO ()
main = withArgs ["with-bluetcl-host-argv-probe"] $ do
    (escaped, initial) <- withBluetcl $ \interp -> do
        bound <- isCurrentThreadBound
        require "withBluetcl callback is not on a bound thread" (bound || not rtsSupportsBoundThreads)
        version <- evalBluetcl interp "Bluetcl::version bsc"
        require "Bluetcl::version bsc returned no version" (not (null version))
        expectResult interp
            "expr {[llength [info procs ::Bluetcl::initBluespec]] == 1}" "1"
        expectResult interp
            "expr {![info exists ::argv] || [llength $::argv] == 0}" "1"
        initial <- snapshot interp
        require "a fresh session already has loaded packages" (null (fst initial))
        void $ evalBluetcl interp "Bluetcl::bpackage load Prelude"
        expectResult interp
            "expr {[lsearch -exact [Bluetcl::bpackage list] Prelude] >= 0}" "1"
        expectResult interp "expr {[llength [Bluetcl::bpackage types Prelude]] > 0}" "1"
        void $ evalBluetcl interp "Bluetcl::flags set -verbose"
        flags <- evalBluetcl interp "Bluetcl::flags show"
        when (flags == snd initial) $
            void $ evalBluetcl interp "Bluetcl::flags set -no-verbose"
        changed <- snapshot interp
        require "flag mutation did not exercise session state" (snd changed /= snd initial)
        void $ evalBluetcl interp "set ::withBluetclProbe stale"

        let text = "A\NUL\x03bb\x6f22\x1f642\&Z"
        expectResult interp ("set ::roundTrip {" ++ text ++ "}") text
        expectFailure "Tcl error" "with-bluetcl-tcl-error" $
            evalBluetcl interp "error {with-bluetcl-tcl-error}"
        expectFailure "nested session" "another session is already active" $ withBluetcl $ \_ -> pure ()
        expectFailure "overlapping session" "another session is already active" $
            onOtherThread (withBluetcl (\_ -> pure ()))
        expectFailure "evaluation on another thread" "on its callback thread" $
            onOtherThread (evalBluetcl interp "expr {6 * 7}")
        expectFailure "embedded exit" "exit is unavailable inside withBluetcl" $ evalBluetcl interp "exit 17"
        expectResult interp "namespace exists ::AtExit" "1"
        expectResult interp "expr {6 * 7}" "42"
        pure (interp, initial)

    expectFailure "escaped interpreter" "current withBluetcl interpreter" $ evalBluetcl escaped "expr {6 * 7}"
    withBluetcl $ \interp -> do
        checkFresh interp initial
        expectFailure "escaped interpreter during a later session" "current withBluetcl interpreter" $
            evalBluetcl escaped "expr {6 * 7}"
        expectResult interp "expr {6 * 7}" "42"
        -- A normal return reports an error from the exit-hook cleanup, so a
        -- collision of its temporaries with user variables would show here.
        void $ evalBluetcl interp "array set scripts {x y}; array set script {x y}"

    expectFailure "callback exception" "with-bluetcl-action-error" $
        withBluetcl $ \interp -> do
            void $ evalBluetcl interp "Bluetcl::bpackage load Prelude"
            void $ evalBluetcl interp "set ::withBluetclProbe stale"
            throwIO (userError "with-bluetcl-action-error")
    -- A timeout that never reached the session would hang it, so a watchdog
    -- turns that into a failure.
    interrupted <- newEmptyMVar
    _ <- forkIO $ timeout 200000
        (withBluetcl $ \interp -> forever (evalBluetcl interp "expr 1") :: IO ())
        >>= putMVar interrupted
    outcome <- timeout 10000000 (takeMVar interrupted)
    require "timeout did not interrupt the session" (outcome == Just Nothing)
    -- Tcl objects Haskell drops are released while another thread collects.
    collector <- forkIO (forever (performMinorGC >> threadDelay 20))
    withBluetcl $ \interp -> replicateM_ 20 $ do
        replicateM_ 1000 (evalBluetcl interp "Bluetcl::version bsc")
        evalBluetcl interp "for {set k 0} {$k < 2000} {incr k} {Bluetcl::version bsc}"
    killThread collector
    withBluetcl $ \interp -> do
        checkFresh interp initial
        expectResult interp "expr {6 * 7}" "42"
    putStrLn "withBluetcl: all checks passed"
