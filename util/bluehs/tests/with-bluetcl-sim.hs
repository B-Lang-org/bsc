-- Supply the .so built from SessionModel.bs as the sole argument.
module Main (main) where

import Bluetcl (evalBluetcl, withBluetcl)
import Control.Exception (SomeException, displayException, throwIO, try)
import Control.Monad (unless, void)
import Data.List (isInfixOf)
import System.Environment (getArgs)

expectFailure :: String -> IO a -> IO ()
expectFailure message action = do
    result <- try (void action) :: IO (Either SomeException ())
    case result of
        Left err -> unless (message `isInfixOf` displayException err) $
            ioError (userError ("wrong exception: " ++ displayException err))
        Right () -> ioError (userError "expected failure")

main :: IO ()
main = do
    args <- getArgs
    model <- case args of
        [path] -> pure path
        _ -> ioError (userError "usage: with-bluetcl-sim.hs model.so")
    -- Braced Tcl paths keep the fixture usable from a directory with spaces.
    let load = "Bluetcl::sim load {" ++ model ++ "} mkSessionModel"
        noModel interp = expectFailure "There is no bluesim model loaded" $
            evalBluetcl interp "Bluetcl::sim time"
        loaded interp = do
            time <- evalBluetcl interp "Bluetcl::sim time"
            unless (time == "0") $ ioError (userError ("unexpected time: " ++ time))
    withBluetcl $ \interp -> do
        void $ evalBluetcl interp load
        loaded interp
        -- An embedded exit leaves the session, its model and its hooks alone.
        expectFailure "exit is unavailable" $ evalBluetcl interp "exit"
        loaded interp
        expectFailure ".missing" $ evalBluetcl interp
            ("Bluetcl::sim load {" ++ model ++ ".missing} mkSessionModel")
        noModel interp
        expectFailure "noSuchTop" $ evalBluetcl interp
            ("Bluetcl::sim load {" ++ model ++ "} noSuchTop")
        noModel interp
        void $ evalBluetcl interp load
        loaded interp
        void $ evalBluetcl interp "Bluetcl::sim unload"
        noModel interp
        void $ evalBluetcl interp load
        void $ evalBluetcl interp "Bluetcl::sim step 1000000000 async"
    withBluetcl $ \interp -> do
        noModel interp
        void $ evalBluetcl interp load
        loaded interp
    expectFailure "with-bluetcl-sim-exception" $ withBluetcl $ \interp -> do
        void $ evalBluetcl interp load
        throwIO (userError "with-bluetcl-sim-exception")
    withBluetcl $ \interp -> do
        noModel interp
        void $ evalBluetcl interp load
        loaded interp
    putStrLn "withBluetcl: simulator lifecycle checks passed"
