{-# LANGUAGE ForeignFunctionInterface #-}

-- Launcher for bluetcl. The Haskell RTS is started by the normal hs-main, then
-- we hand control to Tcl via a small C shim (bluetcl_shim.c) that runs Tcl_Main
-- and registers the Bluespec commands exported from BlueTcl. (The Makefile build
-- instead uses a C main + -no-hs-main + htcl_initHaskellRTS; doing it from a
-- Haskell main lets cabal build this as an ordinary executable.)
module Main (main) where

import BlueTcl () -- force the blueshell_Init_Foreign export to be linked in
import Foreign.C.String (CString, newCString)
import Foreign.C.Types (CInt (..))
import Foreign.Marshal.Array (newArray0)
import Foreign.Ptr (Ptr, nullPtr)
import System.Environment (getArgs, getProgName)
import TopUtils (getBluespecDir)
import Data.Functor (void)

foreign import ccall "run_bluetcl"
  c_run_bluetcl :: CInt -> Ptr CString -> IO ()

main :: IO ()
main = do
  -- The Tcl side reads $BLUESPECDIR, so call getBluespecDir for its setenv side
  -- effect.
  void getBluespecDir
  prog <- getProgName
  args <- getArgs
  let argList = prog : args
  cArgs <- mapM newCString argList
  argv <- newArray0 nullPtr cArgs
  c_run_bluetcl (fromIntegral (length argList)) argv
