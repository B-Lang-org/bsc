{-# LANGUAGE ForeignFunctionInterface #-}
module Main_bluetcl (main) where

import Bluetcl (initBluetcl)
import HTcl (TclInterp, htcl_AddObjErrorInfo)
import Control.Concurrent
import Control.Monad (void)
import qualified Control.Exception as CE
import Foreign.C.String (CString, newCString)
import Foreign.C.Types (CInt(..))
import Foreign.Marshal.Array (newArray0)
import Foreign.Ptr (Ptr, nullPtr)
import System.Environment (getArgs, getProgName)
import System.IO.Error (ioeGetErrorString)
import System.Posix.Signals
import TopUtils (getBluespecDir)

foreign import ccall "run_bluetcl"
  c_run_bluetcl :: CInt -> Ptr CString -> IO ()

main :: IO ()
main = do
  -- The Tcl startup code reads BLUESPECDIR.
  void getBluespecDir
  prog <- getProgName
  args <- getArgs
  let argList = prog : args
  cArgs <- mapM newCString argList
  argv <- newArray0 nullPtr cArgs
  c_run_bluetcl (fromIntegral (length argList)) argv

foreign export ccall "blueshell_Init_Foreign"
  blueshell_Init :: TclInterp -> IO Int

blueshell_Init :: TclInterp -> IO Int
blueshell_Init interp = CE.catch initialize handler
  where
    initialize = do
      initBluetcl interp
      mv <- newEmptyMVar
      _ <- forkIO (handleCtrlC mv)
      _ <- installHandler sigINT (Catch $ recordCtrlC mv) Nothing
      return 0
    handler :: CE.IOException -> IO Int
    handler e = fromEnum <$> htcl_AddObjErrorInfo interp (ioeGetErrorString e)

handleCtrlC :: MVar () -> IO ()
handleCtrlC mv = do
  _ <- takeMVar mv
  putStrLn "Got Ctrl-C!"
  handleCtrlC mv

recordCtrlC :: MVar () -> IO ()
recordCtrlC mv = do
  putStrLn "recording Ctrl-C..."
  _ <- tryPutMVar mv ()
  return ()
