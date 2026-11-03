{-# LANGUAGE ForeignFunctionInterface #-}
module Main where

import Foreign.C.Types
import Foreign.Ptr

type TclInterp = Ptr ()

foreign import ccall "bluetcl_AppInit" bluetcl_AppInit :: TclInterp -> IO CInt
foreign import ccall "Tcl_CreateInterp" tcl_CreateInterp :: IO TclInterp
foreign import ccall "Tcl_Main" tcl_Main :: CInt -> Ptr (Ptr CChar) -> IO ()

main :: IO ()
main = do
    interp <- tcl_CreateInterp
    _ <- bluetcl_AppInit interp
    tcl_Main 0 nullPtr 