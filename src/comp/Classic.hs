module Classic (SyntaxMode(..),
                setSyntax, isSyntaxFrozen,
                isBSV, isClassic, isEse,
               ) where

import IOMutVar(MutableVar, newVar, readVar, writeVar)
import System.IO.Unsafe(unsafePerformIO)

data SyntaxMode = BSV | CLASSIC | ESE
                   deriving Eq

syntax :: MutableVar SyntaxMode
syntax = unsafePerformIO $ (newVar CLASSIC)

syntaxFrozen :: MutableVar Bool
syntaxFrozen = unsafePerformIO $ newVar False

isSyntaxFrozen :: IO Bool
isSyntaxFrozen = readVar syntaxFrozen

setSyntax :: SyntaxMode -> IO ()
setSyntax m = writeVar syntax m

readSyntax :: IO SyntaxMode
readSyntax = do
  writeVar syntaxFrozen True
  readVar syntax

{-# NOINLINE isBSV #-}
isBSV :: () -> Bool
isBSV() = (unsafePerformIO readSyntax) == BSV

{-# NOINLINE isClassic #-}
isClassic :: () -> Bool
isClassic() = (unsafePerformIO readSyntax) == CLASSIC

isEse :: () -> Bool
isEse() = (unsafePerformIO readSyntax) == ESE
