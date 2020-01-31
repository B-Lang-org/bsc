module Main_bsc2bsv(main) where

import System.Environment
import qualified Control.Exception as CE

import FStringCompat
import Parse
import Parser.Classic(pPackage, errSyntax)
import PVPrint
import CVPrint()
import Lex
import Error(internalError, showErrorList)

main =
    do args <- getArgs
       case args of
         [] -> getContents >>= bsc2bsv "-"
         [fn] -> readFile fn >>= bsc2bsv fn
         _ -> error "usage: bsc2bsv filename"

bsc2bsv filename text =
    do let lflags = LFlags { lf_is_stdlib = False,
                             lf_allow_sv_kws = True }
           tokens = lexStart lflags (mkFString filename) text
       case parse pPackage tokens of
         Left  (ss, tokens') -> let es = [errSyntax [s | s@(_:_) <- ss] tokens']
                                in  CE.throw $ CE.ErrorCall (showErrorList es)
         Right ((package,_):_) ->
           putStrLn $ pvpReadable package
         Right [] -> internalError "bsc2bsv: parse succeded with no packages"
