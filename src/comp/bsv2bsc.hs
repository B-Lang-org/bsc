module Main_bsv2bsc(main) where

import System.Environment

import Parser.BSV(bsvParseString)
import PPrint
import FlagsDecode(defaultFlags)
import Error(initErrorHandle)

main =
    do args <- getArgs
       case args of
         [] -> getContents >>= bsv2bsc "-"
         [fn] -> readFile fn >>= bsv2bsc fn
         _ -> error "usage: bsv2bsc filename"

bsv2bsc filename text =
    do errh <- initErrorHandle
       (pkg,_) <- bsvParseString errh (defaultFlags "") True filename (stripExt filename) text
       putStrLn (ppReadable pkg)

stripExt filename =
    case reverse filename of
    ('v':'s':'b':'.':revBase) -> reverse revBase
    _ -> filename
