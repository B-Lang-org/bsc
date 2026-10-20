-- Checks IExpand.iExpandStrings, which evaluates a toplevel definition of
-- type List String to its strings with the static elaborator.
--
-- The script compiles Strings.bs, from the current directory, by the passes
-- that bsc's driver runs before elaboration, against the Lib.bo that bsc has
-- compiled there. It then evaluates each definition that is named below and
-- prints its strings, or bsc's error messages; what a definition prints
-- while it is evaluated comes first.
module Main (main) where

import qualified Control.Exception as CE
import Control.Monad (unless, when)
import Data.List (foldl')
import qualified Data.Map as M
import System.Environment (getEnv)
import System.IO

import BinUtil (readImports, replaceImportedSignatures)
import CSyntax
import CtxRed (cCtxReduceIO)
import Deriving (derive)
import Error (ErrorHandle, bsError, initErrorHandle)
import FStringCompat (mkFString)
import FixupDefs (fixupDefs)
import Flags (Flags)
import FlagsDecode (adjustFinalFlags, decodeFlags, defaultFlags)
import IConv (iConvPackage)
import IExpand (iExpandStrings)
import IExpandUtils (HDef, HExpr)
import ISimplify (iSimplify)
import ISyntax
import Id (Id, getIdBaseString, getIdString)
import Lex (LFlags (..), lexStart)
import MakeSymTab (cConvInst, mkSymTab)
import Parse (parse)
import ParseOp (parseOps)
import Parser.Classic (errSyntax, pPackage)
import Simplify (simplify)
import SymTab (SymTab)
import TypeCheck (cTypeCheck, mergeCATFCaches)

-- The definitions of Strings to evaluate, in the order of the output.
names :: [String]
names =
  [ "plain", "empty", "imported", "recursive", "throughClass", "messaged"
  , "undeterminedElement", "undeterminedSpine", "failing", "notAList", "polymorphic" ]

main :: IO ()
main = do
  -- what bsc prints on stdout and stderr goes to one file, in order
  hSetBuffering stdout LineBuffering
  bluespecdir <- getEnv "BLUESPECDIR"
  flags <- searchFlags bluespecdir
  errh <- initErrorHandle
  source <- readFile "Strings.bs"
  (symt, alldefs, atf, defs) <- compileStrings errh flags source
  mapM_ (evaluate flags symt alldefs atf defs) names

searchFlags :: FilePath -> IO Flags
searchFlags bluespecdir = do
  let (_, _, errs, f, rest) = decodeFlags ["-p", ".:%/Libraries"] ([], [], [], defaultFlags bluespecdir)
      (_, errs', f') = adjustFinalFlags [] errs f
  unless (null errs' && null rest) $ ioError (userError "cannot set the search path")
  pure f'

-- Strings, through the passes that bsc's driver runs before elaborating a
-- module, giving what iExpandStrings takes: the symbol table with every
-- imported definition visible, the definitions of Strings and its imports,
-- and the ATF cache of all of them.
compileStrings :: ErrorHandle -> Flags -> String -> IO (SymTab, M.Map Id HExpr, IATFCache, [HDef])
compileStrings errh flags source = do
  let lflags = LFlags { lf_is_stdlib = False, lf_allow_sv_kws = True }
  cpkg <- case parse pPackage (lexStart lflags (mkFString "Strings.bs") source) of
            Right ((p, _) : _) -> pure p
            Left (ss, ts) -> bsError errh [errSyntax (filter (not . null) ss) ts]
            Right [] -> bsError errh []
  (mimp@(CPackage _ _ _ impsigs _ _ _), binmap, _) <- readImports errh flags M.empty M.empty cpkg
  mop <- parseOps errh mimp
  symt0 <- mkSymTab errh mop
  mder <- derive errh flags symt0 mop
  symt1 <- mkSymTab errh mder
  (mctx, _, ctxATF) <- cCtxReduceIO errh flags symt1 mder
  symt <- mkSymTab errh mctx
  (tmod, tcErrors, _, tcATF) <- cTypeCheck errh flags symt (cConvInst errh symt mctx)
  when tcErrors $ bsError errh []
  imod <- iConvPackage errh flags symt (mergeCATFCaches tcATF ctxATF) (simplify flags tmod)
  let found = [b | CImpSign _ _ (CSignature i _ _ _) <- impsigs, Just b <- [M.lookup (getIdString i) binmap]]
      binmods = [(p, h) | (_, _, _, p, h) <- found]
  internalSymt <- mkSymTab errh (replaceImportedSignatures mctx [s | (_, _, s, _, _) <- found])
  let (imodf, alldefsList) = fixupDefs imod binmods
      IPackage _ _ _ defs atf = iSimplify imodf
      alldefs = M.fromList [(i, e) | IDef i _ e _ <- alldefsList]
      atfAll = foldl' mergeIATFCaches atf [ipkg_atf_cache m | (m, _) <- binmods]
  pure (internalSymt, alldefs, atfAll, defs)

evaluate :: Flags -> SymTab -> M.Map Id HExpr -> IATFCache -> [HDef] -> String -> IO ()
evaluate flags symt alldefs atf defs name =
  case [d | d@(IDef i _ _ _) <- defs, getIdBaseString i == name] of
    [] -> putStrLn (name ++ ": no such definition")
    def : _ -> do
      -- a fresh handle per definition, since a reported error ends the
      -- handle's run
      errh <- initErrorHandle
      r <- CE.try (iExpandStrings errh flags symt alldefs atf def
                     >>= \ ss -> CE.evaluate (length (concat ss)) >> pure ss)
      putStrLn $ name ++ case r of
        Right ss -> " =" ++ concatMap ((' ' :) . show) ss
        -- bsc raises its error messages, for its caller to report
        Left e | Just (CE.ErrorCall m) <- CE.fromException e -> " failed:\n" ++ m
               | otherwise -> " failed: " ++ CE.displayException (e :: CE.SomeException)
