module TclParseUtils(parseTypeExpr, parseQualConstructor) where

import Error(ErrorHandle, EMsg, internalError)
import Flags(Flags(..))

import Classic
import Parser.BSV(pStringWrapper, pTypeExpr, pQualConstructor)
import FStringCompat(mkFString)
import Id(Id)
import Depend(outlaw_sv_kws_as_classic_ids)

import Parser.Classic.CParser(CParser, pType, qcon, eof, errSyntax)
import Parse(parse, (+..))
import Lex(lexStart, LFlags(..))
import CType(CType)

type Parser a = ErrorHandle -> Flags -> String -> IO (Either [EMsg] a)

parseTypeBSV :: Parser CType
parseTypeBSV errh flags s = pStringWrapper errh flags pTypeExpr [s]

parseTypeClassic :: Parser CType
parseTypeClassic _ flags = classicStringWrapper flags pType

parseQConBSV :: Parser Id
parseQConBSV errh flags s = pStringWrapper errh flags pQualConstructor [s]

parseQConClassic :: Parser Id
parseQConClassic _ flags = classicStringWrapper flags qcon

classicStringWrapper :: (Show a) => Flags -> CParser a -> String -> IO (Either [EMsg] a)
classicStringWrapper flags parser s = fullParse $ lex s
  where fullParse ts =
          case parse (parser +.. eof) ts of
            Left (ss,ts)   -> return $ Left [errSyntax (filter (not . null) ss) ts]
            Right []       -> internalError $ "TclParseUtils: Successful no parse: " ++ show s
            Right [(p,[])] -> return $ Right p
            Right ps       -> internalError $ "TclParseUtils: multiple parses: " ++ show ps ++ "\n" ++ show s
        lex = lexStart lflags (mkFString "Commandline")
        lflags = LFlags { lf_is_stdlib = stdlibNames flags,
                          lf_allow_sv_kws = not outlaw_sv_kws_as_classic_ids }

-- Permissive parsing. If either a BSV or Classic parse succeeds, return that result,
-- preferring the selected syntax
permissiveParse :: Parser a -> Parser a -> Parser a
permissiveParse classicParser bsvParser errh flags s = do
  classicParse <- classicParser errh flags s
  bsvParse <- bsvParser errh flags s
  case (isClassic(), classicParse, bsvParse) of
    (True, Right p, _)         -> return $ Right p
    (False, _, Right p)        -> return $ Right p
    (_, Right p, Left _)       -> return $ Right p
    (_, Left _, Right p)       -> return $ Right p
    (True, Left errs, Left _)  -> return $ Left errs
    (False, Left _, Left errs) -> return $ Left errs

parseTypeExpr :: Parser CType
parseTypeExpr = permissiveParse parseTypeClassic parseTypeBSV

parseQualConstructor :: Parser Id
parseQualConstructor = permissiveParse parseQConClassic parseQConBSV
