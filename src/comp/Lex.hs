module Lex(Token(..), LexItem(..), LFlags(..), prLexItem,
           lexStart, lexStartWithPos,
           isIdChar, isSym, convLexErrorToErrMsg) where
-- Bluespec lexical analysis.  Written for speed, not beauty!
import Numeric(readFloat)
import Data.Char
-- import Data.Ratio
import qualified Data.Set as S

import Util(itos)
import Position
import Error(internalError, ErrMsg(..))
import FStringCompat
import PreStrings(fsEmpty)
import SystemVerilogKeywords

-- import Debug.Trace

-- data structure for lexical errors
-- so raw error messages are not in LexItem
data LexError = LexBadCharLit
              | LexBadStringLit
              | LexBadLexChar Char
              | LexUntermComm Position
              | LexMissingNL
              deriving(Eq)

convLexErrorToErrMsg :: LexError -> ErrMsg
convLexErrorToErrMsg (LexBadCharLit) = EBadCharLit
convLexErrorToErrMsg (LexBadStringLit) = EBadStringLit
convLexErrorToErrMsg (LexBadLexChar c) = EBadLexChar c
convLexErrorToErrMsg (LexUntermComm p) = EUntermComm p
convLexErrorToErrMsg (LexMissingNL) = EMissingNL

data LexItem =
          L_varid FString
        | L_conid FString
        | L_varsym FString
        | L_consym FString
        | L_integer (Maybe Integer) Integer Integer                -- bit size (if specified), base, value
        | L_float Rational
        | L_char Char
        | L_string String
        | L_lpar
        | L_rpar
        | L_semi
        | L_uscore
        | L_bquote
        | L_lcurl
        | L_rcurl
        | L_lbra
        | L_rbra
        -- reserved words
        | L_action | L_case | L_class | L_data | L_deriving | L_do | L_else | L_foreign
        | L_if | L_import | L_in
        | L_infix | L_infixl | L_infixr
        | L_interface | L_instance
        | L_let | L_letseq | L_package | L_of
        | L_primitive | L_qualified | L_rules | L_signature | L_struct
        | L_then | L_module | L_type | L_valueOf | L_stringOf | L_verilog | L_synthesize | L_when | L_where
        | L_coherent | L_incoherent
        -- reserved ops
        | L_dcolon | L_colon | L_eq | L_at | L_lam | L_bar
        | L_rarrow | L_larrow | L_dot | L_comma | L_drarrow | L_irarrow
        -- layout items
        | L_lcurl_o | L_rcurl_o | L_semi_o
        -- pragma
        | L_lpragma | L_rpragma
        -- pseudo items
        | L_eof
        | L_error LexError
        deriving (Eq)

prLexItem :: LexItem -> String
prLexItem (L_varid s) = getFString s
prLexItem (L_conid s) = getFString s
prLexItem (L_varsym s) = getFString s
prLexItem (L_consym s) = getFString s
prLexItem (L_integer _ _ i) = itos i
prLexItem (L_float r) = show r
prLexItem (L_char c) = show c
prLexItem (L_string s) = show s
prLexItem L_lpar = "("
prLexItem L_rpar = ")"
prLexItem L_semi = ";"
prLexItem L_uscore = "_"
prLexItem L_bquote = "`"
prLexItem L_lcurl = "{"
prLexItem L_rcurl = "}"
prLexItem L_lbra = "["
prLexItem L_rbra = "]"
prLexItem L_action = "action"
prLexItem L_case = "case"
prLexItem L_class = "class"
prLexItem L_data = "data"
prLexItem L_deriving = "deriving"
prLexItem L_do = "do"
prLexItem L_else = "else"
prLexItem L_foreign = "foreign"
prLexItem L_if = "if"
prLexItem L_import = "import"
prLexItem L_in = "in"
prLexItem L_coherent = "coherent"
prLexItem L_incoherent = "incoherent"
prLexItem L_infix = "infix"
prLexItem L_infixl = "infixl"
prLexItem L_infixr = "infixr"
prLexItem L_interface = "interface"
prLexItem L_instance = "instance"
prLexItem L_let = "let"
prLexItem L_letseq = "letseq"
prLexItem L_package = "package"
prLexItem L_of = "of"
prLexItem L_primitive = "primitive"
prLexItem L_qualified = "qualified"
prLexItem L_rules = "rules"
prLexItem L_signature = "signature"
prLexItem L_struct = "struct"
prLexItem L_module = "module"
prLexItem L_then = "then"
prLexItem L_type = "type"
prLexItem L_valueOf = "valueOf"
prLexItem L_stringOf = "stringOf"
prLexItem L_verilog = "verilog"
prLexItem L_synthesize = "synthesize"
prLexItem L_when = "when"
prLexItem L_where = "where"
prLexItem L_dcolon = "::"
prLexItem L_colon = ":"
prLexItem L_eq = "="
prLexItem L_at = "@"
prLexItem L_lam = "\\"
prLexItem L_bar = "|"
prLexItem L_rarrow = "->"
prLexItem L_larrow = "<-"
prLexItem L_dot = "."
prLexItem L_comma = ","
prLexItem L_drarrow = "==>"
prLexItem L_irarrow = "=>"
prLexItem L_lcurl_o = "{ from layout"
prLexItem L_rcurl_o = "} from layout"
prLexItem L_semi_o = "; from layout"
prLexItem L_lpragma = "{-#"
prLexItem L_rpragma = "#-}"
prLexItem L_eof = "<EOF>"
prLexItem (L_error s) = "Lexical error: " ++ show (convLexErrorToErrMsg s)

data Token = Token Position LexItem deriving (Eq)

instance Show Token where
    showsPrec _ (Token p l) = showString ("(Token " ++ prPosition p ++ " " ++ prLexItem l ++ ")")


data LFlags = LFlags {
    lf_is_stdlib :: Bool,   -- parsing a stdlib file, annotate positions
    lf_allow_sv_kws :: Bool -- allow SV keywords as identifiers
}

type FileName = FString

tabStop :: Int
tabStop = 8
nextTab :: Int -> Int
nextTab c = ((c+tabStop-1) `div` tabStop) * tabStop

lexStart :: LFlags -> FileName -> String -> [Token]
lexStart lflags file cs = lx lflags file 1 0 cs

lexStartWithPos :: LFlags -> Position -> String -> [Token]
lexStartWithPos lflags pos text =
    lx lflags (mkFString (getPositionFile pos)) (getPositionLine pos)
           (getPositionColumn pos) text

lx :: LFlags -> FileName -> Int -> Int -> String -> [Token]
--    flags     file      line   column   input     output
lx lf f (-1)_  cs = internalError "lx: unknown position"
lx lf f _ (-1) cs = internalError "lx: unknown position"

lx lf f l 0 ('#':' ':cs@(c:_)) | isDigit c =
        -- preprocessor output: # <line> "<file>"
        let (li, r) = span (/= '\n') cs
            (ns, spfs) = span isDigit li
            -- after the filename are optional space-separated flags, but we ignore them
            -- XXX should we at least check that the rest of the line is valid?
            fs = takeWhile (not . isSpace) (dropWhile isSpace spfs)
            -- the linenum
            n = read ns
            -- the filename
            -- XXX should we error if it is not a non-empty string in quotes?
            fn = if length fs > 2 && head fs == '"' && last fs == '"' then init (tail fs) else "???"
            -- consume the newline, too, so that we don't add 1 to the linenum
            r' = case r of
                   ('\n':cs) -> cs
                   [] -> []
                   _ -> internalError "lx: span failure"
        in  lx lf (mkFString fn) n 0 r'

lx lf f l c ""                        =
    [Token (mkPositionFull f (l+1) (-1) (lf_is_stdlib lf)) L_eof]
lx lf f l c (' ':cs)            = lx lf f l (c+1) cs
lx lf f l c ('\n':cs)           = lx lf f (l+1) 0 cs
lx lf f l c ('\t':cs)           = lx lf f l (nextTab (c+1)) cs
lx lf f l c ('\r':cs)           = lx lf f l 0 cs
lx lf f l c ('\v':cs)           = lx lf f l 0 cs
lx lf f l c ('\f':cs)           = lx lf f l 0 cs
lx lf f l c ('-':'-':cs) | isComm cs    = skipToEOL lf f l cs
  where isComm ('-':cs) = isComm cs
        isComm ('@':cs) = True
        isComm (c:cs)   = not (isSym c)
        isComm _        = True
lx lf f l c ('{':'-':'#':cs)    = Token (mkPositionFull f l c (lf_is_stdlib lf)) L_lpragma : lx lf f l (c+3) cs
lx lf f l c ('#':'-':'}':cs)    = Token (mkPositionFull f l c (lf_is_stdlib lf)) L_rpragma : lx lf f l (c+3) cs
lx lf f l c ('{':'-':cs)        = skipComm lf (l, c) 1 f l (c+2) cs
lx lf f l c ('(':cs)                = Token (mkPositionFull f l c (lf_is_stdlib lf)) L_lpar : lx lf f l (c+1) cs
lx lf f l c (')':cs)                = Token (mkPositionFull f l c (lf_is_stdlib lf)) L_rpar : lx lf f l (c+1) cs
lx lf f l c (',':cs)                = Token (mkPositionFull f l c (lf_is_stdlib lf)) L_comma : lx lf f l (c+1) cs
lx lf f l c (';':cs)                = Token (mkPositionFull f l c (lf_is_stdlib lf)) L_semi : lx lf f l (c+1) cs
lx lf f l c ('`':cs)                = Token (mkPositionFull f l c (lf_is_stdlib lf)) L_bquote : lx lf f l (c+1) cs
lx lf f l c ('{':cs)                = Token (mkPositionFull f l c (lf_is_stdlib lf)) L_lcurl : lx lf f l (c+1) cs
lx lf f l c ('}':cs)                = Token (mkPositionFull f l c (lf_is_stdlib lf)) L_rcurl : lx lf f l (c+1) cs
lx lf f l c ('[':cs)                = Token (mkPositionFull f l c (lf_is_stdlib lf)) L_lbra  : lx lf f l (c+1) cs
lx lf f l c (']':cs)                = Token (mkPositionFull f l c (lf_is_stdlib lf)) L_rbra  : lx lf f l (c+1) cs
lx lf f l c ('.':cs)                = Token (mkPositionFull f l c (lf_is_stdlib lf)) L_dot  : lx lf f l (c+1) cs
lx lf f l c ('\'':cs)                =
    case lexLitChar' cs of
        Just (cc, n, '\'':cs) -> Token (mkPositionFull f l c (lf_is_stdlib lf)) (L_char cc) : lx lf f l (c+2+n) cs
        _ -> lexerr f l c LexBadCharLit
lx lf f l c ('"':cs)                =
        case lexString cs l (c+1) "" of
            Just (str, l', c', cs') -> Token (mkPositionFull f l c (lf_is_stdlib lf)) (L_string str) : lx lf f l' c' cs'
            _ -> lexerr f l c LexBadStringLit
        where
                lexString :: String -> Int -> Int -> String -> Maybe (String, Int, Int, String)
                lexString ('"':s)      l c r             = Just (reverse r, l, c+1, s)
                lexString s            l c r             = lexLitChar' s >>= \ (x, n, s') -> lexString s' l (c+n) (x:r)
lx lf f l c ('0':x:ch:cs) | (x == 'x' || x == 'X') && isHexDigit ch =
    lInteger 16 isHexDigit Nothing (length "0x") lf f l c (ch:cs)
lx lf f l c ('0':b:ch:cs) | (b == 'b' || b == 'B') && isBinDigit ch =
    lInteger  2 isBinDigit Nothing (length "0b") lf f l c (ch:cs)
lx lf f l c ('0':o:ch:cs) | (o == 'o' || o == 'O') && isOctDigit ch =
    lInteger  8 isOctDigit Nothing (length "0o") lf f l c (ch:cs)
lx lf f l c (ch:cs) | isDigit ch =
  let isSign c = (c == '+' || c == '-')
      -- look for decimal
      lxFloat soFar ('.':cs) =
          -- found decimal, look for an exponent
          case (span isDigit cs) of
          -- no digits after the point, so just make an integer
          ([], _) -> lInteger 10 isDigit Nothing 0 lf f l c (soFar ++ '.':cs)
          (s', cs') -> lxExp (soFar ++ ('.':s')) cs'
      lxFloat soFar (e:cs) | (e == 'e' || e == 'E') =
          -- no decimal, but "e", so handle exponent
          lxExp soFar (e:cs)
      -- Sized bit vectors
      lxFloat soFar ('\'' : fmt : ch : cs)
        | fmt == 'h' && isHexDigit ch = lInteger 16 isHexDigit (Just sz) w_pre lf f l c (ch:cs)
        | fmt == 'd' && isDigit    ch = lInteger 10 isDigit    (Just sz) w_pre lf f l c (ch:cs)
        | fmt == 'b' && isBinDigit ch = lInteger  2 isBinDigit (Just sz) w_pre lf f l c (ch:cs)
        | fmt == 'o' && isOctDigit ch = lInteger  8 isOctDigit (Just sz) w_pre lf f l c (ch:cs)
        where sz = readN 10 soFar
              w_pre = length soFar + length "'h"
      lxFloat soFar cs =
          -- no decimal, exponent or sized literal format, so it's an integer
          lInteger 10 isDigit Nothing 0 lf f l c (soFar ++ cs)
      -- look for an exponent on a float
      lxExp soFar (e:s:d:cs) | (e == 'e' || e == 'E') &&
                               (isSign s) && (isDigit d) =
          -- found a signed exponent
          case (span isDigit cs) of
          (s', cs') -> lReal (soFar ++ (e:s:d:s')) lf f l c cs'
      lxExp soFar (e:d:cs) | (e == 'e' || e == 'E') && (isDigit d) =
          -- found an unsigned exponent
          case (span isDigit cs) of
          (s', cs') -> lReal (soFar ++ (e:d:s')) lf f l c cs'
      lxExp soFar cs =
          -- no exponent, just process the float
          lReal soFar lf f l c cs
  in
    case span isDigit cs of
    (s', cs') -> lxFloat (ch:s') cs'
lx lf f l c ('$':x:cs) | isIdChar x = spanId [] (c+1) cs
    where spanId r cn (y:cs) | (isIdChar y || y == '$') = spanId (y:r) (cn+1) cs
          spanId r cn cs' =
             let fs = mkFString ('$':x:reverse r)
                 pos = mkPositionFull f l c (lf_is_stdlib lf)
             in  Token pos (L_varid fs) : lx lf f l cn cs'
lx lf f l c (x:cs) | isSym x = spanSym [] (c+1) cs
    where
    spanSym r cn (y:cs) | isSym y = spanSym (y:r) (cn+1) cs
    spanSym r cn cs' =
        let s = x:reverse r
            p = mkPositionFull f l c (lf_is_stdlib lf)
            lxrs x = Token p x : lx lf f l cn cs'
        in  case s of
                "::"        -> lxrs L_dcolon
                ":"        -> lxrs L_colon
                "="     -> lxrs L_eq
                "@"     -> lxrs L_at
                "\\"        -> lxrs L_lam
                "->"        -> lxrs L_rarrow
                "==>"        -> lxrs L_drarrow
                "=>"        -> lxrs L_irarrow
                "<-"        -> lxrs L_larrow
                _        -> let fs = mkFString s
                           in
                            if not (lf_allow_sv_kws lf) && isSvSymbol s
                            then internalError
                                 ("SystemVerilog symbol forbidden: " ++ s)
                            else if head s == ':' then
                                Token p (L_consym fs) : lx lf f l cn cs'
                            else
                                Token p (L_varsym fs) : lx lf f l cn cs'
lx lf f l c (x:cs) | isAlpha x || x == '_' = spanId [] (c+1) cs
    where
    spanId r cn (y:cs) | isIdChar y = spanId (y:r) (cn+1) cs
    spanId r cn cs' =
        let s = x:reverse r
            p = mkPositionFull f l c (lf_is_stdlib lf)
            lxr x = Token p x : lx lf f l cn cs'
            token = let fs = mkFString s in
                        if isUpper (head s) then
                            Token p (L_conid fs) : lx lf f l cn cs'
                        else
                            Token p (L_varid fs) : lx lf f l cn cs'
        in  case s of
                "$"             -> lxr (L_varsym (mkFString s))
                "_"                -> lxr L_uscore
                "action"        -> lxr L_action
                "case"                -> lxr L_case
                "class"                -> lxr L_class
                "data"                -> lxr L_data
                "deriving"        -> lxr L_deriving
                "do"                -> lxr L_do
                "else"          -> lxr L_else
                "foreign"       -> lxr L_foreign
                "if"            -> lxr L_if
                "import"        -> lxr L_import
                "in"                -> lxr L_in
                "coherent"      -> lxr L_coherent
                "incoherent"    -> lxr L_incoherent
                "infix"                -> lxr L_infix
                "infixl"        -> lxr L_infixl
                "infixr"        -> lxr L_infixr
                "interface"        -> lxr L_interface
                "instance"        -> lxr L_instance
                "let"                -> lxr L_let
                "letseq"        -> lxr L_letseq
                "module"        -> lxr L_module
                "of"                -> lxr L_of
                -- A hack to allow multiple packages in one file.
                -- We need to generate a closing '}', so the package keyword has to
                -- be in column -1.
                "package"        ->
                    Token (mkPositionFull f l (c-1) (lf_is_stdlib lf)) L_package :
                    lx lf f l cn cs'
                "primitive"        -> lxr L_primitive
                "qualified"        -> lxr L_qualified
                "rules"                -> lxr L_rules
                "signature"        -> lxr L_signature
                "struct"        -> lxr L_struct
                "then"          -> lxr L_then
                "type"          -> lxr L_type
                "valueOf"        -> lxr L_valueOf
                "stringOf"        -> lxr L_stringOf
                "verilog"        -> lxr L_verilog
                "synthesize"        -> lxr L_synthesize
                "when"          -> lxr L_when
                "where"         -> lxr L_where
                _               -> if not (lf_allow_sv_kws lf) && isSvKeyword s
                                   then internalError
                                     ("SystemVerilog keyword forbidden: " ++ s)
                                   else token

lx lf f l c (x:cs) = lexerr f l c (LexBadLexChar x)

-- Note: The caller is expected to make sure that cs starts with one valid, non-_ digit.
-- This should ensure that the readN call succeeds.
lInteger :: Integer -> (Char -> Bool) -> Maybe Integer -> Int -> LFlags
         -> FileName -> Int -> Int -> String -> [Token]
lInteger base isBaseDigit sz w_prefix lf f l c cs =
  case span (\c -> c == '_' || isBaseDigit c) cs of
    (s, cs') ->
      let w = length s + w_prefix
          li = L_integer sz base (readN base $ filter (/= '_') s)
      in Token (mkPositionFull f l c (lf_is_stdlib lf)) li : lx lf f l (c+w) cs'

lReal :: String -> LFlags -> FileName -> Int -> Int -> String -> [Token]
lReal s lf f l c cs =
    let num = case (readFloat s) of
                [(n, "")] -> n
                _ -> internalError ("lReal: readFloat: " ++ s)
        lr = L_float num
    in  Token (mkPositionFull f l c (lf_is_stdlib lf)) lr : lx lf f l (c + length s) cs

{-
isUpper_ ('_':cs) = isUpper_ cs
isUpper_ (c:_) = isUpper c
isUpper_ [] = True
-}

lexerr :: FileName -> Int -> Int -> LexError -> [Token]
lexerr f l c err = map (Token (mkPosition f l c)) (L_error err : repeat L_eof)

isSym :: Char -> Bool
isSym '!' = True; isSym '@' = True; isSym '#' = True; isSym '$' = True
isSym '%' = True; isSym '&' = True; isSym '*' = True; isSym '+' = True
isSym '.' = True; isSym '/' = True; isSym '<' = True; isSym '=' = True
isSym '>' = True; isSym '?' = True; isSym '\\' = True; isSym '^' = True
isSym '|' = True; isSym ':' = True; isSym '-' = True; isSym '~' = True
isSym ',' = True
isSym c | c >= '\x80' = c `elem` ['\162', '\163', '\164', '\165', '\166',
                                  '\167', '\168', '\169', '\170', '\171',
                                  '\172', '\173', '\174', '\175', '\176',
                                  '\177', '\178', '\179', '\180', '\181',
                                  '\183', '\184', '\185', '\186', '\187',
                                  '\188', '\189', '\190', '\191', '\215',
                                  '\247' ] || (isSymbol c && not (isIdChar c))
isSym _ = False

isIdChar :: Char -> Bool
isIdChar '\'' = True
isIdChar '_' = True
isIdChar c = isAlphaNum c

isBinDigit :: Char -> Bool
isBinDigit c = isDigit c && digitToInt c < 2

--isOctDigit c = c >= '0' && c <= '7'

skipComm :: LFlags -> (Int,Int) -> Int -> FileName -> Int -> Int -> String -> [Token]
skipComm lf lc 0 f l c cs             = lx lf f l c cs
skipComm lf lc n f l c ('-':'}':cs) = skipComm lf lc (n-1) f l (c+2) cs
skipComm lf lc n f l c ('{':'-':cs) = skipComm lf lc (n+1) f l (c+2) cs
skipComm lf lc n f l c ('\n':cs)    = skipComm lf lc n     f (l+1) 0 cs
skipComm lf lc n f l c ('\t':cs)    = skipComm lf lc n f l (nextTab (c+1)) cs
skipComm lf lc n f l c (_:cs)       = skipComm lf lc n f l (c+1) cs
skipComm lf (ll,cc) n f l c ""      =
    lexerr f l c (LexUntermComm (mkPosition fsEmpty ll cc))

skipToEOL :: LFlags -> FileName -> Int -> String -> [Token]
skipToEOL lf f l ('\n':cs) = lx lf f (l+1) 0 cs
skipToEOL lf f l (_:cs)    = skipToEOL lf f l cs
skipToEOL lf f l ""        = lexerr f l 0 LexMissingNL

lexLitChar'                :: String -> Maybe (Char, Int, String)
lexLitChar' ('\\':s)        = lexEsc s
        where
        lexEsc ('x':s)        = let (n,s') = span isHexDigit s in Just (chr (fromInteger (readN 16 n)), 2+length n, s')
        lexEsc ('n':s)  = Just ('\n', 1, s)
        lexEsc ('t':s)  = Just ('\t', 1, s)
        lexEsc ('r':s)  = Just ('\r', 1, s)
        lexEsc ('v':s)  = Just ('\v', 1, s)
        lexEsc ('f':s)  = Just ('\f', 1, s)
        lexEsc ('"':s)  = Just ('"', 1, s)
        lexEsc ('\'':s) = Just ('\'', 1, s)
        lexEsc ('\\':s) = Just ('\\', 1, s)
        lexEsc s        = Nothing
lexLitChar' ('\n':_)        = Nothing                -- NL in strings is a bad idea
lexLitChar' (c:s)        = Just (c, 1, s)
lexLitChar' ""                = Nothing

readN :: Integer -> String -> Integer
readN radix s =
     foldl1 (\n d -> n * radix + d)
            (map (toInteger . digitToInt) s)

-- maxexp = 10000 :: Int                -- don't allow exponents greater than this since it would take up too much memory

isSvKeyword :: String -> Bool
isSvKeyword str = str `S.member` svKeywordSet

isSvSymbol :: String -> Bool
isSvSymbol str = str `S.member` svSymbolSet

svKeywordSet :: S.Set String
svKeywordSet =
    S.fromList [str | (tok, str, svVer) <- svKeywordTable]

svSymbolSet :: S.Set String
svSymbolSet =
    S.fromList [str | (tok, str, svVer) <- svSymbolTable]
