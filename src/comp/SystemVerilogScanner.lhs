> {-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fno-warn-name-shadowing #-}

Scanner for SystemVerilog

> module SystemVerilogScanner(scan) where

> import Data.Char
> import Data.List
> import Numeric(readDec, readFloat)
> import Text.Regex
> import qualified Data.Map as M

> import Position
> import Error(ErrMsg(..), internalError)
> import SystemVerilogTokens
> import SystemVerilogKeywords
> import FStringCompat

> newtype ScannerState = ScannerState (Position, String)

> type Scanner = ScannerState -> [SV_Token]

Should we present comments as tokens?

> preserveComments :: Bool
> preserveComments = False

Scan is not in a monad because of laziness requirements (space efficiency)

> scan :: Position  -- initial position
>      -> String    -- input
>      -> [SV_Token]
> scan initPos input = scanMain (ScannerState (initPos, input))

Toplevel scanner function

> scanMain :: Scanner
> -- end of file
> --   note that we don't know its position, so we can't accurately reproduce
> --   spaces at the end of the file
> scanMain state@(ScannerState (pos, [])) = []
> scanMain state@(ScannerState (pos, '#':input))
>     |(isFirstColumn pos)&& (isCPreprocessorDirective input) =
>                           [SV_Token_Error { start_position = pos,
>                                             end_position = pos,
>                                             errMessage = ECPPDirective}]
> -- line comment
> scanMain state@(ScannerState (pos, '/':'/':input)) =
>     scanLineComment pos (eatChars 2 state)
> -- block comment
> scanMain state@(ScannerState (pos, '/':'*':input)) =
>     scanBlockComment pos "" (eatChars 2 state)
> -- string
> scanMain state@(ScannerState (pos, '\"':input)) =
>     scanString pos "" (eatChars 1 state)
> -- system identifier
> scanMain state@(ScannerState (pos, input)) | matchesTaskId input =
>     let (idChars, restOfInput) = span isIdChar input
>         (end_pos, next_pos) = posAtEndAndAfterString pos idChars
>         nextScannerState = ScannerState (next_pos, restOfInput)
>         token = SV_Token_System_Id { start_position = pos,
>                                      end_position = end_pos,
>                                      name = idChars }
>     in token : scanMain nextScannerState
> -- escaped identifier (SV 3.1a LRM A.9.3, also V2001 LRM section 2.7.1)
> scanMain state@(ScannerState (pos, '\\':input)) =
>     let (idChars, restOfInput) = span (not . isWhitespace) input
>         (end_pos, next_pos) = posAtEndAndAfterString pos ('\\':idChars)
>         nextScannerState = ScannerState (next_pos, restOfInput)
>         token = SV_Token_Id { start_position = pos,
>                               end_position = end_pos,
>                               name = idChars }
>     in  token : scanMain nextScannerState
> -- `line compiler directive
> scanMain state@(ScannerState (pos, ('`':'l':'i':'n':'e':'(':restOfInput)))
>     = scanLinePosDirective pos (eatChars 6 state)
> scanMain state@(ScannerState (pos, ('`':'l':'i':'n':'e':c:restOfInput)))
>     | isWhitespace c = scanLineDirective pos (eatChars 6 state)
> -- other compiler directives; assume the words are like identifiers
> scanMain state@(ScannerState (pos, ('`':c:input)))
>     | isIdStart c =
>         let (restDirective, restOfInput) = span isIdChar input
>             directive = '`':c:restDirective
>             (end_pos, next_pos) = posAtEndAndAfterString pos directive
>             token = SV_Token_Directive { start_position = pos,
>                                          end_position = end_pos,
>                                          name = directive }
>             nextScannerState = ScannerState (next_pos, restOfInput)
>         in  token : scanMain nextScannerState
> -- whitespace
> scanMain state@(ScannerState (pos, c:restOfInput)) | isWhitespace c =
>     scanMain (eatChars 1 state)
> -- keyword or simple identifier
> scanMain state@(ScannerState (pos, c:input)) | isIdStart c =
>     let (idRest, restOfInput) = span isIdChar input
>         idChars = c:idRest
>         (end_pos, next_pos) = posAtEndAndAfterString pos idChars
>         token = case M.lookup idChars svKeywords of
>                 Just kw -> SV_Token_Keyword { start_position = pos,
>                                               end_position = end_pos,
>                                               keyword = kw }
>                 Nothing -> SV_Token_Id { start_position = pos,
>                                          end_position = end_pos,
>                                          name = idChars }
>         nextScannerState = ScannerState (next_pos, restOfInput)
>     in  token : scanMain nextScannerState
> -- unbased unsized literal ('0, '1, 'x, 'z, ...)
> scanMain state@(ScannerState (pos, '\'':c:restOfInput))
>     | c /= '_' && isBinXZ_ c =
>         let (end_pos, next_pos) = posAtEndAndAfterString pos ['\'',c]
>             token = SV_Token_Number { start_position = pos,
>                                       end_position = end_pos,
>                                       value = SV_NUM_Repeated (readBit c),
>                                       bitwidth = Nothing,
>                                       base = Nothing,
>                                       signed = False,
>                                       originalText = ['\'',c] }
>             nextScannerState = ScannerState (next_pos, restOfInput)
>         in  token : scanMain nextScannerState
> -- unbased number, sized based number, timescale
> scanMain state@(ScannerState (pos, d:_)) | isDigit d = scanNumber state
> -- unsized based number
> scanMain (ScannerState (pos, '\'':char1:char2:rest))
>     | base `elem` "dboh" = -- decimal, binary, octal, or hex base
>         let (consumedChars, restOfInput) = if signed
>                                            then (['\'',char1,char2], rest)
>                                            else (['\'',char1], char2:rest)
>             (_ {-end_pos-}, next_pos) = posAtEndAndAfterString pos consumedChars
>             nextState = ScannerState (next_pos, restOfInput)
>         in  scanBasedNumber pos Nothing consumedChars signed base
>             nextState
>     where signed = char1 == 's' || char1 == 'S'
>           base = toLower (if signed then char2 else char1)
> -- operators, parsed greedily
> scanMain state@(ScannerState (pos, input@(c:_))) | isSymChar c =
>     let (opChars, restOfInput) = span isSymChar input
>         -- XXX using findLongestMatch is inefficient
>         findLongestMatch table ""  revRest = Nothing
>         findLongestMatch table str revRest =
>             case M.lookup str svSymbols of
>             Just op -> Just (op, str, reverse revRest)
>             Nothing -> findLongestMatch table (init str) (last str : revRest)
>     in  case findLongestMatch svSymbols opChars "" of
>         Nothing ->
>             let (end_pos, _ {- next_pos -}) = posAtEndAndAfterString pos opChars
>             in  [SV_Token_Error { start_position = pos,
>                                   end_position = end_pos,
>                                   errMessage = EBadSymbol opChars}]
>         Just (op, eatenChars, revRest) ->
>             let (end_pos, next_pos) = posAtEndAndAfterString pos eatenChars
>                 token = SV_Token_Symbol { start_position = pos,
>                                           end_position = end_pos,
>                                           symbol = op }
>                 nextScannerState =
>                     ScannerState (next_pos, reverse revRest ++ restOfInput)
>             in  token : scanMain nextScannerState
> -- unknown character
> scanMain state@(ScannerState (pos, c:_)) =
>     [SV_Token_Error { start_position = pos,
>                       end_position = pos,
>                       errMessage = EBadLexChar c }]

> isCPreprocessorDirective :: String -> Bool
> isCPreprocessorDirective rest_of_input =
>     let
>         match_init :: String -> Bool
>         match_init cpp = ((and (zipWith (==) cpp rest_of_input))&&
>                           (notIdChar (drop (length cpp) rest_of_input)))
>         notIdChar :: String -> Bool
>         notIdChar [] = True
>         notIdChar (c:_) = isWhitespace c
>     in
>     or (map match_init
>                 ["define"
>                 ,"undef"
>                 ,"include"
>                 ,"line"
>                 ,"pragma"
>                 ,"endif"
>                 ,"ifdef"
>                 ,"ifndef"
>                 ,"if"
>                 ,"elif"
>                 ,"else"])


Generalize recognizing task ids so that we can treat an identifier
without a leading $ as a task id

> matchesTaskId :: String -> Bool
> matchesTaskId ('$':_) = True
> -- matchesTaskId ('f':'m':'t':x:_) | not (isIdChar x) = True
> matchesTaskId _ = False

Fast lookup table of keywords

> svKeywords :: M.Map String SV_Keyword
> svKeywords = M.fromList [(name, kw) | (kw, name, _) <- svKeywordTable]

Fast lookup table of operators

> svSymbols :: M.Map String SV_Symbol
> svSymbols = M.fromList [(name, op) | (op, name, _) <- svSymbolTable]

STRINGS

Recognize string, handling escape identifiers:
  Verilog 2001:  \n \t \\ \" \ddd
  SystemVerilog: \v \f \a \xhh \NEWLINE

> scanString :: Position     -- init position
>            -> String       -- characters collected so far, reversed
>            -> Scanner      -- the scanner, i.e., state -> tokens
> -- end of string
> scanString initPos reversedSoFar
>            state@(ScannerState (pos, '\"':input)) =
>     let token = SV_Token_String { start_position = initPos,
>                                   end_position = pos,
>                                   contents = reverse reversedSoFar }
>     in  token : scanMain (eatChars 1 state)
> -- escaped newline
> --   note that we actually drop the \ and the newline, so we can't output
> --   the same characters quite right
> scanString initPos reversedSoFar
>            state@(ScannerState (pos, '\\':'\n':input))=
>     scanString initPos reversedSoFar (eatChars 2 state)
> -- octal escape
> scanString initPos reversedSoFar
>            state@(ScannerState (pos, '\\':d1:d2:d3:input))
>     | isOctDigit d1 && isOctDigit d2 && isOctDigit d3 =
>         let c = chr (digitToInt d3 + 8 * digitToInt d2
>                      + 64 * digitToInt d1)
>         in  scanString initPos (c:reversedSoFar) (eatChars 4 state)
> -- hexadecimal escape
> scanString initPos reversedSoFar
>            state@(ScannerState (pos, '\\':'x':d1:d2:input))
>     | isHexDigit d1 && isHexDigit d2 =
>         let c = chr (digitToInt d2 + 16 * digitToInt d1)
>         in  scanString initPos (c:reversedSoFar) (eatChars 4 state)
> -- generic escaped char
> scanString initPos reversedSoFar
>            state@(ScannerState (pos, '\\':e:input)) =
>     -- list is fast enough -- escapes don't happen too often
>     let escapes = [('n', '\n'), ('t', '\t'), ('\\', '\\'), ('\"', '\"'),
>                    ('v', '\v'), ('f', '\f'), ('a', '\a')]
>     in  case lookup e escapes of
>         Just resultChar ->
>             scanString initPos (resultChar:reversedSoFar) (eatChars 2 state)
>         Nothing ->
>             [SV_Token_Error { start_position = pos,
>                               end_position = updatePosChar pos '\\',
>                               errMessage = EBadStringEscapeChar e }]
> scanString initPos reversedSoFar
>            state@(ScannerState (pos, '\n':input)) =
>     [SV_Token_Error { start_position = pos, end_position = pos,
>                       errMessage = EStringNewline }]
> scanString initPos reversedSoFar
>            state@(ScannerState (pos, c:restOfInput)) =
>     scanString initPos (c:reversedSoFar) (eatChars 1 state)
> scanString initPos reversedSoFar state@(ScannerState (pos, "")) =
>     [SV_Token_Error { start_position = pos,
>                       end_position = pos,
>                       errMessage = EStringEOF }]

Line comments

> scanLineComment :: Position     -- init position
>                 -> Scanner      -- the scanner, i.e., state -> tokens
> scanLineComment initPos (ScannerState (pos, input)) =
>     let (commentText, afterCommentText) = span (/= '\n') input
>         (end_pos, next_pos) = posAtEndAndAfterString pos commentText
>         token = SV_Token_Comment { start_position = initPos,
>                                    end_position = end_pos,
>                                    isBlock = False,
>                                    contents = commentText }
>         nextScannerState =
>             case afterCommentText of
>             '\n':restOfInput -> -- skip newline
>               ScannerState (updatePosChar next_pos '\n', restOfInput)
>             -- XXX should an unterminated line comment be an error?
>             restOfInput -> ScannerState (next_pos, restOfInput)
>     in  if preserveComments
>         then token : scanMain nextScannerState
>         else scanMain nextScannerState

> -- XXX this reversed text business is nasty and inefficient for long comments
> scanBlockComment :: Position     -- init position
>                  -> String       -- comment text scanned so far, reversed
>                  -> Scanner      -- the scanner, i.e., state -> tokens
> scanBlockComment initPos reversedText (ScannerState (pos, '*':'/':input)) =
>     let (end_pos, next_pos) = posAtEndAndAfterString pos "*/"
>         token = SV_Token_Comment { start_position = initPos,
>                                    end_position = end_pos,
>                                    isBlock = True,
>                                    contents = reverse reversedText }
>         nextScannerState = ScannerState (next_pos, input)
>     in  if preserveComments
>         then token : scanMain nextScannerState
>         else scanMain nextScannerState
> scanBlockComment initPos reversedText (ScannerState (pos, char:rest)) =
>     scanBlockComment initPos (char : reversedText)
>                          (ScannerState (updatePosChar pos char, rest))
> scanBlockComment initPos reversedText state@(ScannerState (pos, rest@"")) =
>     let token = SV_Token_Error { start_position = pos,
>                                  end_position = pos,
>                                  errMessage = EUntermComm initPos }
>     in  token : scanMain state

line Pos directive. Emitted by the preprocessor

One day the gods will smite me for this.

> -- XXX Errors should be better handled (GitHub issue #584)
> scanLinePosDirective ::Position -> Scanner
> scanLinePosDirective ipos state@(ScannerState (pos,input)) =
>     let (directive, mParenAndRestOfInput) = span (/= ')') input
>         restOfInput = case mParenAndRestOfInput of
>                         (')':rest) -> rest
>                         _ -> internalError "scanLinePosDirective: missing close paren"
>         list = Data.List.groupBy (\x -> \y -> (x /= ',') && (y /= ',')) directive
>         param_list = map (filter (\x -> (not (isWhitespace x))))
>                          (filter ( /= ",") list)
>         -- Expect four arguments (file, line, column, and level)
>         -- but only use the first three
>         (f, l, c) = case param_list of
>                       (a1:a2:a3:_:_) -> (a1, a2, a3)
>                       _ -> internalError "scanLinePosDirective: too few arguments"
>      in
>        scanMain (ScannerState (updatePosFileLineCol pos (mkFString f)
>                                (read l) (read c), restOfInput))

line directives

Verilog 2001 standard specifies they should look like

`line 123 "/foo/../foobar.v" 0

vpp, though, produces

`line 123 foo.v

we accept both, for now

> -- this requires that the `line directive be followed by a newline
> -- it's also an inelegant hack
> scanLineDirective :: Position -> Scanner
> scanLineDirective initPos state@(ScannerState (pos,input)) =
>     let (directive, eolRestOfInput) = span (/= '\n') input
>         restOfInput = case eolRestOfInput of { '\n':cs -> cs; cs -> cs }
>         (end_pos, _) = posAtEndAndAfterString pos directive
>         err = [SV_Token_Error { start_position = initPos,
>                                 end_position = end_pos,
>                                 errMessage = EBadLineDirective }]
>         unquote ('"':cs@(_:_)) | last cs == '"' = Just (init cs)
>                                | otherwise = Nothing
>         unquote cs = Just cs
>         scanLine' :: String -> String -> String -> [SV_Token]
>         scanLine' lineNo filename level =
>             case (reads lineNo, unquote filename) of
>             ([(l, "")], Just f) ->
>                  scanMain (ScannerState (newLinePosition f l, restOfInput))
>             _ -> err
>         wordsDirective :: [String]
>         wordsDirective =
>             case (matchRegex scanLineRegexLevel directive) of
>                  Just x -> x
>                  Nothing ->
>                      case (matchRegex scanLineRegexNoLevel directive) of
>                        Just x -> x
>                        Nothing -> []  -- this will FAIL the case
>                                       -- statement below
>
>     in  case wordsDirective of
>         [lineNo, filename, level] -> scanLine' lineNo filename level
>         [lineNo, filename] -> scanLine' lineNo filename "0"
>         _ -> err

These Regexes are defined at the top level (instead of inside a "let"
in the function above) for efficiency.

> scanLineRegexLevel :: Regex
> scanLineRegexLevel =
>     mkRegex "^[       ]*([0-9]+)[     ]+(.+)[         ]+([0-9]+)[     ]*$"

if you have a non-number as the "level" (third argument), it will get
parsed as part of a filename with spaces in it.  (But if the filename
has quotes, then the unquote function will cause it to bomb out.)

> scanLineRegexNoLevel :: Regex
> scanLineRegexNoLevel =
>     mkRegex "^[       ]*([0-9]+)[     ]+(.+)"

SYSTEM VERILOG CHARACTER CLASSES

Is a character whitespace? (SV 3.1a LRM A.9.4)
(Note that Verilog 2001 LRM section 2.2 -- but not its grammar -- also has \f)
(Also note that we include \r for Windows compatibility)

> isWhitespace :: Char -> Bool
> isWhitespace ' ' = True; isWhitespace '\t' = True; isWhitespace '\n' = True
> isWhitespace '\f' = True; isWhitespace '\r' = True; isWhitespace _ = False

> isHorizontalWhitespace :: Char -> Bool
> isHorizontalWhitespace ' ' = True; isHorizontalWhitespace '\t' = True
> isHorizontalWhitespace _ = False

Does a character start a valid identifier?

> isIdStart :: Char -> Bool
> isIdStart '_' = True -- might be faster as a full table
> isIdStart c   = isLetter c

Does a character continue a valid identifier?

> isIdChar :: Char -> Bool
> isIdChar '_' = True -- might be faster as a full table
> isIdChar '$' = True
> isIdChar c   = isLetter c || isDigit c

Is a character part of a valid operator?

> isSymChar :: Char -> Bool
> isSymChar '!' = True; isSymChar '%' = True; isSymChar '&' = True
> isSymChar '*' = True; isSymChar '+' = True; isSymChar '-' = True
> isSymChar '/' = True; isSymChar '<' = True; isSymChar '>' = True
> isSymChar '=' = True; isSymChar '?' = True; isSymChar '^' = True
> isSymChar '|' = True; isSymChar '~' = True; isSymChar '.' = True
> isSymChar '(' = True; isSymChar ')' = True; isSymChar ',' = True
> isSymChar '[' = True; isSymChar ']' = True; isSymChar ';' = True
> isSymChar '{' = True; isSymChar '}' = True; isSymChar '#' = True
> isSymChar '`' = True; isSymChar ':' = True; isSymChar '\'' = True
> isSymChar _ = False

Is a character a decimal digit or an underscore?

> isDecDigitOr_ :: Char -> Bool
> isDecDigitOr_ '_' = True
> isDecDigitOr_ d = isDigit d

Is a character a binary digit, undefined (x), high-impedance (z, ?), or _?

> isBinXZ_ :: Char -> Bool
> isBinXZ_ '0' = True; isBinXZ_ '1' = True; isBinXZ_ 'X' = True
> isBinXZ_ 'x' = True; isBinXZ_ 'Z' = True; isBinXZ_ 'z' = True
> isBinXZ_ '?' = True; isBinXZ_ '_' = True; isBinXZ_ _   = False

Is a character an undefined (x) or high-impedance (z, ?) digit?

> isXorZ :: Char -> Bool
> isXorZ 'X' = True; isXorZ 'x' = True; isXorZ 'Z' = True; isXorZ 'z' = True;
> isXorZ '?' = True; isXorZ _ = False

Turn a binary digit into a SystemVerilog bit

> readBit :: Char -> SV_Bit
> readBit '0' = SV_BIT_0; readBit '1' = SV_BIT_1;
> readBit 'x' = SV_BIT_X; readBit 'X' = SV_BIT_X;
> readBit 'z' = SV_BIT_Z; readBit 'Z' = SV_BIT_Z;
> readBit '?' = SV_BIT_DontCare;
> readBit c = internalError ("readBit: can't read \"" ++ [c] ++ "\"")

Turn an octal digit into SystemVerilog bits

> octToBits :: Char -> [SV_Bit]
> octToBits '0' = map readBit "000"; octToBits '1' = map readBit "001"
> octToBits '2' = map readBit "010"; octToBits '3' = map readBit "011"
> octToBits '4' = map readBit "100"; octToBits '5' = map readBit "101"
> octToBits '6' = map readBit "110"; octToBits '7' = map readBit "111"
> octToBits 'X' = map readBit "XXX"; octToBits 'x' = map readBit "xxx"
> octToBits 'Z' = map readBit "ZZZ"; octToBits 'z' = map readBit "zzz"
> octToBits '?' = map readBit "???"
> octToBits d = internalError ("octToBits: \""++[d]++"\" not an octal digit")

Turn a hex digit into SystemVerilog bits

> hexToBits :: Char -> [SV_Bit]
> hexToBits '0' = map readBit "0000"; hexToBits '1' = map readBit "0001"
> hexToBits '2' = map readBit "0010"; hexToBits '3' = map readBit "0011"
> hexToBits '4' = map readBit "0100"; hexToBits '5' = map readBit "0101"
> hexToBits '6' = map readBit "0110"; hexToBits '7' = map readBit "0111"
> hexToBits '8' = map readBit "1000"; hexToBits '9' = map readBit "1001"
> hexToBits 'a' = map readBit "1010"; hexToBits 'b' = map readBit "1011"
> hexToBits 'c' = map readBit "1100"; hexToBits 'd' = map readBit "1101"
> hexToBits 'e' = map readBit "1110"; hexToBits 'f' = map readBit "1111"
> hexToBits 'X' = map readBit "XXXX"; hexToBits 'x' = map readBit "xxxx"
> hexToBits 'Z' = map readBit "ZZZZ"; hexToBits 'z' = map readBit "zzzz"
> hexToBits '?' = map readBit "????"
> hexToBits d = internalError ("hexToBits: \""++[d]++"\" not a hex digit")

Turn a hex digit into an Integer

> digitToInteger :: Char -> Integer
> digitToInteger d | d >= '0' && d <= '9' = toInteger (ord d - ord '0')
>                  | d >= 'a' && d <= 'f' = 10 + toInteger (ord d - ord 'a')
>                  | d >= 'A' && d <= 'F' = 10 + toInteger (ord d - ord 'A')
>                  | otherwise = internalError ("digitToInt: \""++[d]++"\"")

distinguish real digits from X, Z, ?

> isSpecialDigit :: Char -> Bool
> isSpecialDigit d | (d == 'X' || d == 'x' ||
>                     d == 'Z' || d == 'z' ||
>                     d == '?') = True
> isSpecialDigit _ = False

group real digits together and special digits with themselves

> groupDigits :: String -> [String]
> groupDigits ds =
>     let digitEq d1 d2 | not (isSpecialDigit d1 || isSpecialDigit d2) = True
>         digitEq d1 d2 = (d1 == d2)
>     in  groupBy digitEq ds

UTILITY FUNCTIONS

Eat n characters of input, updating the position

> eatChars :: Int -> ScannerState -> ScannerState
> eatChars 0 state = state
> eatChars n (ScannerState (pos, c:input)) =
>     eatChars (n-1) (ScannerState (updatePosChar pos c, input))
> eatChars n (ScannerState (pos, "")) =
>     internalError ("eatChars " ++ show n ++ ": no input left")

Eat input characters while they match a predicate

 > eatCharsWhile :: (Char -> Bool) -> ScannerState -> ScannerState
 > eatCharsWhile isEdible state@(ScannerState (pos, "")) = state
 > eatCharsWhile isEdible state@(ScannerState (pos, c:restOfInput))
 >     | isEdible c = (eatCharsWhile isEdible
 >                     (ScannerState (updatePosChar pos c, restOfInput)))
 >     | otherwise = state


NUMBERS AND TIMESCALES

Scan some decimal digits, and subsequent non-newline whitespace.  they could be
  - a standalone integer
  - a bitsize for a base constant
  - a whole-number part of a real number

> scanNumber :: Scanner
> scanNumber (ScannerState (pos, input)) =
>     let (digits, wsAndRest) = span isDecDigitOr_ input
>         (whitespace, restOfInput) = span isHorizontalWhitespace wsAndRest
>         original = digits ++ whitespace
>         nextPos = updatePosString (updatePosString pos digits) whitespace
>     in  scanNumberWith pos digits (not (null whitespace)) original
>             (ScannerState (nextPos, restOfInput))

Utility functions for confirming that more digits follow

> areMoreDigits :: String -> Bool
> areMoreDigits (d:_) | isDigit d = True
> areMoreDigits ('_':rest) = areMoreDigits rest
> areMoreDigits _ = False

> areMoreSignedDigits :: String -> Bool
> areMoreSignedDigits (s:rest) | (s == '+' || s == '-') = areMoreDigits rest
> areMoreSignedDigits ds = areMoreDigits ds

Scan parts of a number following the first, if any;
input must start with non-whitespace

> scanNumberWith :: Position -- where the number starts
>                -> String   -- digits of first number parsed
>                -> Bool     -- was there whitespace after the number?
>                -> String   -- characters scanned so far
>                -> Scanner  -- resulting scanner
> -- decimal point after no space -- scan fractional part and try exponent
> scanNumberWith initPos preDigits False origSoFar (ScannerState (pos, '.':input))
>     | areMoreDigits input =
>     let (postDigits, restOfInput) = span isDecDigitOr_ input
>         nextOrig = origSoFar ++ ('.':postDigits)
>         nextState = ScannerState (updatePosString pos ('.':postDigits),
>                                   restOfInput)
>     in  scanRealExponent initPos preDigits postDigits nextOrig nextState
> -- exponent after no space -- scan the exponent
> scanNumberWith initPos digits False origSoFar state@(ScannerState (pos, c:_))
>     | c == 'e' || c == 'E' = scanRealExponent initPos digits "0" origSoFar state
> -- numeric bases
> scanNumberWith initPos widthDigits hadWS origSoFar
>                    (ScannerState (pos, '\'':char1:char2:rest))
>     | base `elem` "dboh" = -- decimal, binary, octal, or hex base
>         let width = readDecDigitsAnd_ widthDigits
>             (tconsumedChars, wsrestOfInput) = if signed
>                                              then (['\'',char1,char2], rest)
>                                              else (['\'',char1], char2:rest)
>             --removes whitespace between base and number
>             (ws,restOfInput) = span isHorizontalWhitespace wsrestOfInput
>             consumedChars = tconsumedChars++ws
>             newPos = updatePosString pos consumedChars
>             nextState = ScannerState (newPos, restOfInput)
>             orig = origSoFar ++ consumedChars
>         in  scanBasedNumber initPos (Just width) orig signed base nextState
>     where signed = char1 == 's' || char1 == 'S'
>           base = toLower (if signed then char2 else char1)
> -- nothing interesting follows; return the integer
> scanNumberWith initPos digits hadWS origText state@(ScannerState (pos, _)) =
>     let num = readDecDigitsAnd_ digits
>         token = SV_Token_Number { start_position = initPos,
>                                   end_position = updatePosBackspace pos,
>                                   value = SV_NUM_Integer num,
>                                   bitwidth = Nothing,
>                                   base = Nothing,
>                                   signed = False,
>                                   originalText = origText }
>     in  token : scanMain state

Scan a number after a base specifier; the base specifier is always lowercase

> scanBasedNumber :: Position      -- init position
>                 -> Maybe Integer -- bit width, if specified
>                 -> String        -- text of token scanned so far
>                 -> Bool          -- true iff number is signed ('s/'S)
>                 -> Char          -- base: 'd', 'b', 'o', or 'h'
>                 -> Scanner       -- the scanner, i.e., state -> tokens
> -- decimal X, x, Z, z, with underscores
> scanBasedNumber initPos width origSoFar sign 'd'
>                     (ScannerState (pos, input@(c:rest)))
>     | isXorZ c =
>         let (underscores, restOfInput) = span (== '_') rest
>             (end_pos,next_pos) = posAtEndAndAfterString pos (c:underscores)
>             origText = origSoFar ++ (c:underscores)
>             number = SV_NUM_Repeated (readBit c)
>             token = SV_Token_Number { start_position = initPos,
>                                       end_position = end_pos,
>                                       value = number,
>                                       bitwidth = width,
>                                       base = Just SV_NUM_BASE_Dec,
>                                       signed = sign,
>                                       originalText = origText }
>         in  token : scanMain (ScannerState (next_pos, restOfInput))
> -- decimal with no Xs or Zs
> scanBasedNumber initPos width origSoFar sign 'd' state =
>         let -- not used because acceptXZ is false
>             decToBitsErr d = internalError ("scanBasedNumber: \"" ++ [d] ++
>                                             "\" in decimal number")
>         in  (scanBasedNumberCommon initPos width origSoFar sign
>              SV_NUM_BASE_Dec False isDigit decToBitsErr state)
> -- binary
> scanBasedNumber initPos width origSoFar sign 'b' state =
>     let isBinDigit '0' = True; isBinDigit '1' = True; isBinDigit _ = False
>         binToBits = (:[]) . readBit
>     in  (scanBasedNumberCommon initPos width origSoFar sign
>          SV_NUM_BASE_Bin True isBinDigit binToBits state)
> -- octal
> scanBasedNumber initPos width origSoFar sign 'o' state =
>     (scanBasedNumberCommon initPos width origSoFar sign
>      SV_NUM_BASE_Oct True isOctDigit octToBits state)
> -- hexadecimal
> scanBasedNumber initPos width origSoFar sign 'h' state =
>     (scanBasedNumberCommon initPos width origSoFar sign
>      SV_NUM_BASE_Hex True isHexDigit (hexToBits . toLower) state)
> scanBasedNumber _       _     _         _    base _ =
>     internalError ("SystemVerilogScanner.scanBasedNumber: unknown base \""
>                    ++ [base] ++ "\"")

Given base, a digit tester, and a digit converter, scan a number of any base

> scanBasedNumberCommon :: Position           -- position of start of number
>                       -> Maybe Integer      -- width, if specified
>                       -> String             -- text of token scanned so far
>                       -> Bool               -- specified as signed?
>                       -> SV_Numeric_Base    -- number base
>                       -> Bool               -- accept X or Z as digits?
>                       -> (Char -> Bool)     -- acceptable digit test
>                       -> (Char -> [SV_Bit]) -- turn digit to bits
>                       -> Scanner            -- resulting scanner
> scanBasedNumberCommon initPos width origSoFar sign svBase acceptXZ isDigit
>                       digitToBits (ScannerState (pos, input)) =
>     let isOkDigit '_' = True
>         isOkDigit d = isDigit d || (acceptXZ && d `elem` "xXzZ?")
>         (digits, restOfInput) = span isOkDigit input
>         (end_pos, next_pos) = posAtEndAndAfterString pos digits
>         numericDigits = [d | d <- digits, d /= '_']
>         baseVal = svNumericBaseValue svBase
>         mkNum = foldl (\sofar d -> baseVal * sofar + digitToInteger d) 0
>         -- XXX error out if numericDigits = ""
>         num = if any (not . isDigit) numericDigits -- any funky digits?
>               then let grouped_digits = groupDigits numericDigits
>                        mkPair ds@(d:_) | isSpecialDigit d =
>                            case (digitToBits d) of
>                                (b:_) -> (genericLength ds, Right b)
>                                _ -> internalError ("scanBasedNumberCommon: "
>                                                    ++ "no digits")
>                        mkPair ds = (genericLength ds, Left (mkNum ds))
>                    in  SV_NUM_Mixed (map mkPair grouped_digits)
>               else SV_NUM_Integer (mkNum numericDigits)
>         token = SV_Token_Number { start_position = initPos,
>                                   end_position = end_pos,
>                                   value = num,
>                                   bitwidth = width,
>                                   base = Just svBase,
>                                   signed = sign,
>                                   originalText = origSoFar ++ digits }
>     in  token : scanMain (ScannerState (next_pos, restOfInput))

Scan the exponent of a real number, if any

> scanRealExponent :: Position     -- position of start of number
>                  -> String       -- whole part of the number
>                  -> String       -- fractional part of the number
>                  -> String       -- text of token scanned so far
>                  -> Scanner      -- resulting scanner
> scanRealExponent initPos whole fractional origSoFar
>                        (ScannerState (pos, e:input))
>     | (e == 'e' || e == 'E') -- exponent present
>       && (areMoreSignedDigits input) =
>         let (signChars, inputAfterSign) =
>                 case input of
>                 ('+':rest) -> ("+",rest)
>                 ('-':rest) -> ("-",rest)
>                 _          -> ("",input)
>             (expDigits, restOfInput) = span isDecDigitOr_ inputAfterSign
>             consumedChars = e:(signChars ++ expDigits)
>             (end_pos, next_pos) = posAtEndAndAfterString pos consumedChars
>             -- put it all together
>             floatChars = whole ++ "." ++ fractional ++ consumedChars
>             -- XXX since "readFloat" can take forever on large exponents
>             -- XXX we special case for large exponents
>             num = let e = readDecDigitsAnd_ expDigits
>                   in  if (e > 100000)
>                       then if signChars == "-"
>                            then 0     -- zero
>                            else 1/0 -- Infinity
>                       else readFloatDigitsAnd_ floatChars
>             origText = origSoFar ++ consumedChars
>             token = SV_Token_Number { start_position = initPos,
>                                       end_position = end_pos,
>                                       value = SV_NUM_Real num,
>                                       signed = False,
>                                       bitwidth = Nothing,
>                                       base = Nothing,
>                                       originalText = origText }
>         in  token : scanMain (ScannerState (next_pos, restOfInput))
> scanRealExponent initPos whole fractional origText
>                  state@(ScannerState (pos,_)) =
>     let -- put it all together
>         floatChars = whole ++ "." ++ fractional
>         number = SV_NUM_Real (readFloatDigitsAnd_ floatChars)
>         token = SV_Token_Number { start_position = initPos,
>                                   end_position = updatePosBackspace pos,
>                                   value = number,
>                                   signed = False,
>                                   bitwidth = Nothing,
>                                   base = Nothing,
>                                   originalText = origText }
>     in  token : scanMain state

Strip underscores and convert remaining decimal digits to an Integer

> readDecDigitsAnd_ :: String -> Integer
> readDecDigitsAnd_ digits =
>     case readDec [d | d <- digits, d /= '_'] of
>     [(num, "")] -> num
>     [] -> internalError ("readDecDigitsAnd_: no parses of \""
>                          ++ digits ++ "\"")
>     ps -> internalError ("readDecDigitsAnd_: multiple parses of \"" ++ digits
>                          ++ "\": " ++ show ps)

Strip underscores and convert remaining characters to a Double
(may include a decimal place and a signed exponent)

> readFloatDigitsAnd_ :: String -> Double
> readFloatDigitsAnd_ digits =
>     case readFloat [d | d <- digits, d /= '_'] of
>     [(num, "")] -> num
>     [] -> internalError ("readDecDigitsAnd_: no parses of \""
>                          ++ digits ++ "\"")
>     ps -> internalError ("readDecDigitsAnd_: multiple parses of \"" ++ digits
>                          ++ "\": " ++ show ps)
