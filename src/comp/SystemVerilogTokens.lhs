> {-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fno-warn-name-shadowing #-}

Token types: representation passed from the scanner to the parser

> module SystemVerilogTokens(SV_Token(..), SV_Bit(..), SV_Number(..),
>                            SV_Numeric_Base(..), svNumericBaseValue,
>                            svTokenToString) where

> import Position
> import Error(internalError, ErrMsg)
> import SystemVerilogKeywords
> import Util(quote)
> import PPrint
> import Eval

Tokens output by the lexical scanner

> data SV_Token
>     -- reserved keyword (e.g., "begin", "function")
>     = SV_Token_Keyword      { start_position :: Position,
>                               end_position :: Position,
>                               keyword :: SV_Keyword }
>     -- identifier (e.g., "foo", "\-=foo=-")
>     | SV_Token_Id           { start_position :: Position,
>                               end_position :: Position,
>                               name :: String }
>     -- system identifier (e.g., "$display", "$foobar"); name including $
>     | SV_Token_System_Id    { start_position :: Position,
>                               end_position :: Position,
>                               name :: String }
>     -- reserved operator (e.g., "==", "&&")
>     | SV_Token_Symbol       { start_position :: Position,
>                               end_position :: Position,
>                               symbol :: SV_Symbol }
>     -- compiler directive, e.g., `timescale; name including `
>     | SV_Token_Directive    { start_position :: Position,
>                               end_position :: Position,
>                               name :: String }
>     | SV_Token_Number       { start_position :: Position,
>                               end_position :: Position,
>                               value :: SV_Number,        -- numeric value
>                               bitwidth :: Maybe Integer, -- if specified
>                               base :: Maybe SV_Numeric_Base, -- if specified
>                               signed :: Bool,            -- 's or 'S (signed)
>                               originalText :: String }   -- from source
>     -- string, not including quotation marks
>     | SV_Token_String       { start_position :: Position,
>                               end_position :: Position,
>                               contents :: String }
>     -- comment, not including // or /* .. */
>     | SV_Token_Comment      { start_position :: Position,
>                               end_position :: Position,
>                               isBlock :: Bool,
>                               contents :: String }
>     | SV_Token_Error        { start_position :: Position,
>                               end_position :: Position,
>                               errMessage :: ErrMsg }
>       deriving (Show)

> instance PPrint SV_Token where
>   pPrint d p = text . show

> instance NFData SV_Token where
>   rnf svt = rnf (show svt)

Bit representation for number parsing

> data SV_Bit = SV_BIT_0 | SV_BIT_1 |
>               SV_BIT_X | SV_BIT_Z | SV_BIT_DontCare
>       deriving (Show)

Possible bases used in number parsing

> data SV_Numeric_Base
>     = SV_NUM_BASE_Bin
>     | SV_NUM_BASE_Oct
>     | SV_NUM_BASE_Dec
>     | SV_NUM_BASE_Hex
>       deriving (Show)

> {-# SPECIALIZE svNumericBaseValue :: SV_Numeric_Base -> Integer #-}
> {-# SPECIALIZE svNumericBaseValue :: SV_Numeric_Base -> Int #-}
> svNumericBaseValue :: (Num num) => SV_Numeric_Base -> num
> svNumericBaseValue SV_NUM_BASE_Bin = 2
> svNumericBaseValue SV_NUM_BASE_Oct = 8
> svNumericBaseValue SV_NUM_BASE_Dec = 10
> svNumericBaseValue SV_NUM_BASE_Hex = 16

Various forms of values that can be specified as literals:

> data SV_Number
>     -- non-negative whole numbers
>     = SV_NUM_Integer Integer
>     -- non-negative real numbers
>     | SV_NUM_Real Double
>     -- repeated bit (e.g., '0 or 'x)
>     | SV_NUM_Repeated SV_Bit
>     -- value/pattern with some bits set to x or z (e.g., 'h00x0)
>     -- grouped into values along with the number of digits, starting
>     -- with the most significant bit
>     | SV_NUM_Mixed [(Integer, Either Integer SV_Bit)]
>       deriving (Show)

Pretty print SV tokens, e.g., keyword "end", symbol "&"

> svTokenToString :: SV_Token -> String
> svTokenToString (SV_Token_Keyword { keyword = kw }) =
>     let (desc, ver) = (lookupDescAndVer kw svKeywordTable)
>         verdesc = case ver of
>                   Verilog2001 -> "V2K"
>                   SystemVerilog30 -> "SV 3.0"
>                   SystemVerilog31 -> "SV 3.1"
>                   SystemVerilog31a -> "SV 3.1a"
>                   Bluespec38 -> "BSV 3.8"
>                   -- _ -> "internal"
>     in  verdesc ++ " keyword " ++ quote desc
> svTokenToString (SV_Token_Id { name = nm }) =
>     "identifier " ++ quote nm
> svTokenToString (SV_Token_System_Id { name = nm }) =
>     "identifier " ++ quote nm
> svTokenToString (SV_Token_Symbol { symbol = sym }) =
>     quote (lookupDesc sym svSymbolTable)
> svTokenToString (SV_Token_Directive { name = dir }) =
>     "directive " ++ quote dir
> svTokenToString (SV_Token_Number { originalText = num }) =
>     "number " ++ quote num
> svTokenToString (SV_Token_String { contents = str }) =
>     "string " ++ quote str
> svTokenToString (SV_Token_Comment { isBlock = False, contents = txt }) =
>     "comment //" ++ txt
> svTokenToString (SV_Token_Comment { isBlock = True, contents = txt }) =
>     "comment /*" ++ txt ++ "*/"
> svTokenToString (SV_Token_Error { start_position = pos, errMessage = emsg }) =
>     "error" -- unsafeMessageExit serror [(pos, emsg)]

Find a description of a symbol or a keyword in a table
from SystemVerilogKeywords.lhs

> lookupDesc :: Eq key => key -> [(key, String, anything)] -> String
> lookupDesc key table =
>     case [s | (k, s, _) <- table, k == key] of
>     [desc] -> desc
>     [] -> internalError "SystemVerilogTokens.lookupDesc: no description"
>     _  -> internalError
>           "SystemVerilogTokens.lookupDesc: multiple descriptions"

> lookupDescAndVer :: Eq key => key -> [(key, String, SV_Version)]
>                  -> (String, SV_Version)
> lookupDescAndVer key table =
>     case [(s, v) | (k, s, v) <- table, k == key] of
>     [desc] -> desc
>     [] -> internalError "SystemVerilogTokens.lookupDesc: no description"
>     _  -> internalError
>           "SystemVerilogTokens.lookupDesc: multiple descriptions"
