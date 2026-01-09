module SignalNaming (signalNameFromAExpr) where

import Data.List
import Data.Char
import Text.Regex

import ASyntax
import Prim
import ErrorUtil(internalError)
import PPrint
import Id
import PreIds
import Util(itos)

-- remember to allow a few characters for __d3222 etc suffix
signal_length_limit :: Int
signal_length_limit = 50

signalNameFromAExpr :: AExpr -> String
signalNameFromAExpr expr =
    let orig_name = signalNameFromAExpr' expr
        name | length orig_name < signal_length_limit = orig_name
             | otherwise = take (signal_length_limit - 4) orig_name ++ "_ETC"
        dropBadChars str = [c | c <- str, not (c `elem` "$.'")]
        escapeBadStart signal@(c:_) | c `elem` ['0'..'9'] = '_':signal
        escapeBadStart signal = signal
    in  escapeBadStart (dropBadChars name)

signalNameFromAExpr' :: AExpr -> String
signalNameFromAExpr' (expr@APrim { aprim_prim = PrimZeroExt,
                                   ae_args = [arg] }) =
    signalNameFromAExpr' arg
signalNameFromAExpr' (expr@APrim { aprim_prim = PrimSignExt,
                                   ae_args = [arg] }) =
    "SEXT_" ++ signalNameFromAExpr' arg
signalNameFromAExpr' (expr@APrim { aprim_prim = PrimExtract,
                                   ae_args = [arg,hi,lo] })
    | hi == lo =
        connectWith "_BIT_" [signalNameFromAExpr' arg, signalNameFromAExpr' hi]
    | otherwise =
        connectWith "_BITS_" [signalNameFromAExpr' arg,
                              connectWith "_TO_" [signalNameFromAExpr' hi,
                                                  signalNameFromAExpr' lo]]
signalNameFromAExpr' (expr@APrim { aprim_prim = PrimIf,
                                   ae_args = [arg,hi,lo] }) =
    "IF_" ++
    connectWith "_THEN_"
    [signalNameFromAExpr' arg,
     connectWith "_ELSE_" [signalNameFromAExpr' hi, signalNameFromAExpr' lo]]
-- put PrimCase default last (to avoid "DONTCARE" being early in the name)
signalNameFromAExpr' (APrim { aprim_prim = PrimCase,
                              ae_args = (idx:dflt:ces) }) =
    "CASE_" ++
    connectWith "_" (map signalNameFromAExpr' ((idx:ces) ++ [dflt]))
signalNameFromAExpr' (expr@APrim { aprim_prim = prim })
    | binOp prim =
        connectWith ("_" ++ opToString prim ++ "_")
                        (map signalNameFromAExpr' (ae_args expr))
    | otherwise = opToString prim ++ "_" ++
                  connectWith "_" (map signalNameFromAExpr' (ae_args expr))
-- omit "_read" on register reads
signalNameFromAExpr' (expr@AMethCall { })
    | ameth_id expr == idPreludeRead && null (ae_args expr) =
        ppString (ae_objid expr)
signalNameFromAExpr' (expr@AMethCall { }) =
    ppString (ae_objid expr) ++ "_" ++
    ppString (unQualId (ameth_id expr)) ++ "_" ++
    connectWith "_" (map signalNameFromAExpr' (ae_args expr))
signalNameFromAExpr' (expr@AMethValue { }) =
    ppString (ae_objid expr) ++ "_" ++ ppString (unQualId (ameth_id expr))
signalNameFromAExpr' (expr@ATuple { }) =
    "TUPLE_" ++
    connectWith "_" (map signalNameFromAExpr' (ae_elems expr))
signalNameFromAExpr' (expr@ATupleSel { }) =
    signalNameFromAExpr' (ae_exp expr) ++
    "_" ++ itos (ae_index expr)
signalNameFromAExpr' (expr@ANoInlineFunCall { }) =
    -- use the identifier name (it is the user-known function name);
    -- the string in ANoInlineFun is the module name
    -- (don't complicate things with the argument list;
    -- the unique prefix at the end will be enough)
    ppString (unQualId (ae_objid expr))
signalNameFromAExpr' (expr@AFunCall { ae_funname = fun_name }) =
    fun_name ++ "_" ++
    connectWith "_" (map signalNameFromAExpr' (ae_args expr))
signalNameFromAExpr' (expr@ATaskValue { ae_funname = fun_name }) =
    "TASK_" ++ fun_name
signalNameFromAExpr' (expr@ASPort { }) =
    dropGeneratedSuffixes (ppString (ae_objid expr))
signalNameFromAExpr' (expr@ASParam { }) =
    dropGeneratedSuffixes (ppString (ae_objid expr))
signalNameFromAExpr' (expr@ASDef { }) =
    dropGeneratedSuffixes (ppString (ae_objid expr))
signalNameFromAExpr' (expr@ASInt { }) =
    dropGeneratedSuffixes (ppString (ae_ival expr))
signalNameFromAExpr' (expr@ASReal { }) =
    -- replace decimal point with 'd'
    -- replace negative sign with 'neg' (for example in "1e-2")
    dropGeneratedSuffixes (sanitize (ppString (ae_rval expr)))
    where sanitize "" = ""
          sanitize ('.':cs) = 'd' : sanitize cs
          sanitize ('-':cs) = 'n' : 'e' : 'g' : sanitize cs
          sanitize (c:cs) = c : sanitize cs
signalNameFromAExpr' (expr@ASStr { }) =
    dropGeneratedSuffixes ("STR_" ++ sanitize (ae_strval expr))
    where sanitize "" = ""
          sanitize (c:cs) | isAlphaNum c = c : sanitize cs
                          | isSpace c = '_' : sanitize cs
                          | otherwise = sanitize cs
signalNameFromAExpr' (expr@ASAny { }) = "DONTCARE"
signalNameFromAExpr' (expr@ASClock { }) =
    internalError "SignalNaming.signalNameFromAExpr': ASClock"
signalNameFromAExpr' (expr@ASReset { }) =
    internalError "SignalNaming.signalNameFromAExpr': ASReset"
signalNameFromAExpr' (expr@ASInout { }) =
    internalError "SignalNaming.signalNameFromAExpr': ASInout"
signalNameFromAExpr' (expr@AMGate { }) =
    ppString (ae_objid expr) ++ "_" ++
    ppString (unQualId (ae_clkid expr)) ++ "_" ++ "GATE"

-- XXX assumes that "__[a-z][0-9]*" suffices are compiler-generated
dropGeneratedSuffixes :: String -> String
dropGeneratedSuffixes =
    let generated_suffix = mkRegex "__[a-z][0-9]"
    in  \name -> concat (splitRegex generated_suffix name)

opToString :: PrimOp -> String
opToString PrimAdd = "PLUS"
opToString PrimSub = "MINUS"
opToString PrimBAnd = "AND"
opToString PrimBOr = "OR"
opToString PrimBNot = "NOT"
opToString PrimBuildArray = "ARR"
opToString PrimArrayDynSelect = "SEL"
opToString op = map toUpper $
                case show op of
                ('P':'r':'i':'m':rest) -> rest
                all -> all

connectWith :: String -> [String] -> String
connectWith connector =
    let rm_s = reverse . dropWhile (== '_') . reverse . dropWhile (== '_')
    in  intercalate connector . map rm_s
