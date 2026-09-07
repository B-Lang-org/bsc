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

-- The Bool selects how many digits a compiler-generated suffix may have;
-- see dropGeneratedSuffixes.
signalNameFromAExpr :: Bool -> AExpr -> String
signalNameFromAExpr multidigit expr =
    let orig_name = signalNameFromAExpr' multidigit expr
        name | length orig_name < signal_length_limit = orig_name
             | otherwise = take (signal_length_limit - 4) orig_name ++ "_ETC"
        dropBadChars str = [c | c <- str, not (c `elem` "$.'")]
        escapeBadStart signal@(c:_) | c `elem` ['0'..'9'] = '_':signal
        escapeBadStart signal = signal
    in  escapeBadStart (dropBadChars name)

signalNameFromAExpr' :: Bool -> AExpr -> String
signalNameFromAExpr' multidigit (expr@APrim { aprim_prim = PrimZeroExt,
                                              ae_args = [arg] }) =
    signalNameFromAExpr' multidigit arg
signalNameFromAExpr' multidigit (expr@APrim { aprim_prim = PrimSignExt,
                                              ae_args = [arg] }) =
    "SEXT_" ++ signalNameFromAExpr' multidigit arg
signalNameFromAExpr' multidigit (expr@APrim { aprim_prim = PrimExtract,
                                              ae_args = [arg,hi,lo] })
    | hi == lo =
        connectWith "_BIT_" [signalNameFromAExpr' multidigit arg,
                             signalNameFromAExpr' multidigit hi]
    | otherwise =
        connectWith "_BITS_" [signalNameFromAExpr' multidigit arg,
                              connectWith "_TO_"
                                  [signalNameFromAExpr' multidigit hi,
                                   signalNameFromAExpr' multidigit lo]]
signalNameFromAExpr' multidigit (expr@APrim { aprim_prim = PrimIf,
                                              ae_args = [arg,hi,lo] }) =
    "IF_" ++
    connectWith "_THEN_"
    [signalNameFromAExpr' multidigit arg,
     connectWith "_ELSE_" [signalNameFromAExpr' multidigit hi,
                           signalNameFromAExpr' multidigit lo]]
-- put PrimCase default last (to avoid "DONTCARE" being early in the name)
signalNameFromAExpr' multidigit (APrim { aprim_prim = PrimCase,
                                         ae_args = (idx:dflt:ces) }) =
    "CASE_" ++
    connectWith "_" (map (signalNameFromAExpr' multidigit)
                         ((idx:ces) ++ [dflt]))
signalNameFromAExpr' multidigit (expr@APrim { aprim_prim = prim })
    | binOp prim =
        connectWith ("_" ++ opToString prim ++ "_")
                        (map (signalNameFromAExpr' multidigit) (ae_args expr))
    | otherwise = opToString prim ++ "_" ++
                  connectWith "_"
                      (map (signalNameFromAExpr' multidigit) (ae_args expr))
-- omit "_read" on register reads
signalNameFromAExpr' multidigit (expr@AMethCall { })
    | ameth_id expr == idPreludeRead && null (ae_args expr) =
        ppString (ae_objid expr)
signalNameFromAExpr' multidigit (expr@AMethCall { }) =
    ppString (ae_objid expr) ++ "_" ++
    ppString (unQualId (ameth_id expr)) ++ "_" ++
    connectWith "_" (map (signalNameFromAExpr' multidigit)
                         (concatMap argPorts (ae_args expr)))
  where argPorts (ATuple _ es) = es
        argPorts e             = [e]
signalNameFromAExpr' multidigit (expr@AMethValue { }) =
    ppString (ae_objid expr) ++ "_" ++ ppString (unQualId (ameth_id expr))
signalNameFromAExpr' multidigit (expr@ATuple { }) =
    "TUPLE_" ++
    connectWith "_" (map (signalNameFromAExpr' multidigit) (ae_elems expr))
signalNameFromAExpr' multidigit (expr@ATupleSel { }) =
    signalNameFromAExpr' multidigit (ae_exp expr) ++
    "_SEL_" ++ itos (ae_index expr)
signalNameFromAExpr' multidigit (expr@ANoInlineFunCall { }) =
    -- use the identifier name (it is the user-known function name);
    -- the string in ANoInlineFun is the module name
    -- (don't complicate things with the argument list;
    -- the unique prefix at the end will be enough)
    ppString (unQualId (ae_objid expr))
signalNameFromAExpr' multidigit (expr@AFunCall { ae_funname = fun_name }) =
    fun_name ++ "_" ++
    connectWith "_" (map (signalNameFromAExpr' multidigit) (ae_args expr))
signalNameFromAExpr' multidigit (expr@ATaskValue { ae_funname = fun_name }) =
    "TASK_" ++ fun_name
signalNameFromAExpr' multidigit (expr@ASPort { }) =
    dropGeneratedSuffixes multidigit (ppString (ae_objid expr))
signalNameFromAExpr' multidigit (expr@ASParam { }) =
    dropGeneratedSuffixes multidigit (ppString (ae_objid expr))
signalNameFromAExpr' multidigit (expr@ASDef { }) =
    dropGeneratedSuffixes multidigit (ppString (ae_objid expr))
signalNameFromAExpr' multidigit (expr@ASInt { }) =
    dropGeneratedSuffixes multidigit (ppString (ae_ival expr))
signalNameFromAExpr' multidigit (expr@ASReal { }) =
    -- replace decimal point with 'd'
    -- replace negative sign with 'neg' (for example in "1e-2")
    dropGeneratedSuffixes multidigit (sanitize (ppString (ae_rval expr)))
    where sanitize "" = ""
          sanitize ('.':cs) = 'd' : sanitize cs
          sanitize ('-':cs) = 'n' : 'e' : 'g' : sanitize cs
          sanitize (c:cs) = c : sanitize cs
signalNameFromAExpr' multidigit (expr@ASStr { }) =
    dropGeneratedSuffixes multidigit ("STR_" ++ sanitize (ae_strval expr))
    where sanitize "" = ""
          sanitize (c:cs) | isAlphaNum c = c : sanitize cs
                          | isSpace c = '_' : sanitize cs
                          | otherwise = sanitize cs
signalNameFromAExpr' multidigit (expr@ASAny { }) = "DONTCARE"
signalNameFromAExpr' multidigit (expr@ASClock { }) =
    internalError "SignalNaming.signalNameFromAExpr': ASClock"
signalNameFromAExpr' multidigit (expr@ASReset { }) =
    internalError "SignalNaming.signalNameFromAExpr': ASReset"
signalNameFromAExpr' multidigit (expr@ASInout { }) =
    internalError "SignalNaming.signalNameFromAExpr': ASInout"
signalNameFromAExpr' multidigit (expr@AMGate { }) =
    ppString (ae_objid expr) ++ "_" ++
    ppString (unQualId (ae_clkid expr)) ++ "_" ++ "GATE"

-- XXX assumes that "__[a-z][0-9]+" suffixes are compiler-generated.
-- There was a bug where the regex accepted only a single digit. The fix
-- is restricted to when multidigit is True, and this is determined by the
-- -stable-verilog flag setting. The reason to keep the broken regex around
-- is to preserve the signal names in existing generated Verilog. Since
-- the -stable-verilog setting changes those names, the regex fix is allowed
-- as part of that renaming. Otherwise, it is assumed that it is better to
-- keep the names stable even if they have extra digits embedded in them.
dropGeneratedSuffixes :: Bool -> String -> String
dropGeneratedSuffixes multidigit =
    let generated_suffix = mkRegex $ if multidigit
                                     then "__[a-z][0-9]+"
                                     else "__[a-z][0-9]"
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
