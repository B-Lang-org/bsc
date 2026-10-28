module Main where

import Control.Monad (unless)
import qualified Data.Set as S
import APrimitiveSourceTypes (propagatePrimitiveTypes)
import AConditionalSourceTypes (propagateConditionalTypes)
import ASyntax
import CType (TISort(..))
import Id (mk_homeless_id, setIdQualString)
import IntLit (ilDec)
import ISyntax (IType(..), IKind(..))
import ISyntaxUtil (itBool)
import PreIds (idInt, idUInt)
import Prim (PrimOp(..))

name = mk_homeless_id
port w n = ASPort (ATBit w) (name n)
ref w n = ASDef (ATBit w) (name n)
def n w e = ADef (name n) (ATBit w) e []
prim w op = APrim defaultAId (ATBit w) op
lit w n = ASInt defaultAId (ATBit w) (ilDec n)
num con w = ITAp (ITCon con (IKFun IKNum IKStar) TIabstract) (ITNum w)
int = num idInt
uint = num idUInt
nominal = ITCon (setIdQualString (name "Record") "PrimitiveTypes") IKStar TIabstract
package ds observations = ASPackage {
    aspkg_name = name "PrimitiveFixture", aspkg_is_wrapped = False,
    aspkg_parameters = [], aspkg_outputs = [], aspkg_inputs = [], aspkg_inouts = [],
    aspkg_state_instances = [], aspkg_state_outputs = [],
    aspkg_values = ds, aspkg_inout_values = [], aspkg_foreign_calls = [],
    aspkg_inlined_ports = [],
    aspkg_signal_info = ASPSignalInfo [] [] [] [] [] [] [] [] [] [],
    aspkg_comment_info = ASPCommentInfo [] [], aspkg_expr_types = observations }
observe e ts = (e,S.fromList ts)
types pkg expression = S.unions [ts | (e,ts) <- aspkg_expr_types pkg, e == expression]
expect label pkg expression wanted = unless (types pkg expression == S.fromList wanted) $
    error (label ++ ": " ++ show (types pkg expression))
run ds observations = propagatePrimitiveTypes (package ds observations)
checkStable label original = do
    let result = propagatePrimitiveTypes original
    unless (result { aspkg_expr_types = [] } == original { aspkg_expr_types = [] }) $
        error (label ++ ": hardware changed")
    unless (propagatePrimitiveTypes result == result) $ error (label ++ ": not idempotent")
    unless (propagatePrimitiveTypes (original { aspkg_values = reverse (aspkg_values original),
                                               aspkg_expr_types = reverse (aspkg_expr_types original) })
               == result { aspkg_values = reverse (aspkg_values result) }) $
        error (label ++ ": traversal-order dependent")

main = do
    let a = port 8 "signedA"; b = port 8 "signedB"
        u = port 8 "unsignedA"; v = port 8 "unsignedB"
        eqA = port 8 "eqA"; eqB = port 8 "eqB"
        ds = [def "slt" 1 (prim 1 PrimSLT [a,b]),
              def "ult" 1 (prim 1 PrimULT [u,v]),
              def "eq" 1 (prim 1 PrimEQ [eqA,eqB]),
              def "logical" 1 (prim 1 PrimBAnd [port 1 "boolA",port 1 "boolB",port 1 "boolC"]),
              def "rawBitAnd" 1 (prim 1 PrimAnd [port 1 "bitA",port 1 "bitB"]),
              def "nested" 8 (prim 8 PrimIf [prim 1 PrimEQ [port 8 "nestA",port 8 "nestB"],port 8 "x",port 8 "y"])]
        result = run ds []
    mapM_ (\e -> expect "signed operands" result e [int 8]) [a,b]
    mapM_ (\e -> expect "unsigned operands" result e [uint 8]) [u,v]
    mapM_ (\n -> expect "Boolean result" result (ref 1 n) [itBool]) ["slt","ult","eq","logical"]
    mapM_ (\e -> expect "Boolean operands" result e [itBool]) [port 1 "boolA",port 1 "boolB",port 1 "boolC"]
    mapM_ (\e -> expect "untyped raw data" result e []) [eqA,eqB,ref 1 "rawBitAnd",port 1 "bitA",port 1 "bitB",port 8 "x"]
    expect "nested comparison" result (prim 1 PrimEQ [port 8 "nestA",port 8 "nestB"]) [itBool]
    unless (null (aspkg_expr_types (propagateConditionalTypes (package ds [])))) $ error "changed old API"
    checkStable "intrinsic" (package ds [])
    putStrLn "PASS: intrinsic semantic roles, nested traversal, and raw-bit exclusions"

    let a = port 8 "a"; b = port 8 "b"; unknown = port 8 "raw"
        ds = [def "sum" 8 (prim 8 PrimAdd [a,b]),
              def "neg" 8 (prim 8 PrimNeg [ref 8 "sum"]),
              def "mask" 8 (prim 8 PrimAnd [ref 8 "neg",lit 8 15]),
              def "mixed" 8 (prim 8 PrimAdd [a,unknown]),
              def "recordAdd" 8 (prim 8 PrimAdd [port 8 "record",lit 8 1]),
              def "choice" 8 (prim 8 PrimIf [port 1 "condition",ref 8 "mask",port 8 "sibling"])]
        observations = [observe a [int 8,uint 8], observe b [int 8,uint 8], observe (port 8 "record") [nominal]]
        result = run ds observations
    mapM_ (\n -> expect "numeric family union" result (ref 8 n) [int 8,uint 8]) ["sum","neg","mask","choice"]
    expect "selection sibling" result (port 8 "sibling") [int 8,uint 8]
    expect "not back-propagated into other arithmetic input" result unknown []
    expect "common-family requirement" result (ref 8 "mixed") []
    expect "nominal arithmetic is not numeric" result (ref 8 "recordAdd") []
    expect "private literal" result (lit 8 15) []
    checkStable "numeric union" (package ds observations)
    putStrLn "PASS: common numeric families, literal context, CSE/selection union, nominal boundary"

    let a = port 8 "intersectionA"; b = port 8 "intersectionB"; c = port 8 "intersectionC"
        ds = [def "common" 8 (prim 8 PrimAdd [a,b]), def "disjoint" 8 (prim 8 PrimAdd [b,c])]
        observations = [observe a [int 8,uint 8],observe b [uint 8],observe c [int 8]]
        result = run ds observations
    expect "asymmetric family intersection" result (ref 8 "common") [uint 8]
    expect "disjoint signedness is not invented" result (ref 8 "disjoint") []
    checkStable "asymmetric families" (package ds observations)
    putStrLn "PASS: asymmetric intersection and disjoint numeric families"

    let a = port 8 "shiftData"; count = port 3 "shiftCount"
        ds = [def "sra" 8 (prim 8 PrimSRA [a,count]),
              def "srl" 8 (prim 8 PrimSRL [port 8 "logicalData",port 3 "logicalCount"]),
              def "sl" 8 (prim 8 PrimSL [a,port 3 "leftCount"]),
              def "quot" 8 (prim 8 PrimQuot [port 8 "dividend",port 5 "divisor"]),
              def "rem" 5 (prim 5 PrimRem [port 8 "remDividend",port 5 "remDivisor"])]
        result = run ds []
    mapM_ (\e -> expect "signed data" result e [int 8]) [a,ref 8 "sra",ref 8 "sl"]
    mapM_ (\e -> expect "unsigned data" result e [uint 8]) [ref 8 "srl",port 8 "logicalData",ref 8 "quot",port 8 "dividend",port 8 "remDividend"]
    mapM_ (\e -> expect "unsigned own width" result e [uint 5]) [port 5 "divisor",port 5 "remDivisor",ref 5 "rem"]
    mapM_ (\e -> expect "shift amount excluded" result e []) [count,port 3 "logicalCount",port 3 "leftCount"]
    checkStable "shift and divide" (package ds [])
    putStrLn "PASS: operation signedness and operand-specific widths; shift counts excluded"

    let a = port 8 "widthA"; b = port 8 "widthB"
        ds = [def "signedWideMul" 16 (prim 16 PrimMul [a,b]),
              def "lowProduct" 8 (prim 8 PrimTrunc [ref 16 "signedWideMul"]),
              def "unsignedWideMul" 16 (prim 16 PrimMul [port 8 "ua",port 8 "ub"]),
              def "unsignedLow" 8 (prim 8 PrimTrunc [ref 16 "unsignedWideMul"]),
              def "sext" 16 (prim 16 PrimSignExt [a]),
              def "zext" 16 (prim 16 PrimZeroExt [a]),
              def "low" 4 (prim 4 PrimExtract [a,lit 32 3,lit 32 0]),
              def "high" 4 (prim 4 PrimExtract [a,lit 32 7,lit 32 4]),
              def "wrongAddWidth" 16 (prim 16 PrimAdd [a,b])]
        observations = [observe a [int 8],observe b [int 8], observe (port 8 "ua") [uint 8],observe (port 8 "ub") [uint 8]]
        result = run ds observations
    mapM_ (\n -> expect "no invented wide signed multiplication" result (ref 16 n) []) ["signedWideMul","wrongAddWidth"]
    expect "do not reinterpret unsigned raw product as signed" result (ref 8 "lowProduct") []
    expect "unsigned wide product" result (ref 16 "unsignedWideMul") [uint 16]
    expect "unsigned truncated product" result (ref 8 "unsignedLow") [uint 8]
    mapM_ (\n -> expect "declared extension family" result (ref 16 n) [int 16]) ["sext","zext"]
    expect "low-bit truncation" result (ref 4 "low") [int 4]
    expect "arbitrary extraction excluded" result (ref 4 "high") []
    checkStable "width changes" (package ds observations)
    putStrLn "PASS: extension/truncation widths and wide multiplication guards"

    let unknown = ASAny (ATBit 8) Nothing
        unknownBool = ASAny (ATBit 1) Nothing
        ds = [def "rawUnknown" 8 unknown,
              def "typedUnknownOp" 8 (prim 8 PrimSRA [unknown,lit 2 1]),
              def "unrelated" 8 (prim 8 PrimAdd [unknown,lit 8 1]),
              def "unknownChoice" 8 (prim 8 PrimIf [unknownBool,port 8 "safe",lit 8 0]),
              def "anotherZero" 8 (lit 8 0)]
        result = run ds []
    expect "unknown is not a value identity" result unknown []
    expect "unknown selector is not exported" result unknownBool []
    expect "named unknown context can have role" result (ref 8 "typedUnknownOp") [int 8]
    mapM_ (\n -> expect "no unknown/literal leakage" result (ref 8 n) []) ["rawUnknown","unrelated","anotherZero"]
    checkStable "private unknowns" (package ds [])
    putStrLn "PASS: independent unknown/literal occurrences and stable idempotence"

    let ds = [def ("sum" ++ show n) 8 (prim 8 PrimAdd [if n == 0 then port 8 "chain" else ref 8 ("sum" ++ show (n-1)),lit 8 1]) | n <- [0::Int .. 1999]]
        result = run ds [observe (port 8 "chain") [uint 8]]
    expect "long indexed worklist" result (ref 8 "sum1999") [uint 8]
    putStrLn "PASS: 2,000-node arithmetic chain"

    let inputs = [port 8 ("flat" ++ show n) | n <- [0::Int .. 1999]]
        ds = [def "flatAdd" 8 (prim 8 PrimAdd (lit 8 0:inputs))]
        observations = [observe p [uint 8] | p <- inputs]
        result = run ds observations
    expect "flat n-ary intersection" result (ref 8 "flatAdd") [uint 8]
    putStrLn "PASS: 2,000-operand flattened arithmetic without global rescans"
