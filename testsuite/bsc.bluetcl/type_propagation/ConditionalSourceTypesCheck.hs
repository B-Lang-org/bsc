-- Direct tests exercise primitive forms before optimizer rewrites can turn
-- conditionals into muxes or erase the distinction under test.
module Main where

import Control.Monad (unless)
import qualified Data.Set as S

import AConditionalSourceTypes (propagateConditionalTypes)
import ASyntax
import CType (TISort(..))
import Id (mk_homeless_id, setIdQualString)
import ISyntax (IType(..), IKind(..))
import IntLit (ilSizedDec)
import Prim (PrimOp(..))

nominal :: String -> IType
nominal name = ITCon (setIdQualString (mk_homeless_id name) "ConditionalTypes") IKStar TIabstract

nibbles, tagged :: IType
nibbles = nominal "Nibbles"
tagged = nominal "TaggedPayload"

port :: Integer -> String -> AExpr
port width name = ASPort (ATBit width) (mk_homeless_id name)

ref :: Integer -> String -> AExpr
ref width name = ASDef (ATBit width) (mk_homeless_id name)

prim :: String -> Integer -> PrimOp -> [AExpr] -> AExpr
prim name width op args = APrim (mk_homeless_id name) (ATBit width) op args

def :: String -> Integer -> AExpr -> ADef
def name width rhs = ADef (mk_homeless_id name) (ATBit width) rhs []

lit :: Integer -> Integer -> AExpr
lit width value = ASInt defaultAId (ATBit width) (ilSizedDec width value)

package :: [ADef] -> [(AExpr, S.Set IType)] -> ASPackage
package defs observations = ASPackage {
    aspkg_name = mk_homeless_id "ConditionalFixture",
    aspkg_is_wrapped = False,
    aspkg_parameters = [],
    aspkg_outputs = [],
    aspkg_inputs = [],
    aspkg_inouts = [],
    aspkg_state_instances = [],
    aspkg_state_outputs = [],
    aspkg_values = defs,
    aspkg_inout_values = [],
    aspkg_foreign_calls = [],
    aspkg_inlined_ports = [],
    aspkg_signal_info = ASPSignalInfo [] [] [] [] [] [] [] [] [] [],
    aspkg_comment_info = ASPCommentInfo [] [],
    aspkg_expr_types = observations
    }

run :: [ADef] -> [(AExpr, [IType])] -> ASPackage
run defs observations = propagateConditionalTypes $
    package defs [(e, S.fromList ts) | (e, ts) <- observations]

types :: ASPackage -> AExpr -> S.Set IType
types pkg expression = S.unions
    [ts | (e, ts) <- aspkg_expr_types pkg, e == expression]

expect :: String -> ASPackage -> AExpr -> [IType] -> IO ()
expect label pkg expression wanted =
    unless (types pkg expression == S.fromList wanted) $
        error (label ++ ": expected " ++ show wanted ++
               ", got " ++ show (types pkg expression))

checkNested :: IO ()
checkNested = do
    let p = port 1 "p"; q = port 1 "q"
        a = port 8 "a"; b = port 8 "b"; c = port 8 "c"
        inner = prim "inner" 8 PrimIf [q,b,c]
        outer = prim "outer" 8 PrimIf [p,a,ref 8 "inner"]
        defs = [def "inner" 8 inner, def "outer" 8 outer]
        result = run defs [(ref 8 "outer",[nibbles])]
    mapM_ (\e -> expect "nested data arm" result e [nibbles]) [a,b,c,inner,outer]
    mapM_ (\e -> expect "nested predicate" result e []) [p,q]
    unless (aspkg_values result == defs) $ error "hardware definitions changed"
    putStrLn "PASS: nested conditionals and aliases, excluding predicates"

checkShared :: IO ()
checkShared = do
    let p = port 1 "p"; q = port 1 "q"; r = port 1 "r"
        a = port 8 "a"; b = port 8 "b"; c = port 8 "c"; d = port 8 "d"
        shared = prim "shared" 8 PrimIf [r,a,b]
        first = prim "first" 8 PrimIf [p,ref 8 "shared",c]
        second = prim "second" 8 PrimIf [q,ref 8 "longAlias",d]
        defs = [def "shared" 8 shared,
                def "longAlias" 8 (ref 8 "shortAlias"),
                def "shortAlias" 8 (ref 8 "shared")]
        result = run defs [(first,[nibbles]),(second,[tagged])]
    mapM_ (\e -> expect "shared candidate union" result e [nibbles,tagged]) [shared,a,b]
    expect "unshared first arm" result c [nibbles]
    expect "unshared second arm" result d [tagged]
    mapM_ (\e -> expect "shared predicate" result e []) [p,q,r]
    putStrLn "PASS: a shared arm is revisited when another nominal candidate arrives"

checkCase :: IO ()
checkCase = do
    -- Give selector and labels the result width too, so their exclusion is
    -- tested independently of the generic worklist's width guard.
    let selector = port 8 "selector"
        label1 = lit 8 1; label2 = lit 8 2
        a = port 8 "a"; b = port 8 "b"; fallback = port 8 "fallback"
        expression = prim "case" 8 PrimCase [selector,fallback,label1,a,label2,b]
        result = run [] [(expression,[nibbles])]
    mapM_ (\e -> expect "case data arm" result e [nibbles]) [a,b,fallback]
    mapM_ (\e -> expect "case selector/label" result e []) [selector,label1,label2]
    putStrLn "PASS: case default and values, excluding same-width selector and labels"

checkMixed :: IO ()
checkMixed = do
    let p = port 1 "p"; q = port 1 "q"; r = port 1 "r"
        selector = port 2 "selector"
        a = port 8 "a"; b = port 8 "b"; c = port 8 "c"; d = port 8 "d"
        leafIf = prim "leafIf" 8 PrimIf [r,a,b]
        innerMux = prim "innerMux" 8 PrimPriMux [q,leafIf,aTrue,c]
        middleCase = prim "middleCase" 8 PrimCase [selector,d,lit 2 0,innerMux]
        outerMux = prim "outerMux" 8 PrimMux [p,middleCase,aTrue,d]
        result = run [] [(outerMux,[nibbles])]
    mapM_ (\e -> expect "mixed data closure" result e [nibbles]) [a,b,c,d,leafIf,innerMux,middleCase]
    mapM_ (\e -> expect "mixed selector" result e []) [p,q,r,selector,aTrue,lit 2 0]
    putStrLn "PASS: one closure handles alternating mux, case, priority mux, and if"

checkBoundaries :: IO ()
checkBoundaries = do
    let p = port 1 "p"; q = port 1 "q"
        high = port 4 "high"; low = port 4 "low"
        input = port 8 "input"; wide = port 16 "wide"
        joined = prim "joined" 8 PrimConcat [high,low]
        added = prim "added" 8 PrimAdd [input,lit 8 3]
        sliced = prim "sliced" 8 PrimExtract [wide,lit 32 7,lit 32 0]
        expression = prim "result" 8 PrimIf [p,joined,prim "inner" 8 PrimIf [q,added,sliced]]
        result = run [] [(expression,[nibbles])]
    mapM_ (\e -> expect "typed data expression" result e [nibbles]) [joined,added,sliced]
    mapM_ (\e -> expect "operation/width boundary" result e [])
        [high,low,input,wide,lit 8 3,lit 32 7,lit 32 0]
    let mismatched = run [def "wrongWidth" 4 high] [(ref 8 "wrongWidth",[nibbles])]
    expect "mismatched alias width" mismatched high []
    putStrLn "PASS: concatenation, arithmetic, extraction, and width-changing aliases stop propagation"

checkNoForward :: IO ()
checkNoForward = do
    let p = port 1 "p"; a = port 8 "a"; b = port 8 "b"
        expression = prim "result" 8 PrimIf [p,a,b]
        result = run [def "result" 8 expression] [(a,[nibbles])]
    expect "typed original arm" result a [nibbles]
    mapM_ (\e -> expect "no forward inference" result e []) [expression,ref 8 "result",b,p]
    putStrLn "PASS: one typed arm does not type the result or the other arm"

checkNormalized :: IO ()
checkNormalized = do
    let p = port 1 "p"; a = port 8 "a"; b = port 8 "b"
        first = prim "firstOccurrence" 8 PrimIf [p,a,b]
        second = prim "secondOccurrence" 8 PrimIf [p,a,b]
        result = run [] [(first,[nibbles]),(second,[tagged])]
    mapM_ (\e -> expect "normalized occurrence union" result e [nibbles,tagged]) [first,second,a,b]
    unless (propagateConditionalTypes result == result) $ error "propagation is not idempotent"
    putStrLn "PASS: equal expressions with different occurrence IDs union candidates; closure is idempotent"

main :: IO ()
main = do
    checkNested
    checkShared
    checkCase
    checkMixed
    checkBoundaries
    checkNoForward
    checkNormalized
    let empty = package [] []
    unless (propagateConditionalTypes empty == empty) $ error "empty metadata changed"
    putStrLn "PASS: empty metadata leaves package unchanged"
