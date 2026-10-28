-- Direct tests exercise primitive forms before optimizer rewrites can turn
-- conditionals into muxes or erase the distinction under test.
module Main where

import Control.Monad (unless)
import qualified Data.Set as S

import AConditionalSourceTypes (propagateConditionalTypes)
import ASyntax
import ASourceTypes (anchorASPackage)
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
run defs observations =
    let original = package defs [(e, S.fromList ts) | (e, ts) <- observations]
        result = propagateConditionalTypes original
    in if result { aspkg_expr_types = [] } == original { aspkg_expr_types = [] }
       then result else error "candidate propagation changed hardware"

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
    expect "transitive first sibling" result c [nibbles,tagged]
    expect "transitive second sibling" result d [nibbles,tagged]
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

checkForward :: IO ()
checkForward = do
    let p = port 1 "p"; a = port 8 "a"; b = port 8 "b"
        expression = prim "result" 8 PrimIf [p,a,b]
        result = run [def "result" 8 expression] [(a,[nibbles])]
    expect "typed original arm" result a [nibbles]
    mapM_ (\e -> expect "forward and sibling inference" result e [nibbles])
        [expression,ref 8 "result",b]
    expect "forward predicate" result p []
    putStrLn "PASS: one typed arm informs its result and siblings"

checkNormalized :: IO ()
checkNormalized = do
    let p = port 1 "p"; a = port 8 "a"; b = port 8 "b"
        first = prim "firstOccurrence" 8 PrimIf [p,a,b]
        second = prim "secondOccurrence" 8 PrimIf [p,a,b]
        result = run [] [(first,[nibbles]),(second,[tagged])]
    mapM_ (\e -> expect "normalized occurrence union" result e [nibbles,tagged]) [first,second,a,b]
    unless (propagateConditionalTypes result == result) $ error "propagation is not idempotent"
    unless (run [] [(second,[tagged]),(first,[nibbles])] == result) $
        error "candidate union depends on observation order"
    putStrLn "PASS: equal expressions with different occurrence IDs union candidates; closure is idempotent"

checkArrays :: IO ()
checkArrays = do
    let a = port 8 "array_a"; b = port 8 "array_b"
        c = port 8 "array_c"; d = port 8 "array_d"
        ix = port 8 "array_index"; outerIx = port 8 "outer_index"
        rowType = ATArray 2 (ATBit 8)
        row name es = APrim (mk_homeless_id name) rowType PrimBuildArray es
        first = row "row0" [a,b]; second = row "row1" [c,d]
        matrixType = ATArray 2 rowType
        matrix = APrim (mk_homeless_id "matrix") matrixType PrimBuildArray [first,second]
        alias = ASDef matrixType (mk_homeless_id "array_alias")
        selectedRow = APrim (mk_homeless_id "selected_row") rowType PrimArrayDynSelect [alias,outerIx]
        selected = prim "selected_element" 8 PrimArrayDynSelect [selectedRow,ix]
        defs = [ADef (mk_homeless_id "array_alias") matrixType matrix [],
                def "selected_element" 8 selected]
        result = run defs [(a,[nibbles]),(d,[tagged])]
    mapM_ (\e -> expect "array element and selection union" result e [nibbles,tagged])
        [a,b,c,d,selected,ref 8 "selected_element"]
    mapM_ (\e -> expect "no fabricated aggregate or index type" result e [])
        [first,second,matrix,alias,selectedRow,ix,outerIx]
    unless (propagateConditionalTypes result == result) $ error "array closure is not idempotent"
    let wrongCount = row "wrong_count" [a]
        wrongWidth = row "wrong_width" [a,port 4 "array_small"]
        wrongResult = prim "wrong_result" 4 PrimArrayDynSelect [first,ix]
        bad = run [ADef (mk_homeless_id "bad_count") rowType wrongCount [],
                   ADef (mk_homeless_id "bad_width") rowType wrongWidth [],
                   def "bad_result" 4 wrongResult] [(a,[nibbles])]
    mapM_ (\e -> expect "malformed array boundary" bad e [])
        [port 4 "array_small",wrongResult]
    putStrLn "PASS: nested array element hubs, aliases, selections, width guards, and excluded indices"

checkCyclesAndUnknowns :: IO ()
checkCyclesAndUnknowns = do
    let unknown = ASAny (ATBit 8) Nothing
        compound name = prim name 8 PrimAdd [unknown,lit 8 1]
        defs = [def "cycle_a" 8 (ref 8 "cycle_b"),
                def "cycle_b" 8 (ref 8 "cycle_a"),
                def "unknown_a" 8 unknown, def "unknown_b" 8 unknown,
                def "unknown_alias" 8 (ref 8 "unknown_a"),
                def "compound_a" 8 (compound "occurrence_a"),
                def "compound_b" 8 (compound "occurrence_b")]
        seeds = [(ref 8 "cycle_a",[nibbles]),(ref 8 "cycle_b",[tagged]),
                 (ref 8 "unknown_a",[nibbles]),(ref 8 "compound_a",[tagged])]
        result = run defs seeds
    mapM_ (\e -> expect "cyclic alias union" result e [nibbles,tagged])
        [ref 8 "cycle_a",ref 8 "cycle_b"]
    expect "real unknown alias" result (ref 8 "unknown_alias") [nibbles]
    expect "unknown compound anchor" result (ref 8 "compound_a") [tagged]
    mapM_ (\e -> expect "independent unknown isolation" result e [])
        [unknown,ref 8 "unknown_b",ref 8 "compound_b",compound "occurrence_b"]
    unless (propagateConditionalTypes result == result) $ error "unknown closure is not idempotent"
    unless (aspkg_expr_types (run (reverse defs) (reverse seeds)) == aspkg_expr_types result) $
        error "closure depends on definition/seed order"
    putStrLn "PASS: cyclic aliases converge; independent unknowns and compound unknowns remain separate"

checkLiteralIsolation :: IO ()
checkLiteralIsolation = do
    let p = port 1 "literal_p"; q = port 1 "literal_q"
        a = port 8 "literal_a"; b = port 8 "literal_b"
        first = prim "literal_first" 8 PrimIf [p,a,lit 8 0]
        second = prim "literal_second" 8 PrimIf [q,b,lit 8 0]
        result = run [def "literal_first" 8 first,def "literal_second" 8 second]
                     [(a,[nibbles])]
    expect "literal-containing result" result first [nibbles]
    mapM_ (\e -> expect "equal literal is not a global relay" result e [])
        [b,second,lit 8 0]
    unless (propagateConditionalTypes (anchorASPackage result) == result) $
        error "anonymous literal isolation fails after anchoring"
    let shared = ref 8 "shared_constant"
        linkedFirst = prim "linked_first" 8 PrimIf [p,a,shared]
        linkedSecond = prim "linked_second" 8 PrimIf [q,b,shared]
        linked = run [def "shared_constant" 8 (lit 8 0),
                      def "linked_first" 8 linkedFirst,def "linked_second" 8 linkedSecond]
                     [(a,[nibbles]),(b,[tagged])]
    mapM_ (\e -> expect "real named constant sharing" linked e [nibbles,tagged])
        [a,b,shared,linkedFirst,linkedSecond]
    let separateFirst = prim "separate_first" 8 PrimIf [p,a,ref 8 "separate_zero_a"]
        separateSecond = prim "separate_second" 8 PrimIf [q,b,ref 8 "separate_zero_b"]
        separate = run [def "separate_zero_a" 8 (lit 8 0),
                        def "separate_zero_b" 8 (lit 8 0),
                        def "separate_first" 8 separateFirst,
                        def "separate_second" 8 separateSecond] [(a,[nibbles])]
        anchored = propagateConditionalTypes (anchorASPackage separate)
    -- Explicit named definitions remain eligible for the compiler's existing
    -- CSE/anchoring equivalence, including equal constant definitions.
    expect "anchoring preserves named constant CSE" anchored b [nibbles]
    expect "anchoring unions named constant definitions" anchored (ref 8 "separate_zero_b") [nibbles]
    unless (propagateConditionalTypes (anchorASPackage anchored) == anchored) $
        error "anchored literal closure is not idempotent"
    putStrLn "PASS: anonymous literal defaults stay local; explicit named constant CSE still unions"

checkNestedBoundary :: IO ()
checkNestedBoundary = do
    let p = port 1 "boundary_p"; a = port 8 "boundary_a"; b = port 8 "boundary_b"
        selected = prim "boundary_if" 8 PrimIf [p,a,b]
        arithmetic = prim "boundary_add" 8 PrimAdd [selected,lit 8 1]
        result = run [def "boundary_add" 8 arithmetic] [(a,[nibbles])]
    mapM_ (\e -> expect "nested selection discovered below arithmetic" result e [nibbles])
        [selected,b]
    mapM_ (\e -> expect "arithmetic does not forward operand interpretations" result e [])
        [arithmetic,ref 8 "boundary_add",p]
    let malformedMux = prim "bad_mux" 8 PrimMux [p,a,b]
        malformedCase = prim "bad_case" 8 PrimCase [port 8 "case_index",a,lit 8 0,b,lit 8 1]
        malformed = run [] [(malformedMux,[tagged]),(malformedCase,[tagged])]
    mapM_ (\e -> expect "malformed selector has no partial edges" malformed e []) [a,b]
    putStrLn "PASS: nested selections are discovered across operation boundaries; malformed selectors stop"

checkOtherLiveRoots :: IO ()
checkOtherLiveRoots = do
    let p = port 1 "foreign_predicate"
        a = port 8 "foreign_a"; b = port 8 "foreign_b"
        selected = prim "foreign_if" 8 PrimIf [p,a,b]
        original = (package [] [(a,S.singleton nibbles)]) {
            aspkg_foreign_calls = [([], [AForeignCall (mk_homeless_id "foreign")
                                                       "foreign" [aTrue,selected] [] []])] }
        result = propagateConditionalTypes original
    mapM_ (\e -> expect "selection used only by foreign call" result e [nibbles]) [selected,b]
    expect "foreign selection predicate" result p []
    unless (result { aspkg_expr_types = [] } == original { aspkg_expr_types = [] }) $
        error "candidate propagation changed a foreign call"
    putStrLn "PASS: selections in live foreign-call roots are discovered without changing hardware"

checkWideMux :: IO ()
checkWideMux = do
    let arms = [port 8 ("wide_arm_" ++ show n) | n <- [1..2048 :: Int]]
        expression = prim "wide_mux" 8 PrimMux (concatMap (\a -> [aTrue,a]) arms)
        result = run [def "wide_mux" 8 expression] [(head arms,[nibbles])]
    mapM_ (\e -> expect "wide mux member" result e [nibbles]) arms
    putStrLn "PASS: wide selection group uses one hub and reaches every member"

main :: IO ()
main = do
    checkNested
    checkShared
    checkCase
    checkMixed
    checkBoundaries
    checkForward
    checkNormalized
    checkArrays
    checkCyclesAndUnknowns
    checkLiteralIsolation
    checkNestedBoundary
    checkOtherLiveRoots
    checkWideMux
    let empty = package [] []
    unless (propagateConditionalTypes empty == empty) $ error "empty metadata changed"
    putStrLn "PASS: empty metadata leaves package unchanged"
