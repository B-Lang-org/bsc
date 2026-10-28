module Main where

import Control.Monad (unless)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import ASourceTypes (namedSourceTypes, anchorASPackage)
import ASyntax
import AVeriQuirks (aVeriQuirks)
import CType (TISort(..))
import FlagsDecode (defaultFlags)
import Flags (useNegate, keepAddSize, readableMux)
import Id (mk_homeless_id, setIdQualString, getIdString)
import ISyntax (IType(..), IKind(..))
import IntLit (ilDec)
import Prim (PrimOp(..))

name = mk_homeless_id
nominal s = ITCon (setIdQualString (name s) "LateRewriteTypes") IKStar TIabstract
payload = nominal "Payload"
other = nominal "Other"
port w s = ASPort (ATBit w) (name s)
ref w s = ASDef (ATBit w) (name s)
prim w op es = APrim defaultAId (ATBit w) op es
lit w n = ASInt defaultAId (ATBit w) (ilDec n)
def s w e = ADef (name s) (ATBit w) e []
slice e = prim 4 PrimExtract [e,lit 32 3,lit 32 0]
shift = prim 8 PrimSRA [port 8 "input", port 3 "amount"]
flags = defaultFlags ""
package ds ts = ASPackage {
    aspkg_name = name "LateRewriteTypes", aspkg_is_wrapped = False,
    aspkg_parameters = [], aspkg_outputs = [], aspkg_inputs = [], aspkg_inouts = [],
    aspkg_state_instances = [], aspkg_state_outputs = [], aspkg_values = ds,
    aspkg_inout_values = [], aspkg_foreign_calls = [], aspkg_inlined_ports = [],
    aspkg_signal_info = ASPSignalInfo [] [] [] [] [] [] [] [] [] [],
    aspkg_comment_info = ASPCommentInfo [] [], aspkg_expr_types = ts }
named p = namedSourceTypes (aspkg_values p) (aspkg_expr_types p)
types p s = M.findWithDefault S.empty s (named p)
run = runWith flags
runWith f p = let result = aVeriQuirks f p
                  bare = aVeriQuirks f (p {aspkg_expr_types=[]})
              in if result {aspkg_expr_types=[]} == bare then result
                 else error "metadata changed hardware"
expect label got want = unless (got == S.fromList want) $
    error (label ++ ": wrong candidate set: " ++ show got)
helpers w p = [getIdString i | ADef i (ATBit n) _ _ <- aspkg_values p, n == w]

checkShift = do
    let p = run (package [def "result" 4 (slice shift)] [(shift,S.fromList [payload,other])])
    case helpers 8 p of
      [i] -> expect "dynamic SRA helper" (types p i) [payload,other]
      _ -> error "expected one full-width dynamic shift helper"
    expect "no data operand inference" (types p "input") []
    expect "no shift count inference" (types p "amount") []
    expect "no narrower output inference" (types p "result") []
    putStrLn "PASS: nested dynamic shift retains all candidates on the emitted word"

checkConstant = do
    let e = prim 8 PrimSRA [port 8 "input",lit 32 2]
        p = run (package [def "result" 4 (slice e)] [(e,S.singleton payload)])
    case helpers 8 p of
      [i] -> expect "constant SRA helper" (types p i) [payload]
      _ -> error "expected one full-width constant shift helper"
    mapM_ (\i -> expect "narrow extraction helper" (types p i) []) (helpers 6 p)
    putStrLn "PASS: constant shift retains its word type, excluding narrower helpers"

checkCSE = do
    -- Both shifts lower to the same sign-bit replication expression. A helper
    -- created for the first use must accumulate the second use's candidate.
    let a = prim 8 PrimSRA [port 8 "input",lit 32 8]
        b = prim 8 PrimSRA [port 8 "input",lit 32 9]
        p = run (package [def "left" 4 (slice a),def "right" 4 (slice b)]
                         [(a,S.singleton payload),(b,S.singleton other)])
    case helpers 8 p of
      [i] -> expect "CSE helper union" (types p i) [payload,other]
      _ -> error "expected the two rewritten expressions to reuse one helper"
    putStrLn "PASS: newly equal rewritten expressions union candidates on their shared helper"

checkExisting = do
    let empty = run (package [def "result" 4 (slice shift)] [])
        [rhs] = [e | ADef _ (ATBit 8) e _ <- aspkg_values empty]
        p = run (package [def "existing" 8 rhs,def "result" 4 (slice shift)]
                         [(ref 8 "existing",S.singleton other),(shift,S.singleton payload)])
    unless (helpers 8 p == ["existing"]) $ error "existing helper was not reused"
    expect "existing helper union" (types p "existing") [payload,other]
    putStrLn "PASS: rewrite candidates join an existing definition's observations"

checkParent = do
    let e = prim 8 PrimXor [shift,port 8 "mask"]
        p = run (package [def "result" 4 (slice e)] [(e,S.singleton payload)])
    case helpers 8 p of
      [i] -> expect "rewritten enclosing expression" (types p i) [payload]
      _ -> error "expected one full-width enclosing expression helper"
    expect "do not transfer parent candidate to input" (types p "input") []
    putStrLn "PASS: observations on parents survive rewrites of nested operands"

checkUnknown = do
    let e = prim 8 PrimSRA [ASAny (ATBit 8) Nothing,port 3 "amount"]
        p = run (package [def "left" 8 e,def "right" 8 e]
                         [(ref 8 "left",S.singleton payload)])
    expect "named unknown-bearing definition" (types p "left") [payload]
    expect "independent unknown-bearing definition" (types p "right") []
    let anonymous = run (package [def "left" 4 (slice e),def "right" 4 (slice e)]
                                 [(e,S.singleton payload)])
    mapM_ (\i -> expect "anonymous unknowns are not global keys" (types anonymous i) [])
          (helpers 8 anonymous)
    let again = aVeriQuirks flags (anchorASPackage p)
    expect "unknown isolation across repeated pass" (types again "right") []
    putStrLn "PASS: independent unknown-bearing expressions stay separate across passes"

checkIdentity = do
    let p = run (package [def "observed" 8 shift] [(shift,S.singleton payload)])
    expect "original named definition" (types p "observed") [payload]
    let again = aVeriQuirks flags p
    expect "second pass" (types again "observed") [payload]
    unless (again == p) $ error "already rewritten package changed on a second pass"
    putStrLn "PASS: original named observations survive and the pass is idempotent"

checkLiterals = do
    let e = prim 8 PrimSignExt [lit 8 0]
        consumer = prim 8 PrimAdd [e,port 8 "input"]
        anonymous = run (package [def "consumer" 8 consumer,def "unrelated" 8 (lit 8 0)]
                                 [(e,S.singleton payload)])
    expect "anonymous literal must not relay candidates" (types anonymous "unrelated") []
    expect "expression type must not reach arithmetic parent" (types anonymous "consumer") []
    -- Explicit named constants are real CSE equivalents under the existing
    -- source-type model. Preserve the named observation and its alias class.
    let namedConstant = run (package [def "observed" 8 e,def "unrelated" 8 (lit 8 0)]
                                     [(ref 8 "observed",S.singleton payload)])
    expect "named constant retains observation" (types namedConstant "observed") [payload]
    expect "named constant CSE equivalence" (types namedConstant "unrelated") [payload]
    putStrLn "PASS: anonymous literals do not relay candidates; named constant CSE still unions"

checkForeign = do
    let call = AForeignCall (name "foreign") "foreign" [aTrue,slice shift] [] []
        original = (package [] [(shift,S.singleton payload)]) {
                       aspkg_foreign_calls = [([], [call])] }
        p = run original
    case helpers 8 p of
      [i] -> expect "foreign argument helper" (types p i) [payload]
      _ -> error "expected a helper for the foreign argument's nested shift"
    putStrLn "PASS: nested observations in foreign arguments survive lifting"

checkOtherRewrites = do
    let x = port 8 "input"
        narrow = port 4 "narrow"
        expressions =
          [(flags {useNegate=False}, prim 8 PrimNeg [x]),
           (flags {keepAddSize=True}, prim 8 PrimAdd
              [prim 8 PrimZeroExt [narrow],prim 8 PrimZeroExt [port 4 "other"]]),
           (flags {readableMux=False}, prim 8 PrimMux
              [port 1 "select",x,aTrue,port 8 "other"]),
           (flags,prim 8 PrimExtract [port 16 "wide",port 5 "high",port 5 "low"])]
    mapM_ (\(f,e) -> do
        let p = runWith f (package [def "result" 4 (slice e)] [(e,S.singleton payload)])
        case helpers 8 p of
          [i] -> expect "additional whole-value rewrite" (types p i) [payload]
          _ -> error "expected one observed full-width helper") expressions
    mapM_ (\e -> do
        let p = run (package [def "result" 4 (slice e)] [(e,S.singleton payload)])
        expect "identity rewrite to port" (types p "input") [payload])
        [prim 8 PrimSignExt [x],prim 8 PrimExtract [x,lit 32 7,lit 32 0]]
    putStrLn "PASS: dynamic extract, mux, negate, extension and identity rewrites retain observations"

main = mapM_ id [checkShift,checkConstant,checkCSE,checkExisting,checkParent,checkUnknown,checkIdentity,checkLiterals,checkForeign,checkOtherRewrites]
