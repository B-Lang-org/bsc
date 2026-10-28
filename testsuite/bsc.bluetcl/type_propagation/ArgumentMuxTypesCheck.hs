module Main where

import Control.Monad (unless)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import AMuxSourceTypes (propagateArgumentMuxTypes)
import ASourceTypes (namedSourceTypes)
import ASyntax
import CType (TISort(..))
import Id (mk_homeless_id, qualId)
import ISyntax (IType(..), IKind(..))
import ISyntaxUtil (itBitN)
import Prim (PrimOp(..))
import SchedInfo (SchedInfo(..), MethodConflictInfo(..))
import VModInfo

name = mk_homeless_id
nominal n = ITCon (qualId (name "Fixture") (name n)) IKStar TIabstract
payload = nominal "Payload"
nibbles = nominal "Nibbles"
narrow = nominal "Narrow"
port w n = ASPort (ATBit w) (name n)
ref w n = ASDef (ATBit w) (name n)
def n w e = ADef (name n) (ATBit w) e []
mux w op a b = APrim defaultAId (ATBit w) op [port 1 "chooseA", a, port 1 "chooseB", b]

package instances defs = ASPackage {
    aspkg_name = name "MuxFixture", aspkg_is_wrapped = False,
    aspkg_parameters = [], aspkg_outputs = [], aspkg_inputs = [], aspkg_inouts = [],
    aspkg_state_instances = instances, aspkg_state_outputs = [],
    aspkg_values = defs, aspkg_inout_values = [], aspkg_foreign_calls = [],
    aspkg_inlined_ports = [],
    aspkg_signal_info = ASPSignalInfo [] [] [] [] [] [] [] [] [] [],
    aspkg_comment_info = ASPCommentInfo [] [], aspkg_expr_types = [] }

inst methods portTypes = AVInst (name "child") (ATBit 1) False []
    (M.fromList [(VName n, t) | (n,t) <- portTypes])
    (mkVModInfo (VName "Sink") (ClockInfo [] [] [] []) (ResetInfo [] []) [] methods
        (SchedInfo (MethodConflictInfo [(vf_name a,vf_name b) | a <- methods, b <- methods] [] [] [] [] [] []) [] [] []) (VPathInfo [])) [] []

method n mult inputs enable = Method (name n) Nothing Nothing mult
    [[(VName p,[]) | p <- ps] | ps <- inputs] [] (fmap (\p -> (VName p,[])) enable)

argument methodName copy argN portM = mkMethId (name "child") (name methodName) copy (MethodArg argN portM)
argdef methodName copy argN portM w rhs = ADef (argument methodName copy argN portM) (ATBit w) rhs []

types pkg expression = S.unions [ts | (e,ts) <- aspkg_expr_types pkg, e == expression]
expect label pkg expression wanted = unless (types pkg expression == S.fromList wanted) $
    error (label ++ ": " ++ show (types pkg expression))

main :: IO ()
main = do
    let sink = inst [method "putA" 1 [["A"]] (Just "EN"), method "putB" 1 [["B"]] Nothing,
                     method "bits" 1 [["BITS"]] Nothing]
                    [("A", payload), ("B", nibbles), ("BITS", itBitN 8), ("EN", payload)]
        raw = port 8 "sharedRaw"
        sumExpr = APrim defaultAId (ATBit 8) PrimAdd [port 8 "arithmeticInput", port 8 "offset"]
        ds = [argdef "putA" Nothing 1 Nothing 8 (mux 8 PrimMux (ref 8 "shared") sumExpr),
              argdef "putB" Nothing 1 Nothing 8 (mux 8 PrimPriMux (ref 8 "shared") (port 8 "other")),
              argdef "bits" Nothing 1 Nothing 8 (port 8 "bitsOnly"),
              ADef (mkMethId (name "child") (name "putA") Nothing MethodEnable) (ATBit 1) (port 1 "enable") [],
              def "shared" 8 raw]
        original = package [sink] ds
        result = propagateArgumentMuxTypes original
    expect "shared input unions both port interpretations" result raw [payload,nibbles]
    expect "shared alias unions both port interpretations" result (ref 8 "shared") [payload,nibbles]
    expect "other mux arm" result (port 8 "other") [nibbles]
    expect "typed arithmetic result" result sumExpr [payload]
    mapM_ (\e -> expect "no control/arithmetic operand/Bit seed propagation" result e [])
        [port 1 "chooseA", port 1 "chooseB", port 1 "enable", port 8 "arithmeticInput", port 8 "offset", port 8 "bitsOnly"]
    unless (result { aspkg_expr_types = [] } == original) $ error "changed hardware fields"
    putStrLn "PASS: mux/priority mux data arms, CSE union, and hardware/control boundaries"

    let multiple = inst [method "multiple" 2 [["LOW"],["HIGH"]] Nothing]
                        [("LOW",narrow),("HIGH",payload)]
        multiDefs = [argdef "multiple" copy argN Nothing width (port width leaf) |
                     (copy, suffix) <- [(Just 0,"0"),(Just 1,"1")],
                     (argN,width,leaf) <- [(1,4,"argLow" ++ suffix),(2,8,"argHigh" ++ suffix)]]
        multiResult = propagateArgumentMuxTypes (package [multiple] multiDefs)
    mapM_ (\suffix -> do
        expect "first argument has its own type" multiResult (port 4 ("argLow" ++ suffix)) [narrow]
        expect "second argument has its own type" multiResult (port 8 ("argHigh" ++ suffix)) [payload]) ["0","1"]
    putStrLn "PASS: distinct argument types and method multiplicity"

    let split = inst [method "split" 2 [["LOW","HIGH"]] Nothing]
                     [("LOW",narrow),("HIGH",payload)]
        splitDefs = [argdef "split" copy 1 index width (port width leaf) |
                     (copy, suffix) <- [(Just 0,"0"),(Just 1,"1")],
                     (index,width,leaf) <- [(Just 1,4,"low" ++ suffix),(Just 2,8,"high" ++ suffix)]]
        splitResult = propagateArgumentMuxTypes (package [split] splitDefs)
    mapM_ (\suffix -> do
        expect "split lower port has its own type" splitResult (port 4 ("low" ++ suffix)) [narrow]
        expect "split upper port has its own type" splitResult (port 8 ("high" ++ suffix)) [payload]) ["0","1"]
    putStrLn "PASS: split argument ports and method multiplicity"

    let unknown = ASAny (ATBit 8) Nothing
        unknownDefs = [argdef "putA" Nothing 1 Nothing 8 (mux 8 PrimMux (port 8 "known") unknown),
                       def "unrelatedUndefined" 8 unknown]
        unknownResult = propagateArgumentMuxTypes (package [sink] unknownDefs)
        named = namedSourceTypes unknownDefs (aspkg_expr_types unknownResult)
    expect "do not type unspecified mux defaults" unknownResult unknown []
    unless (M.findWithDefault S.empty "unrelatedUndefined" named == S.empty) $
        error "mux default polluted an unrelated undefined wire"
    putStrLn "PASS: unspecified defaults do not transfer types to unrelated wires"
