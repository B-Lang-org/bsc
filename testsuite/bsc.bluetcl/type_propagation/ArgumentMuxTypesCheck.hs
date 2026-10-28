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
import ISyntaxUtil (itBitN, itBool)
import Prim (PrimOp(..))
import SchedInfo (SchedInfo(..), MethodConflictInfo(..))
import VModInfo

name = mk_homeless_id
nominal n = ITCon (qualId (name "Fixture") (name n)) IKStar TIabstract
payload = nominal "Payload"
nibbles = nominal "Nibbles"
narrow = nominal "Narrow"
flag = nominal "Flag"
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

resultMethod n mult outputs = (method n mult [] Nothing) {
    vf_outputs = [(VName p,[]) | p <- outputs] }
resultId methodName copy portM = mkMethId (name "child") (name methodName) copy (MethodResult portM)
resultPort methodName copy portM w = ASPort (ATBit w) (resultId methodName copy portM)
resultDecl methodName copy portM w = (resultId methodName copy portM, ATBit w)

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
    expect "other mux arm" result (port 8 "other") [payload,nibbles]
    expect "typed arithmetic result" result sumExpr [payload,nibbles]
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

    let producer = inst [resultMethod "get" 2 ["VALUE"],
                         resultMethod "bitsOut" 1 ["BITS_OUT"],
                         resultMethod "oneBit" 1 ["ONE_BIT"],
                         resultMethod "ready" 1 ["RDY"],
                         resultMethod "missingType" 1 ["UNTYPED"]]
                        [("VALUE",payload), ("BITS_OUT",itBitN 8), ("ONE_BIT",flag), ("RDY",itBool)]
        valueOut = resultPort "get" (Just 0) Nothing 8
        absentCopy = resultPort "get" (Just 1) Nothing 8
        bitOut = resultPort "bitsOut" Nothing Nothing 8
        flagOut = resultPort "oneBit" Nothing Nothing 1
        readyOut = resultPort "ready" Nothing Nothing 1
        missingType = resultPort "missingType" Nothing Nothing 8
        outputDefs = [def "outputAlias" 8 valueOut,
                      def "outputMux" 8 (mux 8 PrimMux (ref 8 "outputAlias") (port 8 "outputSibling")),
                      def "outputArithmetic" 8 (APrim defaultAId (ATBit 8) PrimAdd [valueOut,port 8 "outputOffset"]),
                      def "absentAlias" 8 absentCopy,
                      def "bitAlias" 8 bitOut,
                      def "flagMux" 1 (APrim defaultAId (ATBit 1) PrimPriMux
                          [readyOut, flagOut, port 1 "chooseB", port 1 "flagSibling"]),
                      def "readyAlias" 1 readyOut,
                      def "untypedAlias" 8 missingType]
        outputOriginal = (package [producer] outputDefs) { aspkg_state_outputs =
            [resultDecl "get" (Just 0) Nothing 8,
             resultDecl "bitsOut" Nothing Nothing 8,
             resultDecl "oneBit" Nothing Nothing 1,
             resultDecl "ready" Nothing Nothing 1,
             resultDecl "missingType" Nothing Nothing 8] }
        outputResult = propagateArgumentMuxTypes outputOriginal
    mapM_ (\e -> expect "known output flows through alias and sibling" outputResult e [payload])
        [valueOut, ref 8 "outputAlias", ref 8 "outputMux", port 8 "outputSibling"]
    mapM_ (\e -> expect "one-bit nominal result flows through data edges" outputResult e [flag])
        [flagOut, ref 1 "flagMux", port 1 "flagSibling"]
    mapM_ (\e -> expect "ready keeps its own Boolean candidate" outputResult e [itBool])
        [readyOut, ref 1 "readyAlias"]
    mapM_ (\e -> expect "output seeding respects presence/type/operation/control boundaries" outputResult e [])
        [absentCopy, ref 8 "absentAlias", bitOut, ref 8 "bitAlias",
         missingType, ref 8 "untypedAlias", ref 8 "outputArithmetic", port 8 "outputOffset",
         port 1 "chooseA", port 1 "chooseB"]
    unless (outputResult { aspkg_expr_types = [] } == outputOriginal) $
        error "output seeding changed hardware fields"
    putStrLn "PASS: result-port seeds, forward aliases, sibling union, and control/presence boundaries"

    let splitProducer = inst [resultMethod "splitResult" 2 ["OUT_LOW","OUT_HIGH"],
                              resultMethod "sameWidth" 1 ["OUT_PAYLOAD","OUT_NIBBLES"]]
                             [("OUT_LOW",narrow),("OUT_HIGH",payload),
                              ("OUT_PAYLOAD",payload),("OUT_NIBBLES",nibbles)]
        splitOutputs = [("splitResult",copy,index,width,leaf,typ) |
                        (copy,suffix) <- [(Just 0,"0"),(Just 1,"1")],
                        (index,width,leaf,typ) <- [(Just 1,4,"outLow" ++ suffix,narrow),
                                                (Just 2,8,"outHigh" ++ suffix,payload)]] ++
                       [("sameWidth",Nothing,Just 1,8,"outPayload",payload),
                        ("sameWidth",Nothing,Just 2,8,"outNibbles",nibbles)]
        splitOutputDefs = [def leaf width (resultPort meth copy index width) |
                           (meth,copy,index,width,leaf,_) <- splitOutputs]
        splitOutputOriginal = (package [splitProducer] splitOutputDefs) { aspkg_state_outputs =
            [resultDecl meth copy index width | (meth,copy,index,width,_,_) <- splitOutputs] }
        splitOutputResult = propagateArgumentMuxTypes splitOutputOriginal
    mapM_ (\(meth,copy,index,width,leaf,typ) -> do
        expect "split result keeps its own port type" splitOutputResult (resultPort meth copy index width) [typ]
        expect "split result alias keeps its own port type" splitOutputResult (ref width leaf) [typ]) splitOutputs
    unless (splitOutputResult { aspkg_expr_types = [] } == splitOutputOriginal) $
        error "split output seeding changed hardware fields"
    putStrLn "PASS: distinct split-result types, same-width nominal results, and method multiplicity"
