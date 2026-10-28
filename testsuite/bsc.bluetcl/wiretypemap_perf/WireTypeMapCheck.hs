-- Direct tests of the production analysis, including ambiguous wire names
-- that cannot be expressed through ordinary source-level port declarations.
-- See run.sh for the correctness and optional scaling commands.
module Main where

import Control.DeepSeq(force)
import Control.Exception(evaluate)
import Control.Monad(unless)
import qualified Data.Map as M
import qualified Data.Set as S
import System.CPUTime(getCPUTime)
import System.Environment(getArgs)
import Text.Printf(printf)
import Text.Read(readMaybe)

import ASyntax
import ASourceTypes(sourceTypeKey, sourceTypeLookup, anchorSourceTypes,
                    namedSourceTypes)
import ASyntaxUtil(inlineDroppedExprTypes)
import Id(mk_homeless_id)
import IntLit(ilDec, ilSizedHex)
import Prim(PrimOp(PrimAdd, PrimBAnd))

import ISyntax(IType)
import ISyntaxUtil(itBool, itBitN, itClock)
import SchedInfo(SchedInfo(..), MethodConflictInfo(..))
import VModInfo
import WireAnalysis(getWireTypeMap, getWireTypeCandidates)
import Wires(emptyWireProps)

clocks :: VClockInfo
clocks = ClockInfo [] [] [] []

resets :: VResetInfo
resets = ResetInfo [] []

package :: [(String, IType)] -> [AVInst] -> APackage
package external instances = APackage {
    apkg_name = mk_homeless_id "test",
    apkg_is_wrapped = False,
    apkg_backend = Nothing,
    apkg_size_params = [],
    apkg_inputs = [],
    apkg_clock_domains = [],
    apkg_external_wires = WireInfo clocks resets [],
    apkg_external_wire_types = M.fromList [(VName n, t) | (n, t) <- external],
    apkg_expr_types = [],
    apkg_final_wire_names = Nothing,
    apkg_final_wire_types = Nothing,
    apkg_reset_list = [],
    apkg_state_instances = instances,
    apkg_local_defs = [],
    apkg_rules = [],
    apkg_schedule_pragmas = [],
    apkg_interface = [],
    apkg_inst_comments = [],
    apkg_inst_tree = M.empty,
    apkg_proof_obligations = []
    }

instanceWithType :: String -> IType -> AVInst
instanceWithType name typ =
    AVInst (mk_homeless_id name) (ATBit 1) False []
        (M.singleton (VName "OUT") typ)
        (mkVModInfo (VName "TestPrimitive") clocks resets [] []
            (SchedInfo (MethodConflictInfo [] [] [] [] [] [] []) [] [] [])
            (VPathInfo [])) [] []

checkPairs :: IO ()
checkPairs = do
    -- The first pair is repeated across external and submodule entries.
    -- The final instance repeats an earlier instance. Bool and Bit#(1)
    -- must both survive under a$OUT and a.OUT, despite their equal width.
    let input = package [("z", itBool), ("a$OUT", itBool)]
            [ instanceWithType "a" itBool,
              instanceWithType "a" (itBitN 1),
              instanceWithType "b" (itBitN 1),
              instanceWithType "a" itBool ]
        expected =
            [ ("a$OUT", itBool), ("z", itBool), ("a.OUT", itBool),
              ("a$OUT", itBitN 1), ("a.OUT", itBitN 1),
              ("b$OUT", itBitN 1), ("b.OUT", itBitN 1) ]
        actual = getWireTypeMap input
    unless (actual == expected) $
        error ("wrong candidate order or deduplication: " ++ show actual)
    unless (null (getWireTypeMap (package [] []))) $
        error "empty package has candidate wires"
    putStrLn "PASS: stable pair deduplication, category order, distinct same-name types"

-- Split results must join evidence to exactly the selected port,
-- both on a submodule call and on the enclosing module's interface.
checkSplitOutputs :: IO ()
checkSplitOutputs = do
    let iid = mk_homeless_id "child"
        mid = mk_homeless_id "get"
        bt = ATBit 1
        tup = ATTuple [bt,bt]
        fi = Method mid Nothing Nothing 1 [] [(VName "LEFT",[]),(VName "RIGHT",[])] Nothing
        vmi = mkVModInfo (VName "TestPrimitive") clocks resets [] [fi]
                  (SchedInfo (MethodConflictInfo [(mid,mid)] [] [] [] [] [] []) [] [] [])
                  (VPathInfo [])
        inst = (instanceWithType "child" (itBitN 1)) {
                    avi_port_types = M.fromList [(VName "LEFT",itBitN 1),(VName "RIGHT",itBitN 1)],
                    avi_vmi = vmi }
        left = ATupleSel bt (AMethCall tup iid mid []) 1
        right = ATupleSel bt (AMethCall tup iid mid []) 2
        intf = AIDef mid [] emptyWireProps left
                   (ADef mid tup (ATuple tup [left,right]) []) fi []
        input = (package [("LEFT",itBitN 1),("RIGHT",itBitN 1)] [inst]) { apkg_interface = [intf],
                  apkg_expr_types = [(left,S.singleton itBool)] }
        actual = M.fromList (getWireTypeCandidates input)
    unless (all (\n -> maybe False (itBool `elem`) (M.lookup n actual))
                ["child$LEFT","child.LEFT","LEFT"]) $
        error ("split output lost its observation: " ++ show actual)
    unless (all (\n -> maybe True (itBool `notElem`) (M.lookup n actual))
                ["child$RIGHT","child.RIGHT","RIGHT","get"]) $
        error ("split output observation escaped to another port: " ++ show actual)
    putStrLn "PASS: split result evidence follows only its physical output port"


checkEmittedNames :: IO ()
checkEmittedNames = do
    let bt = ATBit 1
        old = "bits__h112"
        target = "bits__h1"
        port = ASPort bt (mk_homeless_id "input")
        other = ASPort bt (mk_homeless_id "other")
        raw = (package [("input",itBitN 1)] []) {
                apkg_local_defs = [ADef (mk_homeless_id old) bt port [],
                                   ADef (mk_homeless_id target) bt other []],
                apkg_expr_types = [(port,S.singleton itBool),(other,S.singleton itClock)] }
        final = raw { apkg_final_wire_names = Just (M.fromList [(old,target),("input","input")]) }
        mapped = M.fromList (getWireTypeCandidates final)
        staged = M.fromList (getWireTypeCandidates raw)
    unless (M.lookup target mapped == Just [itBool] && M.notMember old mapped) $
        error ("stale-name collision contaminated final type: " ++ show mapped)
    unless (M.lookup old staged == Just [itBool] && M.lookup target staged == Just [itClock] &&
            maybe False (itBool `elem`) (M.lookup "input" staged)) $
        error ("pre-codegen APackage fallback lost source observations: " ++ show staged)
    let identity = raw { apkg_final_wire_names = Just (M.singleton old old) }
    unless (M.lookup old (M.fromList (getWireTypeCandidates identity)) == Just [itBool]) $
        error "identity emitted-name map lost an internal type"
    let dollars = (package [("x$OUT",itBitN 1)] []) {
                    apkg_expr_types = [(ASPort bt (mk_homeless_id "x$OUT"),S.singleton itBool)],
                    apkg_final_wire_names = Just (M.singleton "x$OUT" "x_OUT") }
    unless (M.lookup "x_OUT" (M.fromList (getWireTypeMap dollars)) == Just itBool) $
        error "renamed declared wire did not retain its type evidence"
    let cached = final { apkg_final_wire_types = Just (M.singleton target (S.singleton itClock)) }
    unless (M.lookup target (M.fromList (getWireTypeCandidates cached)) == Just [itClock]) $
        error "pre-backend observations overrode the final physical candidate map"
    let emptyFinal = final { apkg_final_wire_types = Just M.empty }
    unless (M.notMember target (M.fromList (getWireTypeCandidates emptyFinal))) $
        error "authoritative empty final map fell back to stale observations"
    putStrLn "PASS: emitted names, stale-name exclusion, identity, staged fallback, dollar aliases"

checkSourceTypeAnchors :: IO ()
checkSourceTypeAnchors = do
    let n = mk_homeless_id
        bt = ATBit 8
        p = ASPort bt (n "input")
        e1 = APrim (n "site1") bt PrimAdd [p,ASInt (n "lit1") bt (ilDec 3)]
        e2 = APrim (n "site2") bt PrimAdd [p,ASInt (n "lit2") bt (ilSizedHex 8 3)]
        x = n "x"
        y = n "y"
        defs = [ADef x bt e1 [], ADef y bt e2 []]
        observations = [(ASDef bt x,S.singleton itBool),(ASDef bt y,S.singleton itClock)]
        both = S.fromList [itBool,itClock]
        lookupTypes = sourceTypeLookup defs observations
    unless (e1 == e2 && compare e1 e2 /= EQ &&
            compare (sourceTypeKey e1) (sourceTypeKey e2) == EQ &&
            lookupTypes (ASDef bt x) == both && lookupTypes (ASDef bt y) == both) $
        error "metadata key did not unite equivalent primitive/literal IDs"
    let calls = [AMethCall bt (n receiver) (n "get") [e1] | receiver <- ["a","b"]]
        tasks = [ATaskValue bt (n "task") "task" True cookie | cookie <- [1,2]]
    unless (sourceTypeKey (head calls) /= sourceTypeKey (last calls) &&
            sourceTypeKey (head tasks) /= sourceTypeKey (last tasks)) $
        error "metadata key merged distinct method receivers or task calls"
    -- An early alias disappears before a later RHS simplification. Retained
    -- output anchors must carry its evidence to the newly shared value.
    let out1 = n "out1"
        out2 = n "out2"
        different = APrim (n "other") bt PrimBAnd [p,p]
        old = [ADef x bt e1 [], ADef y bt different [],
               ADef out1 bt (ASDef bt x) [], ADef out2 bt (ASDef bt y) []]
        inlined = [ADef out1 bt e1 [], ADef out2 bt different []]
        kept = inlineDroppedExprTypes old inlined observations
        rewritten = [ADef out1 bt e1 [], ADef out2 bt e2 []]
        result = namedSourceTypes rewritten kept
    unless (M.lookup "out1" result == Just both && M.lookup "out2" result == Just both) $
        error "dropped alias or later equivalent RHS lost source candidates"
    unless (anchorSourceTypes defs (anchorSourceTypes defs observations) ==
            anchorSourceTypes defs observations) $
        error "repeated anchoring accumulated duplicate observations"
    putStrLn "PASS: metadata key normalization, call identity, dropped aliases, later RHS convergence"
    let unknown = ASAny bt Nothing
        compound = APrim defaultAId bt PrimAdd [p,unknown]
        unknownDefs = [ADef (n "u1") bt unknown [], ADef (n "u2") bt unknown [],
                       ADef (n "alias1") bt (ASDef bt (n "u1")) [],
                       ADef (n "alias2") bt (ASDef bt (n "alias1")) [],
                       ADef (n "nested1") bt compound [],
                       ADef (n "nested2") bt compound []]
        unknownTypes = [(ASDef bt (n "u1"),S.singleton itBool),
                        (ASDef bt (n "nested1"),S.singleton itBool),
                        (unknown,S.singleton itClock),(compound,S.singleton itClock)]
        anchored = anchorSourceTypes unknownDefs unknownTypes
        expected = M.fromList [(name,S.singleton itBool) |
                              name <- ["u1","alias1","alias2","nested1"]]
        actual = namedSourceTypes unknownDefs anchored
        rawPackage = (package [] []) {
            apkg_local_defs = unknownDefs, apkg_expr_types = unknownTypes,
            apkg_final_wire_names = Just (M.fromList [(name,name) |
                name <- ["u1","u2","alias1","alias2","nested1","nested2"]]) }
    unless (actual == expected &&
            M.fromList (getWireTypeCandidates rawPackage) == M.map S.toList expected) $
        error "unspecified choices spread evidence between independent definitions"
    putStrLn "PASS: unspecified definitions keep independent identities while real aliases share"


-- Retained anchors and CSE may provide one observation per alias of a value.
-- The result has one entry per alias, even when every observation reaches all
-- of them. Distinct interpretations must be united before that expansion.
aliasPackage :: Int -> APackage
aliasPackage count = (package [] []) {
    apkg_local_defs = [ADef (ident i) bt (rhs i) [] | i <- [1..count]],
    apkg_expr_types = [(ASDef bt (ident i), S.singleton itBool) | i <- [1..count]],
    apkg_final_wire_names = Just (M.fromList [(label i, label i) | i <- [1..count]]) }
  where
    bt = ATBit 8
    label i = "alias" ++ show i
    ident = mk_homeless_id . label
    rhs i | i > 1 && odd i = ASDef bt (ident 1)
          | otherwise = APrim (mk_homeless_id ("site" ++ show i)) bt PrimAdd
              [ASPort bt (mk_homeless_id "input"),
               ASInt (mk_homeless_id ("literal" ++ show i)) bt (ilDec 3)]

checkObservedAliases :: IO ()
checkObservedAliases = do
    let count = 7
        base = aliasPackage count
        names = map fst (M.toList (maybe M.empty id (apkg_final_wire_names base)))
        refs = [ASDef (ATBit 8) (mk_homeless_id n) | n <- names]
        observations = apkg_expr_types base ++
            [(head refs, S.fromList [itBool,itClock,itBitN 8]),
             (last refs, S.empty), (last refs, S.singleton itClock)]
        input = base { apkg_expr_types = observations,
                       apkg_external_wire_types = M.fromList
                           [(VName "alias2",itBitN 8),(VName "alias1",itClock)] }
        expected = M.fromList [(n, S.fromList ([itBool,itClock] ++
                                       [itBitN 8 | n == "alias2"])) | n <- names]
        candidates = M.fromList [(n,S.fromList ts) | (n,ts) <- getWireTypeCandidates input]
    unless (candidates == expected) $
        error ("shared aliases lost candidate interpretations: " ++ show candidates)
    unless (getWireTypeMap input == [("alias1",itClock),("alias2",itBitN 8)]) $
        error "shared interpretations changed declared legacy types or order"
    unless (getWireTypeMap base == [(n,itBool) | n <- names]) $
        error "singleton shared interpretation changed legacy alias order"
    unless (getWireTypeCandidates input == getWireTypeCandidates
                (input { apkg_expr_types = reverse observations })) $
        error "alias candidate union depends on observation order"
    putStrLn "PASS: shared aliases union all interpretations and preserve legacy order"


checkCachedBoundaryAliases :: IO ()
checkCachedBoundaryAliases = do
    let n = mk_homeless_id
        bt = ATBit 8
        expression = APrim defaultAId bt PrimAdd
            [ASPort bt (n "raw"), ASInt defaultAId bt (ilDec 3)]
        input = (package [(name,itBitN 8) |
                    name <- ["boundaryAlias","port","physical","stale"]] []) {
            apkg_local_defs = [ADef (n name) bt expression [] |
                               name <- ["boundaryAlias","hidden","stale"]],
            apkg_expr_types = [(expression,S.singleton itBool),
                               (ASPort bt (n "port"),S.singleton itClock)],
            apkg_final_wire_names = Just (M.fromList
                [("boundaryAlias","physical"),("port","port_renamed"),("stale","stale")]),
            apkg_final_wire_types = Just (M.fromList
                [("physical",S.singleton itClock),("stale",S.singleton itClock),
                 ("port_renamed",S.singleton itBool)]) }
        expected = M.fromList [(name,S.fromList [itBitN 8,t]) | (name,t) <-
            [("boundaryAlias",itBool),("port",itClock),("physical",itClock),
             ("stale",itClock),("port_renamed",itBool)]]
        candidates pkg = M.fromList [(name,S.fromList ts) |
                                    (name,ts) <- getWireTypeCandidates pkg]
    unless (candidates input == expected) $
        error ("cached candidates lost boundaries or exposed stale aliases: " ++ show (candidates input))
    let emptyCache = (aliasPackage 7) { apkg_final_wire_types = Just M.empty }
    unless (null (getWireTypeCandidates emptyCache) && null (getWireTypeMap emptyCache)) $
        error "an authoritative empty cache exposed raw internal aliases"
    putStrLn "PASS: cached physical candidates retain safe boundaries and exclude raw internals"

benchmarkCachedAliases :: Int -> IO ()
benchmarkCachedAliases count = do
    let base = aliasPackage count
        input = base { apkg_final_wire_types = fmap
                           (M.map (const (S.singleton itBool))) (apkg_final_wire_names base) }
    _ <- evaluate (force input)
    start <- getCPUTime
    result <- evaluate (force (getWireTypeCandidates input))
    end <- getCPUTime
    unless (length result == count && all ((== [itBool]) . snd) result) $
        error "incorrect cached shared-alias benchmark candidates"
    printf "%d cached aliases and observations, %d entries: %.6f CPU seconds\n"
        count (length result) (fromIntegral (end - start) / 1e12 :: Double)

benchmarkAliases :: Int -> IO ()
benchmarkAliases count = do
    let input = aliasPackage count
    _ <- evaluate (force input)
    start <- getCPUTime
    result <- evaluate (force (getWireTypeCandidates input))
    end <- getCPUTime
    unless (length result == count && all ((== [itBool]) . snd) result) $
        error "incorrect shared-alias benchmark candidates"
    printf "%d shared aliases and observations, %d entries: %.6f CPU seconds\n"
        count (length result) (fromIntegral (end - start) / 1e12 :: Double)

benchmark :: Int -> IO ()
benchmark count = do
    let input = package []
            [ instanceWithType ("wire" ++ show i) (itBitN 32)
            | i <- [1..count] ]
    -- Exclude package construction; force the entire result inside the
    -- timed interval. This measures analysis, not Tcl/type rendering.
    _ <- evaluate (force input)
    start <- getCPUTime
    result <- evaluate (force (getWireTypeMap input))
    end <- getCPUTime
    unless (length result == 2 * count) $
        error "incorrect benchmark candidate count"
    printf "%d instances, %d entries: %.6f CPU seconds\n"
        count (length result) (fromIntegral (end - start) / 1e12 :: Double)

main :: IO ()
main = do
    args <- getArgs
    case args of
        [] -> checkPairs >> checkSplitOutputs >> checkEmittedNames >> checkSourceTypeAnchors >> checkObservedAliases >> checkCachedBoundaryAliases
        ["--cached-aliases",arg] | Just count <- readMaybe arg, count > 0 -> benchmarkCachedAliases count
        ["--aliases",arg] | Just count <- readMaybe arg, count > 0 -> benchmarkAliases count
        [arg] | Just count <- readMaybe arg, count > 0 -> benchmark count
        _ -> error "usage: WireTypeMapCheck [[--aliases|--cached-aliases] positive-count]"
