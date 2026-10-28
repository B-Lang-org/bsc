-- Source type observations are annotations, not hardware liveness roots.
module ATypePropagation (propagateSourceTypes, propagateSourceTypesFrom,
                         propagateSourceTypesWithPrimitives, muxDataChildren) where

import Data.List (foldl')
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import ASyntax
import CType (TISort(..))
import ISyntax (IType(..), IKind(..))
import ISyntaxUtil (itBool)
import IntLit (ilValue)
import PreIds (idInt, idUInt)
import ASyntaxUtil (aType)
import ASourceTypes (SourceTypeInfo, sourceTypeKey)
import Prim (PrimOp(..))

-- Selection groups share candidate interpretations in both directions. The
-- callback gives DATA child positions, keeping selectors distinct even when
-- a selector and a value happen to be equal-looking unspecified expressions.
propagateSourceTypes :: (AExpr -> [Int]) -> [ADef] ->
                        SourceTypeInfo -> SourceTypeInfo
propagateSourceTypes children = propagateSourceTypesFrom children []

-- Include live expression roots outside definitions (instance arguments and
-- foreign calls) as well as historical metadata roots. Discover the entire
-- graph before seeding it: a typed leaf can inform an untyped enclosing mux.
propagateSourceTypesFrom :: (AExpr -> [Int]) -> [AExpr] -> [ADef] ->
                            SourceTypeInfo -> SourceTypeInfo
propagateSourceTypesFrom = propagateTypes False

-- Opt-in semantic primitive rules. Run before lowering erases signedness;
-- ordinary selection propagation intentionally retains its existing boundary.
propagateSourceTypesWithPrimitives :: (AExpr -> [Int]) -> [AExpr] -> [ADef] ->
                                      SourceTypeInfo -> SourceTypeInfo
propagateSourceTypesWithPrimitives = propagateTypes True

propagateTypes :: Bool -> (AExpr -> [Int]) -> [AExpr] -> [ADef] ->
                  SourceTypeInfo -> SourceTypeInfo
propagateTypes False _ _ _ [] = []
propagateTypes withPrimitives dataChildren roots defs observations =
    M.elems inferred ++ localObservations
  where
    addDefinition graph (ADef i t rhs _) =
        let (lhsNode, graph1) = addExpr (ASDef t i) graph
            (rhsNode, graph2) = addExpr rhs graph1
        in valueEdge lhsNode rhsNode graph2
    defined = foldl' addDefinition emptyGraph defs
    discovered = foldl' (\graph e -> snd (addExpr e graph)) defined roots
    (graph, observed) = foldl' addObservation (discovered, IM.empty) observations
    initial = IM.unionWith S.union observed (primitiveSeeds graph)
    addObservation (g, pending) (e, ts)
        | S.null ts = (g, pending)
        | otherwise = let (node, g') = addExpr e g
                      in (g', IM.insertWith S.union node ts pending)
    inferred = M.fromList
        [(sourceTypeKey e, (e, ts)) |
          (node, ts) <- IM.toList (go IM.empty IM.empty initial),
          Just (Just e, _) <- [IM.lookup node (nodeInfo graph)]]
    -- Constants and expressions containing unspecified choices have no
    -- context-independent identity. Keep direct observations, but never
    -- serialize inferred observations that would reconnect private nodes on
    -- the next pass. Named ASDef anchors still retain their inferred types.
    localObservations = [(e, ts) | (e, ts) <- observations,
                                   not (stableExpression e), not (S.null ts)]
    go seen numeric pending = case IM.minViewWithKey pending of
        Nothing -> seen
        Just ((node, incoming), rest) ->
            let old = IM.findWithDefault S.empty node seen
                delta = incoming `S.difference` old
            in if S.null delta then go seen numeric rest
               else let seen' = IM.insert node (old `S.union` delta) seen
                        adjacent = IM.findWithDefault IS.empty node (links graph)
                        pending' = IS.foldl'
                            (\q n -> IM.insertWith S.union n delta q) rest adjacent
                        families = if withPrimitives then numericFamilies (nodeType graph node) delta else S.empty
                        numeric' = if S.null families then numeric else
                            IM.insertWith S.union node families numeric
                        -- Only the at-most-two numeric families activate rules.
                        -- Nominal candidates never trigger repeated scans.
                        rules = if S.null families then [] else
                            IM.findWithDefault [] node (numericRules graph)
                        pending'' = foldl' (applyNumericRule graph numeric') pending' rules
                    in seen' `seq` pending'' `seq` go seen' numeric' pending''

    addExpr e g =
        let key = sourceTypeKey e
            stable = stableExpression e
        in case if stable then M.lookup key (expressionNodes g) else Nothing of
            Just node -> (node, g)
            Nothing ->
                let (node, g1) = freshNode (aType e)
                                    (if stable then Just e else Nothing) g
                    keyed = if stable then g1 { expressionNodes =
                                  M.insert key node (expressionNodes g1) } else g1
                    g2 = if isUnknown e then keyed { unknownNodes =
                                  IS.insert node (unknownNodes keyed) } else keyed
                    addChild (ns, state) child =
                        let (n, state') = addExpr child state
                        in (n : ns, state')
                    (reversed, g3) = foldl' addChild ([], g2) (expressionChildren e)
                    children = reverse reversed
                    selected = IS.fromList (dataChildren e)
                    g4 = foldl' (\state (n, child) ->
                                     if IS.member n selected
                                     then valueEdge node child state else state)
                                g3 (zip [0..] children)
                in (node, (if withPrimitives then primitiveRules e node children else id)
                              (arrayEdges e node children g4))

-- Each expression has one value node. Array expressions additionally have an
-- element hub at each dimension. Hubs carry element candidates, never an
-- invented source type for the aggregate, and avoid quadratic sibling edges.
type Node = Int
data Graph = Graph {
    nextNode :: !Node,
    expressionNodes :: !(M.Map AExpr Node),
    nodeInfo :: !(IM.IntMap (Maybe AExpr, AType)),
    links :: !(IM.IntMap IS.IntSet),
    elementHubs :: !(IM.IntMap Node),
    unknownNodes :: !IS.IntSet,
    literalNodes :: !IS.IntSet,
    primitiveSeeds :: !(IM.IntMap (S.Set IType)),
    numericRules :: !(IM.IntMap [NumericRule])
    }

emptyGraph :: Graph
emptyGraph = Graph 0 M.empty IM.empty IM.empty IM.empty IS.empty IS.empty IM.empty IM.empty

freshNode :: AType -> Maybe AExpr -> Graph -> (Node, Graph)
freshNode t expression graph =
    let node = nextNode graph
    in (node, graph { nextNode = node + 1,
                     nodeInfo = IM.insert node (expression, t) (nodeInfo graph) })

nodeType :: Graph -> Node -> AType
nodeType graph node = snd (nodeInfo graph IM.! node)

-- Bare unknowns have no shared value identity and cannot acquire candidate
-- interpretations. Unknown-bearing compounds are private nodes, but their
-- known alternatives and real named aliases still participate normally.
isUnknownNode :: Graph -> Node -> Bool
isUnknownNode graph node = IS.member node (unknownNodes graph)

edge :: Node -> Node -> Graph -> Graph
edge a b graph
    | a == b = graph
    | otherwise = graph { links = IM.insertWith IS.union a (IS.singleton b) $
                                  IM.insertWith IS.union b (IS.singleton a) (links graph) }

elementHub :: Node -> Graph -> (Node, Graph)
elementHub node graph = case IM.lookup node (elementHubs graph) of
    Just hub -> (hub, graph)
    Nothing -> case nodeType graph node of
        ATArray _ elemType ->
            let (hub, g1) = freshNode elemType Nothing graph
            in (hub, g1 { elementHubs = IM.insert node hub (elementHubs g1) })
        _ -> error "ATypePropagation.elementHub: not an array"

valueEdge :: Node -> Node -> Graph -> Graph
valueEdge a b graph
    | isUnknownNode graph a || isUnknownNode graph b = graph
    | nodeType graph a /= nodeType graph b = graph
    | otherwise =
        let g1 = edge a b graph
        in case nodeType graph a of
            ATArray {} -> let (ha, g2) = elementHub a g1
                              (hb, g3) = elementHub b g2
                          in valueEdge ha hb g3
            _ -> g1

arrayEdges :: AExpr -> Node -> [Node] -> Graph -> Graph
arrayEdges (APrim _ (ATArray size elemType) PrimBuildArray es) node children graph
    | toInteger (length es) == size && all ((== elemType) . aType) es =
        let (hub, g1) = elementHub node graph
        in foldl' (\g (e, child) -> if isUnknown e then g
                                    else valueEdge hub child g)
                  g1 (zip es children)
arrayEdges (APrim _ resultType PrimArrayDynSelect [arr, index]) node [arrNode, _] graph
    | ATArray _ elemType <- aType arr,
      ATBit _ <- aType index,
      resultType == elemType, not (isUnknown arr) =
        let (hub, g1) = elementHub arrNode graph
        in valueEdge node hub g1
arrayEdges _ _ _ graph = graph

-- All subexpressions are visited, even below an operation which does not
-- transmit its own result interpretation to its operands.
expressionChildren :: AExpr -> [AExpr]
expressionChildren (APrim _ _ _ es) = es
expressionChildren (AMethCall _ _ _ es) = es
expressionChildren (ATuple _ es) = es
expressionChildren (ATupleSel _ e _) = [e]
expressionChildren (ANoInlineFunCall _ _ _ es) = es
expressionChildren (AFunCall _ _ _ _ es) = es
expressionChildren (ASClock _ (AClock osc gate)) = [osc, gate]
expressionChildren (ASReset _ (AReset e)) = [e]
expressionChildren (ASInout _ (AInout e)) = [e]
expressionChildren _ = []

isUnknown :: AExpr -> Bool
isUnknown ASAny {} = True
isUnknown _ = False

containsAny :: AExpr -> Bool
containsAny e = isUnknown e || any containsAny (expressionChildren e)

stableExpression :: AExpr -> Bool
stableExpression ASInt {} = False
stableExpression ASReal {} = False
stableExpression ASStr {} = False
stableExpression e = not (containsAny e)

-- Both mux forms use alternating selector/value pairs, including the default.
-- Malformed pairs introduce no edges. Never type a selector from data.
muxDataChildren :: AExpr -> [Int]
muxDataChildren (APrim _ _ op args)
    | (op == PrimMux || op == PrimPriMux), even (length args) =
        [n | (n, e) <- zip [0..] args, odd n, not (isUnknown e)]
muxDataChildren _ = []


-- Numeric transfers are directional and family-filtered, unlike value edges.
-- An arithmetic operand is not an alias of its result; copying arbitrary
-- candidates here would incorrectly turn records/enums/Bool into numeric types.
data NumericFamily = Signed | Unsigned deriving (Eq, Ord)
data NumericRule = NumericRule Node [Node] (S.Set NumericFamily)

numericType :: NumericFamily -> Integer -> IType
numericType family width = ITAp (ITCon con (IKFun IKNum IKStar) TIabstract) (ITNum width)
  where con = if family == Signed then idInt else idUInt

numericFamilies :: AType -> S.Set IType -> S.Set NumericFamily
numericFamilies (ATBit width) ts = S.fromList
    [family | ITAp (ITCon con _ _) (ITNum n) <- S.toList ts, n == width,
              (i, family) <- [(idInt, Signed), (idUInt, Unsigned)], con == i]
numericFamilies _ _ = S.empty

bothFamilies :: S.Set NumericFamily
bothFamilies = S.fromList [Signed, Unsigned]

applyNumericRule :: Graph -> IM.IntMap (S.Set NumericFamily) ->
                    IM.IntMap (S.Set IType) -> NumericRule -> IM.IntMap (S.Set IType)
applyNumericRule graph known pending (NumericRule target sources allowed) =
    case [IM.findWithDefault S.empty n known | n <- sources,
                                             not (IS.member n (literalNodes graph))] of
        [] -> pending -- constants alone are not evidence of signedness
        first : rest ->
            let families = foldl' S.intersection (S.intersection first allowed) rest
                ATBit width = nodeType graph target
                types = S.map (`numericType` width) families
            in if S.null types then pending
               else IM.insertWith S.union target types pending

primitiveRules :: AExpr -> Node -> [Node] -> Graph -> Graph
primitiveRules ASInt {} node _ graph = graph { literalNodes = IS.insert node (literalNodes graph) }
primitiveRules (APrim _ result op args) node children graph =
    case (op, args, children) of
        (p, [a,b], [na,nb]) | p `elem` comparisons, result == ATBit 1,
                              aType a == aType b, bit a ->
            let g = seed node itBool graph
            in if p `elem` [PrimSLT, PrimSLE] then numericSeed Signed [na,nb] g
               else if p `elem` [PrimULT, PrimULE] then numericSeed Unsigned [na,nb] g
               else g
        (p, _, _) | p `elem` [PrimBAnd, PrimBOr, PrimBNot], result == ATBit 1,
                    (if p == PrimBNot then length args == 1 else not (null args)),
                    all ((== ATBit 1) . aType) args ->
            foldl' (\g n -> seed n itBool g) graph (node : children)
        (PrimIf, [c,a,b], [nc,_,_]) | aType c == ATBit 1,
                                    aType a == result, aType b == result -> seed nc itBool graph
        (p, _, _) | p `elem` [PrimMux, PrimPriMux], not (null args),
                    even (length args),
                    and [aType e == if even n then ATBit 1 else result |
                         (n,e) <- zip [0::Int ..] args] ->
            foldl' (\g n -> seed n itBool g) graph [n | (k,n) <- zip [0::Int ..] children, even k]
        (p, [a,b], [na,nb]) | p `elem` [PrimSRA, PrimSRL],
                              sameResult a, bit b ->
            numericSeed (if p == PrimSRA then Signed else Unsigned) [node,na] graph
        (p, [a,b], [na,nb]) | p `elem` [PrimQuot, PrimRem], bit a, bit b,
                              result == aType (if p == PrimQuot then a else b) ->
            numericSeed Unsigned [node,na,nb] graph
        (p, _, _) | p `elem` [PrimAdd, PrimAnd, PrimOr, PrimXor],
                    not (null args), all sameResult args -> rule bothFamilies children graph
        (PrimSub, [a,b], [na,nb]) | sameResult a, sameResult b ->
            rule bothFamilies [na,nb] graph
        (p, [a], [na]) | p `elem` [PrimInv, PrimNeg], sameResult a ->
            rule bothFamilies [na] graph
        (PrimSL, [a,b], [na,_]) | sameResult a, bit b -> rule bothFamilies [na] graph
        (p, [a], [na]) | p `elem` [PrimSignExt, PrimZeroExt],
                         Just input <- width (aType a), Just output <- width result,
                         output >= input -> rule bothFamilies [na] graph
        (PrimTrunc, [a], [na]) | Just input <- width (aType a), Just output <- width result,
                               output <= input -> rule bothFamilies [na] graph
        (PrimExtract, [a,ASInt _ _ hi,ASInt _ _ lo], [na,_,_]) |
            Just input <- width (aType a), Just output <- width result,
            output <= input, ilValue lo == 0, ilValue hi == output-1 ->
                rule bothFamilies [na] graph
        (PrimMul, [a,b], [na,nb]) |
            Just aw <- width (aType a), Just bw <- width (aType b),
            result == ATBit (aw+bw) -> rule (S.singleton Unsigned) [na,nb] graph
        (PrimRange, [_,_,a], [_,_,na]) | sameResult a -> rule bothFamilies [na] graph
        _ -> graph
  where
    comparisons = [PrimEQ, PrimEQ3, PrimULT, PrimULE, PrimSLT, PrimSLE]
    width (ATBit n) | n > 0 = Just n
    width _ = Nothing
    bit = maybe False (const True) . width . aType
    sameResult a = bit a && aType a == result
    seed n t g | isUnknownNode g n = g
               | otherwise = g { primitiveSeeds = IM.insertWith S.union n (S.singleton t) (primitiveSeeds g) }
    numericSeed family ns g = foldl' (\g' n -> case width (nodeType g' n) of
        Just w -> seed n (numericType family w) g'
        Nothing -> g') g ns
    rule families sources g
        | any (isUnknownNode g) sources = g
        | otherwise = case filter (\n -> not (IS.member n (literalNodes g))) sources of
            [] -> g
            [a] -> register node [a] g
            a:b:rest ->
                -- AOpt can flatten associative primitives to arbitrary arity.
                -- Binary family hubs bound each update's work; repeatedly
                -- intersecting every operand on each arrival would be quadratic.
                let combine (left, state) right =
                        let (hub, state') = freshNode result Nothing state
                        in (hub, register hub [left,right] state')
                    (prefix, g') = foldl' combine (a,g) (b:rest)
                in register node [prefix] g'
      where
        register target inputs state =
            let r = NumericRule target inputs families
            in state { numericRules = foldl' (\m n -> IM.insertWith (++) n [r] m)
                                             (numericRules state) (S.toList (S.fromList inputs)) }
primitiveRules _ _ _ graph = graph
