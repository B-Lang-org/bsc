-- Source type observations are annotations, not hardware liveness roots.
module ATypePropagation (propagateSourceTypes, propagateSourceTypesFrom,
                         muxDataChildren) where

import Data.List (foldl')
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import ASyntax
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
propagateSourceTypesFrom _ _ _ [] = []
propagateSourceTypesFrom dataChildren roots defs observations =
    M.elems inferred ++ localObservations
  where
    addDefinition graph (ADef i t rhs _) =
        let (lhsNode, graph1) = addExpr (ASDef t i) graph
            (rhsNode, graph2) = addExpr rhs graph1
        in valueEdge lhsNode rhsNode graph2
    defined = foldl' addDefinition emptyGraph defs
    discovered = foldl' (\graph e -> snd (addExpr e graph)) defined roots
    (graph, initial) = foldl' addObservation (discovered, IM.empty) observations
    addObservation (g, pending) (e, ts)
        | S.null ts = (g, pending)
        | otherwise = let (node, g') = addExpr e g
                      in (g', IM.insertWith S.union node ts pending)
    inferred = M.fromList
        [(sourceTypeKey e, (e, ts)) |
          (node, ts) <- IM.toList (go IM.empty initial),
          Just (Just e, _) <- [IM.lookup node (nodeInfo graph)]]
    -- Constants and expressions containing unspecified choices have no
    -- context-independent identity. Keep direct observations, but never
    -- serialize inferred observations that would reconnect private nodes on
    -- the next pass. Named ASDef anchors still retain their inferred types.
    localObservations = [(e, ts) | (e, ts) <- observations,
                                   not (stableExpression e), not (S.null ts)]
    go seen pending = case IM.minViewWithKey pending of
        Nothing -> seen
        Just ((node, incoming), rest) ->
            let old = IM.findWithDefault S.empty node seen
                delta = incoming `S.difference` old
            in if S.null delta then go seen rest
               else let seen' = IM.insert node (old `S.union` delta) seen
                        adjacent = IM.findWithDefault IS.empty node (links graph)
                        pending' = IS.foldl'
                            (\q n -> IM.insertWith S.union n delta q) rest adjacent
                    in seen' `seq` pending' `seq` go seen' pending'

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
                in (node, arrayEdges e node children g4)

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
    unknownNodes :: !IS.IntSet
    }

emptyGraph :: Graph
emptyGraph = Graph 0 M.empty IM.empty IM.empty IM.empty IS.empty

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
