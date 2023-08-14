-- RSchedule
--
-- This module exports the data type RAT (resource allocation table) and
-- the function "rSchedule" which is used by ASchedule to create the RAT.
--
module RSchedule(rSchedule, RAT) where

import Data.List((\\),partition)
import Data.Maybe(maybeToList)
import Control.Monad(when)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified GraphMap as G
import ASyntax(AId)
import AUses(RuleId, MethodId, UniqueUse, MethodUsesMap, MethodUsers,
             getMIdPosition, getUUPos, hasSideEffects, differentArgs,
             useDropCond)
import ErrorMonad(ErrorMonad(..))
import Error(internalError, EMsg, ErrMsg(..))
import Util(ordPair, mapFst)
import Flags(ResourceFlag(..))
import PFPrint(pfpString)
import Id(Id)
import Position(prPosition,getPosition)

import Util({- traces, -} allPairs)
import Debug.Trace(traceM)
import IOUtil(progArgs)
import PPrint

-- ==============================
-- Traces

trace_ralloc, trace_uugraph :: Bool
trace_ralloc = "-trace-ralloc" `elem` progArgs
trace_uugraph = "-trace-uugraph" `elem` progArgs

-- ==============================
-- Data types

type RAT = [(MethodId, [(UniqueUse, Integer)])] -- resource allocation table

-- ---------------

type UUGraph = G.GraphMap UniqueUse [UseKind]

type RRM = (RuleId, RuleId, MethodId)
type StkL = [StackItem UniqueUse RRM]

-- We mark UUGraph edges by their kind
-- ActionOf edges can be arbitrated to remove the conflict
-- (in which case the pair tells us the rules to arbitrate).
-- Other edges can't be arb'd, so the info is currently just for debugging?
data UseKind = PredicateOf (RuleId,RuleId)  -- one use is in a rule predicate
             | ActionOf    (RuleId,RuleId)  -- uses are only in rule bodies
             | InstanceOf  (AId,AId)  -- one use is in a submodule instance
     deriving (Eq, Ord, Show)

instance PPrint (UseKind) where
    pPrint d p (PredicateOf x) = text "predicate:" <+> pPrint d p x
    pPrint d p (ActionOf x) = text "action:" <+> pPrint d p x
    pPrint d p (InstanceOf x) = text "instance:" <+> pPrint d p x

data StackItem v r = Vertex (v,[v]) | Edge r

-- ==============================
-- rSchedule

-- assign resources and drop conflicting edges
-- XXX: mapM should be foldM!!!

-- Inputs:
--  * moduleId
--  * rFlag
--  * RMaxs
--  * rMap
--  * areSimult
-- Output:
--  * RAT
--  * [RRM]

rSchedule :: Id -> ResourceFlag -> [(MethodId,Integer)] -> MethodUsesMap ->
             (RuleId -> RuleId -> Bool) -> ErrorMonad (RAT,[RRM])
rSchedule moduleId rFlag rMaxs rMap areSimult =
    let
        concatTuple (xxs,yys) = (concat xxs, concat yys)
        f = rSchedule' moduleId rFlag rMaxs areSimult
    in
        mapM f (M.toList rMap) >>= return . concatTuple . unzip


rSchedule' :: Id -> ResourceFlag -> [(MethodId,Integer)] ->
              (RuleId -> RuleId -> Bool) ->
              (MethodId, [(UniqueUse, MethodUsers)]) ->
              ErrorMonad (RAT, [RRM])
rSchedule' moduleId rFlag rMaxs areSimult mu@(mId, uses0) =
    let
        -- XXX condition-insensitive resource allocation
        -- our graph allocation is not smart enough to handle
        -- different expression uses with the same arguments
        -- but different conditions, so we drop them here and in AState.hs
        uses = mapFst useDropCond uses0
        rMax = lookupRes mId rMaxs

        g :: UUGraph
        g = uuGraph areSimult uses

        dropEdges =
            case rFlag of
                RFoff -> -- don't reschedule
                         errDropEdges mId rMax
                RFsimple -> -- reschedule
                            -- arbitrate resource (drop edge in graph)
                            simpleDropEdges moduleId areSimult (mId, uses) rMax
    in do
         when trace_ralloc
             (traceM $ "rSchedule: allocating " ++ show (length uses) ++
                       " uses of " ++ ppString mId ++ "; " ++
                       if rMax == 0 then "no port limit" else show rMax ++
                       " ports available")
         when trace_uugraph
             (traceM $ "rSchedule: uugraph:\n" ++ ppReadable g)
         -- when (rMax <= 0) (verifySC g)
         if length uses > 16 && fromInteger rMax >= length uses
           then return ([(mId, zip (map fst uses) [1..])], [])
           else do (colors, drops) <- color rMax dropEdges g
                   return ([(mId,colors)], drops)


-- ==============================
-- Function: uuGraph

-- build a graph with UniqueUse vertices
-- and edges where two uses are simultaneous
uuGraph :: (RuleId -> RuleId -> Bool) ->
           [(UniqueUse, MethodUsers)] ->
           UUGraph
uuGraph areSimult uUses =
    let
        gVertices = foldr (flip G.addVertex) G.empty [u | (u,_) <- uUses]

        -- edges for uses in rule actions
        --   diff arguments and uses of the same action
        --   (hasSideEffects uUse) are potential resource conflicts,
        --   requiring checking whether the uses are simultaneous (simult)
        --   (two uses of same action are ok if the action is idempotent,
        --   which is captured in the "simult" check)
        aEdges =
            [(uUse, uUse', ss) |
                ((uUse, (_, rs, _)), (uUse', (_, rs', _))) <- allPairs uUses,
                differentArgs uUse uUse' || hasSideEffects uUse,
                let ss = simult rs rs', not $ null ss]

        simult rs rs' = [ActionOf (r,r') | r <- rs, r' <- rs', areSimult r r']

        -- edges for uses in rule predicates
        -- XXX we currently assume that predicates must always occur
        -- XXX but with urgency we can be smarter (a predicate's use may
        -- XXX be exclusive with the execution of the action of a more
        -- XXX more urgent rule)
        pEdges = concat [[(uUse, uUse', ss), (uUse', uUse, ss)] |
                             (uUse, (prs, _, _)) <- uUses, not (null prs),
                             (uUse', (prs', ars', _)) <- uUses,
                             differentArgs uUse uUse',
                             let ss = [PredicateOf (p, r) |
                                           p <- prs, r <- prs'++ars']]

        -- edges for instantiations
        -- (like rule predicates, the must always occur)
        iEdges = concat [[(uUse, uUse', ss), (uUse', uUse, ss)] |
                             (uUse, (_, _, irs)) <- uUses, not (null irs),
                             (uUse', (prs', ars', irs')) <- uUses,
                             differentArgs uUse uUse',
                             let ss = [InstanceOf (p, r) |
                                           p <- irs, r <- prs'++ars'++irs']]
    in
        foldl G.addEdge gVertices (iEdges ++ pEdges ++ aEdges)


-- ==============================
-- Function: verifySC

{-
verifySC g = mapM_ err [(v,v',r) | (v,ns) <- G.toList g,
                                   (v', us) <- ns,
                                   ActionOf (r,r') <- us,
                                   r == r']
    where err bad@(u,u',r) = EMError (getIdPosition r, EGeneric (emsg bad))
          emsg (u,u',r) = "Rule `" ++ ppString r ++
                          "' uses an SC method twice: `" ++
                          ppString u ++ "' and `" ++ ppString u' ++ "'"
-}


-- ==============================
-- Error messages

errDropEdges :: MethodId -> Integer -> b -> UUGraph -> ErrorMonad a
errDropEdges mId rMax _ g = EMError [eResources mId rMax g]

eResources :: MethodId -> Integer -> UUGraph -> EMsg
eResources mId rMax g =
    (getMIdPosition mId,
     EResources (ppString mId) rMax
         (map (\u -> (ppString u, prPosition (getUUPos u))) (G.vertices g)))

-- XXX It would be nice if EArbitrate had position info
eArbitrate :: Id -> (RuleId, RuleId) -> EMsg
eArbitrate moduleId (r,r') =
    (getPosition moduleId,
     EArbitrate (pfpString moduleId) [ppString r, ppString r'])


-- ==============================
-- Function: simpleDropEdges

simpleDropEdges :: Id -> (RuleId -> RuleId -> Bool) ->
                   (MethodId, [(UniqueUse, MethodUsers)]) ->
                   Integer -> StkL -> UUGraph -> ErrorMonad (StkL, UUGraph)
simpleDropEdges moduleId areSimult (mId,uses) rMax st g =
    if all null droppable || any sameRule rs
    then errDropEdges mId rMax st g
    else EMWarning warn (st',g')
    where droppable = [map fromActionOf w
                       | v <- G.vertices g, v' <- G.neighbors g v,
                       w <- maybeToList (G.lookup (v,v') g), all isActionOf w]
          rs = case droppable of
               (xs:_) -> xs
               _      -> internalError "simpleDropEdges: nothing to drop!"
          sameRule (r,r') = r == r'
          uses' = [u | u@(uu, _) <- uses, uu `elem` G.vertices g]
          st' = [Edge (r,r',mId) | (r,r') <- rs] ++ st

          allDrops = [(r,r') | Edge (r,r',_) <- st] ++ rs
          allDropsSet = S.fromList $ map ordPair allDrops
          areSimult' r r' = (not (ordPair (r,r') `S.member` allDropsSet))
                            && areSimult r r'
          g'  = uuGraph areSimult' uses'
          fromActionOf (ActionOf x) = x
          fromActionOf _ = internalError "fromActionOf"
          isActionOf (ActionOf _) = True
          isActionOf _            = False
          warn = (eResources mId rMax g) : (map (eArbitrate moduleId) allDrops)


-- ==============================
-- Function: color

color :: Integer -> (StkL -> UUGraph -> ErrorMonad (StkL, UUGraph)) ->
         UUGraph -> ErrorMonad ([(UniqueUse,Integer)],[RRM])
color rMax dropEdges g
    | rMax > 0 = colorFw rMax dropEdges [] g >>= colorBk [1..rMax] [] []
    | otherwise = return ([(v,1) | v <- G.vertices g], [])


-- forward pass: generate stack of colorable vertices and dropped edges
colorFw :: Integer -> (StkL -> UUGraph -> ErrorMonad (StkL, UUGraph)) ->
           StkL -> UUGraph -> ErrorMonad StkL
colorFw rMax dropEdges st g
    | G.null g = return st
    | otherwise =
        case partition (colorable rMax g) (G.vertices g) of
            (cv:_, _) -> colorFw rMax dropEdges
                             (Vertex (cv, G.neighbors g cv) : st)
                             (G.deleteVertex g cv)
            (_, _) -> dropEdges st g >>= (uncurry $ colorFw rMax dropEdges)


-- backward pass: pick up vertices and color them
colorBk :: [Integer] -> [(UniqueUse,Integer)] -> [RRM] -> StkL ->
           ErrorMonad ([(UniqueUse, Integer)], [RRM])
colorBk _  cs es [] = return (cs,es)
colorBk rMaxL cs es (Vertex vns@(v,_) : vs) =
    colorBk rMaxL ((v, pickColor rMaxL cs vns):cs) es vs
-- XXX try to reintroduce edges
colorBk rMaxL cs es (Edge e : vs) = colorBk rMaxL cs (e:es) vs


colorable :: Integer -> UUGraph -> UniqueUse -> Bool
colorable rMax g v =
    (toInteger $ foldr1 max $ map length $ G.ncc $
        G.filterVertices g (`elem` v:G.neighbors g v)) <= rMax


pickColor :: [Integer] -> [(UniqueUse, Integer)] -> (a, [UniqueUse]) -> Integer
pickColor rMaxL cs (_,ns) =
    case rMaxL \\ [lookupRes n cs | n <- ns] of
        (r:_) -> r
        _     -> internalError ("pickColor\ncolors:" ++ ppReadable cs ++
                                "available:" ++ ppReadable rMaxL)


-- ==============================
-- Utility functions

lookupRes :: (Eq a, PPrint a, PPrint b) => a -> [(a,b)] -> b
-- return y s.t. (r,y) `elem` rs  or  die
lookupRes r rs = case lookup r rs of
                 (Just x) -> x
                 Nothing  -> internalError $ "RSchedule: phantom resources" ++ ppReadable r ++ ppReadable rs

-- ==============================
