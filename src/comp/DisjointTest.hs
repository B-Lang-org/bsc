module DisjointTest(
                    DisjointTestState,
                    initDisjointTestState,
                    addADefToDisjointTestState,
                    checkDisjointExpr,
                    checkDisjointExprWithCtx,
                    genDisjointSet,
                    RuleDisjointTest
                   ) where

import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad(foldM {- , when -})
import Data.List (genericIndex)

import Util(ordPair,uniquePairs)

import Error(ErrorHandle, internalError)
import Pretty
import PPrint(PPrint(..), ppReadable)

import Flags
import ASyntax
import ASyntaxUtil(AExprs(..), aAnd)
import Pragma

import VModInfo(VModInfo)
import AExpr2Util(getMethodOutputPorts)
--import Debug.Trace(trace)

import qualified AExpr2STP as STP
         (SState, initSState, addADefToSState,
          checkDisjointRulePair, checkDisjointExpr)
import qualified AExpr2Yices as Yices
         (YState, initYState, addADefToYState,
          checkDisjointRulePair, checkDisjointExpr)

-- -------------------------

type RuleDisjointTest = ARuleId -> ARuleId -> Bool

-- A single data type for either of the disjoint-testing state
data DisjointTestState = DTS_Yices DSupportMap Yices.YState
                       | DTS_STP   DSupportMap STP.SState

-- -------------------------

initDisjointTestState ::
    String -> ErrorHandle -> Flags ->
    [ADef] -> [AVInst] -> [(ARuleId, [AExpr], Maybe ARuleId)] ->
    IO DisjointTestState
initDisjointTestState str errh flags ds avis rs = do
    let supportMap = buildSupportMap ds avis rs
    case (satBackend flags) of
      SAT_Yices -> do
          yices_state <- Yices.initYState str flags True ds avis rs
          return (DTS_Yices supportMap yices_state)
      SAT_STP -> do
          stp_state <- STP.initSState str flags True ds avis rs
          return (DTS_STP supportMap stp_state)


addADefToDisjointTestState :: DisjointTestState -> [ADef] ->
                              IO DisjointTestState
addADefToDisjointTestState (DTS_Yices m yices_state) ds = do
    yices_state' <- Yices.addADefToYState yices_state ds
    return (DTS_Yices m yices_state')
addADefToDisjointTestState (DTS_STP m stp_state) ds = do
    stp_state' <- STP.addADefToSState stp_state ds
    return (DTS_STP m stp_state')

-- -------------------------

checkDisjointExpr :: DisjointTestState -> AExpr -> AExpr ->
                     IO (Maybe Bool, DisjointTestState)
checkDisjointExpr (DTS_Yices m yices_state) e1 e2 = do
    (res, yices_state') <- Yices.checkDisjointExpr yices_state e1 e2
    return (res, DTS_Yices m yices_state')
checkDisjointExpr (DTS_STP m stp_state) e1 e2 = do
    (res, stp_state') <- STP.checkDisjointExpr stp_state e1 e2
    return (res, DTS_STP m stp_state')

-- When testing conditions on methods inside one rule (or two rules),
-- we also want to consider the predicates of the rules; the conditions
-- on the methods might not be disjoint, but are disjoint when the rule
-- condition is True.
--
-- XXX We assume that it's easier to test without the predicates first,
-- XXX then test again if that reports not-disjoint.
--
-- XXX For tests within the same rule, might it be cheaper to assert
-- XXX the predicate once?  Particularly if this function is being
-- XXX called many times for the same rule?
--
-- XXX This function could take the rule Ids as arguments, and look up
-- XXX the predicate from the state.
--
checkDisjointExprWithCtx ::
    DisjointTestState -> AExpr -> AExpr -> AExpr -> AExpr ->
    IO (Maybe Bool, DisjointTestState)
checkDisjointExprWithCtx dts ctx1 ctx2 e1 e2 = do
    (res, dts') <- checkDisjointExpr dts e1 e2
    case res of
      Just True -> return (res, dts')
      _ -> do -- try again but with the context included
              let e1' = aAnd ctx1 e1
                  e2' = aAnd ctx2 e2
              checkDisjointExpr dts' e1' e2'

-- -------------------------

genDisjointSet :: DisjointTestState -> [ARuleId] -> [ASchedulePragma] ->
                  IO (S.Set (ARuleId, ARuleId), DisjointTestState)
genDisjointSet dt_state ruleNames pragmas = do
  let me_state = makeMETest pragmas

      addResult :: S.Set (ARuleId, ARuleId) -> (ARuleId, ARuleId) -> Maybe Bool -> S.Set (ARuleId, ARuleId)
      addResult rset (r1,r2) (Just True) = S.insert (r1,r2) (S.insert (r2,r1) rset)
      addResult rset _ _                 = rset

      foldFn (rset, st) p =
          case (checkMERulePair me_state p) of
            res@(Just _) -> let rset' = addResult rset p res
                            in  return (rset', st)
            _            -> do (res, st') <- checkDisjointRulePairTop st p
                               let rset' = addResult rset p res
                               return (rset', st')

  (res, dt_state') <- foldM foldFn (S.empty, dt_state) (uniquePairs ruleNames)

  return (res, dt_state')


supportIntersects :: DSupportMap -> (ARuleId, ARuleId) -> Bool
supportIntersects m (r1, r2) = S.null $ S.intersection s1 s2
    where s1 = lookupSupport m r1
          s2 = lookupSupport m r2


checkDisjointRulePairTop :: DisjointTestState -> (ARuleId, ARuleId) ->
                         IO (Maybe Bool, DisjointTestState)
checkDisjointRulePairTop s p = do
  let dis = supportIntersects (getSupportMap s) p
  if (dis) then return (Just False,s)
    else do checkDisjointRulePair s p
  -- Self check code.....
  -- (res, s') <-checkDisjointRulePair s p
  -- when (dis && (res /= Just False)) $ do
  --   putStrLn $ "DIS " ++ ppReadable p ++ " --> " ++ ppReadable (res, dis)
  --   putStrLn $ "XXXXXX " ++ ppReadable (getSupportMap s)
  --   putStrLn $ "XXXXXX " ++ ppReadable res
  --   fail "bad disjoint map"
  -- return (res, s')


checkDisjointRulePair :: DisjointTestState -> (ARuleId, ARuleId) ->
                         IO (Maybe Bool, DisjointTestState)
checkDisjointRulePair s@(DTS_Yices m yices_state) p = do
    (res, yices_state') <- Yices.checkDisjointRulePair yices_state p
    return (res, DTS_Yices m yices_state')
checkDisjointRulePair s@(DTS_STP m stp_state) p = do
    (res, stp_state') <- STP.checkDisjointRulePair stp_state p
    return (res, DTS_STP m stp_state')

-- -------------------------

type MEMap  = M.Map ARuleId [Integer] -- map rid to a list of me sets
type METest = M.Map (Integer,Integer) (Maybe Bool)


checkMERulePair :: (MEMap, METest) -> (ARuleId,ARuleId) -> Maybe Bool
checkMERulePair (me_map, me_test) (rule1,rule2) =
  case (M.lookup rule1 me_map, M.lookup rule2 me_map) of
          (Just nums1, Just nums2) -> checkMEPairs me_test nums1 nums2
          _                        -> Nothing

checkMEPairs :: METest -> [Integer] -> [Integer] -> Maybe Bool
checkMEPairs me_test [] _  = Nothing
checkMEPairs me_test _  [] = Nothing
checkMEPairs me_test (num1:rest) nums2 =
      let fn [] = Nothing
          fn (num2:rest) = case (M.lookup (ordPair (num1, num2)) me_test) of
                             (Just res) -> res
                             _          -> fn rest
      in  case (fn nums2) of
            (Just y) -> (Just y)
            _        -> checkMEPairs me_test rest nums2


makeMETest :: [ASchedulePragma] -> (MEMap, METest)
makeMETest spms = fst $ foldl addMESPM ((M.empty, M.empty), 0) spms

addMESPM :: ((MEMap, METest), Integer) -> ASchedulePragma ->
            ((MEMap, METest), Integer)
addMESPM s (SPMutuallyExclusive ids) = addMEIds s ids
addMESPM s _ = s

addMEIds :: ((MEMap, METest), Integer) -> [[ARuleId]] ->
            ((MEMap, METest), Integer)
addMEIds s idss =
  let -- XXX this is also in ASchedule
      mkMEPairs [] = []
      mkMEPairs ([]:rest) = mkMEPairs rest
      mkMEPairs (ids:rest) = [(ids, r) | r <- rest] ++ (mkMEPairs rest)

      addMEPair (ids0, ids1) ((me_map, me_test), num) =
          let me_map1 = foldl (addMEId num) me_map ids0
              me_map2 = foldl (addMEId (num+1)) me_map1 ids1
              me_test1 = M.insert (num, num+1) (Just True) me_test
          in  ((me_map2, me_test1), num+2)
  in
      foldr addMEPair s (mkMEPairs idss)

addMEId :: Integer -> MEMap -> ARuleId -> MEMap
addMEId num me_map id = do
  case (M.lookup id me_map) of
      Just nums -> M.insert id (num:nums) me_map
      Nothing   -> M.insert id [num]      me_map

-- -------------------------
-- Disjoint testing can be avoided if there is no overlap i the logic cones of each rule,
-- that is f(as) == 1 and g(bs) == 1 can be satisfied if set as /= set bs
-- we build a map containing the support set (as, bs) for each Aid,  rule
type DSupportMap =  M.Map AId (S.Set ASupport)
data ASupport = DMethod AId AId -- state port
                | DLeaf AId
                | DDef ADef AId
                | DClkGate AId AId
                | DTask AId
                deriving (Show, Eq, Ord)


isLeafDef :: ASupport -> Bool
isLeafDef (DMethod _ _)  = True
isLeafDef (DLeaf _)      = True
isLeafDef (DClkGate _ _) = True
isLeafDef (DTask _)      = True
isLeafDef (DDef _ _)     = False

lookupSupport :: DSupportMap -> AId -> (S.Set ASupport)
lookupSupport m d = M.findWithDefault err d m
    where err = error $ "DisjointTests findSupport, bad lookup: " ++ show d
                ++ "\n" ++ show m

buildSupportMap :: [ADef] -> [AVInst] -> [(ARuleId, [AExpr], Maybe ARuleId)] -> DSupportMap
buildSupportMap adefs avis rs = --trace ("XXX support map:" ++ ppReadable res) $
                                res
  where
    res = foldl generator M.empty [(id,es) | (id,es,_) <- rs]
    --
    idToDef:: M.Map AId ADef
    idToDef     = M.fromList [ (id, def) | def@(ADef id _ _ _) <- adefs]
    err i = error $ "DisjointTest::buildSupportMap Invalid lookup in idtodefmap: " ++ show i ++ "\n" ++ show idToDef
    --
    portMap :: M.Map AId VModInfo
    portMap = M.fromList [(avi_vname avi, avi_vmi avi) | avi <- avis]
    --
    generator :: (AExprs a) => DSupportMap -> (AId,a) -> DSupportMap
    generator m (id, es) | M.member id m = m
                         | otherwise = m''
      where
        fanins = findAExprs findSupport es
        faninIds = [ id | (DDef def id) <- fanins]
        m' = foldl generator m [ (id,def) | (DDef def id) <- fanins]
        --
        localSupports = S.fromList $ filter isLeafDef fanins
        childSupports = S.unions $ map (lookupSupport m') faninIds
        m'' = M.insert id (localSupports `S.union` childSupports) m'
    --
    findSupport                                          :: AExpr -> [ASupport]
    findSupport e@(ASDef _ i)                            = [DDef def i]
        where def = M.findWithDefault (err i) i idToDef
    findSupport e@(APrim { ae_args = es})                = findAExprs findSupport es
    findSupport e@(AMethCall {ae_args = es})             =
      case getMethodOutputPorts portMap (ae_objid e) (ameth_id e) of
        [vlogport] -> findAExprs findSupport es ++ [DMethod (ae_objid e) vlogport]
        ports -> internalError ("buildSupportMap: unexpected output ports: "
                                ++ ppReadable (ae_objid e, ameth_id e, ports))
    findSupport e@(AMethValue {})                        =
      case getMethodOutputPorts portMap (ae_objid e) (ameth_id e) of
        [vlogport] -> [DMethod (ae_objid e) vlogport]
        ports -> internalError ("buildSupportMap: unexpected output ports: "
                                ++ ppReadable (ae_objid e, ameth_id e, ports))
    findSupport e@(ATupleSel _ (AMethCall {ae_args = es}) idx) =
        findAExprs findSupport es ++ [DMethod (ae_objid e) vlogport]
        where
          ports = getMethodOutputPorts portMap (ae_objid e) (ameth_id e)
          vlogport = genericIndex ports (idx - 1)
    findSupport e@(ATupleSel _ (AMethValue {}) idx) =
        [DMethod (ae_objid e) vlogport]
        where
          ports = getMethodOutputPorts portMap (ae_objid e) (ameth_id e)
          vlogport = genericIndex ports (idx - 1)
    findSupport e@(ANoInlineFunCall{ ae_args = es})      = findAExprs findSupport es
    findSupport e@(ATaskValue {ae_objid=id})             = [DTask id]
    findSupport e@(ASPort {ae_objid = id})               = [DLeaf id]
    findSupport e@(ASParam {ae_objid = id})              = [DLeaf id]
    findSupport e@(ASInout {ae_expi = aio})              = findAExprs findSupport wires
        where wires = ainout_wire aio
    findSupport e@(AMGate {ae_objid = id, ae_clkid=clk}) = [DClkGate id clk]
    findSupport _                                        = []

-- -------------------------
getSupportMap :: DisjointTestState -> DSupportMap
getSupportMap (DTS_Yices m _) = m
getSupportMap (DTS_STP m _)   = m


instance PPrint ASupport where
    pPrint d _ (DMethod i m) = parens $ text "DMethod" <+> pPrint d 0 (i,m)
    pPrint d _ (DLeaf   i)   = parens $ text "DLeaf" <+> pPrint d 0 i
    pPrint d _ (DDef _ i)    = parens $ text "DDef" <+> pPrint d 0 i
    pPrint d _ (DClkGate m c) = parens $ text "DClkGate" <+> pPrint d 0 (m,c)
    pPrint d _ (DTask i)    = parens $ text "DTask" <+> pPrint d 0 i
