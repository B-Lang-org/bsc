{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, GeneralizedNewtypeDeriving #-}
-- conversion interface for reasoning about AExpr with Bdds
--
-- TODO
-- Conversion operations are still needed for some of the PrimOp, e.g, SL, SLr
--   these operations can potentially cause bdd blowup
-- Ruletest should look at parent rules,  but this is not important, as rule splitting
--   is not enabled.
-- A more robust test, which looks commom intermediate points should be implemented.
-- This would eliminate most caching, but tests would(could) be faster and
-- avoid bdd explosion

module AExpr2Bdd(

       -- state
       BddBuilder,
       initBDDState,
       addADefToBDDState,

       -- Disjoint checking
       checkDisjointRulePair,
       checkDisjointExpr,
       checkDisjointExprList,

       -- SAT
       checkImplication,
       checkBiImplication,
       isConstExpr,
       checkEq,
       checkNotEq

) where


#if !defined(__GLASGOW_HASKELL__) || (__GLASGOW_HASKELL__ < 710)
import Control.Applicative(Applicative(..))
#endif
import Control.Monad.State
import Text.Printf(printf)
import qualified Data.Map as M
import Prim(PrimOp(..))
import ASyntax
import IntLit
import CuddBdd
import Data.Maybe
import IOUtil(progArgs)
import Util(ordPair, map_insertMany, makePairs)
import Error(internalError, ErrMsg(..), ErrorHandle, bsWarning)
import Position(noPosition)
import Flags(Flags(..))
import Id(qualEq)
import PPrint
import Data.List(sortBy,find)
import VModInfo(VModInfo, vFields, VName(..), VFieldInfo(..))

-- import Util

-- -------------------------
-- The BddBuilder state monad

data AVInstKey = AVInstKey AId  VName  String
                 deriving (Eq, Ord)

instance Show AVInstKey where
    show (AVInstKey m v s) = "AVInstKey (" ++ show m ++ ", " ++  show v ++ "(" ++ s ++ "))"

instance PPrint AVInstKey where
    pPrint d p (AVInstKey m v s) = text "AVInstKey" <+>
                                   parens ((pPrint d p m) <+> (pPrint d p v) <+> parens (text s))

data BddBuilder a =
    BddBuilder{
               errHandle   :: ErrorHandle,
               bddMgr      :: BddMgr,
               defMap      :: (M.Map a ADef),
               deffailfunc :: (a -> Integer -> BddC [Bdd]),
               bddMap      :: (M.Map a [Bdd]),
               stateBddMap :: (M.Map AVInstKey [Bdd]),
               stateMap    :: (M.Map a VModInfo),
               ruleMap     :: (M.Map ARuleId RuleTriple),
               ruleTest    :: (M.Map (ARuleId,ARuleId) (Maybe Bool)),
               exprMap     :: (M.Map (AExpr) (Maybe [Bdd])),
               orderVar    :: (Int,Integer), -- (index, width) for bdd variable ordering
               bddMaxSize  :: (Double,Bool), -- Maximum bdd size for operations
               useShort    :: Bool,          -- use a short message format
               cacheSize   :: Int -- limit on when to do flushed
              }

newtype BddC a = BddC (StateT (BddBuilder AId) IO (a))
  deriving (Monad, MonadIO, Functor)

-- newtype-deriving cannot handle MonadState because it is a MPTC
instance MonadState (BddBuilder AId) BddC where
  get   = BddC get
  put s = BddC (put s)

-- StateT isn't in Applicative for earlier GHC (?) so we can't derive
instance Applicative BddC where
  pure = return
  (<*>) = ap

runBdd :: BddC a -> BddBuilder AId -> IO (a, BddBuilder AId)
runBdd  (BddC s) = runStateT s

execBdd :: BddC a -> BddBuilder AId -> IO (BddBuilder AId)
execBdd (BddC s) = execStateT s

liftIOToBdd :: IO a -> BddC a
liftIOToBdd = liftIO


type RuleTriple = (ARuleId, [AExpr], Maybe ARuleId)

-- -------------------------

debugTrace = False
traceBddConv1 = debugTrace
traceBddConv2 = False           -- Traces each bdd contruction very verbose
traceBddSize  = False
traceBddOrder = False
trace_disjoint_tests = "-trace-disjoint-tests" `elem` progArgs
trace_bdd_size       = "-trace-bdd-limit"      `elem` progArgs


ppAId = ppString

orderVarInit :: (Int,Integer)
orderVarInit = (0,1)

-- -------------------------

-- Examine if 2 AExprs are disjoint using bdd table
-- returns True if the intersection of the 2 expressions can be proven empty.
-- False if a counter example can be generated, and Nothing  otherwise.
checkDisjointExpr :: BddBuilder AId -> AExpr -> AExpr ->
                     IO ((Maybe Bool),(BddBuilder AId))
checkDisjointExpr bddb expr1 expr2 =
    do
      let (maxSize,_) = bddMaxSize  bddb
      if (maxSize <= 0.0 ) then return (Nothing,bddb)
       else do
            (disjoint,s2) <- runBdd (checkDisjointExprM (expr1,expr2)) bddb
            return (disjoint,s2)

-- returns Just True is expr1 'implies' expr2
checkImplication :: BddBuilder AId -> AExpr -> AExpr -> IO ( (Maybe Bool),(BddBuilder AId) )
checkImplication bddb expr1 expr2 =
    do
      let (maxSize,_) = bddMaxSize  bddb
      if (maxSize <= 0.0 ) then return (Nothing,bddb)
       else do
            -- putStrLn ("checkImpl: " ++ ppAll expr1 ++ " : " ++ ppAll expr2)
            (implies,s2) <- runBdd (checkImplicationsM (expr1,expr2)) bddb
            return (implies,s2)

-- returns True is expr1 'implies' expr2
checkBiImplication :: BddBuilder AId -> AExpr -> AExpr -> IO ((Bool, Bool) ,(BddBuilder AId) )
checkBiImplication bddb expr1 expr2 =
    do
      let (maxSize,_) = bddMaxSize  bddb
      if (maxSize <= 0.0 ) then return ((False, False), bddb)
       else do
            -- putStrLn ("checkImpl: " ++ ppAll expr1 ++ " : " ++ ppAll expr2)
            runBdd (checkBiImplicationsM (expr1,expr2)) bddb


-- Exported function taking a list of expressions and returning a list of disjointness
-- Bdd state is updated.
-- Save the caller the trouble of wrapping the bdd state in a monad.
checkDisjointExprList :: BddBuilder AId -> [(AExpr,AExpr)] ->
                         IO ([Maybe Bool],(BddBuilder AId))
checkDisjointExprList bddstate exprpairs =
    do
    let
      (maxSize,_) = bddMaxSize  bddstate
    if (maxSize <= 0.0 )
       then
       return ( (replicate (length exprpairs) Nothing), bddstate )
       else do
            (ress,bdds) <- runBdd (mapM checkDisjointExprM exprpairs ) bddstate
            return (ress,bdds)

-- Apply an operator to BDDs for two exprs.
-- Returns (Just True) if the result is True,
-- (Just False) if the result is False, and Nothing for any other case
checkExprM :: ([Bdd] -> [Bdd] -> BddC Bdd) -> AExpr -> AExpr -> BddC (Maybe Bool)
checkExprM op expr1 expr2 =
    do
    -- check if we want to cleanout the cache here
    cache <- gets bddMap
    when ( trace_bdd_size ) $ liftIO $
         putStrLn ( "Bdd cache size is: " ++ show (M.size cache) )
    conditionalFlushBdds
    bdd1 <- convE2Bdd expr1
    bdd2 <- convE2Bdd expr2
    when ( debugTrace ) $ liftIO $
         putStrLn ("checkExprM: " ++ ppAll expr1 ++ "expr2: " ++ ppAll expr2)
    if ( allOk [bdd1,bdd2] )
       then do v <- op (fromJust bdd1) (fromJust bdd2)
               liftIO $ bddIsConst v
       else return Nothing

checkEq :: BddBuilder AId -> AExpr -> AExpr -> IO (Maybe Bool, BddBuilder AId)
checkEq bddb expr1 expr2 = do
    let (maxSize, _) = bddMaxSize bddb
    if (maxSize <= 0.0 ) then return (Nothing, bddb)
     else do
       let eqOp v1 v2 = do mgr <- gets bddMgr
                           liftIOToBdd $ bddEQVector mgr v1 v2
       (res, bddb') <- runBdd (checkExprM eqOp expr1 expr2) bddb
       return (res, bddb')
    
checkNotEq :: BddBuilder AId -> AExpr -> AExpr -> IO (Maybe Bool, BddBuilder AId)
checkNotEq bddb expr1 expr2 = do
    let (maxSize, _) = bddMaxSize bddb
    if (maxSize <= 0.0 ) then return (Nothing, bddb)
     else do
       let notEqOp v1 v2 = do mgr <- gets bddMgr
                              eq <- liftIOToBdd $ bddEQVector mgr v1 v2
                              liftIOToBdd $ bddNot eq
       (res, bddb') <- runBdd (checkExprM notEqOp expr1 expr2) bddb
       return (res, bddb')


checkDisjointExprM :: (AExpr,AExpr) -> BddC (Maybe Bool)
checkDisjointExprM (expr1,expr2) =
    do
    -- check if we want to cleanout the cache here
    cache <- gets bddMap
    when ( trace_bdd_size ) $ liftIO $
         putStrLn ( "Bdd cache size is: " ++ show (M.size cache) )
    conditionalFlushBdds
    bdd1 <- convE2Bdd expr1
    bdd2 <- convE2Bdd expr2
    when ( debugTrace ) $ liftIO $
         putStrLn ("checkDisjointExprM: " ++ ppAll expr1 ++ "expr2: " ++ ppAll expr2)
    res <- if ( allOk [bdd1,bdd2] )
           then
               liftIO $ disjointBddTestList (fromJust bdd1) (fromJust bdd2)
           else
               return Nothing
    when ( debugTrace ) $ liftIO $
       putStrLn ("checkDisjointExprM: result: " ++ show res )
    return res

-- Must be 1 bit expressions !!!
checkImplicationsM :: (AExpr,AExpr) -> BddC (Maybe Bool)
checkImplicationsM (expr1, expr2) = do
  -- check if we want to cleanout the cache here
  cache <- gets bddMap
  when ( trace_bdd_size ) $ liftIO $
       putStrLn ( "Bdd cache size is: " ++ show (M.size cache) )
  conditionalFlushBdds
  bdd1 <- convE2Bdd expr1
  bdd2 <- convE2Bdd expr2
  case ( bdd1, bdd2 ) of
    (Just [b1], Just [b2]) -> liftIO $ bddImplies b1 b2 >>= bddIsTrue
    _                      -> return Nothing



-- Must be 1 bit expressions !!!
checkBiImplicationsM :: (AExpr,AExpr) -> BddC (Bool, Bool)
checkBiImplicationsM (expr1, expr2) = do
  -- check if we want to cleanout the cache here
  cache <- gets bddMap
  when ( trace_bdd_size ) $ liftIO $
       putStrLn ( "Bdd cache size is: " ++ show (M.size cache) )
  conditionalFlushBdds
  bdd1 <- convE2Bdd expr1
  bdd2 <- convE2Bdd expr2
  case ( bdd1, bdd2 ) of
    (Just [b1], Just [b2]) -> liftIO $ bddBiImplication b1 b2
    _                      -> return (False, False)



-- Given a list of rules,  return True if the rules are disjoint
-- that is the intersection is proven empty
-- Return False if a counter example can be generate, and Nothing otherwise
checkDisjointRules :: RuleTriple -> RuleTriple -> BddC (Maybe Bool)
checkDisjointRules (rn1,exprs1,rnp1) (rn2,exprs2,rnp2)  =
    do
    (maxSize,dowarn)  <- gets bddMaxSize
    if (maxSize <= 0.0 )
       then return Nothing
       else do
            -- mbddl1 :: [Maybe [Bdd]]
            mbddl1 <- mapM convE2Bdd exprs1
            -- each inner list should be 1 width
            -- mbddl2 :: [Maybe [Bdd]]
            mbddl2 <- mapM convE2Bdd exprs2   --
            if ( ( allOk ( mbddl1 ++ mbddl2 ) ) )
               then do
                    let
                      bddl1 = map toSingletonList $ map fromJust mbddl1
                      bddl2 = map toSingletonList $ map fromJust mbddl2
                    mgr <- gets bddMgr
                    b1  <- liftIO $ bddAndList mgr bddl1
                    b2  <- liftIO $ bddAndList mgr bddl2
                    res <- liftIO $ bddIntersect b1 b2 >>= bddIsFalse
                    --
                    when ( trace_disjoint_tests ) $ liftIO $
                         do
                         -- sb1 <- showBdd bddPrinter b1
                         -- sb2 <- showBdd bddPrinter b2
                         -- bdr <- bddIntersect b1 b2 >>= (showBdd bddPrinter)
                         -- bddAnd b1 b2 >>= bddPrintMinterms
                         putStrLn $ "checkDisjointRules: " ++ ppAId rn1
                                  ++ " r2: " ++ ppAId rn2 ++ " Result: " ++ show res
                                  -- ++ "\nbdd1: " ++ sb1
                                  -- ++ "\nbdd2: " ++ sb2
                                  -- ++ "\nbdd andR: " ++ bdr
                    --
                    return res
               else
               return Nothing

{-
-- This code is no longer used

checkIdenticalRules :: RuleTriple -> RuleTriple -> BddC (Maybe Bool)
checkIdenticalRules (rn1,exprs1,rnp1) (rn2,exprs2,rnp2)  =
    do
    (maxSize,dowarn)  <- gets bddMaxSize
    if (maxSize <= 0.0 )
       then return Nothing
       else do
            -- mbddl1 :: [Maybe [Bdd]]
            mbddl1 <- mapM convE2Bdd exprs1
            -- each inner list should be 1 width
            -- mbddl2 :: [Maybe [Bdd]]
            mbddl2 <- mapM convE2Bdd exprs2   --
            if ( ( allOk ( mbddl1 ++ mbddl2 ) ) )
               then do
                    let
                      bddl1 = map toSingletonList $ map fromJust mbddl1
                      bddl2 = map toSingletonList $ map fromJust mbddl2
                    mgr <- gets bddMgr
                    b1  <- liftIO $ bddAndList mgr bddl1
                    b2  <- liftIO $ bddAndList mgr bddl2
                    res <- liftIO $ bddXor b1 b2 >>= bddIsFalse
                    --
                    when ( trace_disjoint_tests ) $ liftIO $
                         do
                         -- sb1 <- showBdd bddPrinter b1
                         -- sb2 <- showBdd bddPrinter b2
                         -- bdr <- bddIntersect b1 b2 >>= (showBdd bddPrinter)
                         -- bddAnd b1 b2 >>= bddPrintMinterms
                         putStrLn $ "checkIdenticalRules: " ++ ppAId rn1
                                  ++ " r2: " ++ ppAId rn2 ++ " Result: " ++ show res
                                  -- ++ "\nbdd1: " ++ sb1
                                  -- ++ "\nbdd2: " ++ sb2
                                  -- ++ "\nbdd andR: " ++ bdr
                    --
                    return res
               else
               return Nothing
-}


-- Given a pair of rules, and determine in the predicate conditions are disjoint.
-- Returns true if the rules are disjoint, False if they intersect,
-- and Nothing if unknown
checkDisjointRulePairM :: (ARuleId,ARuleId) -> BddC (Maybe Bool)
checkDisjointRulePairM (rule1,rule2) =
    do
    conditionalFlushBdds
    when ( traceBddConv2 ) $ liftIO $
         putStrLn( "checkDisjointRulePairM has been called " ++
                   ppAId rule1 ++
                   " " ++ ppAId rule2) ;
    ruletest <- gets ruleTest
    case (M.lookup (ordPair (rule1, rule2)) ruletest) of
      Just res -> return res
      Nothing -> do
        rulemap <- gets ruleMap
        case (M.lookup rule1 rulemap, M.lookup rule2 rulemap) of
          (Just rt1, Just rt2) -> do
             res <- checkDisjointRules rt1 rt2
             state <- get
             put state { ruleTest = M.insert (ordPair (rule1, rule2)) res ruletest }
             return res
          _ ->
             internalError ("checkDisjointRulePairM: Missing rule from Database" )

checkDisjointRulePair :: BddBuilder AId -> (ARuleId, ARuleId) -> IO (Maybe Bool, BddBuilder AId)
checkDisjointRulePair bddb (r1, r2) =
    do
      let (maxSize,_) = bddMaxSize  bddb
      if (maxSize <= 0.0 ) then return (Nothing, bddb)
       else do
            (disjoint,s2) <- runBdd (checkDisjointRulePairM (r1, r2)) bddb
            return (disjoint,s2)

{-
-- This code is no longer used

checkIdenticalRulePair :: (ARuleId,ARuleId) -> BddC (Maybe Bool)
checkIdenticalRulePair (rule1,rule2) =
    do
    conditionalFlushBdds
    when ( traceBddConv2 ) $ liftIO $
         putStrLn( "checkIdenticalRulePair has been called" ++
                   ppAId rule1 ++
                   " " ++ ppAId rule2) ;
    rulemap <- gets ruleMap
    --
    let
      rt1,rt2 :: Maybe RuleTriple
      rt1 = M.lookup rule1 rulemap
      rt2 = M.lookup rule2 rulemap
    --
    if ( (isJust rt1) && (isJust rt2) )
       then
       checkIdenticalRules (fromJust rt1) (fromJust rt2)
       else
       internalError ("checkIdenticalRulePair: Missing rule from Database" )


-- Given 2 defs, return true if the definitions are disjoint
checkDisjointDefs :: BddBuilder AId  -> ADef -> ADef -> IO (Maybe Bool)
checkDisjointDefs bddb adef1 adef2 =
    do
    [bdd1,bdd2] <- evalBdd (mapM convAD2Bdd [adef1, adef2] ) bddb
    --
    -- If these are definitions, then the list size must be 1
    --
    when ( traceBddConv1 ) $
         do
         -- s1 <- showBddList bddPrinter (bdd1)
         putStrLn $ show adef1 -- ++ "\n" ++ s1
         -- s2 <- showBddList bddPrinter (bdd2)
    --
    res <- disjointBddTestList bdd1 bdd2
    when ( traceBddConv1 ) $ putStrLn ( "checkDisjointDefs: " ++ show res )
    return res
-}


-- -------------------------

{-
-- This code is no longer used

type RuleDisjointTest = ARuleId -> ARuleId -> Bool

-- Generates the RuleDisjointTest for all ruls held in BddBuilder.
-- TODO this should only be done on demand......  Save given a list of rule pairs.
genRuleTest :: BddBuilder AId -> [(ARuleId,ARuleId)] -> IO( RuleDisjointTest, BddBuilder AId)
genRuleTest bddb me_pairs = do
            (pairs,newstate) <- runBdd (mkRuleResults me_pairs) bddb
            let test = mkRuleTest pairs
            return (test,newstate)

-- utility procedure to check the result of checkIdenticalRules
is_me_error (_, (Just True)) = True
is_me_error _ = False

-- In the monad, return a list of dijoint test for all rule pair.
mkRuleResults :: [(ARuleId,ARuleId)] -> BddC [((ARuleId,ARuleId),Bool)]
mkRuleResults me_pairs = do
           rulemap  <- gets ruleMap
           let
               pairs   = map ordPair (uniquePairs (M.keys rulemap))
	       filter_pairs = filter (`notElem` me_pairs)
               pairs' = filter_pairs pairs
           results_dsj <- mapM checkDisjointRulePairM pairs'
           results_eq <- mapM checkIdenticalRulePair me_pairs
           let
               results = map (maybe False id) results_dsj
               results_me = map (\x -> True) me_pairs
	       error_list = (map fst (filter is_me_error (zip me_pairs results_eq)))
	   when (not (null error_list)) $ liftIO $ (errMERulesIdentical error_list)
           return ((zip pairs' (results)) ++ (zip me_pairs (results_me)))

errMERulesIdentical :: [(ARuleId,ARuleId)] -> IO ()
errMERulesIdentical pairs = messageExit serror (map errMERulePair pairs)
    where
    errMERulePair :: (ARuleId,ARuleId) -> EMsg
    errMERulePair (aid_0,aid_1) =
	(getPosition aid_0,
	 EMERulesIdentical (ppAId aid_0) (ppAId aid_1))


-- taking a list of ruleid pairs, and their disjointness,
-- create a rule disjoint test which is a lookup into the Map.
mkRuleTest :: [((ARuleId,ARuleId),Bool)] -> RuleDisjointTest
mkRuleTest pairs =
    let
      lookupMap = M.fromList pairs
      err key = internalError $ "mkRuleTest lookup failed on " ++ show key
    in
    (\r1 r2 ->
     (r1 /= r2) &&
     (M.findWithDefault (err (r1,r2)) (ordPair (r1,r2)) lookupMap))

-}

-- -------------------------

-- Add more definitions to  BddBuilder AId
addADefToBDDState :: BddBuilder AId -> [ADef] -> IO (BddBuilder AId)
addADefToBDDState builder adefs = do
              let
                 defmap  = defMap builder
                 defmap' = map_insertMany [(id,def) | def@(ADef id _ _ _) <- adefs] defmap
                 newb = builder{ defMap = defmap'}
              execBdd (loadBuilder adefs) newb


-- Initialize the BddBuilder with the defs, state, and rules
initBDDState :: ErrorHandle -> Flags -> Bool ->
                [ADef] -> [AVInst] -> [RuleTriple] ->
                IO (BddBuilder AId)
initBDDState errh flags doHardFail defs avinsts rules =
    let defFailFn = if doHardFail then defFailHard else defFailSoft
    in
         if ( bddLimit flags > 0.0 ) then do
             mgr  <- newBddMgr
             let
                istate = initBuilder errh flags mgr defs avinsts rules defFailFn
             _ <- bddNewVar mgr
             execBdd (loadBuilder defs)  istate
         else do -- a way to avoid calling bdd and hence to test memory management
             nullmgr <- nullBddMgr
             return $ initBuilder errh flags nullmgr defs avinsts rules defFailFn


-- create an initial BddBuilder state, which has the Adefs load in the def Map
initBuilder :: ErrorHandle -> Flags -> BddMgr ->
               [ADef] -> [AVInst] -> [RuleTriple] ->
               (AId -> Integer -> BddC [Bdd]) -> BddBuilder AId
initBuilder errh flags mgr adefs avinsts rules failf =
    let
      defmap = M.fromList [ (id,def) | def@(ADef id _ _ _) <- adefs ]
      rulem  = M.fromList [ (rid,rl) | rl@(rid, _, _ ) <- rules ]
      statem = M.fromList [ (avi_vname avi, avi_vmi avi) | avi <- avinsts ]
      --
      bddlimit :: Double
      bddlimit = bddLimit flags
      warnlimit = warnSchedLimit flags
    in
    BddBuilder { errHandle=errh,
                 bddMgr=mgr,
                 defMap=defmap,
                 deffailfunc = failf,
                 ruleMap=rulem,
                 ruleTest=M.empty,
                 stateMap=statem,
                 stateBddMap=M.empty,
                 exprMap= M.empty,
                 bddMap=M.empty,
                 bddMaxSize=(bddlimit,warnlimit),
                 useShort=False,
                 orderVar=orderVarInit,
                 cacheSize= bddCacheLimit flags
               }

-- Load the State Monad with the Adef list contents.
-- We do not do anything here, since on-demand is better
loadBuilder :: [ADef] -> BddC ()
loadBuilder adefs =
    do
    liftIO $ when ( traceBddConv1 ) $
           do
           let
             -- some utility function for display and comparing by name
             showadefs (ADef id ty ex _props) =
                 ( "ADef: " ++ ppAId id
                   ++ " (" ++ show ty ++ ")"
                   ++ " :: " ++ ppAll ex
                   )
             cmpADef (ADef id1 _ _ _) (ADef id2 _ _ _) = compare sid1 sid2
                           where
                              sid1 = ppAId id1
                              sid2 = ppAId id2
           putStrLn "Definitions are :"
           mapM_ putStr (map showadefs (sortBy cmpADef adefs))
           putStrLn "\n"
    --
    -- let
    -- There appears to be no advantage to preloading the  bdd variables,
    -- restrict initial bdd construction to independent vars only, all else is lazy
    -- reverse this list, since this give better bdd costruction behavior
    --                    rdefs = reverse $ filter isDerivable adefs
    --
    --                  mapM_ convAD2Bdd rdefs -- load in the var leaf definitions
    --                  mapM_ convAD2Bdd adefs -- load in the var leaf definitions
    return ()

-- -------------------------

{-
clearBddMap :: BddBuilder a -> (BddBuilder a)
clearBddMap bddb = bddb { defMap      = M.empty,
                          bddMap      = M.empty,
                          stateBddMap = M.empty,
                          stateMap    = M.empty,
                          ruleMap     = M.empty,
                          ruleTest    = M.empty }
-}

-- flush out the bdd cache creating a new manager and hence new orders....
flushBdds :: BddBuilder AId -> IO (BddBuilder AId)
flushBdds bddb =
    do
      let (maxSize,_) = bddMaxSize bddb
      newMgr2 <- if (maxSize <= 0.0 ) then nullBddMgr else
                 do
                 newMgr <- newBddMgr
                 _ <- bddNewVar newMgr
                 return newMgr
      let
       newBddB = bddb{ bddMgr = newMgr2,
                       bddMap = M.empty,
                       orderVar = orderVarInit,
                       stateBddMap = M.empty,
                       exprMap = M.empty }
      return newBddB

-- flush bee function on the BddC monad
flushBddsM :: BddC ()
flushBddsM = do
           st <- get
           newState <- liftIO $ flushBdds st
           put newState

{-
-- for debug and tracing
showBddStat :: String -> BddC ()
showBddStat prefix = do
    mgr <- gets bddMgr
    let sz = bddVarCount mgr
    cache <- gets bddMap
    exprM <- gets exprMap
    liftIO $ putStrLn $ prefix ++ ": varcound: " ++ (show sz) ++
               " Cache size: " ++ (show $ M.size cache) ++
               " exprMap size: " ++ (show $ M.size exprM)
    return ()
-}

-- a simple heuristic to flush bdd manager and cache.
conditionalFlushBdds :: BddC ()
conditionalFlushBdds = do
    cache <- gets bddMap
    bddCacheSizeLimit <- gets cacheSize
    let
      flushNow = (bddCacheSizeLimit > 0) && (M.size cache > bddCacheSizeLimit)
      preStr = if ( flushNow )
               then "Flushing bdd cache and manager: "
               else "Deferred flushing bdd cache: "
    when ( trace_bdd_size ) $ do
            mgr <- gets bddMgr
            let sz = bddVarCount mgr
            liftIO $ putStrLn ( preStr ++ show (M.size cache) ++ " : " ++ show sz )
    when ( flushNow ) flushBddsM

-- -------------------------

-- a method which creates a AVInstKey from the method call and its arguments
lookupMethodWire :: (BddBuilder AId) -> AId -> AId -> [AExpr] -> AVInstKey
lookupMethodWire bddb stateId methodId exprsArgs = (AVInstKey stateId wireName argNames)
    where
    statem = stateMap bddb
    err = internalError( "AExpr2Bdd::lookupMethodWire - invalid state or method name"
                         ++ ppReadable (stateId,methodId) )
    vmods :: [VFieldInfo]
    vmods = vFields $ M.findWithDefault err stateId statem
    isTheMethod (Method { vf_name = i }) = qualEq i methodId
    isTheMethod _ = False
    methInfo = maybe err id (find isTheMethod vmods)
    getVnames (Clock _) = []
    getVnames (Reset _) = []
    getVnames (Inout {}) = []
    getVnames m@(Method { }) = i ++ (maybeToList o) ++ (maybeToList e)
     where i = vf_inputs m
           o = vf_output m
           e = vf_enable m
    vnames = getVnames methInfo
    wireName = if (0 /= length vnames) then fst (head vnames) else err
    argNames = unlines (map show exprsArgs)

-- isDerivable :: ADef -> Bool
-- isDerivable (ADef aid atype (APrim atype2 op args)) | elem op validTransOps = False
-- isDerivable _ = True

-- loads the ADef into the BddC container.
convAD2Bdd :: ADef -> BddC [Bdd]
convAD2Bdd adef@(ADef aid (ATBit width) aexpr _) =
    do
    bddmap0    <- gets bddMap
    vars       <- case ( M.lookup aid bddmap0 ) of
                  Nothing      ->
                      do
                      when (traceBddConv2) $ liftIO $
                           putStrLn ( "Converting to Bdd: " ++ ppAId aid )
                      -- TODO check for infinte loops
                      mnewvars <- convE2Bdd aexpr -- Maybe [Bdd]
                      --
                      newvars <- case ( mnewvars ) of
                                 Just( nv ) -> return nv
                                 Nothing    -> interLeaveOrder width
                      --
                      bddmap1 <- gets bddMap
                      let
                        bddmap2 = M.insert aid newvars bddmap1
                      --
                      st <- get
                      put st{ bddMap=bddmap2 }
                      when (traceBddConv2) $ liftIO $
                           putStrLn( "Done Converting to Bdd: " ++ ppAId aid )
                      return newvars
                  --
                  Just i       -> return i
                  -- already present is map
    --
    when ( (fromInteger width) /= (length  vars )) $
         internalError ("convAD2Bdd: incorrect list size: " ++ show width ++ " : "
                        ++ show (length vars) ++ " : " ++ show adef )
    --
    return vars

--
convAD2Bdd adef@(ADef aid (ATReal) aexpr _) =
    internalError ("convAD2Bdd: unexpected pattern" ++ show adef)
convAD2Bdd adef@(ADef aid (ATString _) aexpr _) =
    internalError ("convAD2Bdd: unexpected pattern" ++ show adef )
convAD2Bdd adef@(ADef aid (ATArray _ _) aexpr _) =
    internalError ("convAD2Bdd: unexpected pattern" ++ show adef )
convAD2Bdd adef@(ADef aid (ATAbstract _ _) aexpr _) =
    internalError ("convAD2Bdd: unexpected pattern" ++ show adef )




-- Convert an expression to a BDD
convE2Bdd :: AExpr -> BddC (Maybe [Bdd])

-- Constants via IntLit
-- width and base are meaningless in IntLit, so use the width from type.
convE2Bdd (ASInt _ (ATBit width) (IntLit _ _ ilValue)) =
    do
    mgr <- gets bddMgr
    bddv <- liftIO $ bddConstVector mgr width ilValue
    return $ Just bddv


-- ASDefs require a look up (and possible construction) from bddMap
-- AExpr -> BddC (Maybe [Bdd])
convE2Bdd (ASDef (ATBit width) aid) =
    do
    bddmap    <- gets bddMap
    --
    let
        mbddv :: Maybe [Bdd]
        mbddv =  M.lookup aid bddmap
    vars <- case ( mbddv  ) of
             Nothing ->  convAid2Bdd aid -- [Bdd]
             Just i  ->  return  i

    when  ((fromInteger width) /= length vars)  $
          internalError ( "convE2Bdd: ASDef incorrect sizing: " ++ show aid )
    return (Just vars)
    --
    where
      -- Convert this AID to a bdd
      convAid2Bdd :: AId -> BddC [Bdd]
      convAid2Bdd aid =
          do
            defmap    <- gets defMap
            failf     <- gets deffailfunc
            case ( M.lookup aid defmap ) of
              Nothing      -> failf aid width
              Just i       -> convAD2Bdd i


convE2Bdd (ASPort (ATBit width) aid) =
    do
    bddmap    <- gets bddMap
    --
    vars <- case ( M.lookup aid bddmap ) of
            Nothing ->
                do
                -- WE do not expect to find aid in the definitions, so add indep var
                vars <- interLeaveOrder width --[Bdd]
                --
                bddmap1 <- gets bddMap
                let bddmap2 = M.insert aid vars bddmap1
                state <- get
                --
                put state{ bddMap=bddmap2 }
                return vars
            --
            Just i ->  return i
    --
    when ( (fromInteger width) /= length vars ) $
         internalError $ "convE2Bdd: ASDef incorrect sizing: " ++ show aid
    return (Just vars )

-- treat ASParam the same as ASPort
convE2Bdd (ASParam t@(ATBit width) aid) = convE2Bdd (ASPort t aid)

-- For ASAny, create an independent variable.
-- If it has a tagged value, don't use it!  That's not part of the formal
-- meaning, it's an implementation optimization.
convE2Bdd (ASAny (ATBit width) _) =
           interLeaveOrder width >>= return . Just

convE2Bdd expr@(APrim _ _ _ _) = do
  emap <- gets exprMap
  case (M.lookup expr emap) of
    (Just bdd) -> return bdd
    Nothing    -> do
      ret <- convPrim2Bdd expr
      state <- get
      put state { exprMap = M.insert expr ret emap }
      return ret

-- Method calls create independent variables, with given width
-- TODO note that some methods calls may be mutex, such as FIFO.full and FIFO.empty
convE2Bdd expr@(AMethCall (ATBit width) aid amethodid args) =
    do
    bddb <- get
    let
      -- generate key into the bddStateMap table for this method call
      bddKey = lookupMethodWire bddb aid amethodid args
    stateBddm <- gets stateBddMap
    -- lookup in the table to see if we've seen this before.
    vars <- case ( M.lookup bddKey stateBddm ) of
           Nothing ->
               do
               when (traceBddConv1) $ liftIO $ putStrLn
                        ("convE2Bdd::AMethodCall: added var " ++ ppReadable bddKey )
               newvars    <- interLeaveOrder width -- state changes here.
               stateBddm' <- gets stateBddMap
               let
                 stateBddm'' = M.insert bddKey newvars stateBddm'
               currState <- get
               put currState{ stateBddMap=stateBddm'' }
               return newvars
           Just found ->
               do
               when (traceBddConv1) $ liftIO $
                    putStrLn ("convE2Bdd::AMethodCall: found var " ++ ppReadable bddKey )
               return found

    return $ Just vars

convE2Bdd expr@(AMethValue t@(ATBit width) aid amethodid) =
    -- consider it like a value method call with no arguments
    convE2Bdd (AMethCall t aid amethodid [])

-- XXX should we do like for AMethCall?
convE2Bdd expr@(AMGate (ATBit 1) aid clkid) = addUnknownExpr expr 1

-- For these unknown types, be safe and create an independent variable vector
-- of the specified size.
convE2Bdd expr@(ASStr _ (ATString (Just width)) _ ) = addUnknownExpr expr width
convE2Bdd expr@(ANoInlineFunCall (ATBit width) _ _ _ ) = addUnknownExpr expr width
convE2Bdd expr@(AFunCall (ATBit width) _ _ _ _ )    = addUnknownExpr expr width
convE2Bdd expr@(ATaskValue (ATBit width) _ _ _ _)   = addUnknownExpr expr width
-- For unknown abstract types, error out
convE2Bdd expr = unexpectedType expr

unexpectedType :: AExpr -> BddC (Maybe [Bdd])
unexpectedType expr = internalError ("unexpected type in convE2Bdd: " ++ (show expr))

addUnknownExpr :: AExpr -> Integer -> BddC (Maybe [Bdd])
addUnknownExpr expr width =
    do
    vars <- interLeaveOrder width
    when ( traceBddConv1) $ liftIO $
         putStrLn ( "Added APrim expr with unknown: " ++ show expr )
    return  $ Just vars


-- APrim convert range ops which reduce bdd lists to bdds
convPrim2Bdd :: AExpr -> BddC (Maybe [Bdd])
convPrim2Bdd expr@(APrim _ (ATBit width) primop args) | elem primop rangeOps =
    do
    -- extract out the arguments -- type [Maybe [Bdd] ]
    argsBdd <- mapM convE2Bdd args
    ret <- if ( allOk argsBdd )
           then do
           --
           when (2 /= length args) $
                internalError "Unexpected list size in convPrim2Bdd APrim rangeOps"
           when (width /= 1) $
                internalError "Unexpected width list size in convPrim2Bdd APrim rangeOps"
           mgr   <- gets bddMgr
           let
             a0 = fromJust (argsBdd !! 0)
             a1 = fromJust (argsBdd !! 1)
           --
           tooBig <- isOpTooBig primop a0 a1
           if ( tooBig )
              then  return Nothing
              else do
                   retSingle <- liftIO $
                                case ( primop ) of
                                  PrimEQ   -> bddEQVector  mgr a0 a1
                                  PrimULE  -> bddULEVector mgr a0 a1
                                  PrimULT  -> bddULTVector mgr a0 a1
                                  --
                                  PrimSLE  -> bddSLEVector mgr a0 a1
                                  PrimSLT  -> bddSLTVector mgr a0 a1
                                  _        -> internalError("convPrim2Bdd: range" )
                   --
                   return (Just [retSingle])
           else
           return Nothing
           --
    return ret


-- conversion for APrims with arith ops,  add and subtract
convPrim2Bdd expr@(APrim _ (ATBit width) primop args) | elem primop arithOps =
    do
    -- extract out the arguments -- type [ [Bdd] ]
    argsBdd <- mapM convE2Bdd args
    if ( allOk argsBdd )
       then do
            when (2 /= length args) $
                 internalError "Unexpected list size in convPrim2Bdd APrim arithOps"
            mgr   <- gets bddMgr
            let
              a0 = fromJust (argsBdd !! 0)
              a1 = fromJust (argsBdd !! 1)
            --
            tooBig <- isOpTooBig primop a0 a1
            if ( tooBig )
               then return Nothing
               else do
                    ret <- liftIO $
                           case ( primop ) of
                            PrimAdd   -> bddAddVector mgr a0 a1
                            PrimSub   -> bddSubVector mgr a0 a1
                            _         -> internalError("convPrim2Bdd: arithOps" )
                            --
                    return (Just ret)
       else
       return Nothing

-- -- APrim with  Bool ops which take singleton and return a singleton
convPrim2Bdd expr@(APrim _ (ATBit width) primop args) | elem primop boolOps =
    do
    -- extract out arguments -- type [Maybe [Bdd] ] each inner list should be 1 element
    argsmBdd <- mapM convE2Bdd args
    if ( allOk argsmBdd )
       then do
            let
              argsBdd = map fromJust argsmBdd
              assert = and $ map (\lt -> (1 == length lt)) argsBdd
              argSingles = map head argsBdd -- safe (assert above)
            when (assert /= True) $
                 internalError $ "convPrim2Bdd: unexpected list" ++ show expr
            when (width /= 1) $
                 internalError ("Unexpected width list size in convPrim2Bdd APrim boolOps "
                                ++ show width ++ " " ++ show expr )
            --
            tooBig <- isOpTooBig primop argSingles argSingles
            if ( tooBig )
               then  return Nothing
               else do
                    mgr   <- gets bddMgr
                    retSingle <- liftIO $
                                 case ( primop ) of
                                   PrimBNot -> bddNot (argSingles !! 0)
                                   PrimBAnd -> bddAndList mgr argSingles
                                   PrimBOr  -> bddOrList mgr argSingles
                                   _        -> internalError("convPrim2Bdd: boolOps" )
                    --
                    return (Just [retSingle])
       else
       return Nothing

-- -- APrim with  Bool ops which take vector ad return a vetor
convPrim2Bdd expr@(APrim _ (ATBit width) primop args) | elem primop boolVectorOps =
    do
    -- extract out the arguments -- type [Maybe [Bdd] ]
    argsmBdd <- mapM convE2Bdd args
    if ( allOk argsmBdd )
       then do
            let
              argsBdd = map fromJust argsmBdd  -- [ [Bdd] ]
              assert = and $ map (\lt -> ((fromInteger width) == length lt)) argsBdd
            --
            when ( (assert /= True) && (2 == length args) ) $
                 internalError $ "convPrim2Bdd: unexpected list" ++ show expr
            --
            let
              a0 = argsBdd !! 0
              a1 = argsBdd !! 1
            tooBig <- isOpTooBig primop a0 a1
            if ( tooBig )
               then  return Nothing
               else do
                    ret <- liftIO $
                           case ( primop ) of
                           PrimAnd -> mapM (\(a,b) -> bddAnd a b ) (zip a0 a1)
                           PrimOr  -> mapM (\(a,b) -> bddOr a b ) (zip a0 a1)
                           PrimXor -> mapM (\(a,b) -> bddXor a b ) (zip a0 a1)
                           _       -> internalError("convPrim2Bdd: bool Vector ops" )
                    return (Just ret)
       else
       return Nothing

-- Prim Inv
convPrim2Bdd expr@(APrim _ (ATBit width) PrimInv args@(_:_)) =
    do
    -- extract out the arguments -- type [Maybe [Bdd] ]
    argsmBdd <- mapM convE2Bdd args
    if ( allOk argsmBdd )
       then do
            let
              argsBdd = map fromJust argsmBdd  -- [ [Bdd] ]
              assert = and $ map (\lt -> ((fromInteger width) == length lt)) argsBdd
            --
            when (assert /= True) $
                 internalError ( "convPrim2Bdd: unexpected list" ++ show expr )
            --
            ret <- liftIO $ mapM bddNot (argsBdd !! 0)
            return (Just ret)
       else
       return Nothing


-- -- Prim If,   First arg must be 1 bit
convPrim2Bdd expr@(APrim _ (ATBit width) PrimIf args) =
    do
    argsmBdd <- mapM convE2Bdd args -- [SExpr] -> [Maybe [Bdd]]
    if ( allOk argsmBdd )
       then do
            let
              argsBdd = map fromJust argsmBdd
              assert = and [ ( 3 == length argsBdd ),
                             ( 1 == length (argsBdd !! 0) ),
                             ( length (argsBdd !! 1) == length (argsBdd !!2 )),
                             ( (fromInteger width) == length (argsBdd !! 1)),
                             ( width > 0 )
                           ]
            --
            when (assert /= True) $
                 internalError ( "convPrim2Bdd: unexpected list in convPrim2Bdd " ++
                                 show expr )
            --
            tooBig <- isOpTooBig PrimIf (argsBdd !! 1) (argsBdd !! 2)
            tooBig2 <- isOpTooBig PrimIf (argsBdd !! 0) (argsBdd !! 0)
            if ( tooBig || tooBig2 )
               then  return Nothing
               else do
                    res <- liftIO $
                           bddIteVector (head (argsBdd !! 0))
                                            (argsBdd !! 1)
                                            (argsBdd !! 2)
                    return ( Just res )
       --
       else
       return Nothing

convPrim2Bdd (APrim i (ATBit w) PrimCase (idx : dflt : ces)) =
    -- in the absense of a "case" construct, just convert to if-then-else
    let foldFn (v, e) res =
            let c = APrim i aTBool PrimEQ [idx, v]
            in  APrim i (ATBit w) PrimIf [c, e, res]
    in  convPrim2Bdd (foldr foldFn dflt (makePairs ces))

convPrim2Bdd (APrim i (ATBit w) PrimArrayDynSelect args) =
    case args of
      [APrim _ _ PrimBuildArray es, idx] ->
          -- in the absense of a "case" construct, just convert to if-then-else
          let foldFn (n, e) res =
                  let n_lit = ASInt i (ae_type idx) (ilDec n)
                      c = APrim i aTBool PrimEQ [idx, n_lit]
                  in  APrim i (ATBit w) PrimIf [c, e, res]
              -- number of arms is the min of the elems and the max index
              idx_ty = ae_type idx
              max_idx = case idx_ty of
                          ATBit sz -> (2^sz) - 1
                          _ -> internalError ("convPrim2SExpr: idx_ty")
              arms = zip [0..max_idx] es
              -- default (even if it's not reachable)
              dflt = ASAny (ATBit w) Nothing
          in  convPrim2Bdd (foldr foldFn dflt arms)
      [ASDef _ i_def, idx] -> do
          dmap <- gets defMap
          case (M.lookup i_def dmap) of
            Just (ADef { adef_expr = e_def }) ->
                convPrim2Bdd (APrim i (ATBit w) PrimArrayDynSelect [e_def, idx])
            _ -> internalError ("convPrim2Bdd: PrimArrayDynSelect: " ++
                                ppReadable args)
      _ -> internalError ("convPrim2Bdd: PrimArrayDynSelect: " ++
                          ppReadable args)

-- -- Prim Extract, Vector[Int, Int] -- cannot get too big
convPrim2Bdd expr@(APrim _ (ATBit width)
                PrimExtract [vdata, ub@(ASInt _ _ _), lb@(ASInt _ _ _)]) =
    do
    mdatab     <- convE2Bdd vdata
    if ( isJust mdatab )
       then
       do
       let
         datab = fromJust mdatab
         upperbound = extractInt ub
         lowerbound = extractInt lb
         assert = and [ ( width == 1 + (upperbound - lowerbound ) ),
                        ( (fromInteger upperbound) <= length (datab) ),
                        ( lowerbound >= 0 ),
                        ( width > 0 )
                      ]
                      --
       when (assert /= True) $
            internalError ( "convPrim2Bdd: unexpected list in PrimExtract " ++
                            show expr )
                            -- remember bddvectors are lsb first.
       let res =  take (fromInteger width) (drop (fromInteger lowerbound) datab)
       return (Just res )
       else
       return Nothing

-- -- Prim SignExtend -- replication of bit cannot get too big
convPrim2Bdd expr@(APrim _ (ATBit width)
                PrimSignExt [vdata]) =
    do
    mdatab     <- convE2Bdd vdata
    if ( isJust mdatab )
       then
       do
       let
         datab = fromJust mdatab
         signBit = last datab
         rcount = fromInteger(width) - length (datab)
         res = datab ++ replicate rcount signBit         
         assert = and [ ( rcount > 0 ),
                        ( width > 0 ),
                        length res == fromInteger(width)
                      ]
                      --
       when (assert /= True) $
            internalError ( "convPrim2Bdd: unexpected list in PrimSignExtend " ++
                            show expr )
                            -- remember bddvectors are lsb first.

       return (Just res )
       else
       return Nothing

-- manage list of bdds  cannot get too big.
convPrim2Bdd expr@(APrim _ (ATBit width) PrimConcat args) =
    do
      argsmBdd <- mapM convE2Bdd args   -- [Maybe [Bdd]]
      if (allOk argsmBdd) then
          do
            let argsBdd = concat $ reverse $ map fromJust argsmBdd
            return $ Just argsBdd
       else return Nothing
      
    
convPrim2Bdd expr@(APrim _ (ATBit width) _ _ ) = addUnknownExpr expr width
convPrim2Bdd expr = internalError ("convPrim2Bdd: " ++ show expr )



-- To help with the bdd ordering, we want to interleave all variables,
-- this is not optimal, but it helps the vector compares and add ops,
--  which should deal with most cases.  A more optimal
-- ordering would come from a traversal of the Adefs before construction
interLeaveOrder :: Integer -> BddC [Bdd]
interLeaveOrder newwidth =
    do
    (startindex,oldwidthI) <- gets orderVar
    mgr                    <- gets bddMgr
    let
      oldwidth = fromInteger oldwidthI
      idxs = [startindex .. (startindex + oldwidth - 1)] ++
             (repeat (startindex + oldwidth - 1))
      ids  = take (fromInteger newwidth) idxs
    --
    oldOrder <- if ( traceBddOrder )
                then liftIO $ mapM (bddGetLevel mgr) ids
                else return []
    --
    -- Interleave or string variable in order
    vars <- liftIO $ mapM (\id -> (bddGetLevel mgr id) >>=
                                  (\l -> bddNewVarAtLevel mgr (l))
                          ) ids
    -- vars <- liftIO $ mapM (\id -> bddGetLevel mgr id >> (bddNewVar mgr) ) ids
    index <- liftIO $ bddGetIndex (head vars)
    --
    when ( traceBddOrder ) $
         do
         let newIds = [index .. index + (fromInteger newwidth) -1]
         newerLevel <- liftIO $ mapM (bddGetLevel mgr) ids
         level  <- liftIO $ mapM (bddGetLevel mgr) newIds
         liftIO $ putStrLn $ "Old Orders " ++ show (zip ids oldOrder)
         liftIO $ putStrLn $ "new Orders " ++ show (zip ids newerLevel)
         liftIO $ putStrLn $ "New Var Orders " ++ show (zip newIds level)
    --
    let
      order = if (newwidth > oldwidthI)
              then (index,newwidth)
              else (startindex,oldwidthI)
    --
    state <- get
    put state{orderVar=order}
    return $ reverse vars

-- -------------------------

allOk ::  [Maybe a] -> Bool
allOk maybes = all isJust maybes

-- -------------------------

-- Estimates the complexity of a bdd operation for the given operator and operands.
bddOpEstimate :: PrimOp -> [Bdd] -> [Bdd] -> IO Double
-- PrimEQ is a logical AND of the EQ of each bit the cost is lower than LT
-- A bad idea
-- bddOpEstimate op bdds1 bdds2 | op == PrimEQ = do
--               squares <- dagProducts bdds1 bdds2
--               return $ checkForZeroSize maximum squares

-- these are reduction operator, which PI (n*n)
bddOpEstimate op bdds1 bdds2 | elem op (rangeOps) = do
              squares <- dagProducts bdds1 bdds2
              return $ checkForZeroSize product squares

-- Arith should be easier, since the ordering is relativley maintained.
bddOpEstimate op bdds1 bdds2 | elem op (arithOps ) = do
              squares <- dagProducts bdds1 bdds2
              return $ checkForZeroSize  maximum squares

-- special case for negate -- a constant time operations
bddOpEstimate op bdds1 bdds2 | elem op ([PrimBNot]) =
    return 1.0

-- the list bdds1 and bdds2 are identical  (AND OR)
bddOpEstimate op bdds1 bdds2 | elem op (boolOps) = do
              ratios <- mapM (bddDagRatio) bdds1
              return $ checkForZeroSize product ratios

-- These operation are max ( a_i * b_i)  element by element operations
bddOpEstimate op bdds1 bdds2 | elem op (boolVectorOps ++ [PrimIf] ) = do
              squares <- dagProducts bdds1 bdds2
              return $ checkForZeroSize maximum squares

-- these operations are constant time
bddOpEstimate op bdds1 bdds2 | elem op ([PrimExtract]) = do
              return 1.0

bddOpEstimate _ _ _ = return 1.0

checkForZeroSize :: ([Double] -> Double) -> [Double] ->  Double
checkForZeroSize realf ds = if any ((==) 0 ) ds then 0.0  else realf ds


dagProducts :: [Bdd] -> [Bdd] -> IO [Double]
dagProducts bdds1 bdds2 = do
              dags1 <- mapM (bddDagRatio) bdds1
              dags2 <- mapM (bddDagRatio) bdds2
              return $  map (\(a,b) -> (a*b) ) (zip dags1 dags2)

--
isOpTooBig :: PrimOp -> [Bdd] -> [Bdd] -> BddC Bool
isOpTooBig op bdd1s bdd2s =
    do
    (maxSize,dowarn)  <- gets bddMaxSize
    opSize  <- liftIO $ bddOpEstimate op bdd1s bdd2s
    --
    let res = ( opSize > maxSize ) || (opSize == 0.0)
    --
    when (dowarn && res) $ do
      short <- gets useShort
      modify (\s -> s{useShort = True })
      let opS = printf "%.2g" opSize
          maxS = printf "%.2g" maxSize
      let wmsg = WSchedulerEffortLimit opS maxS short
      errh <- gets errHandle
      liftIO $ bsWarning errh [(noPosition, wmsg)]
    --
    liftIO $ when (trace_bdd_size && res) $ do
           putStrLn $ "Bdd Limit exceeded: in " ++ show op ++ " " ++ (printf "%.2g" opSize )
           stat1 <- mapM bddStats bdd1s
           stat2 <- mapM bddStats bdd1s
           putStrLn $ "S1: " ++ show stat1
           putStrLn $ "S2: " ++ show stat2
    --
    liftIO $ when (traceBddSize )  $
           do
           stat1 <- liftIO $ mapM bddStats bdd1s
           stat2 <- liftIO $ mapM bddStats bdd2s
           --
           putStrLn ("OpTooBigR: " ++ show res ++
                        " opsize: " ++ show opSize )
           putStrLn ( "OpTooBig1: " ++ show stat1 )
           putStrLn ( "OpTooBig2: " ++ show stat2 )
    return res

-- -------------------------

-- common extraction which tests that the bdds are disjoint
disjointBddTestList :: [Bdd] -> [Bdd] -> IO (Maybe Bool)
disjointBddTestList  bddl1 bddl2 = do
                let [b1,b2] = map toSingletonList [bddl1,bddl2]
                bddIntersect b1 b2 >>= bddIsFalse

-- -------------------------

rangeOps :: [PrimOp]
rangeOps = [PrimEQ, PrimULE, PrimULT, PrimSLE, PrimSLT]
boolOps :: [PrimOp]
boolOps = [PrimBNot, PrimBAnd, PrimBOr ]
boolVectorOps :: [PrimOp]
boolVectorOps = [PrimAnd,PrimOr,PrimXor]
arithOps :: [PrimOp]
arithOps = [PrimAdd,PrimSub]            -- we really do not want to do mult here.
--otherOps :: [PrimOp]
--otherOps = [PrimIf,PrimExtract,PrimInv]

--validTransOps :: [PrimOp]
--validTransOps = rangeOps ++ boolOps ++ boolVectorOps ++ arithOps ++ otherOps



extractInt :: AExpr -> Integer
extractInt (ASInt _ atype (IntLit _ _ value)) = value
extractInt _ = internalError $ "extractInt: unexpected pattern"


toSingletonList :: [a] -> a
toSingletonList as =
    if (1 == length as)
       then (head as)
       else (internalError "toSingletonList: Unexpected list" )

-- used for printing bdd
--bddPrinter :: Int -> String
--bddPrinter bddid =  "B" ++ show bddid

-- -------------------------

{-
-- This code is no longer used

-- A tester which generates all pairsfrom Adefs, and
-- calculates which pairs are disjoint.
checkDisjointTester :: Flags -> [ADef] -> [AVInst] -> [RuleTriple] -> IO ()
checkDisjointTester flags adefs avinsts rules =
    do
    putStrLn "checkDisjointTester:"
    --
    putStrLn "Definitions are :"
    mapM_ print adefs
    putStrLn "\n\n"
    --
    state   <- genADefState flags adefs avinsts rules
{-
                    let
                        bddmap = bddMap state
                        unmapped = (M.toList bddmap )

                    bstr <- mapM (\(a,b) -> showBddList bddPrinter b ) unmapped
                    let foo = zip (map fst unmapped) bstr
                    mapM (print) foo

-}
    let
      idexp = [(aid,def) | def@(ADef aid (ATBit 1) aexpr) <- adefs]
      --
      allpairs = [((id1,id2),(def1,def2)) | (id1,def1) <- idexp, (id2,def2) <- idexp ]
    v <- mapM (\(a,b) -> checkDisjointDefs state a b) (map snd allpairs)
    --
    putStrLn "Rules are :"
    mapM_ print rules
    putStrLn "\n\n"
    --
    let
      t1 = (zip (map fst allpairs) v )
      --  t2 = filter (\(a,b) -> b) t1
    mapM_ print t1
    --
    return ()
-}

-- -------------------------

-- When a lookup in the def map does not result in a match, then we need do something
-- here is where we can do that.
defFailHard :: AId -> Integer -> BddC [Bdd]
defFailHard aid _ = internalError ( "convAid2Bdd:  definition not found in map: " ++ show aid )

defFailSoft :: AId -> Integer -> BddC [Bdd]
defFailSoft aid width = do
    vars <- interLeaveOrder width
    bddmap1 <- gets bddMap
    let bddmap2 = M.insert aid vars bddmap1
    state <- get
    --
    put state{ bddMap=bddmap2 }
    return vars

-- -------------------------

isConstExpr :: BddBuilder AId -> AExpr ->  IO (Maybe Bool, BddBuilder AId)
isConstExpr bddb aexpr = do
  let (maxSize,_) = bddMaxSize bddb
  if (maxSize <= 0.0 ) then return (Nothing,bddb) else
      runBdd (isConstExprM aexpr) bddb

isConstExprM :: AExpr -> BddC (Maybe Bool)
isConstExprM aexpr@(APrim aid (ATBit 1) op aas) =
    do bdds <- convE2Bdd aexpr
       res  <- case bdds of
                 Nothing   -> return Nothing
                 Just [b1] -> liftIO $ bddIsConst b1
                 Just _    -> internalError "AExpr2Bdd::isConstExprM"
       return res
isConstExprM _ = return Nothing

-- -------------------------

