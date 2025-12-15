module AExpr2Yices(
       YState,
       initYState,
       addADefToYState,

       checkDisjointExpr,
       checkDisjointRulePair,

       checkBiImplication,
       isConstExpr,
       checkEq,
       checkNotEq
) where

import Control.Monad(when)
import Control.Monad.State(StateT, runStateT, liftIO,
                           gets, get, put, modify)
import qualified Data.Map as M
import qualified Yices as Y
import Data.Word(Word32)
import Data.List (genericIndex)

import ErrorUtil(internalError)
import Flags
import Id(getIdBaseString, dummy_id)
import Prim
import IntLit
import ASyntax
import ASyntaxUtil(aAnds, aSize)
import VModInfo(VModInfo)
import PFPrint
import Util(itos, map_insertMany, makePairs)
import TopUtils(withElapsed)
import AExpr2Util(getMethodOutputPorts)

import Debug.Trace(traceM)
import IOUtil(progArgs)

traceTest :: Bool
traceTest = "-trace-smt-test" `elem` progArgs

traceConv :: Bool
traceConv = "-trace-smt-conv" `elem` progArgs

-- -------------------------

initYState :: String -> Flags -> Bool ->
              [ADef] -> [AVInst] -> [RuleTriple] -> IO YState
initYState str flags doHardFail ds avis rs = do
  -- this can throw an error
  ver <- Y.checkVersion
  when traceTest $ putStrLn $ "Using yices version: " ++ ver
  --
  ctx <- Y.mkContext
  return (YState { context = ctx,
                   --flags = flags,
                   hardFail = doHardFail,

                   defMap = M.fromList [(i,d) | d@(ADef i _ _ _) <- ds],
                   ruleMap = M.fromList [(i,r) | r@(i,_,_) <- rs],
                   stateMap = M.fromList [(avi_vname avi, avi_vmi avi)
                                            | avi <- avis],
                   proofMap = M.empty,

                   anyId = 0,
                   unknownId = 0,

                   defYExprMap = M.empty,
                   portYExprMap = M.empty,
                   expYExprMap = M.empty
                 })


addADefToYState :: YState -> [ADef] -> IO YState
addADefToYState s ds = do
  let defmap  = defMap s
      defmap' = map_insertMany [(id, d) | d@(ADef id _ _ _) <- ds] defmap
  return (s { defMap = defmap' })

withTraceTest :: PPrint a => YM a -> YM a
withTraceTest m =
  if traceTest
  then withElapsed $ do
         res <- m
         liftIO $ putStr ("result: " ++ ppReadable res)
         return res
  else m

-- -------------------------

checkDisjointExpr :: YState -> AExpr -> AExpr -> IO (Maybe Bool, YState)
checkDisjointExpr s e1 e2 = runStateT (checkDisjointExprM e1 e2) s

checkDisjointExprM :: AExpr -> AExpr -> YM (Maybe Bool)
checkDisjointExprM e1 e2 = withTraceTest $ do
  when traceTest $ traceM("comparing exprs: " ++ ppString (e1, e2))
  when traceConv $ traceM("   e1 = " ++ show e1)
  when traceConv $ traceM("   e2 = " ++ show e2)

  let doProof = do
        (ye1, _) <- convAExpr2YExpr_Force True e1
        --when traceTest $ traceM("conv1 done")
        (ye2, _) <- convAExpr2YExpr_Force True e2
        --when traceTest $ traceM("conv2 done")
        ctx <- gets context

        -- push a new ctx so that we can cleanly retract some assertions
        -- (this is more efficient than retracting them individually)
        liftIO $ Y.ctxPush ctx
        liftIO $ Y.assert ctx ye1
        --when traceTest $ traceM("assert1 done")
        liftIO $ Y.assert ctx ye2
        --when traceTest $ traceM("assert2 done")

        sat_res <- liftIO $ Y.ctxStatus ctx

        -- retract the assertions
        liftIO $ Y.ctxPop ctx
        -- memoize the result
        addToProofMap e1 e2 sat_res
        return sat_res

  memRes <- lookupProofMap e1 e2
  sat_res <- case memRes of
    Just r  -> return r
    Nothing -> doProof

  -- if the conditions can both be satisfied, then they are not ME
  return $ case (cvtStatus sat_res) of
              Just b -> Just (not b)
              Nothing -> Nothing

checkDisjointRulePair :: YState -> (ARuleId, ARuleId) -> IO (Maybe Bool, YState)
checkDisjointRulePair s rp = runStateT (checkDisjointRulePairM rp) s

checkDisjointRulePairM :: (ARuleId, ARuleId) -> YM (Maybe Bool)
checkDisjointRulePairM (r1, r2) = do
  when traceTest $ traceM("comparing rules: " ++ ppString (r1,r2))
  c1 <- getRuleCond r1
  c2 <- getRuleCond r2
  checkDisjointExprM c1 c2

getRuleCond :: ARuleId -> YM AExpr
getRuleCond rid = do
  rulemap <- gets ruleMap
  case (M.lookup rid rulemap) of
    Just (_, cond, _) -> return (aAnds cond)
    Nothing -> internalError ("getRuleCond: cannot find rule: " ++
                              ppReadable rid)

-- -------------------------

checkBiImplication :: YState -> AExpr -> AExpr -> IO ((Bool, Bool), YState)
checkBiImplication s e1 e2 = runStateT (checkBiImplicationM e1 e2) s

checkBiImplicationM :: AExpr -> AExpr -> YM (Bool, Bool)
checkBiImplicationM e1 e2 = withTraceTest $ do

  when traceTest $ traceM("checking bi-implication: " ++ ppString (e1, e2))
  when traceConv $ traceM("   e1 = " ++ show e1)
  when traceConv $ traceM("   e2 = " ++ show e2)
  (ye1, _) <- convAExpr2YExpr_Force True e1
  (ye2, _) <- convAExpr2YExpr_Force True e2
  e1_implies_e2 <- checkImplication ye1 ye2
  e2_implies_e1 <- checkImplication ye2 ye1
  return $ (e1_implies_e2, e2_implies_e1)

-- If (!a || b) is True, then a implies b
checkImplication :: Y.Expr -> Y.Expr -> YM Bool
{-
-- Yices has a built in implication operator, so it use it instead of this
checkImplication ye1 ye2 = do
  not_ye1 <- liftIO $ Y.mkNot ye1
  yor <- liftIO $ Y.mkOr [not_ye1, ye2]
  isTrueYExpr yor
-}
checkImplication ye1 ye2 = do
  yimp <- liftIO $ Y.mkImplies ye1 ye2
  when traceTest $ traceM("checking if implication is true")
  isTrueYExpr yimp

isConstExpr :: YState -> AExpr -> IO (Maybe Bool, YState)
isConstExpr s e = runStateT (isConstExprM e) s

isConstExprM :: AExpr -> YM (Maybe Bool)
isConstExprM e = withTraceTest $ do

  when traceTest $ traceM("checking is-constant: " ++ ppString e)
  when traceConv $ traceM("   e = " ++ show e)
  (ye, _) <- convAExpr2YExpr_Force True e
  isConstYExpr ye

isConstYExpr :: Y.Expr -> YM (Maybe Bool)
isConstYExpr ye = do
  is_true <- isTrueYExpr ye
  if is_true
     then return $ Just True
     else do is_false <- isFalseYExpr ye
             if (is_false)
                then return $ Just False
                else return Nothing

isTrueYExpr :: Y.Expr -> YM Bool
isTrueYExpr ye = do
  ctx <- gets context
  not_ye <- liftIO $ Y.mkNot ye

  -- push a new ctx so that we can cleanly retract some assertions
  -- (this is more efficient than retracting them individually)
  liftIO $ Y.ctxPush ctx
  liftIO $ Y.assert ctx not_ye

  sat_res <- checkSAT

  -- retract the assertions
  liftIO $ Y.ctxPop ctx

  -- if there are no values that make "!e" true, then "e" is always true
  return (sat_res == Just False)

isFalseYExpr :: Y.Expr -> YM Bool
isFalseYExpr ye = do
  ctx <- gets context

  -- push a new ctx so that we can cleanly retract some assertions
  -- (this is more efficient than retracting them individually)
  liftIO $ Y.ctxPush ctx
  liftIO $ Y.assert ctx ye

  sat_res <- checkSAT

  -- retract the assertions
  liftIO $ Y.ctxPop ctx

  -- if there are no values that make "e" true, then it is always false
  return (sat_res == Just False)

checkEq :: YState -> AExpr -> AExpr -> IO (Maybe Bool, YState)
checkEq s e1 e2 = runStateT (checkEqM e1 e2) s

checkNotEq :: YState -> AExpr -> AExpr -> IO (Maybe Bool, YState)
checkNotEq s e1 e2 = runStateT (checkNotEqM e1 e2) s

checkEqM :: AExpr -> AExpr -> YM (Maybe Bool)
checkEqM e1 e2 = withTraceTest $ do

  when traceTest $ traceM("checking eq: " ++ ppString (e1,e2))
  when traceConv $ traceM("   e1 = " ++ show e1)
  when traceConv $ traceM("   e2 = " ++ show e2)
  ctx <- gets context
  -- force the exprs to be of the same type
  (y_e1, ty_e1) <- convAExpr2YExpr Nothing e1
  (y_e2, _) <- convAExpr2YExpr (Just ty_e1) e2 >>= convType (Just ty_e1)
  ynoteq <- liftIO $ Y.mkNEq y_e1 y_e2

  -- push a new ctx so that we can cleanly retract some assertions
  -- (this is more efficient than retracting them individually)
  liftIO $ Y.ctxPush ctx
  liftIO $ Y.assert ctx ynoteq

  sat_res <- checkSAT

  -- retract the assertions
  liftIO $ Y.ctxPop ctx

  -- if there are no values that make "e1 != e2", then "e1" and "e2" are equal
  return $ case (sat_res) of
              Just False -> Just True
              Just True  -> Just False
              Nothing    -> Nothing

checkNotEqM :: AExpr -> AExpr -> YM (Maybe Bool)
checkNotEqM e1 e2 = withTraceTest $ do

  when traceTest $ traceM("checking not eq: " ++ ppString (e1,e2))
  when traceConv $ traceM("   e1 = " ++ show e1)
  when traceConv $ traceM("   e2 = " ++ show e2)
  ctx <- gets context
  -- force the exprs to be of the same type
  (y_e1, ty_e1) <- convAExpr2YExpr Nothing e1
  (y_e2, _) <- convAExpr2YExpr (Just ty_e1) e2 >>= convType (Just ty_e1)
  yeq <- liftIO $ Y.mkEq y_e1 y_e2

  -- push a new ctx so that we can cleanly retract some assertions
  -- (this is more efficient than retracting them individually)
  liftIO $ Y.ctxPush ctx
  liftIO $ Y.assert ctx yeq

  sat_res <- checkSAT

  -- retract the assertions
  liftIO $ Y.ctxPop ctx

  -- if there are no values that make "e1 == e2", then "e1" and "e2" are not equal
  return $ case (sat_res) of
              Just False -> Just True
              Just True  -> Just False
              Nothing    -> Nothing

checkSAT :: YM (Maybe Bool)
checkSAT = do
  ctx <- gets context
  res <- liftIO $ Y.ctxStatus ctx
  return $ cvtStatus  res

cvtStatus :: Y.Status -> Maybe Bool
cvtStatus res = case (res) of
  Y.Satisfiable   -> Just True
  Y.Unsatisfiable -> Just False
  _               -> Nothing

-- -------------------------

data YState =
    YState {
               context       :: Y.Context,
               --flags         :: Flags,
               hardFail      :: Bool,

               defMap        :: M.Map AId ADef,
               ruleMap       :: M.Map ARuleId RuleTriple,
               stateMap      :: M.Map AId VModInfo,
               proofMap      :: M.Map (AExpr, AExpr) Y.Status,

               anyId         :: Integer,
               unknownId     :: Integer,

               defYExprMap   :: M.Map AId (Y.Expr, YType),
               portYExprMap  :: M.Map AId (Y.Expr, YType),
               -- for expressions which we treat as variables
               expYExprMap   :: M.Map AExpr (Y.Expr, YType)
              }

type YM = StateT YState IO

type RuleTriple = (ARuleId, [AExpr], Maybe ARuleId)

-- AExpr has no separate Bool type, and instead uses Bit#(1),
-- while Yices requires a conversion between the two.
-- So we have to keep track of types, to insert conversion when necessary.
data YType = YBits Integer | YBool deriving (Show, Eq)

instance PPrint YType where
  pPrint d p t = text (show t)


-- -------------------------

-- Use these functions to make sure that info is added to the most recent maps.
-- If you have a local copy of the map around, but then call monadic functions,
-- the local copy may become stale, and you'll lose info if you write back the
-- stale copy.

addToExpMap :: AExpr -> (Y.Expr, YType) -> YM ()
addToExpMap e res = do
    s <- get
    let emap = expYExprMap s
        emap' = M.insert e res emap
    put (s { expYExprMap = emap' })

addToDefMap :: AId -> (Y.Expr, YType) -> YM ()
addToDefMap d res = do
    s <- get
    let dmap = defYExprMap s
        dmap' = M.insert d res dmap
    put (s { defYExprMap = dmap' })

addToPortMap :: AId -> (Y.Expr, YType) -> YM ()
addToPortMap p res = do
    s <- get
    let pmap = portYExprMap s
        pmap' = M.insert p res pmap
    put (s { portYExprMap = pmap' })

addToProofMap :: AExpr -> AExpr -> Y.Status -> YM()
addToProofMap e1 e2 res = do
  rmap <- gets proofMap
  -- insert both orderings for expressions
  let rmap1 = M.insert (e1,e2) res rmap
      rmapX = M.insert (e2,e1) res rmap1
  modify (\s -> s {proofMap = rmapX})

lookupProofMap :: AExpr -> AExpr -> YM (Maybe Y.Status)
lookupProofMap e1 e2 = do
  rmap <- gets proofMap
  return $ M.lookup (e1,e2) rmap


-- -------------------------

getAnyName :: YM String
getAnyName = do
    s <- get
    let n = anyId s
    -- XXX we need to check for name clash with the defs, ports, etc
    let str = "__any_" ++ itos n
    put (s { anyId = n + 1 })
    return str

getUnknownName :: YM String
getUnknownName = do
    s <- get
    let n = unknownId s
    -- XXX we need to check for name clash
    let str = "__unknown_" ++ itos n
    put (s { unknownId = n + 1})
    return str

{-
assertDef :: AId -> (Y.Expr, YType) -> YM (Y.Expr, YType)
assertDef i (y_e, ty_e) = do
    ctx <- gets context
    let width = case ty_e of { YBool -> 1; YBits w -> w }
    -- XXX we need to check for name clash
    let str = "__def_" ++ ppString i
    var@(y_var, _) <- makeDeclAndVar (Just ty_e) str width
    yeq <- liftIO $ Y.mkEq y_var y_e
    liftIO $ Y.assert ctx yeq
    return var
-}

makeDeclAndVar :: Maybe YType -> String -> Integer -> YM (Y.Expr, YType)
-- If the context expects Bool, create a Bool variable
makeDeclAndVar (Just YBool) str width = do
    when (width /= 1) $
        internalError ("makeDeclAndVar: invalid width: " ++ ppReadable width)
    ty <- liftIO $ Y.mkBoolType
    var <- liftIO $ Y.mkUninterpretedTerm ty
    -- XXX str is unused? use "set_term_name"?
    return (var, YBool)
makeDeclAndVar _ str width = do
    ty <- liftIO $ Y.mkBitVectorType (fromInteger width)
    var <- liftIO $ Y.mkUninterpretedTerm ty
    -- XXX str is unused? use "set_term_name"?
    return (var, YBits width)

addUnknownExpr :: Maybe YType -> AExpr -> Integer -> YM (Y.Expr, YType)
addUnknownExpr mty e width = do
    when traceConv $ traceM("addUnknownExpr: " ++ ppString e)
    emap <- gets expYExprMap
    case (M.lookup e emap) of
      Just res -> do when traceConv $ traceM("   reusing.")
                     return res
      Nothing -> do
        when traceConv $ traceM("   making new var.")
        str <- getUnknownName
        res <- makeDeclAndVar mty str width
        addToExpMap e res
        return res

convType :: Maybe YType -> (Y.Expr, YType) -> YM (Y.Expr, YType)
convType Nothing res = return res
convType (Just (YBool))   res@(_, YBool)   = return res
convType (Just (YBits _)) res@(_, YBits _) = return res
convType (Just (YBool)) (ye, YBits width) = do
    when traceConv $ traceM("converting Bits to Bool")
    when (width /= 1) $
        internalError ("convType: invalid width: " ++ ppReadable width)
{-
    -- XXX Can this be memoized?
    yb <- liftIO $ Y.mkBVConstantFromInteger 1 1
    yeq <- liftIO $ Y.mkEq ye yb
    return (yeq, YBool)
-}
    -- this built-in conversion might be better?
    yconv <- liftIO $ Y.mkBVBoolExtract ye 0
    return (yconv, YBool)
convType (Just (YBits width)) (ye, YBool) = do
    when traceConv $ traceM("converting Bool to Bits")
    when (width /= 1) $
        internalError ("convType: invalid width: " ++ ppReadable width)
{-
    -- XXX Can this be memoized?
    yb1 <- liftIO $ Y.mkBVConstantFromInteger 1 1
    yb0 <- liftIO $ Y.mkBVConstantFromInteger 1 0
    yif <- liftIO $ Y.mkIte ye yb1 yb0
    return (yif, YBits width)
-}
    -- Yices has a built-in conversion function
    yconv <- liftIO $ Y.mkBoolsToBitVector [ye]
    return (yconv, YBits width)

toBool :: (Y.Expr, YType) -> YM (Y.Expr, YType)
toBool res@(_, YBool) = return res
toBool res@(_, YBits 1) = convType (Just YBool) res
toBool res@(_, YBits n) = internalError("toBool: wrong size: " ++ ppReadable n)

toBits :: (Y.Expr, YType) -> YM (Y.Expr, YType)
toBits res@(_, YBits _) = return res
toBits res = convType (Just (YBits 1)) res

-- This is needed because we pass an expected type that includes the width,
-- rather than just saying whether we expect Bits or Bool (with no size)
getBitType :: AExpr -> YType
getBitType e = case (ae_type e) of
                 ATBit w -> YBits w
                 t -> internalError ("getBitType: " ++ ppReadable t)

-- -------------------------

convAExpr2YExpr :: Maybe YType -> AExpr -> YM (Y.Expr, YType)

-- If the context expects Bool, create a Bool value
convAExpr2YExpr (Just YBool) (ASInt _ (ATBit width) (IntLit _ _ ilValue)) = do
    when traceConv $ traceM("conv IntLit (Bool)" ++ itos ilValue)
    when (width /= 1) $
        internalError ("convAExpr2YExpr: invalid width: " ++ ppReadable width)
    ye <- liftIO $ if (ilValue == 0)
                    then Y.mkFalse
                    else if (ilValue == 1)
                         then Y.mkTrue
                         else internalError ("convAExpr2YExpr: invalid Bool" ++
                                             ppReadable ilValue)
    return (ye, YBool)
convAExpr2YExpr _ (ASInt _ (ATBit width) (IntLit _ _ ilValue)) = do
    when traceConv $ traceM("conv IntLit " ++ itos ilValue)
    ye <- liftIO $ Y.mkBVConstantFromInteger width ilValue
    return (ye, YBits width)

convAExpr2YExpr mty e@(ASDef (ATBit width) aid) = do
    when traceConv $ traceM("conv def " ++ ppString aid)
    ymap <- gets defYExprMap
    case (M.lookup aid ymap) of
      Just res -> do when traceConv $ traceM("   reusing.")
                     return res
      Nothing -> do
        when traceConv $ traceM("   converting new.")
        dmap <- gets defMap
        case (M.lookup aid dmap) of
          Just (ADef { adef_expr = e' }) -> do
            when traceConv $ traceM("   e' = " ++ show e')
            -- Go ahead and give it the current context
            -- XXX This is just a heuristic
            res_e <- convAExpr2YExpr mty e'

{- -- XXX This appears to hurt more than it helps
            -- assert it as a variable, to speed up the SMT solver
            def <- assertDef aid res_e
-}
            let def = res_e

            -- memoize the result
            addToDefMap aid def
            return def
          Nothing -> do
            doHardFail <- gets hardFail
            if (doHardFail)
              then internalError ("convAExpr2YExpr: missing def: " ++
                                  ppReadable aid)
              else addUnknownExpr mty e width

convAExpr2YExpr mty (ASPort (ATBit width) aid) = do
    when traceConv $ traceM("conv port " ++ ppReadable aid)
    -- We could use "getVarDeclFromName" to see if a decl exists for this yet,
    -- but we avoid the foreign call (two calls!) and keep our own map
    ymap <- gets portYExprMap
    case (M.lookup aid ymap) of
      Just res -> do when traceConv $ traceM("   reusing.")
                     return res
      Nothing -> do
        when traceConv $ traceM("   making new var.")
        let str = getIdBaseString aid
        -- Go ahead and give it the current context
        -- XXX This is just a heuristic
        res <- makeDeclAndVar mty str width
        addToPortMap aid res
        return res

convAExpr2YExpr mty (ASParam t@(ATBit _) aid) =
    convAExpr2YExpr mty (ASPort t aid)

-- For ASAny, create an independent variable.
-- If it has a tagged value, don't use it!  That's not part of the formal
-- meaning, it's an implementation optimization.
convAExpr2YExpr mty (ASAny (ATBit width) _) = do
    when traceConv $ traceM("conv any")
    str <- getAnyName
    makeDeclAndVar mty str width

convAExpr2YExpr mty (APrim i (ATBit width) p args) = do
    when traceConv $ traceM("conv prim " ++ ppString p)
    convPrim2YExpr mty p i width args

-- Method calls create independent variables, with given width
-- XXX Passing the current context is just a heuristic
-- XXX TODO: some methods calls may be mutex, such as FIFO.full and FIFO.empty
convAExpr2YExpr mty (AMethCall ty@(ATBit width) modId methId args) = do
    -- get the actual port name, so that methods which share the same output port
    -- will appear logically equivalent
    smap <- gets stateMap
    let e = case getMethodOutputPorts smap modId methId of
              [portId] -> AMethCall ty modId portId args
              ports -> internalError ("convAExpr2YExpr: unexpected output ports: "
                               ++ ppReadable (modId, methId, ports))
    -- XXX This could be an unevaluated function, applied to converted arguments
    addUnknownExpr mty e width
convAExpr2YExpr mty (AMethValue ty@(ATBit width) modId methId) = do
    -- get the actual port name, so that methods which share the same output port
    -- will appear logically equivalent
    smap <- gets stateMap
    let e = case getMethodOutputPorts smap modId methId of
              [portId] -> AMethValue ty modId portId
              ports -> internalError ("convAExpr2YExpr: unexpected output ports: "
                               ++ ppReadable (modId, methId, ports))
    -- XXX This could be an unevaluated function, applied to converted arguments
    addUnknownExpr mty e width
convAExpr2YExpr mty (ATupleSel ty@(ATBit width) (AMethCall _ modId methId args) selIdx) = do
    -- get the actual port name, so that methods which share the same output port
    -- will appear logically equivalent
    smap <- gets stateMap
    let portId = getMethodOutputPorts smap modId methId `genericIndex` selIdx
        e = (AMethCall ty modId portId args)
    -- XXX This could be an unevaluated function, applied to converted arguments
    addUnknownExpr mty e width
convAExpr2YExpr mty (ATupleSel ty@(ATBit width) (AMethValue _ modId methId) selIdx) = do
    -- get the actual port name, so that methods which share the same output port
    -- will appear logically equivalent
    smap <- gets stateMap
    let portId = getMethodOutputPorts smap modId methId `genericIndex` selIdx
        e = (AMethValue ty modId portId)
    -- XXX This could be an unevaluated function, applied to converted arguments
    addUnknownExpr mty e width

convAExpr2YExpr mty e@(AMGate (ATBit 1) _ _) =
    -- Gates are used as Bool, so the current context should be YBool,
    -- but pass the current context just to be safe
    -- XXX Passing the current context is just a heuristic
    addUnknownExpr mty e 1

-- For these unknown types, be safe and create an independent variable vector
-- of the specified size.
-- XXX Passing the current context is just a heuristic
convAExpr2YExpr mty e@(ASStr _ (ATString (Just width)) _ ) =
    addUnknownExpr mty e width
convAExpr2YExpr mty e@(ANoInlineFunCall (ATBit width) _ _ _ ) =
    -- XXX This could be an unevaluated function, applied to converted arguments
    addUnknownExpr mty e width
convAExpr2YExpr mty e@(AFunCall (ATBit width) _ _ _ _ ) =
    -- XXX This could be an unevaluated function, applied to converted arguments
    addUnknownExpr mty e width
convAExpr2YExpr mty e@(ATaskValue (ATBit width) _ _ _ _) =
    addUnknownExpr mty e width

-- For unknown abstract types, error out
convAExpr2YExpr _ e =
   internalError ("unexpected expr/type in convAExpr2YExpr: " ++ show e)


convAExpr2YExpr_Force :: Bool -> AExpr -> YM (Y.Expr, YType)
convAExpr2YExpr_Force True e = convAExpr2YExpr (Just YBool) e >>= toBool
convAExpr2YExpr_Force False e =
    convAExpr2YExpr (Just (getBitType e)) e >>= toBits

convPrim2YExpr :: Maybe YType ->
                  PrimOp -> AId -> Integer -> [AExpr] -> YM (Y.Expr, YType)
convPrim2YExpr mty PrimIf _ _ [c, t, f] = do
    -- force "c" to be Bool
    (yc, _) <- convAExpr2YExpr_Force True c
    res0_t@(y0_t, ty0_t) <- convAExpr2YExpr mty t
    res0_f@(y0_f, ty0_f) <- convAExpr2YExpr mty f
    -- if the types of the arms don't match, force them to the expected type
    (yt, yf, ty) <- if (ty0_t == ty0_f)
                    then return (y0_t, y0_f, ty0_t)
                    else do (y1_t, ty1_t) <- convType mty res0_t
                            -- feed in ty1_t, in case mty is Nothing,
                            -- so that at least both arms match
                            (y1_f, ty1_f) <- convType (Just ty1_t) res0_f
                            return (y1_t, y1_f, ty1_f)
    yif <- liftIO $ Y.mkIte yc yt yf
    return (yif, ty)

convPrim2YExpr mty PrimCase i w (idx : dflt : ces) =
    -- in the absence of a "case" construct, just convert to if-then-else
    let foldFn (v, e) res =
            let c = APrim i aTBool PrimEQ [idx, v]
            in  APrim i (ATBit w) PrimIf [c, e, res]
    in  convAExpr2YExpr mty (foldr foldFn dflt (makePairs ces))

convPrim2YExpr mty PrimArrayDynSelect i w args =
    case args of
      [APrim _ _ PrimBuildArray es, idx] ->
          -- in the absence of a "case" construct, just convert to if-then-else
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
          in  convAExpr2YExpr mty (foldr foldFn dflt arms)
      [ASDef _ i_def, idx] -> do
          dmap <- gets defMap
          case (M.lookup i_def dmap) of
            Just (ADef { adef_expr = e_def }) ->
                convPrim2YExpr mty PrimArrayDynSelect i w [e_def, idx]
            _ -> internalError ("convPrim2YExpr: PrimArrayDynSelect: " ++
                                ppReadable args)
      _ -> internalError ("convPrim2YExpr: PrimArrayDynSelect: " ++
                          ppReadable args)

-- Arguments must be the same type (either Bits or Bool), result is Bool
convPrim2YExpr _ PrimEQ   _ _ args =
  case args of
    [arg1, arg2] -> do
        -- force the arms to be of the same type
        (y_arg1, ty_arg1) <- convAExpr2YExpr Nothing arg1
        (y_arg2, _) <- convAExpr2YExpr (Just ty_arg1) arg2
                           >>= convType (Just ty_arg1)
        yeq <- liftIO $ Y.mkEq y_arg1 y_arg2
        return (yeq, YBool)
    _ -> internalError ("convPrim2YExpr: PrimEQ: wrong number of args: " ++
                        ppReadable args)

-- Bool arguments, Bool result
convPrim2YExpr _ PrimBOr  _ w args = doBinManyPrim_BoolBool Y.mkOr args
convPrim2YExpr _ PrimBAnd _ w args = doBinManyPrim_BoolBool Y.mkAnd args
convPrim2YExpr _ PrimBNot _ w args = doUnPrim_BoolBool Y.mkNot args

-- Bit arguments, Bool result
convPrim2YExpr _ PrimULE  _ w args = doBinPrim_BitsBool Y.mkBVLe args
convPrim2YExpr _ PrimULT  _ w args = doBinPrim_BitsBool Y.mkBVLt args
convPrim2YExpr _ PrimSLE  _ w args = doBinPrim_BitsBool Y.mkBVSle args
convPrim2YExpr _ PrimSLT  _ w args = doBinPrim_BitsBool Y.mkBVSlt args

-- Bit arguments, Bit result
convPrim2YExpr _ PrimAnd  _ w args = doBinPrim_BitsBits w Y.mkBVAnd args
convPrim2YExpr _ PrimOr   _ w args = doBinPrim_BitsBits w Y.mkBVOr args
convPrim2YExpr _ PrimXor  _ w args = doBinPrim_BitsBits w Y.mkBVXOr args
-- bitwise negation
convPrim2YExpr _ PrimInv  _ w args = doUnPrim_BitsBits w Y.mkBVNot args

-- Bit arguments, Bit result
--   Yices requires the arguments to be the same size
--   (and the result is the same size as the args?)
--   So Mul needs to have its arguments extended to the result size;
--   Div and Rem need to have their arguments extended to the larger size,
--   and the result truncated if the larger size is not the result size.
convPrim2YExpr _ PrimAdd  _ w args = doBinPrim_BitsBits w Y.mkBVAdd args
convPrim2YExpr _ PrimSub  _ w args = doBinPrim_BitsBits w Y.mkBVSub args
convPrim2YExpr _ PrimMul  _ w args =
  let args' = map (aZeroExtend w) args
  in  doBinPrim_BitsBits w Y.mkBVMul args'
convPrim2YExpr _ PrimQuot _ w args =
    let arg_size = maximum $ map (getWidth . ae_type) args
        args' = map (aZeroExtend arg_size) args
    in  doBinPrim_BitsBits arg_size Y.mkBVDiv args' >>= yTruncate w
convPrim2YExpr _ PrimRem  _ w args =
    let arg_size = maximum $ map (getWidth . ae_type) args
        args' = map (aZeroExtend arg_size) args
    in  doBinPrim_BitsBits arg_size Y.mkBVRem args' >>= yTruncate w
-- arith negation
convPrim2YExpr _ PrimNeg  _ w args = doUnPrim_BitsBits w Y.mkBVMinus args

-- Bit arguments, Bit result
--   Yices supports dynamic shifts
--   A with arith operators, Yices requires shift arguments to be the same size;
--   so extend the arguments to the max size and truncate if the max is not the
--   expected result size.
convPrim2YExpr _ PrimSL _ w args =
  let arg_size = maximum $ map (getWidth . ae_type) args
      args' = map (aZeroExtend arg_size) args
  in  doBinPrim_BitsBits arg_size Y.mkBVShiftLeft args' >>= yTruncate w
convPrim2YExpr _ PrimSRL _ w args =
  let arg_size = maximum $ map (getWidth . ae_type) args
      args' = map (aZeroExtend arg_size) args
  in  doBinPrim_BitsBits arg_size Y.mkBVShiftRightLogical args' >>= yTruncate w
convPrim2YExpr _ PrimSRA _ w [e1,e2] =
  let arg_size = maximum $ map (getWidth . ae_type) [e1,e2]
      e1' = aSignExtend arg_size e1
      e2' = aZeroExtend arg_size e2
  in  doBinPrim_BitsBits arg_size Y.mkBVShiftRightArith [e1',e2'] >>= yTruncate w

-- Bit argument, identical static Int arguments, Bool result
convPrim2YExpr (Just YBool) PrimExtract _ _
               [e, ub@(ASInt {}), lb@(ASInt {})] | (yub == ylb) = do
    (ye, _) <- convAExpr2YExpr_Force False e
    yext <- liftIO $ Y.mkBVBoolExtract ye ylb
    return (yext, YBool)
  where yub = extractWord32 ub
        ylb = extractWord32 lb
-- Bit argument, static Int arguments, Bit result
convPrim2YExpr _ PrimExtract _ _ [e, ub@(ASInt {}), lb@(ASInt {})] = do
    let yub = extractWord32 ub
        ylb = extractWord32 lb
        width = toInteger (yub - ylb + 1)
        ty = YBits width
    (ye, _) <- convAExpr2YExpr_Force False e
    yext <- liftIO $ Y.mkBVExtract ye ylb yub
    return (yext, ty)
-- Don't handle dynamic extraction
-- XXX We could implement the logic for this?
convPrim2YExpr mty PrimExtract i w args =
    -- XXX This could be an unevaluated function, applied to converted arguments
    addUnknownExpr mty (APrim i (ATBit w) PrimExtract args) w

-- Bit arguments, Bit result
convPrim2YExpr _ PrimConcat i w args@[_, _] =
    doBinPrim_BitsBits w Y.mkBVConcat args
convPrim2YExpr _ PrimConcat i width (a1:args) =
    let a1width = case (ae_type a1) of
                   ATBit n -> n
                   t -> internalError ("convPrim2YExpr: PrimConcat width: " ++
                                       ppReadable t)
        a2width = width - a1width
        a2 = APrim i (ATBit a2width) PrimConcat args
    in  doBinPrim_BitsBits width Y.mkBVConcat [a1, a2]

-- Sign extend,  sizes take from argument and return type
convPrim2YExpr _ PrimSignExt i w [e] =
  doBinWord32Prim_BitsBits w Y.mkBVSignExtend e (fromInteger (w - (aSize e)))

convPrim2YExpr mty p i w args = do
  -- XXX This could be an unevaluated function, applied to converted arguments
  -- traceM ("unexpected prim: " ++ ppReadable (p, args))
  addUnknownExpr mty (APrim i (ATBit w) p args) w
  -- internalError ("unexpected prim: " ++ ppReadable (p, args))


-- -----

doBinManyPrim_BoolBool :: ([Y.Expr] -> IO Y.Expr) -> [AExpr]
                       -> YM (Y.Expr, YType)
doBinManyPrim_BoolBool mkFn args =
    boolArgs args >>= doBinManyPrim mkFn >>= boolRes

doUnPrim_BoolBool :: (Y.Expr -> IO Y.Expr) -> [AExpr]
                  -> YM (Y.Expr, YType)
doUnPrim_BoolBool mkFn args =
    boolArgs args >>= doUnPrim mkFn >>= boolRes

doBinPrim_BitsBool :: (Y.Expr -> Y.Expr -> IO Y.Expr) -> [AExpr]
                   -> YM (Y.Expr, YType)
doBinPrim_BitsBool mkFn args =
    bitsArgs args >>= doBinPrim mkFn >>= boolRes

doBinPrim_BitsBits :: Integer -> (Y.Expr -> Y.Expr -> IO Y.Expr) -> [AExpr]
                   -> YM (Y.Expr, YType)
doBinPrim_BitsBits w mkFn args =
    bitsArgs args >>= doBinPrim mkFn >>= bitsRes w

doUnPrim_BitsBits :: Integer -> (Y.Expr -> IO Y.Expr) -> [AExpr]
                  -> YM (Y.Expr, YType)
doUnPrim_BitsBits w mkFn args =
    bitsArgs args >>= doUnPrim mkFn >>= bitsRes w

doBinWord32Prim_BitsBits :: Integer -> (Y.Expr -> Word32 -> IO Y.Expr) -> AExpr -> Word32
                      -> YM (Y.Expr, YType)
doBinWord32Prim_BitsBits w mkFn e n = do
    (ye, _) <- convAExpr2YExpr_Force False e
    yp <- doBinWord32Prim mkFn ye n
    bitsRes w yp


boolArgs :: [AExpr] -> YM [Y.Expr]
boolArgs = mapM (\ a -> convAExpr2YExpr_Force True a >>= return . fst)
bitsArgs :: [AExpr] -> YM [Y.Expr]
bitsArgs = mapM (\ a -> convAExpr2YExpr_Force False a >>= return . fst)

boolRes :: Monad m => a -> m (a, YType)
boolRes   ye = return (ye, YBool)
bitsRes :: Monad m => Integer -> a -> m (a, YType)
bitsRes w ye = return (ye, YBits w)


doUnPrim :: (Y.Expr -> IO Y.Expr) -> [Y.Expr] -> YM Y.Expr
doUnPrim mkFn [y_arg] = do
    liftIO $ mkFn y_arg
doUnPrim _ args =
    internalError ("doUnPrim: wrong number of args: " ++
                   ppReadable (length args))

doBinPrim :: (Y.Expr -> Y.Expr -> IO Y.Expr) -> [Y.Expr] -> YM Y.Expr
doBinPrim mkFn [y_arg1, y_arg2] = do
    liftIO $ mkFn y_arg1 y_arg2
doBinPrim _ args =
    internalError ("doBinPrim: wrong number of args: " ++
                   ppReadable (length args))

doBinManyPrim :: ([Y.Expr] -> IO Y.Expr) -> [Y.Expr] -> YM Y.Expr
doBinManyPrim _ args | (length args < 2) =
    internalError ("doBinManyPrim: wrong number of args: " ++
                   ppReadable (length args))
doBinManyPrim mkFn ys_args = do
    liftIO $ mkFn ys_args

-- Second argument cannot be dynamic
doBinWord32Prim :: (Y.Expr -> Word32 -> IO Y.Expr) -> Y.Expr -> Word32 -> YM Y.Expr
doBinWord32Prim mkFn y_arg1 n_arg2 = do
    liftIO $ mkFn y_arg1 n_arg2


-- -----

extractWord32 :: AExpr -> Word32
extractWord32 (ASInt _ _ (IntLit _ _ val)) = fromInteger val
extractWord32 e = internalError ("extractWord32: unexpected pattern: " ++ show e)


-- -----

getWidth :: AType -> Integer
getWidth (ATBit w) = w
getWidth t = internalError ("AExpr2Yices.getWidth: " ++ ppReadable t)

-- copied from similar function in AOpt
aZeroExtend :: Integer -> AExpr -> AExpr
aZeroExtend w e =
    let e_size = getWidth (ae_type e)
        pad_size = w - e_size
    in  case (compare pad_size 0) of
          EQ -> e
          GT -> APrim dummy_id (ATBit w) PrimConcat
                    [ASInt defaultAId (ATBit pad_size) (ilDec 0), e]
          LT -> internalError ("AExpr2Yices.aZeroExtend: " ++ ppReadable (w, e))

aSignExtend :: Integer -> AExpr -> AExpr
aSignExtend w e =
    let e_size = getWidth (ae_type e)
        pad_size = w - e_size
    in  case (compare pad_size 0) of
          EQ -> e
          GT -> APrim dummy_id (ATBit w) PrimSignExt [e]
          LT -> internalError ("AExpr2Yices.aSignExtend: " ++ ppReadable (w, e))

yTruncate :: Integer -> (Y.Expr, YType) -> YM (Y.Expr, YType)
yTruncate w res@(ye, YBits e_sz) | w == e_sz = return res
yTruncate w (ye, YBits e_sz) | e_sz > w =
    do ytrunc <- liftIO $ Y.mkBVExtract ye 0 (fromInteger (w-1))
       return (ytrunc, YBits w)
yTruncate w (ye, yt) =
    internalError ("AExpr2Yices.yTruncate: " ++ ppReadable (w, yt))


-- -------------------------
