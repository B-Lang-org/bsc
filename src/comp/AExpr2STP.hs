module AExpr2STP(
       SState,
       initSState,
       addADefToSState,

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
import qualified STP as S

import Data.Maybe(fromMaybe)
import Data.List (genericIndex)

import ErrorUtil(internalError)
import Flags
import Id(getIdBaseString, dummy_id)
import Prim
import IntLit
import ASyntax
import ASyntaxUtil(aAnds)
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

initSState :: String -> Flags -> Bool ->
              [ADef] -> [AVInst] -> [RuleTriple] -> IO SState
initSState str flags doHardFail ds avis rs = do
  ctx <- S.mkContext
  falseE <- S.mkFalse ctx
  return (SState { context = ctx,
                   --flags = flags,
                   hardFail = doHardFail,

                   defMap = M.fromList [(i,d) | d@(ADef i _ _ _) <- ds],
                   ruleMap = M.fromList [(i,r) | r@(i,_,_) <- rs],
                   stateMap = M.fromList [(avi_vname avi, avi_vmi avi)
                                            | avi <- avis],
                   proofMap = M.empty,
                   proofMapS = M.empty,

                   anyId = 0,
                   unknownId = 0,

                   falseExpr = falseE,

                   defSExprMap = M.empty,
                   portSExprMap = M.empty,
                   expSExprMap = M.empty
                 })


addADefToSState :: SState -> [ADef] -> IO SState
addADefToSState s ds = do
  let defmap  = defMap s
      defmap' = map_insertMany [(id, d) | d@(ADef id _ _ _) <- ds] defmap
  return (s { defMap = defmap' })

withTraceTest :: PPrint a => SM a -> SM a
withTraceTest m =
  if traceTest
  then withElapsed $ do
         res <- m
         liftIO $ putStr ("result: " ++ ppReadable res)
         return res
  else m

-- -------------------------

checkDisjointExpr :: SState -> AExpr -> AExpr -> IO (Maybe Bool, SState)
checkDisjointExpr s e1 e2 = runStateT (checkDisjointExprM e1 e2) s

checkDisjointExprM :: AExpr -> AExpr -> SM (Maybe Bool)
checkDisjointExprM e1 e2 = withTraceTest $ do

  when traceTest $ traceM("comparing exprs: " ++ ppString (e1, e2))
  when traceConv $ traceM("   e1 = " ++ show e1)
  when traceConv $ traceM("   e2 = " ++ show e2)

  let doProof = do
        ctx <- gets context
        liftIO $ S.ctxPush ctx
        --
        (ye1, _) <- convAExpr2SExpr_Force True e1
        --when traceTest $ traceM("conv1 done")
        (ye2, _) <- convAExpr2SExpr_Force True e2
        --when traceTest $ traceM("conv2 done")

        liftIO $ S.assert ctx ye1
        liftIO $ S.assert ctx ye2

        yf <- gets falseExpr
        sat_res <- liftIO $ S.query ctx yf
        liftIO $ S.ctxPop ctx
        --
        addToProofMap e1 e2 sat_res
        return sat_res

  memRes <- lookupProofMap e1 e2
  sat_res <- case memRes of
    Just r -> return r
    Nothing -> doProof

  -- if query(False) is Valid, then there is an inconsistency
  -- when both "e1" and "e2" are asserted, so they are ME
  return $ case (sat_res) of
              S.Invalid -> Just False
              S.Valid   -> Just True
              S.Timeout -> Nothing
              S.Error   -> internalError ("STP query error")

checkDisjointRulePair :: SState -> (ARuleId, ARuleId) -> IO (Maybe Bool, SState)
checkDisjointRulePair s rp = runStateT (checkDisjointRulePairM rp) s

checkDisjointRulePairM :: (ARuleId, ARuleId) -> SM (Maybe Bool)
checkDisjointRulePairM (r1, r2) = do
  when traceTest $ traceM("comparing rules: " ++ ppString (r1,r2))
  c1 <- getRuleCond r1
  c2 <- getRuleCond r2
  checkDisjointExprM c1 c2

getRuleCond :: ARuleId -> SM AExpr
getRuleCond rid = do
  rulemap <- gets ruleMap
  case (M.lookup rid rulemap) of
    Just (_, cond, _) -> return (aAnds cond)
    Nothing -> internalError ("getRuleCond: cannot find rule: " ++
                              ppReadable rid)

-- -------------------------

checkBiImplication :: SState -> AExpr -> AExpr -> IO ((Bool, Bool), SState)
checkBiImplication s e1 e2 = runStateT (checkBiImplicationM e1 e2) s

checkBiImplicationM :: AExpr -> AExpr -> SM (Bool, Bool)
checkBiImplicationM e1 e2 = withTraceTest $ do

  when traceTest $ traceM("checking bi-implication: " ++ ppString (e1, e2))
  when traceConv $ traceM("   e1 = " ++ show e1)
  when traceConv $ traceM("   e2 = " ++ show e2)
  (ye1, _) <- convAExpr2SExpr_Force True e1
  when traceTest $ traceM("conv1 done")
  (ye2, _) <- convAExpr2SExpr_Force True e2
  --when traceTest $ traceM("conv2 done")
  e1_implies_e2 <- checkImplication ye1 ye2
  when traceTest $ traceM("e1_implies_e2")
  e2_implies_e1 <- checkImplication ye2 ye1
  when traceTest $ traceM("e2_implies_e1")
  return $ (e1_implies_e2, e2_implies_e1)

checkImplication :: S.Expr -> S.Expr -> SM Bool
{-
-- STP has a built in implication operator, so use it instead of this
checkImplication ye1 ye2 = do
  ctx <- gets context
  -- If (!a || b) is True, then a implies b
  not_ye1 <- liftIO $ S.mkNot ctx ye1
  yor <- liftIO $ S.mkOr ctx not_ye1 ye2
  when traceTest $ traceM("checking if implication is true")
  isTrueSExpr yor >>= return . fromMaybe False
-}
checkImplication ye1 ye2 = do
  ctx <- gets context
  yimp <- liftIO $ S.mkImplies ctx ye1 ye2
  when traceTest $ traceM("checking if implication is true")
  isTrueSExpr yimp >>= return . fromMaybe False

isConstExpr :: SState -> AExpr -> IO (Maybe Bool, SState)
isConstExpr s e = runStateT (isConstExprM e) s

isConstExprM :: AExpr -> SM (Maybe Bool)
isConstExprM e = withTraceTest $ do

  when traceTest $ traceM("checking is-constant: " ++ ppString e)
  when traceConv $ traceM("   e = " ++ show e)
  (ye, _) <- convAExpr2SExpr_Force True e
  isConstSExpr ye

isConstSExpr :: S.Expr -> SM (Maybe Bool)
isConstSExpr ye = do
  is_true <- isTrueSExpr ye
  case (is_true) of
    Just True -> return $ Just True
    otherwise -> do is_false <- isFalseSExpr ye
                    case (is_false) of
                      Just True -> return $ Just False
                      otherwise -> return Nothing

isTrueSExpr :: S.Expr -> SM (Maybe Bool)
isTrueSExpr ye = do
  ctx <- gets context
  not_ye <- liftIO $ S.mkNot ctx ye
  isFalseSExpr not_ye

isFalseSExpr :: S.Expr -> SM (Maybe Bool)
isFalseSExpr ye = do
  let doProof = do
        ctx <- gets context
        liftIO $ S.ctxPush ctx
        liftIO $ S.assert ctx ye
        --
        yf <- gets falseExpr
        sat_res <- liftIO $ S.query ctx yf
        liftIO $ S.ctxPop ctx
        addToProofMapS ye sat_res
        return sat_res

  memRes <- lookupProofMapS ye
  sat_res <- case memRes of
    Just r -> return r
    Nothing -> doProof

  -- if query(False) is Valid, then there is an inconsistency,
  -- so the expression is False
  let res = case (sat_res) of
              S.Invalid -> Just False
              S.Valid   -> Just True
              S.Timeout -> Nothing
              S.Error   -> internalError ("STP query error")
  return res

checkEq :: SState -> AExpr -> AExpr -> IO (Maybe Bool, SState)
checkEq s e1 e2 = runStateT (checkEqM e1 e2) s

checkNotEq :: SState -> AExpr -> AExpr -> IO (Maybe Bool, SState)
checkNotEq s e1 e2 = runStateT (checkNotEqM e1 e2) s

checkEqM :: AExpr -> AExpr -> SM (Maybe Bool)
checkEqM e1 e2 = withTraceTest $ do

  when traceTest $ traceM("checking eq: " ++ ppString (e1,e2))
  when traceConv $ traceM("   e1 = " ++ show e1)
  when traceConv $ traceM("   e2 = " ++ show e2)
  -- force the exprs to be of the same type
  (y_e1, ty_e1) <- convAExpr2SExpr Nothing e1
  --when traceTest $ traceM("conv1 done")
  (y_e2, _) <- convAExpr2SExpr (Just ty_e1) e2 >>= convType (Just ty_e1)
  --when traceTest $ traceM("conv2 done")
  ctx <- gets context

  -- mkEq segfaults on Bool inputs, so use iff
  let eqFn = if (ty_e1 == SBool) then S.mkIff else S.mkEq
  yeq <- liftIO $ eqFn ctx y_e1 y_e2

  isTrueSExpr yeq


checkNotEqM :: AExpr -> AExpr -> SM (Maybe Bool)
checkNotEqM e1 e2 = withTraceTest $ do

  when traceTest $ traceM("checking not eq: " ++ ppString (e1,e2))
  when traceConv $ traceM("   e1 = " ++ show e1)
  when traceConv $ traceM("   e2 = " ++ show e2)
  -- force the exprs to be of the same type
  (y_e1, ty_e1) <- convAExpr2SExpr Nothing e1
  --when traceTest $ traceM("conv1 done")
  (y_e2, _) <- convAExpr2SExpr (Just ty_e1) e2 >>= convType (Just ty_e1)
  --when traceTest $ traceM("conv2 done")
  ctx <- gets context

  -- mkEq segfaults on Bool inputs, so use iff
  let eqFn = if (ty_e1 == SBool) then S.mkIff else S.mkEq
  yeq <- liftIO $ eqFn ctx y_e1 y_e2

  isFalseSExpr yeq


-- -------------------------

data SState =
    SState {
               context       :: S.Context,
               --flags         :: Flags,
               hardFail      :: Bool,

               defMap        :: M.Map AId ADef,
               ruleMap       :: M.Map ARuleId RuleTriple,
               stateMap      :: M.Map AId VModInfo,
               proofMap      :: M.Map (AExpr, AExpr) S.Result,
               proofMapS     :: M.Map S.Expr S.Result,

               anyId         :: Integer,
               unknownId     :: Integer,

               falseExpr     :: S.Expr,

               defSExprMap   :: M.Map AId (S.Expr, SType),
               portSExprMap  :: M.Map AId (S.Expr, SType),
               -- for expressions which we treat as variables
               expSExprMap   :: M.Map AExpr (S.Expr, SType)
              }

type SM = StateT SState IO

type RuleTriple = (ARuleId, [AExpr], Maybe ARuleId)

-- AExpr has no separate Bool type, and instead uses Bit#(1),
-- while STP requires a conversion between the two.
-- So we have to keep track of types, to insert conversion when necessary.
data SType = SBits Integer | SBool deriving (Show, Eq)

instance PPrint SType where
  pPrint d p t = text (show t)


-- -------------------------

-- Use these functions to make sure that info is added to the most recent maps.
-- If you have a local copy of the map around, but then call monadic functions,
-- the local copy may become stale, and you'll lose info if you write back the
-- stale copy.

addToExpMap :: AExpr -> (S.Expr, SType) -> SM ()
addToExpMap e res = do
    s <- get
    let emap = expSExprMap s
        emap' = M.insert e res emap
    put (s { expSExprMap = emap' })

addToDefMap :: AId -> (S.Expr, SType) -> SM ()
addToDefMap d res = do
    s <- get
    let dmap = defSExprMap s
        dmap' = M.insert d res dmap
    put (s { defSExprMap = dmap' })

addToPortMap :: AId -> (S.Expr, SType) -> SM ()
addToPortMap p res = do
    s <- get
    let pmap = portSExprMap s
        pmap' = M.insert p res pmap
    put (s { portSExprMap = pmap' })

addToProofMap :: AExpr -> AExpr -> S.Result -> SM()
addToProofMap e1 e2 res = do
  rmap <- gets proofMap
  -- insert both orderings for expressions
  let rmap1 = M.insert (e1,e2) res rmap
      rmapX = M.insert (e2,e1) res rmap1
  modify (\s -> s {proofMap = rmapX})

lookupProofMap :: AExpr -> AExpr -> SM (Maybe S.Result)
lookupProofMap e1 e2 = do
  rmap <- gets proofMap
  return $ M.lookup (e1,e2) rmap

addToProofMapS :: S.Expr -> S.Result -> SM()
addToProofMapS e1 res = do
  rmap <- gets proofMapS
  let rmapX = M.insert e1 res rmap
  modify (\s -> s {proofMapS = rmapX})

lookupProofMapS :: S.Expr -> SM (Maybe S.Result)
lookupProofMapS e1 = do
  rmap <- gets proofMapS
  return $ M.lookup e1 rmap

-- -------------------------

getAnyName :: SM String
getAnyName = do
    s <- get
    let n = anyId s
    -- XXX we need to check for name clash with the defs, ports, etc
    let str = "__any_" ++ itos n
    put (s { anyId = n + 1 })
    return str

getUnknownName :: SM String
getUnknownName = do
    s <- get
    let n = unknownId s
    -- XXX we need to check for name clash
    let str = "__unknown_" ++ itos n
    put (s { unknownId = n + 1})
    return str

{-
assertDef :: AId -> (S.Expr, SType) -> SM (S.Expr, SType)
assertDef i (y_e, ty_e) = do
    ctx <- gets context
    let width = case ty_e of { SBool -> 1; SBits w -> w }
    -- XXX we need to check for name clash
    let str = "__def_" ++ ppString i
    var@(y_var, _) <- makeDeclAndVar (Just ty_e) str width
    yeq <- liftIO $ S.mkEq ctx y_var y_e
    liftIO $ S.assert ctx yeq
    return var
-}

makeDeclAndVar :: Maybe SType -> String -> Integer -> SM (S.Expr, SType)
-- If the context expects Bool, create a Bool variable
makeDeclAndVar (Just SBool) str width = do
    when (width /= 1) $
        internalError ("makeDeclAndVar: invalid width: " ++ ppReadable width)
    ctx <- gets context
    ty <- liftIO $ S.mkBoolType ctx
    var <- liftIO $ S.mkVar ctx str ty
    return (var, SBool)
makeDeclAndVar _ str width = do
    ctx <- gets context
    ty <- liftIO $ S.mkBitVectorType ctx (fromInteger width)
    var <- liftIO $ S.mkVar ctx str ty
    return (var, SBits width)

addUnknownExpr :: Maybe SType -> AExpr -> Integer -> SM (S.Expr, SType)
addUnknownExpr mty e width = do
    when traceConv $ traceM("addUnknownExpr: " ++ ppString e)
    emap <- gets expSExprMap
    case (M.lookup e emap) of
      Just res -> do when traceConv $ traceM("   reusing.")
                     return res
      Nothing -> do
        when traceConv $ traceM("   making new var.")
        str <- getUnknownName
        res <- makeDeclAndVar mty str width
        addToExpMap e res
        return res

convType :: Maybe SType -> (S.Expr, SType) -> SM (S.Expr, SType)
convType Nothing res = return res
convType (Just (SBool))   res@(_, SBool)   = return res
convType (Just (SBits _)) res@(_, SBits _) = return res
convType (Just (SBool)) (ye, SBits width) = do
    when traceConv $ traceM("converting Bits to Bool")
    when (width /= 1) $
        internalError ("convType: invalid width: " ++ ppReadable width)
    ctx <- gets context
    -- XXX Can this be memoized?
    yb <- liftIO $ S.mkBVConstantFromInteger ctx 1 1
    yeq <- liftIO $ S.mkEq ctx ye yb
    return (yeq, SBool)
{-
    -- this built-in conversion might be better?
    yconv <- liftIO $ S.mkBVBoolExtract ctx 0 ye
    return (yconv, SBool)
-}
convType (Just (SBits width)) (ye, SBool) = do
    when traceConv $ traceM("converting Bool to Bits")
    when (width /= 1) $
        internalError ("convType: invalid width: " ++ ppReadable width)
    ctx <- gets context
    -- XXX Can this be memoized?
    yb1 <- liftIO $ S.mkBVConstantFromInteger ctx 1 1
    yb0 <- liftIO $ S.mkBVConstantFromInteger ctx 1 0
    yif <- liftIO $ S.mkIte ctx ye yb1 yb0
    return (yif, SBits width)
{-
    -- STP has a built-in conversion function
    yconv <- liftIO $ S.mkBoolToBitVector ctx ye
    return (yconv, SBits width)
-}

toBool :: (S.Expr, SType) -> SM (S.Expr, SType)
toBool res@(_, SBool) = return res
toBool res@(_, SBits 1) = convType (Just SBool) res
toBool res@(_, SBits n) = internalError("toBool: wrong size: " ++ ppReadable n)

toBits :: (S.Expr, SType) -> SM (S.Expr, SType)
toBits res@(_, SBits _) = return res
toBits res = convType (Just (SBits 1)) res

-- This is needed because we pass an expected type that includes the width,
-- rather than just saying whether we expect Bits or Bool (with no size)
getBitType :: AExpr -> SType
getBitType e = case (ae_type e) of
                 ATBit w -> SBits w
                 t -> internalError ("getBitType: " ++ ppReadable t)

-- -------------------------

convAExpr2SExpr :: Maybe SType -> AExpr -> SM (S.Expr, SType)

-- If the context expects Bool, create a Bool value
convAExpr2SExpr (Just SBool) (ASInt _ (ATBit width) (IntLit _ _ ilValue)) = do
    when traceConv $ traceM("conv IntLit (Bool)" ++ itos ilValue)
    when (width /= 1) $
        internalError ("convAExpr2SExpr: invalid width: " ++ ppReadable width)
    ctx <- gets context
    ye <- liftIO $ if (ilValue == 0)
                    then S.mkFalse ctx
                    else if (ilValue == 1)
                         then S.mkTrue ctx
                         else internalError ("convAExpr2SExpr: invalid Bool" ++
                                             ppReadable ilValue)
    return (ye, SBool)
convAExpr2SExpr _ (ASInt _ (ATBit width) (IntLit _ _ ilValue)) = do
    when traceConv $ traceM("conv IntLit " ++ itos ilValue)
    ctx <- gets context
    ye <- liftIO $ S.mkBVConstantFromInteger ctx width ilValue
    return (ye, SBits width)

convAExpr2SExpr mty e@(ASDef (ATBit width) aid) = do
    when traceConv $ traceM("conv def " ++ ppString aid)
    ymap <- gets defSExprMap
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
            res_e <- convAExpr2SExpr mty e'

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
              then internalError ("convAExpr2SExpr: missing def: " ++
                                  ppReadable aid)
              else addUnknownExpr mty e width

convAExpr2SExpr mty (ASPort (ATBit width) aid) = do
    when traceConv $ traceM("conv port " ++ ppReadable aid)
    -- We could use "getVarDeclFromName" to see if a decl exists for this yet,
    -- but we avoid the foreign call (two calls!) and keep our own map
    ymap <- gets portSExprMap
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

convAExpr2SExpr mty (ASParam t@(ATBit _) aid) =
    convAExpr2SExpr mty (ASPort t aid)

-- For ASAny, create an independent variable.
-- If it has a tagged value, don't use it!  That's not part of the formal
-- meaning, it's an implementation optimization.
convAExpr2SExpr mty (ASAny (ATBit width) _) = do
    when traceConv $ traceM("conv any")
    str <- getAnyName
    makeDeclAndVar mty str width

convAExpr2SExpr mty (APrim i (ATBit width) p args) = do
    when traceConv $ traceM("conv prim " ++ ppString p)
    convPrim2SExpr mty p i width args

-- Method calls create independent variables, with given width
-- XXX Passing the current context is just a heuristic
-- XXX TODO: some methods calls may be mutex, such as FIFO.full and FIFO.empty
convAExpr2SExpr mty (AMethCall ty@(ATBit width) modId methId args) = do
    -- get the actual port name, so that methods which share the same output port
    -- will appear logically equivalent
    smap <- gets stateMap
    let e = case getMethodOutputPorts smap modId methId of
              [portId] -> AMethCall ty modId portId args
              ports -> internalError ("convAExpr2SExpr: unexpected output ports: " ++
                                       ppReadable (modId, methId, ports))
    -- XXX This could be an unevaluated function, applied to converted arguments
    addUnknownExpr mty e width
convAExpr2SExpr mty (AMethValue ty@(ATBit width) modId methId) = do
    -- get the actual port name, so that methods which share the same output port
    -- will appear logically equivalent
    smap <- gets stateMap
    let e = case getMethodOutputPorts smap modId methId of
              [portId] -> AMethValue ty modId portId
              ports -> internalError ("convAExpr2SExpr: unexpected output ports: " ++
                                       ppReadable (modId, methId, ports))
    -- XXX This could be an unevaluated function, applied to converted arguments
    addUnknownExpr mty e width
convAExpr2SExpr mty (ATupleSel ty@(ATBit width) (AMethCall _ modId methId args) selIdx) = do
    -- get the actual port name, so that methods which share the same output port
    -- will appear logically equivalent
    smap <- gets stateMap
    let portId = getMethodOutputPorts smap modId methId `genericIndex` selIdx
        e = (AMethCall ty modId portId args)
    -- XXX This could be an unevaluated function, applied to converted arguments
    addUnknownExpr mty e width
convAExpr2SExpr mty (ATupleSel ty@(ATBit width) (AMethValue _ modId methId) selIdx) = do
    -- get the actual port name, so that methods which share the same output port
    -- will appear logically equivalent
    smap <- gets stateMap
    let portId = getMethodOutputPorts smap modId methId `genericIndex` selIdx
        e = (AMethValue ty modId portId)
    -- XXX This could be an unevaluated function, applied to converted arguments
    addUnknownExpr mty e width

convAExpr2SExpr mty e@(AMGate (ATBit 1) _ _) =
    -- Gates are used as Bool, so the current context should be SBool,
    -- but pass the current context just to be safe
    -- XXX Passing the current context is just a heuristic
    addUnknownExpr mty e 1

-- For these unknown types, be safe and create an independent variable vector
-- of the specified size.
-- XXX Passing the current context is just a heuristic
convAExpr2SExpr mty e@(ASStr _ (ATString (Just width)) _ ) =
    addUnknownExpr mty e width
convAExpr2SExpr mty e@(ANoInlineFunCall (ATBit width) _ _ _ ) =
    -- XXX This could be an unevaluated function, applied to converted arguments
    addUnknownExpr mty e width
convAExpr2SExpr mty e@(AFunCall (ATBit width) _ _ _ _ ) =
    -- XXX This could be an unevaluated function, applied to converted arguments
    addUnknownExpr mty e width
convAExpr2SExpr mty e@(ATaskValue (ATBit width) _ _ _ _) =
    addUnknownExpr mty e width

-- For unknown abstract types, error out
convAExpr2SExpr _ e =
   internalError ("unexpected expr/type in convAExpr2SExpr: " ++ show e)


convAExpr2SExpr_Force :: Bool -> AExpr -> SM (S.Expr, SType)
convAExpr2SExpr_Force True e = convAExpr2SExpr (Just SBool) e >>= toBool
convAExpr2SExpr_Force False e =
    convAExpr2SExpr (Just (getBitType e)) e >>= toBits

convPrim2SExpr :: Maybe SType ->
                  PrimOp -> AId -> Integer -> [AExpr] -> SM (S.Expr, SType)
convPrim2SExpr mty PrimIf _ _ [c, t, f] = do
    -- force "c" to be Bool
    (yc, _) <- convAExpr2SExpr_Force True c
    res0_t@(y0_t, ty0_t) <- convAExpr2SExpr mty t
    res0_f@(y0_f, ty0_f) <- convAExpr2SExpr mty f
    -- if the types of the arms don't match, force them to the expected type
    (yt, yf, ty) <- if (ty0_t == ty0_f)
                    then return (y0_t, y0_f, ty0_t)
                    else do (y1_t, ty1_t) <- convType mty res0_t
                            -- feed in ty1_t, in case mty is Nothing,
                            -- so that at least both arms match
                            (y1_f, ty1_f) <- convType (Just ty1_t) res0_f
                            return (y1_t, y1_f, ty1_f)
    ctx <- gets context
    yif <- liftIO $ S.mkIte ctx yc yt yf
    return (yif, ty)

-- XXX what if the type of the case is String etc?
convPrim2SExpr mty PrimCase i w (idx : dflt : ces) =
    -- in the absence of a "case" construct, just convert to if-then-else
    let foldFn (v, e) res =
            let c = APrim i aTBool PrimEQ [idx, v]
            in  APrim i (ATBit w) PrimIf [c, e, res]
    in  convAExpr2SExpr mty (foldr foldFn dflt (makePairs ces))
{-
    -- force "idx" to be Bits
    (yidx, _) <- convAExpr2SExpr_Force False idx
    let (cs, es) = split (makePairs ces)
    -- force the conditions to be Bits
    ycs <- mapM (convAExpr2SExpr_Force False) cs >>= mapM (return . fst)
    -- convert the arms
    res0_es <- mapM (convAExpr2SExpr mty) es
    -- convert the default
    res0_dflt@(y0_dflt, ty0_dflt) <- convAExpr2SExpr mty dflt
    -- make sure that all the arms and default have the same type
    (y_dflt, y_es, ty) <-
        -- do all of the types of the arms match?
        if (allSame (map snd) res0_es)
        then do -- make sure the default has the same type
                let mty_arms =
                        case res0_es of
                          ((_,ty):_) -> Just ty
                          _ -> mty  -- no arms? use the expected type
                (y_dflt, ty) <- convType mty_arms res0_dflt
                return (y_dflt, map fst res0_es, ty)
        else do -- force them all to the expected type
                -- (if no expected type, use the first type)
                let mty_arms =
                        if (isJust mty)
                        then mty
                        else case res0_es of
                                ((_,ty):_) -> Just ty
                                _ -> -- can't be no arms if they differ!
                                     internalError ("convPrim2SExpr: case")
                res_es <- map (convType mty_arms) res0_es
                (y_dflt, ty) <- convType mty_arms res0_dflt
                return (y_dflt, map fst res_es, ty)
    -- put it all together
-}

convPrim2SExpr mty PrimArrayDynSelect i w args =
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
          in  convAExpr2SExpr mty (foldr foldFn dflt arms)
      [ASDef _ i_def, idx] -> do
          dmap <- gets defMap
          case (M.lookup i_def dmap) of
            Just (ADef { adef_expr = e_def }) ->
                convPrim2SExpr mty PrimArrayDynSelect i w [e_def, idx]
            _ -> internalError ("convPrim2SExpr: PrimArrayDynSelect: " ++
                                ppReadable args)
      _ -> internalError ("convPrim2SExpr: PrimArrayDynSelect: " ++
                          ppReadable args)

-- Arguments must be the same type (either Bits or Bool), result is Bool
convPrim2SExpr _ PrimEQ   _ _ args =
  case args of
    [arg1, arg2] -> do
        -- force the arms to be of the same type
        (y_arg1, ty_arg1) <- convAExpr2SExpr Nothing arg1
        (y_arg2, _) <- convAExpr2SExpr (Just ty_arg1) arg2
                           >>= convType (Just ty_arg1)
        ctx <- gets context

        -- mkEq segfaults on Bool inputs, so use iff
        let eqFn = if (ty_arg1 == SBool) then S.mkIff else S.mkEq

        yeq <- liftIO $ eqFn ctx y_arg1 y_arg2
        return (yeq, SBool)
    _ -> internalError ("convPrim2SExpr: PrimEQ: wrong number of args: " ++
                        ppReadable args)

-- Bool arguments, Bool result
convPrim2SExpr _ PrimBOr  _ w args = doBinManyPrim_BoolBool S.mkOrMany args
convPrim2SExpr _ PrimBAnd _ w args = doBinManyPrim_BoolBool S.mkAndMany args
convPrim2SExpr _ PrimBNot _ w args = doUnPrim_BoolBool S.mkNot args

-- Bit arguments, Bool result
convPrim2SExpr _ PrimULE  _ w args = doBinPrim_BitsBool S.mkBVLe args
convPrim2SExpr _ PrimULT  _ w args = doBinPrim_BitsBool S.mkBVLt args
convPrim2SExpr _ PrimSLE  _ w args = doBinPrim_BitsBool S.mkBVSle args
convPrim2SExpr _ PrimSLT  _ w args = doBinPrim_BitsBool S.mkBVSlt args

-- Bit arguments, Bit result
convPrim2SExpr _ PrimAnd  _ w args = doBinPrim_BitsBits w S.mkBVAnd args
convPrim2SExpr _ PrimOr   _ w args = doBinPrim_BitsBits w S.mkBVOr args
convPrim2SExpr _ PrimXor  _ w args = doBinPrim_BitsBits w S.mkBVXor args
-- bitwise negation
convPrim2SExpr _ PrimInv  _ w args = doUnPrim_BitsBits w S.mkBVNot args

-- Bit arguments, Bit result
--   STP requires the arguments to be the same size
--   (and the same size as the operator?)
--   So Mul needs to have its arguments extended to the result size;
--   Div and Rem need to have their arguments extended to the larger size,
--   and the result truncated if the larger size is not the result size.
convPrim2SExpr _ PrimAdd  _ w args = doBinPrimSz_BitsBits w S.mkBVAdd args
convPrim2SExpr _ PrimSub  _ w args = doBinPrimSz_BitsBits w S.mkBVSub args
convPrim2SExpr _ PrimMul  _ w args =
    let args' = map (aZeroExtend w) args
    in  doBinPrimSz_BitsBits w S.mkBVMul args'
convPrim2SExpr _ PrimQuot _ w args =
    let arg_size = maximum $ map (getWidth . ae_type) args
        args' = map (aZeroExtend arg_size) args
    in  doBinPrimSz_BitsBits arg_size S.mkBVDiv args' >>= sTruncate w
convPrim2SExpr _ PrimRem  _ w args =
    let arg_size = maximum $ map (getWidth . ae_type) args
        args' = map (aZeroExtend arg_size) args
    in  doBinPrimSz_BitsBits arg_size S.mkBVMod args' >>= sTruncate w
-- arith negation
convPrim2SExpr _ PrimNeg  _ w args = doUnPrim_BitsBits w S.mkBVMinus args

-- Bit argument, static Int argument, Bit result
convPrim2SExpr _ PrimSL _ w [e, n@(ASInt {})] =
    doBinIntPrim_BitsBits w S.mkBVShiftLeft e (extractInt n)
convPrim2SExpr _ PrimSRL i w [e, n@(ASInt {})] =
    doBinIntPrim_BitsBits w S.mkBVShiftRight e (extractInt n)

-- Dynamic Shifting must extend all arguments to same size
convPrim2SExpr mty PrimSL  i w args =
  let arg_size = maximum $ map (getWidth . ae_type) args
      args' = map (aZeroExtend arg_size) args
  in  doBinPrimSz_BitsBits arg_size S.mkBVShiftLeftExpr args' >>= sTruncate w

convPrim2SExpr mty PrimSRL i w args =
  let arg_size = maximum $ map (getWidth . ae_type) args
      args' = map (aZeroExtend arg_size) args
  in  doBinPrimSz_BitsBits arg_size S.mkBVShiftRightExpr args' >>= sTruncate w

-- For signed shift right, the left operator must be sign extended...
convPrim2SExpr mty PrimSRA i w [e1,e2] =
  let arg_size = maximum $ map (getWidth . ae_type) [e1,e2]
      e1' = aSignExtend arg_size e1
      e2' = aZeroExtend arg_size e2
  in  doBinPrimSz_BitsBits arg_size S.mkBVSignedShiftRightExpr [e1',e2'] >>= sTruncate w


-- Bit argument, identical static Int arguments, Bool result
convPrim2SExpr (Just SBool) PrimExtract _ _
               [e, ub@(ASInt {}), lb@(ASInt {})] | (yub == ylb) = do
    (ye, _) <- convAExpr2SExpr_Force False e
    ctx <- gets context
    yext <- liftIO $ S.mkBVBoolExtract ctx ylb ye
    return (yext, SBool)
  where yub = extractInt ub
        ylb = extractInt lb
-- Bit argument, static Int arguments, Bit result
convPrim2SExpr _ PrimExtract _ _ [e, ub@(ASInt {}), lb@(ASInt {})] = do
    let yub = extractInt ub
        ylb = extractInt lb
        width = toInteger (yub - ylb + 1)
        ty = SBits width
    (ye, _) <- convAExpr2SExpr_Force False e
    ctx <- gets context
    yext <- liftIO $ S.mkBVExtract ctx ylb yub ye
    return (yext, ty)
-- Don't handle dynamic extraction
-- XXX We could implement the logic for this?
convPrim2SExpr mty PrimExtract i w args =
    -- XXX This could be an unevaluated function, applied to converted arguments
    addUnknownExpr mty (APrim i (ATBit w) PrimExtract args) w

-- Bit arguments, Bit result
convPrim2SExpr _ PrimConcat i w args@[_, _] =
    doBinPrim_BitsBits w S.mkBVConcat args
convPrim2SExpr _ PrimConcat i width (a1:args) =
    let a1width = case (ae_type a1) of
                   ATBit n -> n
                   t -> internalError ("convPrim2SExpr: PrimConcat width: " ++
                                       ppReadable t)
        a2width = width - a1width
        a2 = APrim i (ATBit a2width) PrimConcat args
    in  doBinPrim_BitsBits width S.mkBVConcat [a1, a2]

-- Sign extend,  sizes take from argument and return type
convPrim2SExpr _ PrimSignExt i w [e] =
    doBinIntPrim_BitsBits w S.mkBVSignExtend e (fromInteger w)

convPrim2SExpr mty p i w args =
    addUnknownExpr mty (APrim i (ATBit w) p args) w
    --internalError ("unexpected prim: " ++ ppReadable (p, args))


-- -----

doBinManyPrim_BoolBool :: (S.Context -> [S.Expr] -> IO S.Expr) -> [AExpr]
                       -> SM (S.Expr, SType)
doBinManyPrim_BoolBool mkFn args =
    boolArgs args >>= doBinManyPrim mkFn >>= boolRes

doUnPrim_BoolBool :: (S.Context -> S.Expr -> IO S.Expr) -> [AExpr]
                  -> SM (S.Expr, SType)
doUnPrim_BoolBool mkFn args =
    boolArgs args >>= doUnPrim mkFn >>= boolRes

doBinPrim_BitsBool :: (S.Context -> S.Expr -> S.Expr -> IO S.Expr) -> [AExpr]
                   -> SM (S.Expr, SType)
doBinPrim_BitsBool mkFn args =
    bitsArgs args >>= doBinPrim mkFn >>= boolRes

doBinPrim_BitsBits :: Integer
                   -> (S.Context -> S.Expr -> S.Expr -> IO S.Expr)
                   -> [AExpr]
                   -> SM (S.Expr, SType)
doBinPrim_BitsBits w mkFn args =
    bitsArgs args >>= doBinPrim mkFn >>= bitsRes w

doBinPrimSz_BitsBits :: Integer
                     -> (S.Context -> Int -> S.Expr -> S.Expr -> IO S.Expr)
                     -> [AExpr]
                     -> SM (S.Expr, SType)
doBinPrimSz_BitsBits w mkFn args =
    bitsArgs args >>=
    doBinPrim (\ctx -> mkFn ctx (fromInteger w)) >>=
    bitsRes w

doUnPrim_BitsBits :: Integer
                  -> (S.Context -> S.Expr -> IO S.Expr)
                  -> [AExpr]
                  -> SM (S.Expr, SType)
doUnPrim_BitsBits w mkFn args =
    bitsArgs args >>= doUnPrim mkFn >>= bitsRes w

doBinIntPrim_BitsBits :: Integer
                      -> (S.Context -> S.Expr -> Int -> IO S.Expr)
                      -> AExpr
                      -> Int
                      -> StateT SState IO (S.Expr, SType)
doBinIntPrim_BitsBits w mkFn e n = do
    (ye, _) <- convAExpr2SExpr_Force False e
    yp <- doBinIntPrim mkFn ye n
    bitsRes w yp


boolArgs :: [AExpr] -> SM [S.Expr]
boolArgs = mapM (\ a -> convAExpr2SExpr_Force True a >>= return . fst)
bitsArgs :: [AExpr] -> SM [S.Expr]
bitsArgs = mapM (\ a -> convAExpr2SExpr_Force False a >>= return . fst)

boolRes :: Monad m => a -> m (a, SType)
boolRes   ye = return (ye, SBool)
bitsRes :: Monad m => Integer -> a -> m (a, SType)
bitsRes w ye = return (ye, SBits w)


doUnPrim :: (S.Context -> S.Expr -> IO S.Expr) -> [S.Expr] -> SM S.Expr
doUnPrim mkFn [y_arg] = do
    ctx <- gets context
    liftIO $ mkFn ctx y_arg
doUnPrim _ args =
    internalError ("doUnPrim: wrong number of args: " ++
                   ppReadable (length args))

doBinPrim :: (S.Context -> S.Expr -> S.Expr -> IO S.Expr) ->
             [S.Expr] -> SM S.Expr
doBinPrim mkFn [y_arg1, y_arg2] = do
    ctx <- gets context
    liftIO $ mkFn ctx y_arg1 y_arg2
doBinPrim _ args =
    internalError ("doBinPrim: wrong number of args: " ++
                   ppReadable (length args))

doBinManyPrim :: (S.Context -> [S.Expr] -> IO S.Expr) ->
                 [S.Expr] -> SM S.Expr
doBinManyPrim _ args | (length args < 2) =
    internalError ("doBinManyPrim: wrong number of args: " ++
                   ppReadable (length args))
doBinManyPrim mkFn ys_args = do
    ctx <- gets context
    liftIO $ mkFn ctx ys_args

-- Second argument cannot be dynamic
doBinIntPrim :: (S.Context -> S.Expr -> Int -> IO S.Expr) ->
                S.Expr -> Int -> SM S.Expr
doBinIntPrim mkFn y_arg1 n_arg2 = do
    ctx <- gets context
    liftIO $ mkFn ctx y_arg1 n_arg2


-- -----

extractInt :: AExpr -> Int
extractInt (ASInt _ _ (IntLit _ _ val)) = fromInteger val
extractInt e = internalError ("extractInt: unexpected pattern: " ++ show e)


-- -----

getWidth :: AType -> Integer
getWidth (ATBit w) = w
getWidth t = internalError ("AExpr2STP.getWidth: " ++ ppReadable t)

-- copied from similar function in AOpt
aZeroExtend :: Integer -> AExpr -> AExpr
aZeroExtend w e =
    let e_size = getWidth (ae_type e)
        pad_size = w - e_size
    in  case (compare pad_size 0) of
          EQ -> e
          GT -> APrim dummy_id (ATBit w) PrimConcat
                    [ASInt defaultAId (ATBit pad_size) (ilDec 0), e]
          LT -> internalError ("AExpr2STP.aZeroExtend: " ++ ppReadable (w, e))

aSignExtend :: Integer -> AExpr -> AExpr
aSignExtend w e =
    let e_size = getWidth (ae_type e)
        pad_size = w - e_size
    in  case (compare pad_size 0) of
          EQ -> e
          GT -> APrim dummy_id (ATBit w) PrimSignExt [e]
          LT -> internalError ("AExpr2STP.aSignExtend: " ++ ppReadable (w, e))

sTruncate :: Integer -> (S.Expr, SType) -> SM (S.Expr, SType)
sTruncate w res@(ye, SBits e_sz) | w == e_sz = return res
sTruncate w (ye, SBits e_sz) | e_sz > w =
    do ctx <- gets context
       ytrunc <- liftIO $ S.mkBVExtract ctx 0 (fromInteger (w-1)) ye
       return (ytrunc, SBits w)
sTruncate w (ye, yt) =
    internalError ("AExpr2STP.sTruncate: " ++ ppReadable (w, yt))


-- -------------------------
