module Pred2STP(
       SState,
       initSState,
       solvePred
) where

import Control.Monad(when)
import Control.Monad.State(StateT, liftIO, gets, get, put, runStateT)
import qualified Data.Map as M
import qualified STP as S

import ErrorUtil(internalError)
--import Flags
import PFPrint
import Id
import PreIds
import CType
import Type
import Pred
import Util(itos)

import Debug.Trace(traceM)
import IOUtil(progArgs)

traceTest :: Bool
traceTest = "-trace-smt-test" `elem` progArgs

traceConv :: Bool
traceConv = "-trace-smt-conv" `elem` progArgs

-- -------------------------

data SState =
    SState {
               context       :: S.Context,
               --flags         :: Flags,

               -- source of unique identifiers
               unknownId     :: Integer,

               -- all BSV types will be represented by one type in STP,
               -- so keep a handle to the type
               intType       :: S.Type,

               -- a map from types to their converted form
               -- (this is used both to avoid duplicate conversion
               -- and as a list of possible terms for solving)
               typeSExprMap   :: M.Map Type (S.Expr, [S.Expr])
              }

type SM = StateT SState IO

-- represent numeric types as 32-bit vectors
-- (since that provides a division operator and log/exp via shifting)
intWidth :: (Integral t) => t
intWidth = 32

-- -------------------------

initSState :: IO SState
initSState = do
  ctx <- liftIO $ S.mkContext
  int_ty <- liftIO $ S.mkBitVectorType ctx intWidth
  return (SState { context = ctx,
                   --flags = flags,
                   unknownId = 0,
                   intType = int_ty,
                   typeSExprMap = M.empty
                 })

-- -------------------------

{-
-- XXX We'll eventually want to test that user-given provisos are satisfiable
-- XXX and give a user error if not.  We'll also want to test, before reporting
-- XXX that additional provisos are needed, that the additional provisos are
-- XXX satisfiable.

-- Check if a set of predicates is consistent

checkPreds :: SState -> [Pred] -> IO ([EMsg], SState)
checkPreds s ps = runStateT (checkPredsM ps) s

checkPredsM :: [Pred] -> SM [EMsg]
checkPredsM ps = do
  ctx <- gets context

  -- push a new context, so we can cleanly retract the work when we're done
  liftIO $ S.ctxPush ctx

  -- assert the given provisos
  mapM_ assertPred ps

  -- check if there exists a solution
  sat <- checkSAT

  -- pop the context
  liftIO $ S.ctxPop ctx

  -- if there is no solution, report an error to the user
  if (sat /= Just True)
    then reportMinUnsatPreds [] ps
    else return []


reportMinUnsatPreds :: [Pred] -> [Pred] -> SM [EMsg]
reportMinUnsatPreds qs [] =
  -- XXX "satisfy" will need to take a position and plumb it to "reducePred"
  return [(noPosition, EGeneric ("unsat preds: " ++ ppReadable qs))]

reportMinUnsatPreds qs (p:ps) = do
  ctx <- gets context

  -- push a new context, so we can cleanly retract the work when we're done
  liftIO $ S.ctxPush ctx

  -- assert all the provisos besides "p"
  mapM_ assertPred (qs ++ ps)

  -- check if there exists a solution
  sat <- checkSAT

  -- pop the context
  liftIO $ S.ctxPop ctx

  -- if there is still no solution, then drop "p" else keep it
  if (sat /= Just True)
    then reportMinUnsatPreds qs ps
    else reportMinUnsatPreds (p:qs) ps
-}

-- -------------------------

-- XXX should this take the BVS and DVS?

solvePred :: SState -> [Pred] -> Pred -> IO (Maybe Pred, SState)
solvePred s ps p = runStateT (solvePredM ps p) s

solvePredM :: [Pred] -> Pred -> SM (Maybe Pred)
solvePredM ps p = do
  ctx <- gets context

  when traceTest $ traceM ("solvePred: " ++ ppReadable p)

  -- check that the pred is one that we handle, and if so then
  -- construct p as an inequality (along with its additional assertions)
  m_yneq <- genPredInequality p
  case m_yneq of
    Nothing -> do
      -- the pred is not of the form that we can handle
      when traceTest $ traceM("solvePred: not handled")
      return Nothing
    Just (yneq, as) -> do

      -- first make sure that the preds have at least one solution
      is_sat <- do
          -- push a new context,
          -- so we can cleanly retract the work when we're done
          liftIO $ S.ctxPush ctx
          -- assert the given provisos
          mapM_ assertPred (p:ps)
          -- check if there exists a solution
          sat <- checkSAT
          -- pop the context
          liftIO $ S.ctxPop ctx
          return (sat == Just True)

      -- if there is no solution, return the pred unsatisfied
      -- (if an error needs to be reported, it will be reported later)
      if (not is_sat)
        then do when traceTest $ traceM("solvePred: not satisfiable")
                return Nothing
        else do

          -- push a new context,
          -- so we can cleanly retract the work when we're done
          liftIO $ S.ctxPush ctx
          -- assert the given provisos
          mapM_ assertPred ps

          -- XXX for now, we only resolve provisos where no substitution is learned

          -- assert the inequality and associated assumptions
          mapM_ (liftIO . S.assert ctx) (yneq:as)
          -- check if there exists a solution
          sat <- checkSAT
          -- if it is satisfiable, then the equality does not hold
          let res = case sat of
                      Just False -> Just p
                      _ -> Nothing
          -- retract the assertions
          liftIO $ S.ctxPop ctx
          when traceTest $
              case res of
                Nothing -> traceM ("solvePred: unresolved: " ++ ppReadable p)
                Just _  -> traceM ("solvePred: resolved: " ++ ppReadable p)
          return res


genPredInequality :: Pred -> SM (Maybe (S.Expr, [S.Expr]))
genPredInequality p@(IsIn c [t1, t2]) | classId c == idNumEq = do
  when traceTest $ traceM("pred: " ++ ppReadable p)
  (yt1, as1) <- convType2SExpr t1
  (yt2, as2) <- convType2SExpr t2
  ynp <- mkNEq yt1 yt2
  return $ Just (ynp, as1 ++ as2)
genPredInequality p@(IsIn c [t1, t2, t3]) | classId c == idAdd = do
  when traceTest $ traceM("pred: " ++ ppReadable p)
  (yt3, as3) <- convType2SExpr t3
  (yadd, as12) <- convType2SExpr (TAp (TAp tAdd t1) t2)
  ynp <- mkNEq yadd yt3
  return $ Just (ynp, as3 ++ as12)
genPredInequality p@(IsIn c [t1, t2, t3]) | classId c == idMul = do
  when traceTest $ traceM("pred: " ++ ppReadable p)
  (yt3, as3) <- convType2SExpr t3
  (ymul, as12) <- convType2SExpr (TAp (TAp tMul t1) t2)
  ynp <- mkNEq ymul yt3
  return $ Just (ynp, as3 ++ as12)
genPredInequality p@(IsIn c [t1, t2, t3]) | classId c == idMax = do
  when traceTest $ traceM("pred: " ++ ppReadable p)
  (yt3, as3) <- convType2SExpr t3
  (ymax, as12) <- convType2SExpr (TAp (TAp tMax t1) t2)
  ynp <- mkNEq ymax yt3
  return $ Just (ynp, as3 ++ as12)
genPredInequality p@(IsIn c [t1, t2, t3]) | classId c == idMin = do
  when traceTest $ traceM("pred: " ++ ppReadable p)
  (yt3, as3) <- convType2SExpr t3
  (ymin, as12) <- convType2SExpr (TAp (TAp tMin t1) t2)
  ynp <- mkNEq ymin yt3
  return $ Just (ynp, as3 ++ as12)
genPredInequality p@(IsIn c [t1, t2, t3]) | classId c == idDiv = do
  when traceTest $ traceM("pred: " ++ ppReadable p)
  (yt3, as3) <- convType2SExpr t3
  (ydiv, as12) <- convType2SExpr (TAp (TAp tDiv t1) t2)
  ynp <- mkNEq ydiv yt3
  return $ Just (ynp, as3 ++ as12)
genPredInequality p@(IsIn c [t1, t2, t3]) | classId c == idLog = do
  when traceTest $ traceM("pred: " ++ ppReadable p)
  (yt3, as3) <- convType2SExpr t3
  (ylog, as12) <- convType2SExpr (TAp (TAp tLog t1) t2)
  ynp <- mkNEq ylog yt3
  return $ Just (ynp, as3 ++ as12)
genPredInequality p = do
  when traceTest $ traceM("pred unknown: " ++ ppReadable p)
  return Nothing

-- -------------------------

checkSAT :: SM (Maybe Bool)
checkSAT = do
  ctx <- gets context
  yf <- liftIO $ S.mkFalse ctx
  sat_res <- liftIO $ S.query ctx yf
  -- if query(False) is Valid, then there is an inconsistency,
  -- so the asserted expressions are not satisfiable
  case (sat_res) of
    S.Invalid -> return $ Just True
    S.Valid -> return $ Just False
    S.Timeout -> return Nothing
    S.Error -> internalError ("STP query error")

-- -------------------------

-- Use these functions to make sure that info is added to the most recent maps.
-- If you have a local copy of the map around, but then call monadic functions,
-- the local copy may become stale, and you'll lose info if you write back the
-- stale copy.

addToTypeMap :: Type -> (S.Expr, [S.Expr]) -> SM ()
addToTypeMap t res = do
    s <- get
    let tmap = typeSExprMap s
        tmap' = M.insert t res tmap
    put (s {typeSExprMap = tmap' })

-- -------------------------

getUnknownName :: SM String
getUnknownName = do
    s <- get
    let n = unknownId s
    -- XXX we need to check for name clash
    let str = "__unknown_" ++ itos n
    put (s { unknownId = n + 1})
    return str

mkUnknownVar :: SM S.Expr
mkUnknownVar = do
    ctx <- gets context
    str <- getUnknownName
    ty <- gets intType
    liftIO $ S.mkVar ctx str ty

addUnknownType :: Type -> SM (S.Expr, [S.Expr])
addUnknownType t = do
    when traceConv $ traceM("addUnknownType: " ++ ppString t)
    tmap <- gets typeSExprMap
    case (M.lookup t tmap) of
      Just res -> do when traceConv $ traceM("   reusing.")
                     return res
      Nothing -> do
        when traceConv $ traceM("   making new var.")
        var <- mkUnknownVar
        let res = (var, [])
        addToTypeMap t res
        return res

-- -------------------------

convType2SExpr :: Type -> SM (S.Expr, [S.Expr])
convType2SExpr t = do
  when traceConv $ traceM("converting: " ++ ppReadable t)
  tmap <- gets typeSExprMap
  case (M.lookup t tmap) of
    Just res -> do when traceConv $ traceM("   reusing.")
                   return res
    Nothing -> do
      when traceConv $ traceM("   converting new.")
      yt <- convType2SExpr' t
      addToTypeMap t yt
      return yt

convType2SExpr' :: Type -> SM (S.Expr, [S.Expr])
convType2SExpr' t@(TVar {}) = do
  when traceConv $ traceM("conv TyVar: " ++ ppReadable t)
  addUnknownType t
convType2SExpr' t@(TCon (TyNum n _)) = do
  when traceConv $ traceM("conv TyNum: " ++ ppReadable n)
  ctx <- gets context
  res <- liftIO $ S.mkBVConstantFromInteger ctx intWidth n
  return (res, [])
convType2SExpr' t@(TAp (TAp tc t1) t2) | (tc == tAdd) = do
  when traceConv $ traceM("conv TAdd: " ++ ppReadable t)
  ctx <- gets context
  (yt1, as1) <- convType2SExpr t1
  (yt2, as2) <- convType2SExpr t2
  res <- liftIO $ S.mkBVAdd ctx intWidth yt1 yt2
  -- assert that there is no overflow
  ygte1 <- liftIO $ S.mkBVGe ctx res yt1
  return (res, [ygte1] ++ as1 ++ as2)
convType2SExpr' t@(TAp (TAp tc t1) t2) | (tc == tSub) = do
  when traceConv $ traceM("conv TSub: " ++ ppReadable t)
  ctx <- gets context
  (yt1, as1) <- convType2SExpr t1
  (yt2, as2) <- convType2SExpr t2
  res <- liftIO $ S.mkBVSub ctx intWidth yt1 yt2
  -- assert that there is no underflow
  ygte1 <- liftIO $ S.mkBVGe ctx yt1 res
  return (res, [ygte1] ++ as1 ++ as2)
convType2SExpr' t@(TAp (TAp tc t1) t2) | (tc == tMul) = do
  when traceConv $ traceM("conv TMul: " ++ ppReadable t)
  ctx <- gets context
  (yt1, as1) <- convType2SExpr t1
  (yt2, as2) <- convType2SExpr t2
  res <- liftIO $ S.mkBVMul ctx intWidth yt1 yt2
  -- assert that there is no overflow: (t2 == 0) || (res >= t1)
  yzero <- liftIO $ S.mkBVConstantFromInteger ctx intWidth 0
  yeqz2 <- liftIO $ S.mkEq ctx yt2 yzero
  ygte1 <- liftIO $ S.mkBVGe ctx res yt1
  yor <- liftIO $ S.mkOr ctx yeqz2 ygte1
  return (res, [yor] ++ as1 ++ as2)
convType2SExpr' t@(TAp tc t1) | (tc == tExp) = do
  when traceConv $ traceM("conv TExp: " ++ ppReadable t)
  ctx <- gets context
  (yt1, as1) <- convType2SExpr t1
  yone <- liftIO $ S.mkBVConstantFromInteger ctx intWidth 1
  res <- liftIO $ S.mkBVShiftLeftExpr ctx intWidth yone yt1
  -- assert that there is no overflow: (t1 == 0) || (res >= t1)
  yzero <- liftIO $ S.mkBVConstantFromInteger ctx intWidth 0
  yeqz1 <- liftIO $ S.mkEq ctx yt1 yzero
  ygte1 <- liftIO $ S.mkBVGe ctx res yt1
  yor <- liftIO $ S.mkOr ctx yeqz1 ygte1
  return (res, [yor] ++ as1)
convType2SExpr' t@(TAp (TAp tc t1) t2) | (tc == tMax) = do
  when traceConv $ traceM("conv TMax: " ++ ppReadable t)
  ctx <- gets context
  (yt1, as1) <- convType2SExpr t1
  (yt2, as2) <- convType2SExpr t2
  y_t1gt <- liftIO $ S.mkBVGt ctx yt1 yt2
  res <- liftIO $ S.mkIte ctx y_t1gt yt1 yt2
  return (res, as1 ++ as2)
convType2SExpr' t@(TAp (TAp tc t1) t2) | (tc == tMin) = do
  when traceConv $ traceM("conv TMin: " ++ ppReadable t)
  ctx <- gets context
  (yt1, as1) <- convType2SExpr t1
  (yt2, as2) <- convType2SExpr t2
  y_t1gt <- liftIO $ S.mkBVGt ctx yt1 yt2
  res <- liftIO $ S.mkIte ctx y_t1gt yt2 yt1
  return (res, as1 ++ as2)
convType2SExpr' t@(TAp (TAp tc t1) t2) | (tc == tDiv) = do
  when traceConv $ traceM("conv TDiv: " ++ ppReadable t)
  ctx <- gets context
  (yt1, as1) <- convType2SExpr t1
  (yt2, as2) <- convType2SExpr t2
  -- A division operator exists, but TDiv returns the ceiling, not floor.
  -- So create a variable "v" ...
  var <- mkUnknownVar
  -- and assert that:
  -- (t2 * v <= t1)
  ymul <- liftIO $ S.mkBVMul ctx intWidth yt2 var
  yle <- liftIO $ S.mkBVLe ctx ymul yt1
  -- and (t1 < t2 * (v + 1))
  -- XXX consider using (t2 * v) + t2 for better sharing?
  yone <- liftIO $ S.mkBVConstantFromInteger ctx intWidth 1
  yt2plus1 <- liftIO $ S.mkBVAdd ctx intWidth yt2 yone
  ymul1 <- liftIO $ S.mkBVMul ctx intWidth yt2 yt2plus1
  ylt <- liftIO $ S.mkBVLt ctx yt1 ymul1
  -- assert that t2 is not zero
  -- XXX is this necessary?
  yzero <- liftIO $ S.mkBVConstantFromInteger ctx intWidth 0
  yneqz2 <- mkNEq yt2 yzero
  -- return the variable
  return (var, [yle, ylt, yneqz2] ++ as1 ++ as2)
convType2SExpr' t@(TAp tc t1) | (tc == tLog) = do
  when traceConv $ traceM("conv TLog: " ++ ppReadable t)
  ctx <- gets context
  (yt1, as1) <- convType2SExpr t1
  -- Create a variable "v" ...
  var <- mkUnknownVar
  -- and assert that:
  -- ((1 << v) <= t1)
  yone <- liftIO $ S.mkBVConstantFromInteger ctx intWidth 1
  texp <- liftIO $ S.mkBVShiftLeftExpr ctx intWidth yone var
  yle <- liftIO $ S.mkBVLe ctx texp yt1
  -- and (t1 < (1 << (v + 1)))
  -- but expressed as a multiply for better sharing:
  -- (t1 < (2 * (1 << v)))
  ytwo <- liftIO $ S.mkBVConstantFromInteger ctx intWidth 2
  yexp1 <- liftIO $ S.mkBVMul ctx intWidth ytwo texp
  ylt <- liftIO $ S.mkBVLt ctx yt1 yexp1
  -- assert that t1 is not zero
  -- XXX is this necessary?
  yzero <- liftIO $ S.mkBVConstantFromInteger ctx intWidth 0
  yneqz1 <- mkNEq yt1 yzero
  -- return the variable
  return (var, [yle, ylt, yneqz1] ++ as1)
convType2SExpr' t = do
  when traceConv $ traceM("conv unknown: " ++ ppReadable t)
  addUnknownType t

-- -------------------------

assertPred :: Pred -> SM ()
assertPred p@(IsIn c [t1, t2]) | classId c == idNumEq = do
  when traceTest $ traceM("asserting: " ++ ppReadable p)
  ctx <- gets context
  (yt1, as1) <- convType2SExpr t1
  (yt2, as2) <- convType2SExpr t2
  yeq <- liftIO $ S.mkEq ctx yt1 yt2
  mapM_ (liftIO . S.assert ctx) $ [yeq] ++ as1 ++ as2
assertPred p@(IsIn c [t1, t2, t3]) | classId c == idAdd = do
  when traceTest $ traceM("asserting: " ++ ppReadable p)
  ctx <- gets context
  (yt3, as3) <- convType2SExpr t3
  (yadd, as12) <- convType2SExpr (TAp (TAp tAdd t1) t2)
  yeq <- liftIO $ S.mkEq ctx yadd yt3
  mapM_ (liftIO . S.assert ctx) $ [yeq] ++ as3 ++ as12
assertPred p@(IsIn c [t1, t2, t3]) | classId c == idMul = do
  when traceTest $ traceM("asserting: " ++ ppReadable p)
  ctx <- gets context
  (yt3, as3) <- convType2SExpr t3
  (ymul, as12) <- convType2SExpr (TAp (TAp tMul t1) t2)
  yeq <- liftIO $ S.mkEq ctx ymul yt3
  mapM_ (liftIO . S.assert ctx) $ [yeq] ++ as3 ++ as12
assertPred p@(IsIn c [t1, t2, t3]) | classId c == idMax = do
  when traceTest $ traceM("asserting: " ++ ppReadable p)
  ctx <- gets context
  (yt3, as3) <- convType2SExpr t3
  (ymax, as12) <- convType2SExpr (TAp (TAp tMax t1) t2)
  yeq <- liftIO $ S.mkEq ctx ymax yt3
  mapM_ (liftIO . S.assert ctx) $ [yeq] ++ as3 ++ as12
assertPred p@(IsIn c [t1, t2, t3]) | classId c == idMin = do
  when traceTest $ traceM("asserting: " ++ ppReadable p)
  ctx <- gets context
  (yt3, as3) <- convType2SExpr t3
  (ymin, as12) <- convType2SExpr (TAp (TAp tMin t1) t2)
  yeq <- liftIO $ S.mkEq ctx ymin yt3
  mapM_ (liftIO . S.assert ctx) $ [yeq] ++ as3 ++ as12
assertPred p@(IsIn c [t1, t2, t3]) | classId c == idDiv = do
  when traceTest $ traceM("asserting: " ++ ppReadable p)
  ctx <- gets context
  (yt3, as3) <- convType2SExpr t3
  (ydiv, as12) <- convType2SExpr (TAp (TAp tDiv t1) t2)
  yeq <- liftIO $ S.mkEq ctx ydiv yt3
  mapM_ (liftIO . S.assert ctx) $ [yeq] ++ as3 ++ as12
assertPred p@(IsIn c [t1, t2]) | classId c == idLog = do
  when traceTest $ traceM("asserting: " ++ ppReadable p)
  ctx <- gets context
  (yt2, as2) <- convType2SExpr t2
  (ylog, as1) <- convType2SExpr (TAp tLog t1)
  yeq <- liftIO $ S.mkEq ctx ylog yt2
  mapM_ (liftIO . S.assert ctx) $ [yeq] ++ as2 ++ as1
assertPred p = do
  when traceTest $ traceM("ignoring pred: " ++ ppReadable p)
  return ()

-- -------------------------

classId :: Class -> Id
classId = typeclassId . name

-- -------------------------

mkNEq :: S.Expr -> S.Expr -> SM S.Expr
mkNEq y1 y2 = do
  ctx <- gets context
  yeq <- liftIO $ S.mkEq ctx y1 y2
  liftIO $ S.mkNot ctx yeq

-- -------------------------
