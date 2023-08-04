module Pred2Yices(
       YState,
       initYState,
       solvePred
) where

import Control.Monad(when)
import Control.Monad.State(StateT, liftIO, gets, get, put, runStateT)
import qualified Data.Map as M
import qualified Yices as Y

--import Flags
import PFPrint
import Id
import PreIds
import CType
import Type
import Pred

import Debug.Trace(traceM)
import IOUtil(progArgs)

traceTest :: Bool
traceTest = "-trace-smt-test" `elem` progArgs

traceConv :: Bool
traceConv = "-trace-smt-conv" `elem` progArgs

-- -------------------------

data YState =
    YState {
               context       :: Y.Context,
               --flags         :: Flags,

               -- all BSV types will be represented by one type in Yices,
               -- so keep a handle to the type
               intType       :: Y.Type,

               -- a map from types to their converted form
               -- (this is used both to avoid duplicate conversion
               -- and as a list of possible terms for solving)
               typeYExprMap   :: M.Map Type (Y.Expr, [Y.Expr])
              }

type YM = StateT YState IO

-- represent numeric types as 32-bit vectors
-- (since that provides a division operator and log/exp via shifting)
intWidth :: (Integral t) => t
intWidth = 32

-- -------------------------

initYState :: IO YState
initYState = do
  ctx <- liftIO $ Y.mkContext
  int_ty <- liftIO $ Y.mkBitVectorType intWidth
  return (YState { context = ctx,
                   --flags = flags,
                   intType = int_ty,
                   typeYExprMap = M.empty
                 })

-- -------------------------

-- XXX should this take the BVS and DVS?

solvePred :: YState -> [Pred] -> Pred -> IO (Maybe Pred, YState)
solvePred s ps p = runStateT (solvePredM ps p) s

solvePredM :: [Pred] -> Pred -> YM (Maybe Pred)
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
          liftIO $ Y.ctxPush ctx
          -- assert the given provisos
          mapM_ assertPred (p:ps)
          -- check if there exists a solution
          sat <- checkSAT
          -- pop the context
          liftIO $ Y.ctxPop ctx
          return (sat == Just True)

      -- if there is no solution, return the pred unsatisfied
      -- (if an error needs to be reported, it will be reported later)
      if (not is_sat)
        then do when traceTest $ traceM("solvePred: not satisfiable")
                return Nothing
        else do

          -- push a new context,
          -- so we can cleanly retract the work when we're done
          liftIO $ Y.ctxPush ctx
          -- assert the given provisos
          mapM_ assertPred ps

          -- XXX for now, we only resolve provisos where no substitution is learned

          -- assert the inequality and associated assumptions
          mapM_ (liftIO . Y.assert ctx) (yneq:as)
          -- check if there exists a solution
          sat <- checkSAT
          -- if it is satisfiable, then the equality does not hold
          let res = case sat of
                      Just False -> Just p
                      _ -> Nothing
          -- retract the assertions
          liftIO $ Y.ctxPop ctx
          when traceTest $
              case res of
                Nothing -> traceM ("solvePred: unresolved: " ++ ppReadable p)
                Just _  -> traceM ("solvePred: resolved: " ++ ppReadable p)
          return res


genPredInequality :: Pred -> YM (Maybe (Y.Expr, [Y.Expr]))
genPredInequality p@(IsIn c [t1, t2]) | classId c == idNumEq = do
  when traceTest $ traceM("pred: " ++ ppReadable p)
  (yt1, as1) <- convType2YExpr t1
  (yt2, as2) <- convType2YExpr t2
  ynp <- liftIO $ Y.mkBVNEq yt1 yt2
  return $ Just (ynp, as1 ++ as2)
genPredInequality p@(IsIn c [t1, t2, t3]) | classId c == idAdd = do
  when traceTest $ traceM("pred: " ++ ppReadable p)
  (yt3, as3) <- convType2YExpr t3
  (yadd, as12) <- convType2YExpr (TAp (TAp tAdd t1) t2)
  ynp <- liftIO $ Y.mkBVNEq yadd yt3
  return $ Just (ynp, as3 ++ as12)
genPredInequality p@(IsIn c [t1, t2, t3]) | classId c == idMul = do
  when traceTest $ traceM("pred: " ++ ppReadable p)
  (yt3, as3) <- convType2YExpr t3
  (ymul, as12) <- convType2YExpr (TAp (TAp tMul t1) t2)
  ynp <- liftIO $ Y.mkBVNEq ymul yt3
  return $ Just (ynp, as3 ++ as12)
genPredInequality p@(IsIn c [t1, t2, t3]) | classId c == idMax = do
  when traceTest $ traceM("pred: " ++ ppReadable p)
  (yt3, as3) <- convType2YExpr t3
  (ymax, as12) <- convType2YExpr (TAp (TAp tMax t1) t2)
  ynp <- liftIO $ Y.mkBVNEq ymax yt3
  return $ Just (ynp, as3 ++ as12)
genPredInequality p@(IsIn c [t1, t2, t3]) | classId c == idMin = do
  when traceTest $ traceM("pred: " ++ ppReadable p)
  (yt3, as3) <- convType2YExpr t3
  (ymin, as12) <- convType2YExpr (TAp (TAp tMin t1) t2)
  ynp <- liftIO $ Y.mkBVNEq ymin yt3
  return $ Just (ynp, as3 ++ as12)
genPredInequality p@(IsIn c [t1, t2, t3]) | classId c == idDiv = do
  when traceTest $ traceM("pred: " ++ ppReadable p)
  (yt3, as3) <- convType2YExpr t3
  (ydiv, as12) <- convType2YExpr (TAp (TAp tDiv t1) t2)
  ynp <- liftIO $ Y.mkBVNEq ydiv yt3
  return $ Just (ynp, as3 ++ as12)
genPredInequality p@(IsIn c [t1, t2, t3]) | classId c == idLog = do
  when traceTest $ traceM("pred: " ++ ppReadable p)
  (yt3, as3) <- convType2YExpr t3
  (ylog, as12) <- convType2YExpr (TAp (TAp tLog t1) t2)
  ynp <- liftIO $ Y.mkBVNEq ylog yt3
  return $ Just (ynp, as3 ++ as12)
genPredInequality p = do
  when traceTest $ traceM("pred unknown: " ++ ppReadable p)
  return Nothing

-- -------------------------

checkSAT :: YM (Maybe Bool)
checkSAT = do
  ctx <- gets context
  res <- liftIO $ Y.ctxStatus ctx
  case (res) of
    Y.Satisfiable -> return $ Just True
    Y.Unsatisfiable -> return $ Just False
    _ -> return Nothing

-- -------------------------

-- Use these functions to make sure that info is added to the most recent maps.
-- If you have a local copy of the map around, but then call monadic functions,
-- the local copy may become stale, and you'll lose info if you write back the
-- stale copy.

addToTypeMap :: Type -> (Y.Expr, [Y.Expr]) -> YM ()
addToTypeMap t res = do
    s <- get
    let tmap = typeYExprMap s
        tmap' = M.insert t res tmap
    put (s {typeYExprMap = tmap' })

-- -------------------------

addUnknownType :: Type -> YM (Y.Expr, [Y.Expr])
addUnknownType t = do
    when traceConv $ traceM("addUnknownType: " ++ ppString t)
    tmap <- gets typeYExprMap
    case (M.lookup t tmap) of
      Just res -> do when traceConv $ traceM("   reusing.")
                     return res
      Nothing -> do
        when traceConv $ traceM("   making new var.")
        ty <- gets intType
        var <- liftIO $ Y.mkUninterpretedTerm ty
        let res = (var, [])
        addToTypeMap t res
        return res

-- -------------------------

convType2YExpr :: Type -> YM (Y.Expr, [Y.Expr])
convType2YExpr t = do
  when traceConv $ traceM("converting: " ++ ppReadable t)
  tmap <- gets typeYExprMap
  case (M.lookup t tmap) of
    Just res -> do when traceConv $ traceM("   reusing.")
                   return res
    Nothing -> do
      when traceConv $ traceM("   converting new.")
      yt <- convType2YExpr' t
      addToTypeMap t yt
      return yt

convType2YExpr' :: Type -> YM (Y.Expr, [Y.Expr])
convType2YExpr' t@(TVar {}) = do
  when traceConv $ traceM("conv TyVar: " ++ ppReadable t)
  addUnknownType t
convType2YExpr' t@(TCon (TyNum n _)) = do
  when traceConv $ traceM("conv TyNum: " ++ ppReadable n)
  res <- liftIO $ Y.mkBVConstantFromInteger intWidth n
  return (res, [])
convType2YExpr' t@(TAp (TAp tc t1) t2) | (tc == tAdd) = do
  when traceConv $ traceM("conv TAdd: " ++ ppReadable t)
  (yt1, as1) <- convType2YExpr t1
  (yt2, as2) <- convType2YExpr t2
  res <- liftIO $ Y.mkBVAdd yt1 yt2
  -- assert that there is no overflow
  ygte1 <- liftIO $ Y.mkBVGe res yt1
  return (res, [ygte1] ++ as1 ++ as2)
convType2YExpr' t@(TAp (TAp tc t1) t2) | (tc == tSub) = do
  when traceConv $ traceM("conv TSub: " ++ ppReadable t)
  (yt1, as1) <- convType2YExpr t1
  (yt2, as2) <- convType2YExpr t2
  res <- liftIO $ Y.mkBVSub yt1 yt2
  -- assert that there is no underflow
  ygte1 <- liftIO $ Y.mkBVGe yt1 res
  return (res, [ygte1] ++ as1 ++ as2)
convType2YExpr' t@(TAp (TAp tc t1) t2) | (tc == tMul) = do
  when traceConv $ traceM("conv TMul: " ++ ppReadable t)
  (yt1, as1) <- convType2YExpr t1
  (yt2, as2) <- convType2YExpr t2
  res <- liftIO $ Y.mkBVMul yt1 yt2
  -- assert that there is no overflow: (t2 == 0) || (res >= t1)
  yzero <- liftIO $ Y.mkBVConstantFromInteger intWidth 0
  yeqz2 <- liftIO $ Y.mkBVEq yt2 yzero
  ygte1 <- liftIO $ Y.mkBVGe res yt1
  yor <- liftIO $ Y.mkOr [yeqz2, ygte1]
  return (res, [yor] ++ as1 ++ as2)
convType2YExpr' t@(TAp tc t1) | (tc == tExp) = do
  when traceConv $ traceM("conv TExp: " ++ ppReadable t)
  (yt1, as1) <- convType2YExpr t1
  yone <- liftIO $ Y.mkBVConstantOne intWidth
  res <- liftIO $ Y.mkBVShiftLeft yone yt1
  -- assert that there is no overflow: (t1 == 0) || (res >= t1)
  yzero <- liftIO $ Y.mkBVConstantFromInteger intWidth 0
  yeqz1 <- liftIO $ Y.mkBVEq yt1 yzero
  ygte1 <- liftIO $ Y.mkBVGe res yt1
  yor <- liftIO $ Y.mkOr [yeqz1, ygte1]
  return (res, [yor] ++ as1)
convType2YExpr' t@(TAp (TAp tc t1) t2) | (tc == tMax) = do
  when traceConv $ traceM("conv TMax: " ++ ppReadable t)
  (yt1, as1) <- convType2YExpr t1
  (yt2, as2) <- convType2YExpr t2
  y_t1gt <- liftIO $ Y.mkBVGt yt1 yt2
  res <- liftIO $ Y.mkIte y_t1gt yt1 yt2
  return (res, as1 ++ as2)
convType2YExpr' t@(TAp (TAp tc t1) t2) | (tc == tMin) = do
  when traceConv $ traceM("conv TMin: " ++ ppReadable t)
  (yt1, as1) <- convType2YExpr t1
  (yt2, as2) <- convType2YExpr t2
  y_t1gt <- liftIO $ Y.mkBVGt yt1 yt2
  res <- liftIO $ Y.mkIte y_t1gt yt2 yt1
  return (res, as1 ++ as2)
convType2YExpr' t@(TAp (TAp tc t1) t2) | (tc == tDiv) = do
  when traceConv $ traceM("conv TDiv: " ++ ppReadable t)
  (yt1, as1) <- convType2YExpr t1
  (yt2, as2) <- convType2YExpr t2
  -- A division operator exists, but TDiv returns the ceiling, not floor.
  -- So create a variable "v" ...
  ty <- gets intType
  var <- liftIO $ Y.mkUninterpretedTerm ty
  -- and assert that:
  -- (t2 * v <= t1)
  ymul <- liftIO $ Y.mkBVMul yt2 var
  yle <- liftIO $ Y.mkBVLe ymul yt1
  -- and (t1 < t2 * (v + 1))
  -- XXX consider using (t2 * v) + t2 for better sharing?
  yone <- liftIO $ Y.mkBVConstantOne intWidth
  yt2plus1 <- liftIO $ Y.mkBVAdd yt2 yone
  ymul1 <- liftIO $ Y.mkBVMul yt2 yt2plus1
  ylt <- liftIO $ Y.mkBVLt yt1 ymul1
  -- assert that t2 is not zero
  -- XXX is this necessary?
  yzero <- liftIO $ Y.mkBVConstantFromInteger intWidth 0
  yneqz2 <- liftIO $ Y.mkBVNEq yt2 yzero
  -- return the variable
  return (var, [yle, ylt, yneqz2] ++ as1 ++ as2)
convType2YExpr' t@(TAp tc t1) | (tc == tLog) = do
  when traceConv $ traceM("conv TLog: " ++ ppReadable t)
  (yt1, as1) <- convType2YExpr t1
  -- Create a variable "v" ...
  ty <- gets intType
  var <- liftIO $ Y.mkUninterpretedTerm ty
  -- and assert that:
  -- ((1 << v) <= t1)
  yone <- liftIO $ Y.mkBVConstantOne intWidth
  texp <- liftIO $ Y.mkBVShiftLeft yone var
  yle <- liftIO $ Y.mkBVLe texp yt1
  -- and (t1 < (1 << (v + 1)))
  -- but expressed as a multiply for better sharing:
  -- (t1 < (2 * (1 << v)))
  ytwo <- liftIO $ Y.mkBVConstantFromInteger intWidth 2
  yexp1 <- liftIO $ Y.mkBVMul ytwo texp
  ylt <- liftIO $ Y.mkBVLt yt1 yexp1
  -- assert that t1 is not zero
  -- XXX is this necessary?
  yzero <- liftIO $ Y.mkBVConstantFromInteger intWidth 0
  yneqz1 <- liftIO $ Y.mkBVNEq yt1 yzero
  -- return the variable
  return (var, [yle, ylt, yneqz1] ++ as1)
convType2YExpr' t = do
  when traceConv $ traceM("conv unknown: " ++ ppReadable t)
  addUnknownType t

-- -------------------------

assertPred :: Pred -> YM ()
assertPred p@(IsIn c [t1, t2]) | classId c == idNumEq = do
  when traceTest $ traceM("asserting: " ++ ppReadable p)
  ctx <- gets context
  (yt1, as1) <- convType2YExpr t1
  (yt2, as2) <- convType2YExpr t2
  yeq <- liftIO $ Y.mkBVEq yt1 yt2
  mapM_ (liftIO . Y.assert ctx) $ [yeq] ++ as1 ++ as2
assertPred p@(IsIn c [t1, t2, t3]) | classId c == idAdd = do
  when traceTest $ traceM("asserting: " ++ ppReadable p)
  ctx <- gets context
  (yt3, as3) <- convType2YExpr t3
  (yadd, as12) <- convType2YExpr (TAp (TAp tAdd t1) t2)
  yeq <- liftIO $ Y.mkBVEq yadd yt3
  mapM_ (liftIO . Y.assert ctx) $ [yeq] ++ as3 ++ as12
assertPred p@(IsIn c [t1, t2, t3]) | classId c == idMul = do
  when traceTest $ traceM("asserting: " ++ ppReadable p)
  ctx <- gets context
  (yt3, as3) <- convType2YExpr t3
  (ymul, as12) <- convType2YExpr (TAp (TAp tMul t1) t2)
  yeq <- liftIO $ Y.mkBVEq ymul yt3
  mapM_ (liftIO . Y.assert ctx) $ [yeq] ++ as3 ++ as12
assertPred p@(IsIn c [t1, t2, t3]) | classId c == idMax = do
  when traceTest $ traceM("asserting: " ++ ppReadable p)
  ctx <- gets context
  (yt3, as3) <- convType2YExpr t3
  (ymax, as12) <- convType2YExpr (TAp (TAp tMax t1) t2)
  yeq <- liftIO $ Y.mkBVEq ymax yt3
  mapM_ (liftIO . Y.assert ctx) $ [yeq] ++ as3 ++ as12
assertPred p@(IsIn c [t1, t2, t3]) | classId c == idMin = do
  when traceTest $ traceM("asserting: " ++ ppReadable p)
  ctx <- gets context
  (yt3, as3) <- convType2YExpr t3
  (ymin, as12) <- convType2YExpr (TAp (TAp tMin t1) t2)
  yeq <- liftIO $ Y.mkBVEq ymin yt3
  mapM_ (liftIO . Y.assert ctx) $ [yeq] ++ as3 ++ as12
assertPred p@(IsIn c [t1, t2, t3]) | classId c == idDiv = do
  when traceTest $ traceM("asserting: " ++ ppReadable p)
  ctx <- gets context
  (yt3, as3) <- convType2YExpr t3
  (ydiv, as12) <- convType2YExpr (TAp (TAp tDiv t1) t2)
  yeq <- liftIO $ Y.mkBVEq ydiv yt3
  mapM_ (liftIO . Y.assert ctx) $ [yeq] ++ as3 ++ as12
assertPred p@(IsIn c [t1, t2]) | classId c == idLog = do
  when traceTest $ traceM("asserting: " ++ ppReadable p)
  ctx <- gets context
  (yt2, as2) <- convType2YExpr t2
  (ylog, as1) <- convType2YExpr (TAp tLog t1)
  yeq <- liftIO $ Y.mkBVEq ylog yt2
  mapM_ (liftIO . Y.assert ctx) $ [yeq] ++ as2 ++ as1
assertPred p = do
  when traceTest $ traceM("ignoring pred: " ++ ppReadable p)
  return ()

-- -------------------------

classId :: Class -> Id
classId = typeclassId . name

-- -------------------------
