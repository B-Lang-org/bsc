module SATPred(
  SATPredState,
  initSATPredState,
  solvePred
  ) where

import Flags
import Pred

import qualified Pred2STP as STP
         (SState, initSState, solvePred)
import qualified Pred2Yices as Yices
         (YState, initYState, solvePred)

-- -------------------------

-- A single data type for any of the solver state
-- For now, we always use STP for this
data SATPredState =
           SATPredS_STP STP.SState
         | SATPredS_Yices Yices.YState

-- -------------------------

initSATPredState :: Flags -> IO SATPredState
initSATPredState flags = do
    case (satBackend flags) of
      SAT_STP -> do
        stp_state <- STP.initSState
        return (SATPredS_STP stp_state)
      SAT_Yices -> do
        yices_state <- Yices.initYState
        return (SATPredS_Yices yices_state)

-- -------------------------

{-
checkPreds :: SATPredState -> [Pred] -> IO ([EMsg], SATPredState)
checkPreds (SATPredS_STP stp_state) ps = do
    (res, stp_state') <- STP.checkPreds stp_state ps
    return (res, SATPredS_STP stp_state')
checkPreds (SATPredS_Yices yices_state) ps = do
    (res, yices_state') <- Yices.checkPreds yices_state ps
    return (res, SATPredS_Yices yices_state')
-}

-- -------------------------

solvePred :: SATPredState -> [Pred] -> Pred -> IO (Maybe Pred, SATPredState)
solvePred (SATPredS_STP stp_state) ps p = do
    (res, stp_state') <- STP.solvePred stp_state ps p
    return (res, SATPredS_STP stp_state')
solvePred (SATPredS_Yices yices_state) ps p = do
    (res, yices_state') <- Yices.solvePred yices_state ps p
    return (res, SATPredS_Yices yices_state')

-- -------------------------

