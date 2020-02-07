module SATPred(
  SATPredState,
  initSATPredState,
  solvePred
  ) where

import Flags
import Pred

import qualified Pred2Yices as Yices
         (YState, initYState, solvePred)

-- -------------------------

-- A single data type for any of the solver state
-- For now, we always use Yices for this
data SATPredState = SATPredS_Yices Yices.YState

-- -------------------------

initSATPredState :: Flags -> IO SATPredState
initSATPredState flags =
    case (satBackend flags) of
      SAT_Yices -> do
        yices_state <- Yices.initYState
        return (SATPredS_Yices yices_state)

-- -------------------------

solvePred :: SATPredState -> [Pred] -> Pred -> IO (Maybe Pred, SATPredState)
solvePred (SATPredS_Yices yices_state) ps p = do
    (res, yices_state') <- Yices.solvePred yices_state ps p
    return (res, SATPredS_Yices yices_state')

-- -------------------------

