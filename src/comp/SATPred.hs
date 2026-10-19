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

-- A single data type for any of the solver state.
--
-- NOTE: the vendored Yices binding resets the entire library whenever
-- a context is created after the first (see HaskellIfc/Yices.hs,
-- doInit), relying on the assumption that only one context is ever in
-- use.  A SATPredState must therefore live entirely within a single
-- atomic evaluation (one unsafePerformIO block): kept any longer, it
-- can be invalidated by another session's creation -- e.g. by a
-- nested typecheck run from a lazily forced thunk -- turning later
-- queries into use-after-reset.  batchSolveNumericPreds (TCMisc)
-- creates one session per batch inside its own IO block for exactly
-- this reason.

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

solvePred :: SATPredState -> [Pred] -> Pred -> IO (Maybe Pred, SATPredState)
solvePred (SATPredS_STP stp_state) ps p = do
    (res, stp_state') <- STP.solvePred stp_state ps p
    return (res, SATPredS_STP stp_state')
solvePred (SATPredS_Yices yices_state) ps p = do
    (res, yices_state') <- Yices.solvePred yices_state ps p
    return (res, SATPredS_Yices yices_state')

-- -------------------------
