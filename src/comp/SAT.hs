{-# LANGUAGE CPP #-}
module SAT(
           SATState,
           initSATState,
           checkBiImplication,
           isConstExpr,
           checkEq,
           checkNotEq,
           checkSATFlags
          ) where

import qualified Control.Exception as CE

import Error(ErrorHandle,bsWarning, ErrMsg(..))
import Flags
import ASyntax
import Position(cmdPosition)

import qualified AExpr2STP as STP
         (SState, initSState, checkBiImplication, isConstExpr,
          checkEq, checkNotEq)
import qualified AExpr2Yices as Yices
         (YState, initYState, checkBiImplication, isConstExpr,
          checkEq, checkNotEq)
import qualified AExpr2Bdd as BDD
         (BddBuilder, initBDDState, checkBiImplication, isConstExpr,
          checkEq, checkNotEq)

import Yices(checkVersion)

#if !defined(__GLASGOW_HASKELL__) || (__GLASGOW_HASKELL__ >= 609)
type ExceptionType = CE.SomeException
#else
type ExceptionType = CE.Exception
#endif

-- -------------------------

-- A single data type for either of the solver state
data SATState = SATS_BDD (BDD.BddBuilder AId)
              | SATS_Yices Yices.YState
              | SATS_STP STP.SState

-- -------------------------

initSATState :: String -> ErrorHandle -> Flags -> Bool -> [ADef] -> [AVInst] ->
                IO SATState
initSATState str errh flags doHardFail ds avis =
    case (satBackend flags) of
      SAT_CUDD -> do
          bdd_state <- BDD.initBDDState errh flags doHardFail ds avis []
          return (SATS_BDD bdd_state)
      SAT_Yices -> do
          yices_state <- Yices.initYState str flags doHardFail ds avis []
          return (SATS_Yices yices_state)
      SAT_STP -> do
          stp_state <- STP.initSState str flags doHardFail ds avis []
          return (SATS_STP stp_state)

checkSATFlags :: ErrorHandle -> Flags -> IO Flags
checkSATFlags eh f =
  if (SAT_Yices == satBackend f)
  then let
           handler :: ExceptionType -> IO Flags
           handler _ = do
               -- generate warning
               let w = (cmdPosition,
                        WSATNotAvailable "-sat-yices" "libyices.so.2" )
               bsWarning eh [w]
               let f' = f { satBackend = SAT_STP }
               return f'
       in  CE.catch (Yices.checkVersion >> return f) handler
  else return f

-- -------------------------

checkBiImplication :: SATState -> AExpr -> AExpr -> IO ((Bool, Bool), SATState)
checkBiImplication (SATS_BDD bdd_state) e1 e2 = do
    (res, bdd_state') <- BDD.checkBiImplication bdd_state e1 e2
    return (res, SATS_BDD bdd_state')
checkBiImplication (SATS_Yices yices_state) e1 e2 = do
    (res, yices_state') <- Yices.checkBiImplication yices_state e1 e2
    return (res, SATS_Yices yices_state')
checkBiImplication (SATS_STP stp_state) e1 e2 = do
    (res, stp_state') <- STP.checkBiImplication stp_state e1 e2
    return (res, SATS_STP stp_state')


isConstExpr :: SATState -> AExpr -> IO (Maybe Bool, SATState)
isConstExpr (SATS_BDD bdd_state) e = do
    (res, bdd_state') <- BDD.isConstExpr bdd_state e
    return (res, SATS_BDD bdd_state')
isConstExpr (SATS_Yices yices_state) e = do
    (res, yices_state') <- Yices.isConstExpr yices_state e
    return (res, SATS_Yices yices_state')
isConstExpr (SATS_STP stp_state) e = do
    (res, stp_state') <- STP.isConstExpr stp_state e
    return (res, SATS_STP stp_state')


checkEq :: SATState -> AExpr -> AExpr -> IO (Maybe Bool, SATState)
checkEq (SATS_BDD bdd_state) e1 e2 = do
    (res, bdd_state') <- BDD.checkEq bdd_state e1 e2
    return (res, SATS_BDD bdd_state')
checkEq (SATS_Yices yices_state) e1 e2 = do
    (res, yices_state') <- Yices.checkEq yices_state e1 e2
    return (res, SATS_Yices yices_state')
checkEq (SATS_STP stp_state) e1 e2 = do
    (res, stp_state') <- STP.checkEq stp_state e1 e2
    return (res, SATS_STP stp_state')


checkNotEq :: SATState -> AExpr -> AExpr -> IO (Maybe Bool, SATState)
checkNotEq (SATS_BDD bdd_state) e1 e2 = do
    (res, bdd_state') <- BDD.checkNotEq bdd_state e1 e2
    return (res, SATS_BDD bdd_state')
checkNotEq (SATS_Yices yices_state) e1 e2 = do
    (res, yices_state') <- Yices.checkNotEq yices_state e1 e2
    return (res, SATS_Yices yices_state')
checkNotEq (SATS_STP stp_state) e1 e2 = do
    (res, stp_state') <- STP.checkNotEq stp_state e1 e2
    return (res, SATS_STP stp_state')

-- -------------------------

