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

import Error(ErrorHandle, bsError, ErrMsg(..))
import Flags
import ASyntax
import Position(cmdPosition)

import qualified AExpr2STP as STP
         (SState, initSState, checkBiImplication, isConstExpr,
          checkEq, checkNotEq)
import qualified AExpr2Yices as Yices
         (YState, initYState, checkBiImplication, isConstExpr,
          checkEq, checkNotEq)

import STP(checkVersion)
import Yices(checkVersion)

-- -------------------------

-- A single data type for either of the solver state
data SATState = SATS_Yices Yices.YState
              | SATS_STP STP.SState

-- -------------------------

initSATState :: String -> ErrorHandle -> Flags -> Bool -> [ADef] -> [AVInst] ->
                IO SATState
initSATState str errh flags doHardFail ds avis =
    case (satBackend flags) of
      SAT_Yices -> do
          yices_state <- Yices.initYState str flags doHardFail ds avis []
          return (SATS_Yices yices_state)
      SAT_STP -> do
          stp_state <- STP.initSState str flags doHardFail ds avis []
          return (SATS_STP stp_state)


checkSATFlags :: ErrorHandle -> Flags -> IO Flags
checkSATFlags eh f =
  let
      hasYices :: IO Bool
      hasYices = let handler :: CE.SomeException -> IO Bool
                     handler _ = return False
                 in  CE.catch (Yices.checkVersion >> return True) handler

      hasSTP :: IO Bool
      hasSTP = STP.checkVersion

      checkFn :: String -> String -> IO Bool -> IO Flags
      checkFn flag_str lib_str hasFn = do
        res <- hasFn
        if res
          then return f
          else -- Rather than defaulting to another solver,
               -- just report an error
               bsError eh [(cmdPosition,
                            WSATNotAvailable flag_str lib_str Nothing)]
  in  case (satBackend f) of
        SAT_Yices -> checkFn "-sat-yices" "libyices.so.2" hasYices
        SAT_STP -> checkFn "-sat-stp" "libstp.so" hasSTP

-- -------------------------

checkBiImplication :: SATState -> AExpr -> AExpr -> IO ((Bool, Bool), SATState)
checkBiImplication (SATS_Yices yices_state) e1 e2 = do
    (res, yices_state') <- Yices.checkBiImplication yices_state e1 e2
    return (res, SATS_Yices yices_state')
checkBiImplication (SATS_STP stp_state) e1 e2 = do
    (res, stp_state') <- STP.checkBiImplication stp_state e1 e2
    return (res, SATS_STP stp_state')


isConstExpr :: SATState -> AExpr -> IO (Maybe Bool, SATState)
isConstExpr (SATS_Yices yices_state) e = do
    (res, yices_state') <- Yices.isConstExpr yices_state e
    return (res, SATS_Yices yices_state')
isConstExpr (SATS_STP stp_state) e = do
    (res, stp_state') <- STP.isConstExpr stp_state e
    return (res, SATS_STP stp_state')


checkEq :: SATState -> AExpr -> AExpr -> IO (Maybe Bool, SATState)
checkEq (SATS_Yices yices_state) e1 e2 = do
    (res, yices_state') <- Yices.checkEq yices_state e1 e2
    return (res, SATS_Yices yices_state')
checkEq (SATS_STP stp_state) e1 e2 = do
    (res, stp_state') <- STP.checkEq stp_state e1 e2
    return (res, SATS_STP stp_state')


checkNotEq :: SATState -> AExpr -> AExpr -> IO (Maybe Bool, SATState)
checkNotEq (SATS_Yices yices_state) e1 e2 = do
    (res, yices_state') <- Yices.checkNotEq yices_state e1 e2
    return (res, SATS_Yices yices_state')
checkNotEq (SATS_STP stp_state) e1 e2 = do
    (res, stp_state') <- STP.checkNotEq stp_state e1 e2
    return (res, SATS_STP stp_state')

-- -------------------------
