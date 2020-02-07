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

import qualified AExpr2Yices as Yices
         (YState, initYState, checkBiImplication, isConstExpr,
          checkEq, checkNotEq)

import Yices(checkVersion)

#if !defined(__GLASGOW_HASKELL__) || (__GLASGOW_HASKELL__ >= 609)
type ExceptionType = CE.SomeException
#else
type ExceptionType = CE.Exception
#endif

-- -------------------------

-- A single data type for either of the solver state
data SATState = SATS_Yices Yices.YState

-- -------------------------

initSATState :: String -> ErrorHandle -> Flags -> Bool -> [ADef] -> [AVInst] ->
                IO SATState
initSATState str errh flags doHardFail ds avis =
    case (satBackend flags) of
      SAT_Yices -> do
          yices_state <- Yices.initYState str flags doHardFail ds avis []
          return (SATS_Yices yices_state)

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
               return f
       in  CE.catch (Yices.checkVersion >> return f) handler
  else return f

-- -------------------------

checkBiImplication :: SATState -> AExpr -> AExpr -> IO ((Bool, Bool), SATState)
checkBiImplication (SATS_Yices yices_state) e1 e2 = do
    (res, yices_state') <- Yices.checkBiImplication yices_state e1 e2
    return (res, SATS_Yices yices_state')


isConstExpr :: SATState -> AExpr -> IO (Maybe Bool, SATState)
isConstExpr (SATS_Yices yices_state) e = do
    (res, yices_state') <- Yices.isConstExpr yices_state e
    return (res, SATS_Yices yices_state')


checkEq :: SATState -> AExpr -> AExpr -> IO (Maybe Bool, SATState)
checkEq (SATS_Yices yices_state) e1 e2 = do
    (res, yices_state') <- Yices.checkEq yices_state e1 e2
    return (res, SATS_Yices yices_state')


checkNotEq :: SATState -> AExpr -> AExpr -> IO (Maybe Bool, SATState)
checkNotEq (SATS_Yices yices_state) e1 e2 = do
    (res, yices_state') <- Yices.checkNotEq yices_state e1 e2
    return (res, SATS_Yices yices_state')

-- -------------------------

