{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, TypeSynonymInstances #-}
module AProofs (aCheckProofs) where

import Control.Monad.State

import Error(ErrorHandle)
import Flags
import ASyntax
import ProofObligation
import SAT(SATState, initSATState, checkEq, checkNotEq)
import PPrint


-- -------------------------

aCheckProofs :: ErrorHandle -> Flags -> APackage -> IO (APackage, Bool)
aCheckProofs errh flags amod = do
    let obs = apkg_proof_obligations amod
        ds = apkg_local_defs amod
        ss = apkg_state_instances amod
    let str = "aproofs_" ++ ppString (apkg_name amod)
    sat_state <- initSATState str errh flags True ds ss
    (ok, _) <- runStateT (checkProofs errh obs) sat_state
    let amod' = amod { apkg_proof_obligations = [] }
    return (amod', ok)


-- -------------------------

-- A common monad to check the proofs in
type SIO = StateT SATState IO

instance HasProve (ProofObligation AExpr) (StateT SATState IO) where
  prove (ProveEq    x y) = proveEq x y
  prove (ProveNotEq x y) = proveNotEq x y


proveEq :: AExpr -> AExpr -> SIO ProofResult
proveEq x y = do
  s <- get
  (eq_res, s') <- liftIO $ checkEq s x y
  put s'
  case eq_res of
    (Just True) -> return Proven
    _ -> do (neq_res, s'') <- liftIO $ checkNotEq s' x y
            put s''
            return $ case neq_res of
                       (Just True) -> Disproven
                       _           -> Inconclusive

proveNotEq :: AExpr -> AExpr -> SIO ProofResult
proveNotEq x y = do
  s <- get
  (neq_res, s') <- liftIO $ checkNotEq s x y
  put s'
  case neq_res of
    (Just True) -> return Proven
    _ -> do (eq_res, s'') <- liftIO $ checkEq s' x y
            put s''
            return $ case eq_res of
                       (Just True) -> Disproven
                       _           -> Inconclusive

-- -------------------------

