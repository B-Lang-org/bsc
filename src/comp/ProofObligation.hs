{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts #-}
module ProofObligation (
                        ProofObligation(..),
                        HasProve(..), ProofResult(..), MsgFn(..), MsgTuple,
                        warnUnlessProof, errorUnlessProof,
                        checkProofs
                       ) where

import Error(EMsg, ErrorHandle, bsWarningsAndErrors)
import PPrint
import Eval

import Control.Monad(when)
import Control.Monad.Trans(MonadIO, liftIO)
import Data.List(sortBy, groupBy)

-- import Debug.Trace

-- A proof attempt to can yield one of 3 results
data ProofResult = Proven | Disproven | Inconclusive
  deriving (Eq, Show)

-- This class encapsulates the property of supporting proofs
class HasProve a m where
  prove :: a -> m ProofResult

-- This is a generic framework for recording different types
-- of provable statements.  The instance declarations for
-- various types of ProofObligations are defined elsewhere,
-- to avoid recursive module dependencies.
data ProofObligation a = ProveEq a a
                       | ProveNotEq a a

instance Eq a => Eq (ProofObligation a) where
  (ProveEq x1 y1)    == (ProveEq x2 y2)    = (x1 == x2) && (y1 == y2)
  (ProveNotEq x1 y1) == (ProveNotEq x2 y2) = (x1 == x2) && (y1 == y2)
  _                  == _                  = False

instance Show a => Show (ProofObligation a) where
  show (ProveEq    x y) = (show x) ++ " == " ++ (show y)
  show (ProveNotEq x y) = (show x) ++ " != " ++ (show y)

instance PPrint a => PPrint (ProofObligation a) where
  pPrint d p (ProveEq    x y) = (pPrint d 0 x)<+>(text "==")<+>(pPrint d 0 y)
  pPrint d p (ProveNotEq x y) = (pPrint d 0 x)<+>(text "!=")<+>(pPrint d 0 y)

instance NFData a => NFData (ProofObligation a) where
  rnf (ProveEq e1 e2) = rnf2 e1 e2
  rnf (ProveNotEq e1 e2) = rnf2 e1 e2

-- This allows us to group related tests to produce better
-- error messages
data MsgFn =
  MsgFn { mf_ident :: String
        , mf_fn    :: ProofResult -> MsgTuple -> MsgTuple
        }

-- (warnings, demotable errors, errors)
type MsgTuple = ([EMsg], [EMsg], [EMsg])

instance Eq MsgFn where
  mf1 == mf2 = (mf_ident mf1) == (mf_ident mf2)

instance Ord MsgFn where
  compare mf1 mf2 = compare (mf_ident mf1) (mf_ident mf2)

instance Show MsgFn where
  show (MsgFn s _) = s

instance PPrint MsgFn where
  pPrint _ _ x = text (show x)

instance NFData MsgFn where
  rnf (MsgFn s _) = rnf s

errorUnlessProof :: [EMsg] -> ProofResult -> MsgTuple -> MsgTuple
errorUnlessProof _  Proven (ws, ds, es) = (ws, ds, es)
errorUnlessProof em _      (ws, ds, es) = (ws, ds, es ++ em)

warnUnlessProof :: [EMsg] -> ProofResult -> MsgTuple -> MsgTuple
warnUnlessProof _  Proven (ws, ds, es) = (ws, ds, es)
warnUnlessProof wm _      (ws, ds, es) = (ws ++ wm, ds, es)

-- Check a set of mixed proof obligations by first grouping them
-- by message function type and then checking each group
checkProofs :: (MonadIO m, HasProve (ProofObligation a) m) =>
               ErrorHandle -> [(ProofObligation a, MsgFn)] -> m Bool
checkProofs _ [] = return True
checkProofs errh ps =
  do let cmpSnd (_,x1) (_,x2) = x1 `compare` x2
         eqSnd  (_,x1) (_,x2) = x1 == x2
         groups = groupBy eqSnd (sortBy cmpSnd ps)
     bs <- mapM (checkProofSet errh) groups
     return (and bs)

-- Check one group of proof obligations
checkProofSet :: (MonadIO m, HasProve (ProofObligation a) m) =>
                 ErrorHandle -> [(ProofObligation a, MsgFn)] -> m Bool
checkProofSet _ [] = return True
checkProofSet errh ps =
  do results <- mapM (prove . fst) ps
     let fns          = [ fn | (_,(MsgFn _ fn)) <- ps ]
         (warns, demerrs, errs) = buildErrs (zip fns results) ([], [], [])
     when (any (not . null) [warns, demerrs, errs]) $
         liftIO (bsWarningsAndErrors errh warns demerrs errs)
     return ((null demerrs) && (null errs))
  where buildErrs []            we = we
        buildErrs ((fn,res):xs) we = buildErrs xs (fn res we)
