module APrims(evalAExprToInteger) where 

import PPrint(ppReadable)
import ASyntax
import ASyntaxUtil
import Prim
import IntLit(IntLit(..))
import Util(separate)
import Error(ErrMsg)
import ErrorUtil(internalError)

-- import Debug.Trace


-- This is an evaluation function for AExprs on Integers.
-- It takes a value function which tries to determine an Integer
-- value for an identifier, and expression function which tries to find
-- an expression to compute the value for an identifier, and a method
-- function which gives a list of identifiers to look in for the value
-- of the method.  The function is quite limited and will return a
-- Left String containing a failure message in many cases.
evalAExprToInteger :: (AId -> Maybe Integer) -> (AId -> Maybe AExpr) -> 
                      ((AId,AId) -> [AId]) ->
                      AExpr -> Either String Integer
evalAExprToInteger _ _ _ (ASInt _ _ lit) = Right (ilValue lit)
evalAExprToInteger valfn exprfn methfn (ASDef _ i) =
    case (valfn i) of
      (Just n) -> Right n
      Nothing  -> -- def value is not available, so attempt
                  -- to reconstruct it from its AExpr
                  case (exprfn i) of
                    (Just e) -> evalAExprToInteger valfn exprfn methfn e
                    Nothing  -> Left $ "unable to determine value of: " ++ (ppReadable i)
evalAExprToInteger valfn exprfn methfn e@(APrim _ _ op args) =
    let (errs,vs) = separate $ map (evalAExprToInteger valfn exprfn methfn) args
    in if (null errs)
       then evalPrim op (getOpSizes op e) vs
       else Left $ unlines errs
evalAExprToInteger valfn exprfn methfn e@(AMethCall t oid mid []) =
    let alts = [ ASDef t i | i <- methfn (oid,mid) ]
    in case (separate $ map (evalAExprToInteger valfn exprfn methfn) alts) of
         ([],(ok:_)) -> Right ok
         ([],[])     -> Left $ "Unable to resolve value of " ++ (ppReadable e)
         (errs,_)    -> Left $ unlines errs
evalAExprToInteger _ _ _ e = Left $ "evalAExprToInteger: cannot handle expression " ++
                                    (ppReadable e)

-- utilities for working with the return of primInts
use :: (a -> b) -> (Maybe (Either ErrMsg a)) -> PrimOp -> (Either String b)
use fn (Just (Right x)) _  = Right (fn x)
use _  (Just (Left s))  _  = Left (show s)
use _  Nothing          op = Left $ "evalPrim: no primitive function available for " ++ (show op)

asBool :: Bool -> Integer
asBool b = if b then 1 else 0

asInteger :: Integer -> Integer
asInteger = id

-- Select the return type based on the PrimOp
evalPrim :: PrimOp -> [Integer] -> [Integer] -> Either String Integer
evalPrim op ss vs | op `elem` boolOps 
                  = use asBool (primResult op ss (map I vs)) op
evalPrim op ss vs = use asInteger (primResult op ss (map I vs)) op

-- See Prim.hs::evalIntPrimToBool
boolOps :: [PrimOp]
boolOps = [ PrimEQ, PrimULE, PrimULT, PrimSLE, PrimSLT
          , PrimBNot, PrimBAnd, PrimBOr
          , PrimIntegerEQ, PrimIntegerLE, PrimIntegerLT
          ]

-- An unused size, which will generate an error if it is ever actually used
unused :: Integer
unused = internalError "size parameter used unexpectedly"

-- Get the list of size parameters needed to evaluate a primitive.
-- These must match the patterns in Prim.hs
getOpSizes :: PrimOp -> AExpr -> [Integer]
getOpSizes PrimMul     e = [unused, unused, aSize e]
getOpSizes PrimQuot    e = [aSize e, unused]
getOpSizes PrimRem     e = [unused, aSize e]
getOpSizes PrimSL      e = [aSize e, unused]
getOpSizes PrimSRL     e = [aSize e, unused]
getOpSizes PrimSRA     e = [aSize e, unused]
getOpSizes PrimZeroExt _ = [unused, unused, unused]
getOpSizes PrimSignExt e = [unused, aSize ((ae_args e)!!0), aSize e]
getOpSizes PrimTrunc   e = [unused, aSize e, unused]
getOpSizes PrimExtract e = [aSize ((ae_args e)!!0), unused, aSize e]
getOpSizes PrimConcat  e = [aSize ((ae_args e)!!0), aSize ((ae_args e)!!1), aSize e]
getOpSizes PrimSelect  e = internalError $ "APrims: PrimSelect should not occur"
getOpSizes _           e = [aSize e]  -- by default just give the result size

