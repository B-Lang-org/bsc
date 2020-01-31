module IPrims(doPrimOp) where

import Error(internalError, ErrMsg)
import PPrint(ppReadable)
import Position
import IntLit
import ISyntax
import ISyntaxUtil(iMkLitSizeAt, iMkBoolAt, iMkLitAt, iMkRealLitAt,
                   iMkPairAt, iMkTripleAt, iMkStringAt, iMkList,
                   itInteger, itBit1, itReal, itList)
import Prim

-- ---------------

-- This returns a Maybe for two reasons:
-- (1) The check for whether the arguments are known constants is inside
--     doPrimOp.  And so we have to return Maybe in the case that the
--     arguments are not known.
-- (2) ITransform's "iTrAp" calls this without any guard as to whether
--     the operator is one that should be handled
--     XXX perhaps it needs no guard, but that investigation needs to be done
--
-- If these two issues can be resolved, then we can remove the Maybe
-- and internal error on any conditions which are not expected.

doPrimOp :: Position -> PrimOp -> [IType] -> [IExpr a] ->
            Maybe (Either ErrMsg (IExpr a))
doPrimOp pos op ts es =
  let isLit e = isIConInt e || isIConReal e
      mkPrimArg (ICon _ (ICInt { iVal = IntLit { ilValue = v } })) = I v
      mkPrimArg (ICon _ (ICReal { iReal = v })) = D v
      mkPrimArg e = internalError ("mkPrimArg: " ++ ppReadable e)
  in  if (all isLit es)
      then let tints = [ i | ITNum i <- ts]
               eints = map mkPrimArg es
           in  doPrimOp' pos op tints eints
      else Nothing

-- ---------------

use :: (a -> b) -> (Maybe (Either ErrMsg a)) -> (Maybe (Either ErrMsg b))
use fn (Just (Right x)) = Just (Right (fn x))
use _  (Just (Left x))  = Just (Left x)
use _  Nothing          = Nothing

-- This does primResult to compute the value and then applies the right literal
-- creation function to produce the IExpr for each primitive result.
doPrimOp' :: Position -> PrimOp -> [Integer] -> [PrimArg] ->
             Maybe (Either ErrMsg (IExpr a))
doPrimOp' pos op@PrimAdd  ss@[s]     vs = use (iMkLitSizeAt pos s) (primResult op ss vs)
doPrimOp' pos op@PrimSub  ss@[s]     vs = use (iMkLitSizeAt pos s) (primResult op ss vs)
doPrimOp' pos op@PrimMul  ss@[_,_,s] vs = use (iMkLitSizeAt pos s) (primResult op ss vs)
doPrimOp' pos op@PrimQuot ss@[s,_]   vs = use (iMkLitSizeAt pos s) (primResult op ss vs)
doPrimOp' pos op@PrimRem  ss@[_,s]   vs = use (iMkLitSizeAt pos s) (primResult op ss vs)
doPrimOp' pos op@PrimAnd  ss@[s]     vs = use (iMkLitSizeAt pos s) (primResult op ss vs)
doPrimOp' pos op@PrimOr   ss@[s]     vs = use (iMkLitSizeAt pos s) (primResult op ss vs)
doPrimOp' pos op@PrimXor  ss@[s]     vs = use (iMkLitSizeAt pos s) (primResult op ss vs)
doPrimOp' pos op@PrimSL   ss@[s,_]   vs = use (iMkLitSizeAt pos s) (primResult op ss vs)
doPrimOp' pos op@PrimSRL  ss@[s,_]   vs = use (iMkLitSizeAt pos s) (primResult op ss vs)
doPrimOp' pos op@PrimSRA  ss@[s,_]   vs = use (iMkLitSizeAt pos s) (primResult op ss vs)
doPrimOp' pos op@PrimNeg  ss@[s]     vs = use (iMkLitSizeAt pos s) (primResult op ss vs)
doPrimOp' pos op@PrimInv  ss@[s]     vs = use (iMkLitSizeAt pos s) (primResult op ss vs)

doPrimOp' pos op@PrimEQ  ss vs = use (iMkBoolAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimEQ3 ss vs = use (iMkBoolAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimULE ss vs = use (iMkBoolAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimULT ss vs = use (iMkBoolAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimSLE ss vs = use (iMkBoolAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimSLT ss vs = use (iMkBoolAt pos) (primResult op ss vs)

--doPrimOp' pos op@PrimZeroExt ss@[_,_,s] vs = use (iMkLitSizeAt pos s) (primResult op ss vs)
doPrimOp' pos op@PrimSignExt ss@[_,_,s] vs = use (iMkLitSizeAt pos s) (primResult op ss vs)
--doPrimOp' pos op@PrimTrunc ss@[_,s,_] vs = use (iMkLitSizeAt pos s) (primResult op ss vs)

doPrimOp' pos op@PrimRange ss@[s] vs = use (iMkLitSizeAt pos s) (primResult op ss vs)
doPrimOp' pos op@PrimExtract ss@[_,_,s] vs = use (iMkLitSizeAt pos s) (primResult op ss vs)
doPrimOp' pos op@PrimConcat ss@[_,_,s] vs = use (iMkLitSizeAt pos s) (primResult op ss vs)
--doPrimOp' pos PrimSplit _ _ = 

doPrimOp' pos op@PrimBNot ss vs = use (iMkBoolAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimBAnd ss vs = use (iMkBoolAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimBOr  ss vs = use (iMkBoolAt pos) (primResult op ss vs)

doPrimOp' pos op@PrimIf ss@[s] vs = use (iMkLitSizeAt pos s) (primResult op ss vs)

doPrimOp' pos op@PrimSelect ss@[s,_,_] vs = use (iMkLitSizeAt pos s) (primResult op ss vs)

doPrimOp' pos op@PrimIntegerToBit ss@[s] vs = use (iMkLitSizeAt pos s) (primResult op ss vs)
doPrimOp' pos op@PrimBitToInteger ss vs = use (iMkLitAt pos itInteger) (primResult op ss vs)

doPrimOp' pos op@PrimIntegerAdd ss vs = use (iMkLitAt pos itInteger) (primResult op ss vs)
doPrimOp' pos op@PrimIntegerSub ss vs = use (iMkLitAt pos itInteger) (primResult op ss vs)
doPrimOp' pos op@PrimIntegerNeg ss vs = use (iMkLitAt pos itInteger) (primResult op ss vs)
doPrimOp' pos op@PrimIntegerMul ss vs = use (iMkLitAt pos itInteger) (primResult op ss vs)
doPrimOp' pos op@PrimIntegerDiv ss vs = use (iMkLitAt pos itInteger) (primResult op ss vs)
doPrimOp' pos op@PrimIntegerMod ss vs = use (iMkLitAt pos itInteger) (primResult op ss vs)
doPrimOp' pos op@PrimIntegerQuot ss vs = use (iMkLitAt pos itInteger) (primResult op ss vs)
doPrimOp' pos op@PrimIntegerRem ss vs = use (iMkLitAt pos itInteger) (primResult op ss vs)
doPrimOp' pos op@PrimIntegerExp ss vs = use (iMkLitAt pos itInteger) (primResult op ss vs)
doPrimOp' pos op@PrimIntegerLog2 ss vs = use (iMkLitAt pos itInteger) (primResult op ss vs)

doPrimOp' pos op@PrimIntegerEQ ss vs = use (iMkBoolAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimIntegerLE ss vs = use (iMkBoolAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimIntegerLT ss vs = use (iMkBoolAt pos) (primResult op ss vs)


doPrimOp' pos op@PrimIntegerToReal ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimBitsToReal    ss vs = use (iMkRealLitAt pos) (primResult op ss vs)

doPrimOp' pos op@PrimRealEQ ss vs = use (iMkBoolAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealLE ss vs = use (iMkBoolAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealLT ss vs = use (iMkBoolAt pos) (primResult op ss vs)

doPrimOp' pos op@PrimRealToString ss vs = use (iMkStringAt pos) (primResult op ss vs)

doPrimOp' pos op@PrimRealAdd     ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealSub     ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealNeg     ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealMul     ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealDiv     ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealAbs     ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealSignum  ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealExpE    ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealPow     ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealLogE    ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealLogBase ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealLog2    ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealLog10   ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealSqrt    ss vs = use (iMkRealLitAt pos) (primResult op ss vs)

doPrimOp' pos op@PrimRealToBits ss vs = use (iMkLitSizeAt pos 64) (primResult op ss vs)

doPrimOp' pos op@PrimRealSin   ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealCos   ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealTan   ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealSinH  ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealCosH  ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealTanH  ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealASin  ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealACos  ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealATan  ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealASinH ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealACosH ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealATanH ss vs = use (iMkRealLitAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealATan2 ss vs = use (iMkRealLitAt pos) (primResult op ss vs)

doPrimOp' pos op@PrimRealTrunc ss vs = use (iMkLitAt pos itInteger) (primResult op ss vs)
doPrimOp' pos op@PrimRealCeil  ss vs = use (iMkLitAt pos itInteger) (primResult op ss vs)
doPrimOp' pos op@PrimRealFloor ss vs = use (iMkLitAt pos itInteger) (primResult op ss vs)
doPrimOp' pos op@PrimRealRound ss vs = use (iMkLitAt pos itInteger) (primResult op ss vs)

doPrimOp' pos op@PrimSplitReal ss vs = use mk_pair (primResult op ss vs)
    where mk_pair (whole,fraction) = 
              let w = iMkLitAt pos itInteger whole
                  f = iMkRealLitAt pos fraction
              in  iMkPairAt pos itInteger itReal w f

doPrimOp' pos op@PrimDecodeReal ss vs = use mk_triple (primResult op ss vs)
    where mk_triple (is_pos, mantissa, exponent) =
              let s = iMkBoolAt pos is_pos
                  m = iMkLitAt pos itInteger mantissa
                  e = iMkLitAt pos itInteger exponent
              in  iMkTripleAt pos itBit1 itInteger itInteger s m e

doPrimOp' pos op@PrimRealToDigits ss vs = use mk_pair (primResult op ss vs)
    where mk_pair (digits, exponent) =
              let ds = iMkList itInteger (map (iMkLitAt pos itInteger) digits)
                  e = iMkLitAt pos itInteger exponent
              in  iMkPairAt pos (itList itInteger) itInteger ds e

doPrimOp' pos op@PrimRealIsInfinite ss vs = use (iMkBoolAt pos) (primResult op ss vs)
doPrimOp' pos op@PrimRealIsNegativeZero ss vs = use (iMkBoolAt pos) (primResult op ss vs)

-- The rest are presumably here to allow replacing of the default "Nothing"
-- with a trace or error, for debugging, without triggering these prims:

doPrimOp' pos PrimChr _ _ = Nothing
--doPrimOp' pos PrimOrd _ _ = 

doPrimOp' pos PrimNoRules ts es = internalError ("primNoRules " ++ ppReadable (ts, es))
doPrimOp' pos PrimNoActions ts es = internalError ("primNoActions " ++ ppReadable (ts ,es))

--doPrimOp' pos PrimError _ _ = 

-- other prims may be called by ITransform, but we don't know how to "do" them
doPrimOp' _ op _ _ = Nothing
-- doPrimOp' p ts es = internalError ("doPrimOp' " ++ ppReadable (p, ts, es))

