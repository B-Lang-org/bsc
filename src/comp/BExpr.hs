{-# LANGUAGE CPP #-}
module BExpr(BExpr, bNothing, bAdd, bImplies, bImpliesB) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Util(isOrdSubset, mergeOrdNoDup)
import PPrint
import ISyntax
import ISyntaxUtil
--import BDD
import Prim

--import Debug.Trace


-- A BExpr records information when is know to be true.
-- bNothing is no information
-- bAdd adds an additional fact
-- bImplies checks if the know facts implies an expression.
--  bImplies is allowed to answer False even if the implication
--  is true, but not the other way around.

bNothing :: BExpr a
bAdd :: IExpr a -> BExpr a -> BExpr a
bImplies :: BExpr a -> IExpr a -> Bool
bImpliesB :: BExpr a -> BExpr a -> Bool

{-
-- This implementation is exact, but slow.
newtype BExpr = B (BDD IExpr)

instance PPrint BExpr where
    pPrint d p _ = text "BExpr"

toBExpr :: IExpr -> BDD IExpr
toBExpr (IAps (ICon _ (ICPrim _ PrimBAnd)) _ [e1, e2]) = bddAnd (toBExpr e1) (toBExpr e2)
toBExpr (IAps (ICon _ (ICPrim _ PrimBOr))  _ [e1, e2]) = bddOr  (toBExpr e1) (toBExpr e2)
toBExpr (IAps (ICon _ (ICPrim _ PrimBNot)) _ [e]) = bddNot (toBExpr e)
toBExpr e = if e == iTrue then bddTrue else if e == iFalse then bddFalse else bddVar e

bNothing = B bddTrue

bAdd e (B bdd) = B (bddAnd (toBExpr e) bdd)

bImplies (B bdd) e = bddIsTrue (bddImplies bdd (toBExpr e))
-}

---------

{-
-- Trivial implementation.

newtype BExpr a = B ()

instance PPrint (BExpr a) where
    pPrint d p _ = text "BExpr"

bNothing = B ()

bAdd _ _ = B ()

bImplies _ e = isTrue e

bImpliesB _ _ = False

---------
-}

newtype BExpr a = A [IExpr a]

instance PPrint (BExpr a) where
    pPrint d p (A es) = text "(B" <+> pPrint d 0 es <> text ")"

bNothing = A [iTrue]

bAdd e (A es) = A $ mergeOrdNoDup (get e) es

bImplies (A es) e =
--        if length es > 1 then trace (ppReadable (e, es, isOrdSubset (get e) es)) $ isOrdSubset (get e) es
        isOrdSubset (get e) es

bImpliesB b (A es) = all (bImplies b) es

get :: IExpr a -> [IExpr a]
get = getAnds . norm

getAnds :: IExpr a -> [IExpr a]
getAnds (IAps (ICon _ (ICPrim _ PrimBAnd)) _ [e1, e2]) = mergeOrdNoDup (getAnds e1) (getAnds e2)
getAnds e = [e]

norm :: IExpr a -> IExpr a
norm (IAps (ICon _ (ICPrim _ PrimBNot)) _ [e]) = invert e
norm e = e

invert :: IExpr a -> IExpr a
invert (IAps (ICon _ (ICPrim _ PrimBAnd)) _ [e1, e2]) = ieOr  (invert e1) (invert e2)
invert (IAps (ICon _ (ICPrim _ PrimBOr )) _ [e1, e2]) = ieAnd (invert e1) (invert e2)
invert (IAps (ICon _ (ICPrim _ PrimBNot)) _ [e]     ) = e
invert e = ieNot e
