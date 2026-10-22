{-# LANGUAGE CPP #-}
module BExpr(BExpr, bNothing, bAdd, bImplies, bImpliesB,
             BFacts, bFacts, bAddFacts, bImpliesFacts) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import qualified Data.Set as S
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

-- The known facts, as a set of conjuncts.  Adding a fact under a
-- branch shares the rest of the set rather than copying it.
newtype BExpr a = A (S.Set (IExpr a))

instance PPrint (BExpr a) where
    pPrint d p (A es) = text "(B" <+> pPrint d 0 (S.toAscList es) <> text ")"

bNothing = A (S.singleton iTrue)

bAdd e = bAddFacts (bFacts e)

bImplies b e = bImpliesFacts b (bFacts e)

-- The facts that bAdd adds for an expression, which are also the facts
-- that bImplies checks for it: the set of conjuncts of the normalized
-- expression.  A caller that tests the same expression repeatedly can
-- compute them once.
newtype BFacts a = BFacts (S.Set (IExpr a))

bFacts :: IExpr a -> BFacts a
bFacts = BFacts . getAnds . norm

bAddFacts :: BFacts a -> BExpr a -> BExpr a
bAddFacts (BFacts cs) (A es) = A $ S.union cs es

bImpliesFacts :: BExpr a -> BFacts a -> Bool
bImpliesFacts (A es) (BFacts cs) = cs `S.isSubsetOf` es

bImpliesB b (A es) = all (bImplies b) (S.toAscList es)

getAnds :: IExpr a -> S.Set (IExpr a)
getAnds e = go e S.empty
  where go (IAps (ICon _ (ICPrim _ PrimBAnd)) _ [e1, e2]) acc = go e1 (go e2 acc)
        go e acc = S.insert e acc

norm :: IExpr a -> IExpr a
norm (IAps (ICon _ (ICPrim _ PrimBNot)) _ [e]) = invert e
norm e = e

invert :: IExpr a -> IExpr a
invert (IAps (ICon _ (ICPrim _ PrimBAnd)) _ [e1, e2]) = ieOr  (invert e1) (invert e2)
invert (IAps (ICon _ (ICPrim _ PrimBOr )) _ [e1, e2]) = ieAnd (invert e1) (invert e2)
invert (IAps (ICon _ (ICPrim _ PrimBNot)) _ [e]     ) = e
invert e = ieNot e
