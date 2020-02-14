{-# LANGUAGE CPP #-}
module BoolExp(BoolExp(..), sSimplify, aSimplify, nSimplify, {- getBEVars, substBE -}) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

--import Data.List(union)
import Util(toMaybe)
import PPrint
import BDD
import qualified Data.Set as S

--import Util(traces)


data BoolExp a
	= And (BoolExp a) (BoolExp a)
	| Or  (BoolExp a) (BoolExp a)
	| Not (BoolExp a)
	| If  (BoolExp a) (BoolExp a) (BoolExp a)
	| Var a
	| TT
	| FF
	deriving (Eq, Ord)

--iF :: BoolExp a -> BoolExp a -> BoolExp a -> BoolExp a
--iF c t e = (c `And` t) `Or` (Not c `And` e)

{-
getBEVars :: (Eq a) => BoolExp a -> [a]
getBEVars (And e1 e2) = getBEVars e1 `union` getBEVars e2
getBEVars (Or  e1 e2) = getBEVars e1 `union` getBEVars e2
getBEVars (Not e)     = getBEVars e
getBEVars (If e1 e2 e3) = getBEVars e1 `union` getBEVars e2 `union` getBEVars e3
getBEVars (Var v) = [v]
getBEVars _ = []

substBE :: (Eq a) => a -> BoolExp a -> BoolExp a -> BoolExp a
substBE v n (And e1 e2) = And (substBE v n e1) (substBE v n e2)
substBE v n (Or  e1 e2) = Or  (substBE v n e1) (substBE v n e2)
substBE v n (Not e)     = Not (substBE v n e)
substBE v n (If e1 e2 e3) = If (substBE v n e1) (substBE v n e2) (substBE v n e3)
substBE v n e@(Var v') = if v == v' then n else e
substBE v n e = e
-}

instance (Show a) => Show (BoolExp a) where
	show e = pp e

pp :: (Show a) => BoolExp a -> String
pp e = pp' (0::Integer) e
  where pp' p (e1 `And` e2) = paren (p>3) (pp' 3 e1 ++ " & " ++ pp' 3 e2)
	pp' p (e1 `Or` e2) = paren (p>2) (pp' 2 e1 ++ " | " ++ pp' 2 e2)
	pp' p (If e1 e2 e3) = paren (p>1) (pp' 1 e1 ++ " ? " ++ pp' 1 e2 ++ " : " ++ pp' 1 e3)
	pp' _ (Not e) = "~" ++ pp' 10 e
	pp' _ (Var v) = show v
	pp' _ TT = "T"
	pp' _ FF = "F"

	paren True s = "("++s++")"
	paren False s = s

instance (PPrint a) => PPrint (BoolExp a) where
    pPrint d p (e1 `And` e2) = pparen (p>3) (pPrint d 3 e1 <+> text "&" <+> pPrint d 3 e2)
    pPrint d p (e1 `Or` e2) = pparen (p>2) (pPrint d 2 e1 <+> text "|" <+> pPrint d 2 e2)
    pPrint d p (If e1 e2 e3) = pparen (p>1) (pPrint d 1 e1 <+> text "?" <+> pPrint d 1 e2 <+> text ":" <+> pPrint d 1 e3)
    pPrint d _ (Not e) = text "~" <> pPrint d 10 e
    pPrint d p (Var v) = pPrint d p v
    pPrint d _ TT = text "T"
    pPrint d _ FF = text "F"

bNot :: BoolExp a -> BoolExp a
bNot (Not e) = e
bNot e = Not e

reduce :: (Ord a) => BoolExp a -> Maybe (BoolExp a)
reduce (And TT e) = Just e
reduce (And FF e) = Just FF
reduce (And e TT) = Just e
reduce (And e FF) = Just FF
reduce (And (If c1 t1 e1) (If c2 t2 e2)) | c1==c2 = Just (If c1 (rAnd t1 t2) (rAnd e1 e2))
reduce (And e1 e2) | e1 == e2 = Just e1
reduce (And e1 e2) | e1 == bNot e2 = Just FF
reduce e@(And _ _) = me'
  where me' = fmap (rrAnds . reverse) (redAnd False S.empty [] es)
	es = collAnd e

reduce (Or TT e) = Just TT
reduce (Or FF e) = Just e
reduce (Or e TT) = Just TT
reduce (Or e FF) = Just e
reduce (Or (If c1 t1 e1) (If c2 t2 e2)) | c1==c2 = Just (If c1 (rOr t1 t2) (rOr e1 e2))
reduce (Or (And x1 y1) (And x2 y2)) | x1 == x2 = Just (And x1 (rOr y1 y2))
reduce (Or (And x1 y1) (And x2 y2)) | y1 == y2 = Just (And (rOr x1 x2) y2)
{-
reduce (Or e1 (Or e1' e2)) | e1 == e1' = Just (Or e1 e2)
-}
reduce (Or e1 e2) | e1 == e2 = Just e1
reduce (Or e1 e2) | e1 == bNot e2 = Just TT
reduce e@(Or _ _) = me'
  where me' = fmap (rrOrs . reverse) (redOr False S.empty [] es)
	es = collOr e

reduce (Not (And e1 e2)) = Just (Or  (rNot e1) (rNot e2))
reduce (Not (Or  e1 e2)) = Just (And (rNot e1) (rNot e2))
reduce (Not (Not e)) = Just e
reduce (Not (If c t e)) = Just (If c (rNot t) (rNot e))
reduce (Not TT) = Just FF
reduce (Not FF) = Just TT
reduce (If TT t e) = Just t
reduce (If FF t e) = Just e
reduce (If c TT e) = Just (Or c e)
reduce (If c FF e) = Just (And (Not c) e)
reduce (If c t TT) = Just (Or (Not c) t)
reduce (If c t FF) = Just (And c t)
reduce (If c  t e) | t == e = Just t
reduce _ = Nothing

-- redAnd and redOr keep a list of expressions
-- as well as the set so they can return
-- the originally anded or ored expressions in the right
-- order if no optimization is done

redAnd change s rs [] = toMaybe change rs
redAnd change s rs (e:es) = if e `S.member` s then redAnd True s rs es
                     else if Not e `S.member` s then Just [FF]
		          else redAnd change (S.insert e s) (e:rs) es

redOr change s rs [] = toMaybe change rs
redOr change s rs (e:es) = if e `S.member` s then redOr True s rs es
                    else if Not e `S.member` s then Just [TT]
		         else redOr change (S.insert e s) (e:rs) es

foldrx f z [] = z
foldrx f z [x] = x
foldrx f z xs = foldr1 f xs

collAnd (And e1 e2) = collAnd e1 ++ collAnd e2
collAnd e = [e]

collOr (Or e1 e2) = collOr e1 ++ collOr e2
collOr e = [e]

rAnd :: (Ord a) => BoolExp a -> BoolExp a -> BoolExp a
rAnd x1 x2 = red (And x1 x2)
rOr  :: (Ord a) => BoolExp a -> BoolExp a -> BoolExp a
rOr  x1 x2 = red (Or  x1 x2)
rNot :: (Ord a) => BoolExp a -> BoolExp a
rNot x1    = red (Not x1)

rrOr :: BoolExp a -> BoolExp a -> BoolExp a
rrOr e TT = TT
rrOr e1 e2 = Or e1 e2

rrOrs :: [BoolExp a] -> BoolExp a
rrOrs = foldrx rrOr FF

rrAnd :: BoolExp a -> BoolExp a -> BoolExp a
rrAnd e FF = FF
rrAnd e1 e2 = And e1 e2

rrAnds :: [BoolExp a] -> BoolExp a
rrAnds = foldrx rrAnd TT

rrNot :: BoolExp a -> BoolExp a
rrNot (Not e) = e
rrNot e = Not e

-- simple simplify
sSimplify :: (Ord a) => BoolExp a -> BoolExp a
sSimplify (And e1 e2) =
	let e' = And (sSimplify e1) (sSimplify e2) in
	case reduce e' of
	Just e -> sSimplify e
	Nothing -> e'
sSimplify (Or e1 e2) =
	let e' = Or (sSimplify e1) (sSimplify e2) in
	case reduce e' of
	Just e -> sSimplify e
	Nothing -> e'
sSimplify (If e1 e2 e3) =
	let e' = If (sSimplify e1) (sSimplify e2) (sSimplify e3) in
	case reduce e' of
	Just e -> sSimplify e
	Nothing -> e'
sSimplify (Not e) =
	let e' = Not (sSimplify e) in
	case reduce e' of
	Just e -> sSimplify e
	Nothing -> e'
sSimplify e@(Var _) = e
sSimplify TT = TT
sSimplify FF = FF

-- Do some further simplification with Not
nSimplify :: (Ord a) => BoolExp a -> BoolExp a
nSimplify = sSimplify . nSimp . sSimplify
  where nSimp (And e1 e2) =
	    -- (x || y || z) && !y  -->  (x || z) && !y
	    simpAO collAnd collOr rrAnds rrOrs e1 e2
	nSimp (Or  e1 e2) =
	    -- (x && y && z) || !y  -->  (x && z) || !y
	    simpAO collOr collAnd rrOrs rrAnds e1 e2
	nSimp (Not e) = Not (nSimp e)
	nSimp (If c t e) = If (nSimp c) (nSimp t) (nSimp e)
	nSimp e = e
	simpAO cA cO rA rO e1 e2 =
	    let es = cA (nSimp e1) ++ cA (nSimp e2)
		ess = map cO es
		ess' = red S.empty [] ess
		red remSet rss [] = reverse (map (rem remSet) rss)
		red remSet rss ([e]:ess) = let e' = rrNot e in red (S.insert e' remSet) ([e]:rss) ess
		red remSet rss (es:ess) = red remSet (es:rss) ess
		rem remSet es = filter (\e -> not (S.member e remSet)) es
	    in  rA (map rO ess')

-- "Advanced" simplify
aSimplify :: (Ord a) => BoolExp a -> BoolExp a
aSimplify = sSimplify . simp bddTrue . sSimplify

red :: (Ord a) => BoolExp a -> BoolExp a
red e =
    case reduce e of
    Just e' -> red e'
    Nothing -> e

implies :: (Ord a) => BDD a -> BDD a -> BDD a -> Bool
implies bdd e1 e2 = bddIsTrue (bddImplies (bddAnd bdd e1) e2)

simp :: (Ord a) => BDD a -> BoolExp a -> BoolExp a
simp bdd e =
-- let
--  r=
    let e' = boolExpToBDD e
    in  if bddIsTrue (bddImplies bdd e') then
	    TT
	else if bddIsTrue (bddImplies bdd (bddNot e')) then
	    FF
	else
	    red $
	    case e of
	    And e1 e2 ->
		let e1' = boolExpToBDD e1
		    e2' = boolExpToBDD e2
		in       if implies bdd e1' e2' then simp bdd e1
		    else if implies bdd e2' e1' then simp bdd e2
		    else And (simp (bddAnd bdd e2') e1) (simp (bddAnd bdd e1') e2)
	    Or  e1 e2 ->
		let e1' = bddNot (boolExpToBDD e1)
		    e2' = bddNot (boolExpToBDD e2)
		in       if implies bdd e1' e2' then simp bdd e1
		    else if implies bdd e2' e1' then simp bdd e2
		    else Or (simp (bddAnd bdd e2') e1) (simp (bddAnd bdd e1') e2)
	    Not e -> Not (simp bdd e)
	    If e1 e2 e3 ->
		let e1' = boolExpToBDD e1
		in  If (simp bdd e1) (simp (bddAnd bdd e1') e2) (simp (bddAnd bdd (bddNot e1')) e3)
	    e -> e
-- in traces (ppReadable e ++ "====>\n" ++ ppReadable r) r

------------


-- bddToBoolExp :: (Eq a) => BDD a -> BoolExp a
-- bddToBoolExp = sSimplify . bddToBoolExp'

-- bddToBoolExp' :: (Eq a) => BDD a -> BoolExp a
-- bddToBoolExp' e | bddIsTrue  e = TT
-- bddToBoolExp' e | bddIsFalse e = FF
-- bddToBoolExp' e = If (Var c) (bddToBoolExp' t) (bddToBoolExp' f)
--   where Just (c, t, f) = bddIsIf e


boolExpToBDD :: (Ord a) => BoolExp a -> BDD a
boolExpToBDD (And e1 e2) = bddAnd (boolExpToBDD e1) (boolExpToBDD e2)
boolExpToBDD (Or  e1 e2) = bddOr  (boolExpToBDD e1) (boolExpToBDD e2)
boolExpToBDD (If  e1 e2 e3) =
	let e1' = boolExpToBDD e1
	    e2' = boolExpToBDD e2
	    e3' = boolExpToBDD e3
	in  (e1' `bddAnd` e2') `bddOr` (bddNot e1' `bddAnd` e3')
boolExpToBDD (Not e)     = bddNot (boolExpToBDD e)
boolExpToBDD (Var v)     = bddVar v
boolExpToBDD TT          = bddTrue
boolExpToBDD FF          = bddFalse
