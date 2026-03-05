{-# LANGUAGE PatternGuards #-}
module Unify(Unify(..), matchList) where
import Type
import Subst
import CType
import ErrorUtil(internalError)
import Util(fastNub)

-- For tracing
import PFPrint
import Util(traces)
import IOUtil(progArgs)

doRTrace :: Bool
doRTrace = elem "-trace-type" progArgs
rtrace :: String -> a -> a
rtrace s x = if doRTrace then traces s x else x

class Unify t where
    mgu :: [TyVar] {- bound type vars: don't substitute with other tyvars -}
        -> ATFEqMap {- ATF equations for expansion during unification -}
        -- result: list of substitutions and required type equalities
        -> t -> t -> Maybe (Subst, [(Type, Type)])

instance Unify Type where
    mgu bound_tyvars eqmap t1@(TAp _ _) t2 | Just t1' <- tryExpandATF eqmap t1 =
         mgu bound_tyvars eqmap t1' t2
    mgu bound_tyvars eqmap t1 t2@(TAp _ _) | Just t2' <- tryExpandATF eqmap t2 =
         mgu bound_tyvars eqmap t1 t2'
    mgu bound_tyvars eqmap t1 t2
        | kind t1 == KNum =
      case kind t2 of
        KNum -> numUnify bound_tyvars t1 t2
        _ -> internalError("unify kind mismatch: " ++ ppReadable(t1, kind t1, t2, kind t2))
    -- don't substitute a variable for itself
    mgu bound_tyvars eqmap tu@(TVar u) tv@(TVar v) = varUnify bound_tyvars u v tu tv
    mgu bound_tyvars eqmap (TVar u) t        = varBindWithEqs u t
    mgu bound_tyvars eqmap t (TVar u)        = varBindWithEqs u t
    mgu bound_tyvars eqmap (TCon tc1) (TCon tc2) | tc1==tc2 = Just (nullSubst, [])
    -- an unreducable ATF application: identical types unify cleanly (reflexivity);
    -- different types generate a deferred equality constraint without structural
    -- decomposition (no injective type family reasoning).
    mgu bound_tyvars eqmap t1 t2 | isATFAp t1 || isATFAp t2 =
        if t1 == t2 then Just (nullSubst, []) else Just (nullSubst, [(t1, t2)])
    mgu bound_tyvars eqmap t1@(TAp l r) t2@(TAp l' r')
        | Just (s1, eqs1) <- mgu bound_tyvars eqmap l l',
          Just (s2, eqs2) <- mgu bound_tyvars eqmap (apSub s1 r) (apSub s1 r')
        = Just (s2 @@ s1, fastNub (eqs1 ++ eqs2))
    mgu bound_tyvars _ _ _ = Nothing

numUnify :: [TyVar] -> Type -> Type -> Maybe (Subst, [(Type, Type)])
numUnify bound_tyvars t1 t2
    | t1 == t2 = Just (nullSubst, [])
numUnify bound_tyvars (TCon (TyNum n1 _)) (TCon (TyNum n2 _))
    | n1 /= n2 = Nothing
numUnify bound_tyvars tu@(TVar u) tv@(TVar v) =
    case (varUnify bound_tyvars u v tu tv) of
      Nothing -> Just (nullSubst, [(tu,tv)])
      res@(Just _) -> res
-- if the type we're unifying against has no type variables
-- (e.g. a number) then just do the substitution
-- should not be necessary because of bound variable handling in ctxreduce
-- numUnify bound_tyvars (TVar u) t | null (tv t) = varBind u t
-- numUnify bound_tyvars t (TVar u) | null (tv t) = varBind u t
-- prefer an equality constraint to unifying a bound type variable
-- or defining a variable in terms of itself
numUnify bound_tyvars (TVar u) t
    | not (u `elem` (bound_tyvars ++ tv t)) = varBindWithEqs u t
numUnify bound_tyvars t (TVar u)
    | not (u `elem` (bound_tyvars ++ tv t)) = varBindWithEqs u t
numUnify bound_tyvars t1 t2 = Just (nullSubst, [(t1,t2)])

varUnify :: [TyVar] -> TyVar -> TyVar -> Type -> Type -> Maybe (Subst, [(Type, Type)])
varUnify bound_tyvars u v tu tv
    | u == v = Just (nullSubst, [])
varUnify bound_tyvars u v tu tv
    -- don't substitute one bound var for another
    | u `elem` bound_tyvars, v `elem` bound_tyvars = Nothing
varUnify bound_tyvars u v tu tv
    -- don't substitute a bound var with an unbound var
    | u `elem` bound_tyvars = varBindWithEqs v tu
varUnify bound_tyvars u v tu tv
    | v `elem` bound_tyvars = varBindWithEqs u tv
varUnify bound_tyvars u@(TyVar _ nu _) v@(TyVar _ nv _) tu tv
    | (isGeneratedTVar u) && (isGeneratedTVar v) =
        case (compare nu nv) of
          GT -> varBindWithEqs u tv
          LT -> varBindWithEqs v tu
          EQ -> internalError("don't substitute a variable for itself")
-- varUnify fall-throughs for ctxreduce
    | isGeneratedTVar u = varBindWithEqs u tv
    | isGeneratedTVar v = varBindWithEqs v tu
varUnify bound_tyvars u v tu tv = varBindWithEqs u tv
    {- traces ("varUnify fall-through (no generated): " ++
            ppReadable (bound_tyvars, u, tv)) $ varBind u tv -}

instance (Types t, Unify t) => Unify [t] where
    mgu bound_tyvars eqmap (x:xs) (y:ys) = do
        (s1,eqs1) <- mgu bound_tyvars eqmap x y
        (s2,eqs2) <- mgu bound_tyvars eqmap (apSub s1 xs) (apSub s1 ys)
        return (s2 @@ s1, fastNub (eqs1 ++ eqs2))
    mgu bound_tyvars eqmap []     []     = return (nullSubst, [])
    mgu bound_tyvars eqmap _      _      = Nothing

varBindWithEqs :: TyVar -> Type -> Maybe (Subst, [(Type, Type)])
varBindWithEqs u t = fmap no_eqs $ varBind u t
 where no_eqs s = (s,[])

varBind :: TyVar -> Type -> Maybe Subst
varBind u t | t == TVar u      = Just nullSubst
            | isUnSatSyn t               = Nothing
            | u `elem` tv t    = Nothing
            | kind u == kind t = Just (u +-> t)
            | otherwise        = Nothing

-- Cannot allow a variable to be bound to an unsaturated type synonym.
isUnSatSyn :: Type -> Bool
isUnSatSyn t = isUnSatSyn' t 0
isUnSatSyn' :: Type -> Integer -> Bool
isUnSatSyn' (TCon (TyCon _ _ (TItype n _))) args = n > args
isUnSatSyn' (TAp f a) args = isUnSatSyn' f (args + 1)
isUnSatSyn' _  _ = False

match :: Type -> Type -> Maybe Subst
match (TAp l r) (TAp l' r') = rtrace ("match: TAp: " ++ ppReadable (l,r)) $ do
    sl <- match l l'
    sr <- match r r'
    rtrace ("match: TAp result:  " ++ ppReadable (merge sl sr, sl, sr)) $ merge sl sr
match (TVar u1)  (TVar u2)  | u1 == u2         =
   rtrace ("match: Var, Var: " ++ ppReadable (u1, u2))  $ Just nullSubst
match (TVar u)   t          | kind u == kind t =
   rtrace ("match: Var, oth: " ++ ppReadable (u,t))     $ Just (u +-> t)
match (TCon tc1) (TCon tc2) | tc1 == tc2       =
   rtrace ("match: Con, Con: " ++ ppReadable (tc1,tc2)) $ Just nullSubst
match t1         t2                            =
   rtrace ("match: Nothing: " ++ ppReadable (t1,t2))    $ Nothing

matchList :: [Type] -> [Type] -> Maybe Subst
matchList ts ts' = mergeListWith merge (zipWith match ts ts')
