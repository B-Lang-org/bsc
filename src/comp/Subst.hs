{-# LANGUAGE CPP #-}
module Subst(
             Subst,
             nullSubst, isNullSubst, (+->), mkSubst,
             Types(..), (@@), merge, mergeWith, mergeListWith,
             mergeAgreements,
             trimSubst, trimSubstByVars,
             {- removeFromSubst, -}
             apSubstToSubst,
             getSubstDomain, getSubstRange, sizeSubst,
             chkSubstOrder
             ) where

import PPrint
import CType
import Type
import Util(fromJustOrErr)
import Data.List(nub,union)
import Position

import qualified Data.Set as Set
import qualified Data.Map as Map
import ErrorUtil(internalError)

-- import Debug.Trace


infixr 4 @@

--we carry around a set of the variables on the right hand side
--and a mapping from RHS variables to which LHS variable uses them

type Set_TyVar = Set.Set TyVar
type Set_vars = Map.Map TyVar Set_TyVar
type S_map = Map.Map TyVar Type

data Subst  = S S_map Set_vars
        deriving (Show, Eq)

instance PPrint Subst where
    pPrint d p (S s v) = pparen (p>0) $ text "Subst" <+> pPrint d 0
                         ((Map.assocs s){-, printable_s_var v-} )


nullSubst  :: Subst
nullSubst   = S Map.empty Map.empty

isNullSubst :: Subst -> Bool
isNullSubst (S m _) = Map.null m

(+->)      :: TyVar -> Type -> Subst
u +-> t     = S (Map.singleton u t)
                (back_set u t)

back_set :: TyVar -> Type -> Set_vars
back_set u t = (Map.fromList (map (\v -> (v, Set.singleton u)) (tv t)))

mkSubst :: [(TyVar, Type)] -> Subst
mkSubst vts = -- trace ("mkSubst: " ++ ppReadable vts) $
        S (Map.fromListWith avoid_duplicate_substitutions vts)
          (mk_set_vars vts)

mk_set_vars :: [(TyVar, Type)] -> Set_vars
mk_set_vars vts = (Map.unionsWith Set.union (map (uncurry back_set) vts))
{- all calls to union (Map.union, Set.union, *.union*with) will be efficient
   because of the O(N+M) running time.  Repeated inserts would be less
   efficient because they are O(N*log(M)) time. -}

-- check that concatenating a new substitution with an old one (via @@)
-- will result in a valid substitution
-- basically check that the RHS of the new substitution should not
-- involve any variables in the LHS of the old substitution
chkSubstOrder :: Subst -> Subst -> Bool
chkSubstOrder (S _ new_rhs) (S old_lhs _) =
  Set.null (Set.intersection
             (Map.keysSet new_rhs)
             (Map.keysSet old_lhs))

-- Add a newer substitution (ss1) to an older substitution (ss2).
-- Any knowledge in ss1 is applied to ss2, and then the bindings are merged.
--
(@@) :: Subst -> Subst -> Subst
ss1@(S s1 _) @@ ss2@(S _ var_old) =
    case (Set.null (Set.intersection (Map.keysSet var_old)
                                     (Map.keysSet s1))) of
     True -> --no need to apply s1 to s2
             --trace ("no ap: " ++ ppReadable (ss1, ss2)) $
                merge_sv ss1 ss2
     _ -> -- trace ("ap: " ++ ppReadable (ss1, ss2, finished_2)) $
          (merge_sv (apSubstToSubst ss1 ss2) ss1)


-- Apply the knowledge from one substitution to another, but without adding
-- the bindings
--
apSubstToSubst :: Subst -> Subst -> Subst
apSubstToSubst ss1@(S s1 _) ss2 = finished_2
          where
          finished_2 :: Subst
          finished_2 = Map.foldrWithKey fast_apply ss2 s1
          fast_apply ::  TyVar -> Type -> Subst -> Subst
          fast_apply v t a@(S ss vv) =
              case (Map.lookup v vv) of
               Nothing -> a
               Just lhs ->
-- Forcing the apSub saves some memory (20%) at the cost of some time.
                S (Set.fold (Map.adjust (seqCType . (apSub this_sub)))
                            ss lhs)
                  after_adds
                where
                this_sub = ( v +-> t)
                delete_old :: Set_vars
                --set left after variables that will get substituted are deleted
                delete_old = Set.fold
                             (\l -> Map.update (possibly_delete l) v)
                             vv lhs
                possibly_delete :: TyVar -> Set_TyVar -> Maybe Set_TyVar
                possibly_delete l s = let
                                        r = Set.delete l s
                                      in case Set.null r of
                                          True -> Nothing
                                          _ -> Just r
                after_adds :: Set_vars
                -- set left after additions to the set delete_old
                after_adds = foldr add_tyvar delete_old (tv t)
                add_tyvar :: TyVar -> Set_vars  -> Set_vars
                add_tyvar x set =
                      Map.unionWith Set.union
                         (Map.singleton x lhs) set

avoid_duplicate_substitutions::Type -> Type -> Type
avoid_duplicate_substitutions _ b = b
--       case (a==b) of True -> a
--                      _ ->error "duplicate different Tyvars in Subst"

merge_s :: S_map -> S_map -> S_map
merge_s = Map.unionWith avoid_duplicate_substitutions

merge_v :: Set_vars -> Set_vars -> Set_vars
merge_v = Map.unionWith Set.union

merge_sv :: Subst -> Subst -> Subst
merge_sv (S s1 var1) (S s2 var2) = (S (merge_s s1 s2)
                                    (merge_v var1 var2)
                                   )

merge      :: Subst -> Subst -> Maybe Subst
merge ss1 ss2 =
    if agree then return (merge_sv ss1 ss2)
      else fail "merge fails"
    where
       agree = and (map_on_the_intersection (==) ss1 ss2)

map_on_the_intersection :: (Type -> Type -> a) -> Subst -> Subst -> [a]
map_on_the_intersection call_f ss1@(S s1 _) ss2@(S s2 _) =
   map (\v -> call_f (apSub ss1 (TVar v))
                     (apSub ss2 (TVar v)))
       (Set.toList (Set.intersection (Map.keysSet s1)
                                     (Map.keysSet s2)))

mergeListWith :: (Subst -> Subst -> Maybe Subst) -> [Maybe Subst] -> Maybe Subst
mergeListWith merge_func = foldr cons (Just nullSubst)
 where cons :: Maybe Subst -> Maybe Subst -> Maybe Subst
       cons (Just s) (Just s') =
           -- rtrace ("mergeListWith: Just, Just: " ++ ppReadable (merge s s', s, s')) $
           merge_func s s'
       cons a        b         =
           -- rtrace ("mergeListWith: Nothing: " ++ ppReadable (a,b)) $
           Nothing

-- the merge func is always unification
-- it is a parameter because Unify imports subst
-- this is why we do the @@ below - applying new knowledge to the subst
-- is the right thing to do when unifying
mergeWith :: (Type -> Type -> Maybe Subst) -> Subst -> Subst -> Maybe Subst
mergeWith func ss1 ss2 =
  case merged_subts of
      Nothing -> Nothing
      -- need to apply anything we've learned to both substitutions
      Just ms -> Just (ms @@ (merge_sv ss1 ss2))
  where merged_subts::Maybe Subst
        merged_subts = mergeListWith (mergeWith func)
                           (map_on_the_intersection func ss1 ss2)

-- merge substitutions, but drop mappings where there are disagreements
-- used for typeclass defaulting
mergeAgreements :: Subst -> Subst -> Subst
mergeAgreements s1 s2 = fj $ merge diff1 diff2
  where agree s v t = v' == t || v' == TVar v
          where v' = apSub s (TVar v)
        diff1 = trimSubstBy (agree s2) s1
        diff2 = trimSubstBy (agree s1) s2
        fj = fromJustOrErr ("mergeAgreements: " ++
                            ppReadable (s1, s2, diff1, diff2))


-------

class Types t where
  apSub :: Subst -> t -> t
  tv    :: t -> [TyVar]

instance Types Type where
  apSub (S seo _) v@(TVar u) =
        case slookup u seo of
        Just t  ->
            case t of
            (TGen _ _) -> t -- (kind (TGen _ _)) errors out -- don't check kind
            _ -> if isKVar (kind v) || kind t == kind v
                 then t
                 else internalError ("Subst.Type.apSub: bad kind: " ++
                                     ppString t ++ "::" ++ ppString (kind t) ++
                                     "@" ++ ppString (getPosition t) ++
                                     " / " ++ ppString v ++ "::" ++
                                     ppString (kind v) ++ "@" ++
                                     ppString (getPosition v))
        Nothing -> v
  apSub s (TAp l r) = normTAp (apSub s l) (apSub s r)
  apSub s t         = t

  tv (TVar u)  = [u]
  tv (TAp l r) = tv l `union` tv r
  tv t         = []

instance Types a => Types [a] where
  apSub s ts = map (apSub s) ts
  tv ts      = nub (concatMap tv ts)

slookup :: TyVar -> S_map -> Maybe Type
slookup v xs = {-if length xs > 1300 then trace ("slookup " ++ unwords [itos x|(_,x,_)<-xs]) slookup' v xs else-} Map.lookup v xs

-------

-- These functions are useful for tracing and detecting internal errors
-- on the substitution.

sizeSubst :: Subst -> Int
sizeSubst (S eo _) = (Map.size eo)

getSubstDomain :: Subst -> [TyVar]
getSubstDomain (S eo _) = (Map.keys eo)

getSubstRange :: Subst -> [TyVar]
getSubstRange (S eo _ ) = concat (map tv (Map.elems eo))


-------

-- This is a general substitution trimming function to unify
-- the shared code from trimSubst and trimSubstByVars
-- it also uses map and set operations to compute the new
-- substitution efficiently

fixupBack :: S_map -> Set_vars -> Set_vars
fixupBack new_map old_back = Map.mapMaybe handle_entry old_back
  where retained_vars = Map.keysSet new_map
        handle_entry vs
            | Set.null vs'  = Nothing
            | otherwise     = Just vs'
          where vs' = Set.intersection vs retained_vars

-- It takes a function that determines what elements of the
-- substitution to keep and fixes the subst and the back set
trimSubstBy :: (TyVar -> Type -> Bool) -> Subst -> Subst
trimSubstBy filterFunc (S old_map old_back) = S new_map new_back
  where new_map       = Map.filterWithKey filterFunc old_map
        new_back      = fixupBack new_map old_back

-- This trims substitutions for all variables above a certain number.
-- It is used in type-checking explicitly typed let-bindings, in order
-- to roll the substitution back and throw away all the new associations
-- introduced for the let-binding (which are not needed again).
-- It takes advantage of the fact that new type variables are created
-- in numeric order.
trimSubst :: TyVar -> Subst -> Subst
trimSubst v (S old_map old_back) = S new_map new_back
  where (new_map, _) = Map.split v old_map
        new_back     = fixupBack new_map old_back

-- This removes substitution entries whose LHS or RHS contains the variables.
-- (That is, entried for a type variable and whose associated type contains
-- the variable.)
-- It is used to removed mention of type variables inside a type lambda
-- (to prevent name capture on the lambda-bound variables when substituting
-- inside the lambda).

trimSubstByVars :: [TyVar] -> Subst -> Subst
trimSubstByVars vs = if (null vs) then id else trimSubstBy filterFunc
  where filterFunc v t = not ((elem v vs) ||
                              (any (\u -> elem u vs) (tv t)))

{-
-- This removes variables just from the LHS of the substitution,
-- and returns a list of the variables which were found.
removeFromSubst :: [TyVar] -> Subst -> (Subst, [TyVar])
removeFromSubst vs (S e o) =
    let
       -- removes and returns a list of the removed vars
       removeFunc s@(v,_,_) (ss, removed_vs) =
           if (elem v vs)
           then (ss, v:removed_vs)
           else (s:ss, removed_vs)

       (e',rvs1) = foldr removeFunc ([],[]) e
       (o',rvs2) = foldr removeFunc ([],rvs1) o
    in
       (S e' o', rvs2)
-}
