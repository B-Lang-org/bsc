{-# LANGUAGE PatternGuards #-}
module StdPrel(
    preTypes, preClasses, isPreClass, preValues,
    tiArrow, tiSizeOf,
    tiUnit, tiPair, tiMaybe, tiList,
    tiBit, tiBool,
    tiInteger, tiReal, tiString, tiChar,
    tiHandle, tiBufferMode,
    tiFmt,
    tiAction, tiRules,
    tiClock, tiReset, tiInout,
    tiPrimArray,
    tiPosition, tiType, tiName, tiPred, tiSchedPragma
   ) where

import qualified Bag as B
import qualified Data.Set as S

import Util(log2, ordPair, integerSqrt, take3OrErr)
import Position
import ErrorUtil(internalError)
import Id
import SymTab
import CType
import Type
import Pred
import PreIds
import CSyntax(anyTExpr)
import Subst(Types(..))
import Unify(mgu)

--import PPrint
--import Debug.Trace

-- -------------------------

v1, v2, v3 :: Id
(v1, v2, v3) = take3OrErr "StdPrel tmpTyVarIds" tmpTyVarIds

tvarh1, tvarh2, tvarh3 :: TyVar
tvarh1 = tVarKind v1 KNum
tvarh2 = tVarKind v2 KNum
tvarh3 = tVarKind v3 KNum

-- instance for p' :=> p
-- avoid mkInst because it does quantification
-- that will introduce unnecessary (and sometimes harmful)
-- fresh type variables
mkImpliedInst :: Pred -> Pred -> Inst
mkImpliedInst p' p = Inst r [] ([pp'] :=> p) (Just idPrelude)
  where pp' = mkPredWithPositions [] p'
        r   = anyTExpr (predToType p' `fn` predToType p)

-- the DVS are the type variables in the concrete type of a type signature
-- (i.e.  without provisos)
-- we only want to drop type variables with a numeric function if:
-- (a) those type variables don't appear in the concrete type
-- (b) the numeric function is determined by type variables in the concrete type
-- multi-step dependencies are handled because we reconsider provisos
-- when an instance-match introduces a substitution
checkDVS :: Types t => [TyVar] -> t -> Bool
checkDVS dvs t = all (flip elem dvs) (tv t)

-- -------------------------

clsAdd :: SymTab -> Class
clsAdd symT = Class {
        name = CTypeclass idAdd,
        csig = [tvarh1, tvarh2, tvarh3],
        super = [],  -- [IsIn clsSize [TVar tvarh1], IsIn clsSize [TVar tvarh2], IsIn clsSize [TVar tvarh3]]
        genInsts = genAddInsts symT,
        tyConOf = TyCon idAdd (Just (Kfun KNum (Kfun KNum (Kfun KNum KStar)))) (TIstruct SClass []),
        funDeps = [[False, False, True], [False, True, False], [True, False, False]],
        funDeps2 = [[Just False, Just False, Just True],
                    [Just False, Just True, Just False],
                    [Just True, Just False, Just False]],
        allowIncoherent = Just False,
        isComm = True,
        pkg_src = Just idPrelude
        }

genAddInsts :: SymTab -> [TyVar] -> Maybe [TyVar] -> Pred -> [Inst]

-- (C1, C2, ?) : (C1, C2, C1+C2)
genAddInsts _ _ _ (IsIn c [t1@(TCon (TyNum n1 p1)), t2@(TCon (TyNum n2 _)), _])
        = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t3]
        t3 = TCon (TyNum (n1+n2) p1)

-- (C1, ?, C3) : (C1, C3-C1, C3)
genAddInsts _ _ _ (IsIn c [t1@(TCon (TyNum i1 p1)), _, t3@(TCon (TyNum i3 _))])
        | i3 >= i1 = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t3]
        t2 = TCon (TyNum (i3 - i1) p1)

-- (?, C2, C3) : (C3-C2, C2, C3)
genAddInsts _ _ _ (IsIn c [_, t2@(TCon (TyNum i2 p2)), t3@(TCon (TyNum i3 _))])
        | i3 >= i2 = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t3]
        t1 = TCon (TyNum (i3 - i2) p2)

-- (0, T, ?) : (0, T, T)
genAddInsts _ _ _ (IsIn c [t1@(TCon (TyNum 0 _)), t2, _])
        = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t2]

-- (T, 0, ?) : (0, T, T)
genAddInsts _ _ _ (IsIn c [t1, t2@(TCon (TyNum 0 _)), _])
        = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t1]

-- (?, T, T) : (0, T, T)
genAddInsts _ _ _ (IsIn c [_, t2, t3])
        | t2 == t3 = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t3]
        t1 = TCon (TyNum 0 (getPosition t2))

-- (T, ?, T) : (T, 0, T)
genAddInsts _ _ _ (IsIn c [t1, _, t3])
        | t1 == t3 = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t3]
        t2 = TCon (TyNum 0 (getPosition t1))

-- (T, T, C) : NumEq(T, C/2) => itself, when C is even
genAddInsts symT _ _ p@(IsIn c [t1, t2, TCon (TyNum n npos)])
    | t1 == t2, even n
    = [ mkImpliedInst (IsIn clsNumEq [t1, TCon (TyNum (n `div` 2) npos)]) p ]
  where
    -- look up the class, rather than construct it, for better sharing
    clsNumEq = mustFindClass symT (CTypeclass idNumEq)

-- (T1, T2, TAdd#(T1,T2)) : itself
-- (T1, T2, TAdd#(T2,T1)) : itself
genAddInsts _ _ _ p@(IsIn c [t1, t2, t3])
    | t3 == cTApplys tAdd [t1, t2] ||
      t3 == cTApplys tAdd [t2, t1] = [ mkInst r ([] :=> p) (Just idPrelude) ]
 where r = anyTExpr (predToType p)

-- (T1, T2, TAdd#(T1, T3)) : NumEq(T2,T3) => itself
-- (T1, T2, TAdd#(T3, T1)) : NumEq(T2,T3) => itself
-- (T1, T2, TAdd#(T2, T3)) : NumEq(T1,T3) => itself
-- (T1, T2, TAdd#(T3, T2)) : NumEq(T1,T3) => itself
genAddInsts symT _ _ p@(IsIn c [t1, t2, t3@(TAp (TAp tc tA) tB)])
    | tc == tAdd,
      t1 == tA
    = [ mkImpliedInst (IsIn clsNumEq [t2, tB]) p ]
    | tc == tAdd,
      t1 == tB
    = [ mkImpliedInst (IsIn clsNumEq [t2, tA]) p ]
    | tc == tAdd,
      t2 == tA
    = [ mkImpliedInst (IsIn clsNumEq [t1, tB]) p ]
    | tc == tAdd,
      t2 == tB
    = [ mkImpliedInst (IsIn clsNumEq [t1, tA]) p ]
  where
    -- look up the class, rather than construct it, for better sharing
    clsNumEq = mustFindClass symT (CTypeclass idNumEq)

-- XXX The above rules are simple cases of this:
genAddInsts symT _ _ p@(IsIn c [t1, t2, t3])
    | not (nullAddTerms b1_b2_intersection) =
        [mkImpliedInst (IsIn clsNumEq [t12',t3']) p]
{-
        -- We can pre-simplify the NumEq, if it is more efficient:
        if (nullAddTerms b1_rem && nullAddTerms b2_rem)
        then let r = anyTExpr (predToType p)
             in  [mkInst r ([] :=> p) (Just idPrelude)]
        else case (fromAddTerms b1_rem) of
               (TAp (TAp tc t1') t2') | tc == tAdd
                 -> [mkImpliedInst (IsIn c [t1',t2',t3']) p]
               t -> [mkImpliedInst (IsIn clsNumEq [t,t3']) p]
-}
  where b1 = toAddTerms (TAp (TAp tAdd t1) t2)
        b2 = toAddTerms t3
        b1_b2_intersection = intersectionAddTerms b1 b2
        b1_rem = differenceAddTerms b1 b1_b2_intersection
        b2_rem = differenceAddTerms b2 b1_b2_intersection
        t12' = fromAddTerms b1_rem
        t3' = fromAddTerms b2_rem
        -- look up the class, rather than construct it, for better sharing
        clsNumEq = mustFindClass symT (CTypeclass idNumEq)

-- when satisfyFV, as a last resort:
-- (T1, T2, V) : (T1, T2, TAdd#(T1,T2))
--   when V is not bound or dependent and T1 and T2 contain only variables
--        which are bound or dependent
genAddInsts _ bvs (Just dvs) (IsIn c [t1,t2, tv@(TVar v)])
    | v `notElem` dvs,
      checkDVS dvs (t1, t2),
      mgu bvs tv t3 /= Nothing =
        --trace ("TAdd " ++ ppReadable (r, p)) $
        [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t3]
        t3 = TAp (TAp tAdd t1) t2

-- when satisfyFV, as a last resort:
-- (T1, V, T3) : (T1, TSub#(T3, T1), T3)
--   when T1 is known to be <= T3, usually because T3 is TMax#(T1,?) or a
--      nested TMax structure containing T1, or because T1 is TMin#(T3, ?)
--      or a nested TMin structure containing T3
--   when V is not bound or dependent
--   and T1 and T2 contain only variables which are bound or dependent
-- and the other permutation:
-- (V, T2, T3) : (TSub#(T3, T2), T2, T3)
--
-- This is safe to do because we know that the TSub will always be non-negative.
-- A general rule from (T1, V, T3) to (T1, TSub#(T3,T1), T3) would cause Add
-- provisos to no longer be required!  But the TSub could fail during elab.
-- This would move numeric checking to elaboration time, which we don't want
-- because we want to catch bugs early.
genAddInsts _ bvs (Just dvs) (IsIn c [t1, tv@(TVar v), t3])
    | t1 `isKnownLTE` t3,
      v `notElem` dvs,
      checkDVS dvs (t1, t3),
      mgu bvs tv t2 /= Nothing =
        --trace ("Add TMax " ++ ppReadable p) $
        [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t3]
        t2 = cTApplys tSub [t3, t1]
genAddInsts _ bvs (Just dvs) (IsIn c [tv@(TVar v), t2, t3])
    | t2 `isKnownLTE` t3,
      v `notElem` dvs,
      checkDVS dvs (t2, t3),
      mgu bvs tv t1 /= Nothing =
        --trace ("Add TMax " ++ ppReadable p) $
        [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t3]
        t1 = cTApplys tSub [t3, t2]

-- else, no instances to match
genAddInsts _ _ _ _ = []

-- -------------------------

-- A bag of non-constant, non-TAdd/TSub terms which have been added;
-- a bag of non-constant, non-TAdd/TSub terms which have been subtracted;
-- and a sum of constant terms
--  * The constant sum may not be needed when the proviso reduces fully;
--    but when the proviso does not reduce, it allows us to make some
--    progress and hopefully report a slightly simpler proviso error.
--    It may also improve efficiency in the fully-reducible case by
--    avoiding having to do multiple steps of reduction.
--  * We will keep the two bags reduced: if a type appears in both,
--    we remove it from both
data AddTerms = AddTerms Integer (B.Bag Type) (B.Bag Type)

unionAddTerms :: AddTerms -> AddTerms -> AddTerms
unionAddTerms (AddTerms i1 add_b1 sub_b1) (AddTerms i2 add_b2 sub_b2) =
    let
        -- cross out any sub terms from one that appear in the other
        (add_b1', sub_b2') = B.removeIntersection add_b1 sub_b2
        (add_b2', sub_b1') = B.removeIntersection add_b2 sub_b1
    in
        AddTerms (i1 + i2)
                 (B.union add_b1' add_b2')
                 (B.union sub_b1' sub_b2')

singletonAddTerms :: Type -> AddTerms
singletonAddTerms (TCon (TyNum { tynum_value = n })) = AddTerms n B.empty B.empty
singletonAddTerms t = AddTerms 0 (B.singleton t) B.empty

invertAddTerms :: AddTerms -> AddTerms
invertAddTerms (AddTerms i add_b sub_b) = (AddTerms (-i) sub_b add_b)

toAddTerms :: Type -> AddTerms
toAddTerms (TAp (TAp tc t1) t2)
    | tc == tAdd = unionAddTerms (toAddTerms t1) (toAddTerms t2)
toAddTerms (TAp (TAp tc t1) t2)
    | tc == tSub = unionAddTerms (toAddTerms t1) (invertAddTerms (toAddTerms t2))
toAddTerms t = singletonAddTerms t

fromAddTerms :: AddTerms -> Type
fromAddTerms (AddTerms 0 add_b sub_b) =
    mkAddType (B.toList add_b) (B.toList sub_b)
fromAddTerms (AddTerms i add_b sub_b) =
    let it = cTNum (abs i) noPosition  -- XXX better position?
    in  if (i > 0)
        then mkAddType (it : B.toList add_b) (B.toList sub_b)
        else mkAddType (B.toList add_b)      (it : B.toList sub_b)

mkAddType :: [Type] -> [Type] -> Type
mkAddType add_ts sub_ts =
    let mkTAdd t1 t2 = TAp (TAp tAdd t1) t2
        mkTSub t1 t2 = TAp (TAp tSub t1) t2
        add_val = case add_ts of
                     [] -> cTNum 0 noPosition  -- XXX better position?
                     ts -> foldr1 mkTAdd add_ts
    in  foldl mkTSub add_val sub_ts

differenceAddTerms :: AddTerms -> AddTerms -> AddTerms
differenceAddTerms big small = unionAddTerms big (invertAddTerms small)

intersectionAddTerms :: AddTerms -> AddTerms -> AddTerms
intersectionAddTerms (AddTerms i1 add_b1 sub_b1) (AddTerms i2 add_b2 sub_b2) =
    AddTerms (min i1 i2)
             (B.intersection add_b1 add_b2)
             (B.intersection sub_b1 sub_b2)

nullAddTerms :: AddTerms -> Bool
nullAddTerms (AddTerms i a s) = (i == 0) && (B.null a) && (B.null s)

-- -------------------------

-- Return whether a type "t1" is known to be less than or equal to type "t2".
-- This is true when the types are equal or when "t2" is a TMax (or nested
-- TMax) containing "t1".  It is also true if "t1" is a TMin (or nested TMin)
-- containing "t2".
isKnownLTE :: Type -> Type -> Bool
isKnownLTE t1 (TAp (TAp tc tA) tB) | tc == tMax =
   (isKnownLTE t1 tA) || (isKnownLTE t1 tB)
isKnownLTE (TAp (TAp tc tA) tB) t2 | tc == tMin =
   (isKnownLTE tA t2) || (isKnownLTE tB t2)
isKnownLTE t1 t2 | t1 == t2 = True
isKnownLTE _ _ = False

-- -------------------------

clsMax :: Class
clsMax = Class {
        name = CTypeclass idMax,
        csig = [tvarh1, tvarh2, tvarh3],
        super = [],  -- [IsIn clsSize [TVar tvarh1], IsIn clsSize [TVar tvarh2], IsIn clsSize [TVar tvarh3]]
        genInsts = genMaxInsts,
        tyConOf = TyCon idMax (Just (Kfun KNum (Kfun KNum (Kfun KNum KStar)))) (TIstruct SClass []),
        funDeps = [[False, False, True]],
        funDeps2 = [[Just False, Just False, Just True]],
        allowIncoherent = Just False,
        isComm = True,
        pkg_src = Just idPrelude
        }

genMaxInsts :: [TyVar] -> Maybe [TyVar] -> Pred -> [Inst]

-- (C1, C2, ?) : (C1, C2, max(C1,C2))
genMaxInsts _ _ (IsIn c [t1@(TCon (TyNum n1 p1)), t2@(TCon (TyNum n2 _)), _])
        = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t3]
        t3 = TCon (TyNum (n1 `max` n2) p1)

-- (0, T, ?) : (0, T, T)
genMaxInsts _ _ (IsIn c [t1@(TCon (TyNum 0 _)), t2, _])
        = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t2]

-- (T, 0, ?) : (T, 0, T)
genMaxInsts _ _ (IsIn c [t1, t2@(TCon (TyNum 0 _)), _])
        = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t1]

-- (T1, T2, TMax#(T1,T2)) : itself
-- (T1, T2, TMax#(T2,T1)) : itself
genMaxInsts _ _ (IsIn c [t1, t2, t3])
    | t3 == cTApplys tMax [t1, t2] ||
      t3 == cTApplys tMax [t2, t1] = [ mkInst r ([] :=> p) (Just idPrelude) ]
 where r = anyTExpr (predToType p)
       p = IsIn c [t1, t2, t3]

-- XXX The above rules are a simple case of this
-- Note that this rule only matches if the terms on either side are equal
-- (this rule does not try to reduce the terms to a smaller set)
genMaxInsts _ _ p@(IsIn c [t1, t2, t3]) | equalMaxTerms s1 s2 =
        [ mkInst r ([] :=> p) (Just idPrelude) ]
  where s1 = toMaxTerms (TAp (TAp tMax t1) t2)
        s2 = toMaxTerms t3
        r = anyTExpr (predToType p)

-- when satisfyFV, as a last resort:
-- (T1, T2, V) : (T1, T2, TMax#(T1,T2))
--   when V is not bound or dependent and T1 and T2 contain only variables
--        which are bound or dependent
genMaxInsts bvs (Just dvs) (IsIn c [t1, t2, tv@(TVar v)])
    | v `notElem` dvs,
      checkDVS dvs (t1, t2),
      mgu bvs tv t3 /= Nothing =
        [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t3]
        t3 = TAp (TAp tMax t1) t2

-- else, no instances to match
genMaxInsts _ _ _ = []

-- -------------------------

-- A set of non-constant, non-TMax terms and the max of constant terms
data MaxTerms = MaxTerms Integer (S.Set Type)

unionMaxTerms :: MaxTerms -> MaxTerms -> MaxTerms
unionMaxTerms (MaxTerms i1 s1) (MaxTerms i2 s2) =
    MaxTerms (max i1 i2) (S.union s1 s2)

singletonMaxTerms :: Type -> MaxTerms
singletonMaxTerms (TCon (TyNum { tynum_value = n })) = MaxTerms n S.empty
singletonMaxTerms t = MaxTerms 0 (S.singleton t)

toMaxTerms :: Type -> MaxTerms
toMaxTerms (TAp (TAp tc t1) t2)
    | tc == tMax = unionMaxTerms (toMaxTerms t1) (toMaxTerms t2)
toMaxTerms t = singletonMaxTerms t

equalMaxTerms :: MaxTerms -> MaxTerms -> Bool
equalMaxTerms (MaxTerms i1 s1) (MaxTerms i2 s2) = (i1 == i2) && (s1 == s2)

-- -------------------------

clsMin :: Class
clsMin = Class {
        name = CTypeclass idMin,
        csig = [tvarh1, tvarh2, tvarh3],
        super = [],  -- [IsIn clsSize [TVar tvarh1], IsIn clsSize [TVar tvarh2], IsIn clsSize [TVar tvarh3]]
        genInsts = genMinInsts,
        tyConOf = TyCon idMin (Just (Kfun KNum (Kfun KNum (Kfun KNum KStar)))) (TIstruct SClass []),
        funDeps = [[False, False, True]],
        funDeps2 = [[Just False, Just False, Just True]],
        allowIncoherent = Just False,
        isComm = True,
        pkg_src = Just idPrelude
        }

genMinInsts :: [TyVar] -> Maybe [TyVar] -> Pred -> [Inst]

-- (C1, C2, ?) : (C1, C2, min(C1,C2))
genMinInsts _ _ (IsIn c [t1@(TCon (TyNum n1 p1)), t2@(TCon (TyNum n2 _)), _])
        = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t3]
        t3 = TCon (TyNum (n1 `min` n2) p1)

-- (0, T, ?) : (0, T, 0)
genMinInsts _ _ (IsIn c [t1@(TCon (TyNum 0 _)), t2, _])
        = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t1]

-- (T, 0, ?) : (T, 0, 0)
genMinInsts _ _ (IsIn c [t1, t2@(TCon (TyNum 0 _)), _])
        = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t2]

-- (T1, T2, TMin#(T1,T2)) : itself
-- (T1, T2, TMin#(T2,T1)) : itself
genMinInsts _ _ (IsIn c [t1, t2, t3])
    | t3 == cTApplys tMin [t1, t2] ||
      t3 == cTApplys tMin [t2, t1] = [ mkInst r ([] :=> p) (Just idPrelude) ]
 where r = anyTExpr (predToType p)
       p = IsIn c [t1, t2, t3]

-- XXX The above rules are a simple case of this
-- Note that this rule only matches if the terms on either side are equal
-- (this rule does not try to reduce the terms to a smaller set)
genMinInsts _ _ p@(IsIn c [t1, t2, t3]) | equalMinTerms s1 s2 =
        [ mkInst r ([] :=> p) (Just idPrelude) ]
  where s1 = toMinTerms (TAp (TAp tMin t1) t2)
        s2 = toMinTerms t3
        r = anyTExpr (predToType p)

-- when satisfyFV, as a last resort:
-- (T1, T2, V) : (T1, T2, TMin#(T1,T2))
--   when V is not bound or dependent and T1 and T2 contain only variables
--        which are bound or dependent
genMinInsts bvs (Just dvs) (IsIn c [t1, t2, tv@(TVar v)])
    | v `notElem` dvs,
      checkDVS dvs (t1, t2),
      mgu bvs tv t3 /= Nothing =
        [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t3]
        t3 = TAp (TAp tMin t1) t2

-- else, no instances to match
genMinInsts _ _ _ = []

-- -------------------------

-- A set of non-constant, non-TMin terms and the min of constant terms
data MinTerms = MinTerms (Maybe Integer) (S.Set Type)

unionMinTerms :: MinTerms -> MinTerms -> MinTerms
unionMinTerms (MinTerms mi1 s1) (MinTerms mi2 s2) =
    let mi' = case (mi1, mi2) of
                (Nothing, _) -> mi2
                (_, Nothing) -> mi1
                (Just i1, Just i2) -> Just (min i1 i2)
    in  MinTerms mi' (S.union s1 s2)

singletonMinTerms :: Type -> MinTerms
singletonMinTerms (TCon (TyNum { tynum_value = n })) = MinTerms (Just n) S.empty
singletonMinTerms t = MinTerms Nothing (S.singleton t)

toMinTerms :: Type -> MinTerms
toMinTerms (TAp (TAp tc t1) t2)
    | tc == tMin = unionMinTerms (toMinTerms t1) (toMinTerms t2)
toMinTerms t = singletonMinTerms t

equalMinTerms :: MinTerms -> MinTerms -> Bool
equalMinTerms (MinTerms i1 s1) (MinTerms i2 s2) = (i1 == i2) && (s1 == s2)

-- -------------------------

clsLog :: Class
clsLog = Class {
        name = CTypeclass idLog,
        csig = [tvarh1, tvarh2],
        super = [],  -- [IsIn clsSize [TVar tvarh1], IsIn clsSize [TVar tvarh2], IsIn clsSize [TVar tvarh3]]
        genInsts = genLogInsts,
        tyConOf = TyCon idLog (Just (Kfun KNum (Kfun KNum KStar))) (TIstruct SClass []),
        funDeps = [[False, True]],
        funDeps2 = [[Just False, Just True]],
        allowIncoherent = Just False,
        isComm = False,
        pkg_src = Just idPrelude
        }

genLogInsts :: [TyVar] -> Maybe [TyVar] -> Pred -> [Inst]

-- (0, ?) : no instance
genLogInsts _ _ (IsIn c [t1@(TCon (TyNum i1 p1)), _])
        | i1 == 0 = []

-- (C, ?) : (C, log(C))
genLogInsts _ _ (IsIn c [t1@(TCon (TyNum i1 p1)), _])
        | i1 > 0 = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2]
        t2 = TCon (TyNum (log2 i1) p1)

-- For most C, there are multiple X for which Log#(X,C) is an instance.
-- This code produces only one instance, and it would only match if the
-- first type is the exact TyNum, which would have been caught by the
-- above case arm.  So this case arm is useless:
{-
-- (?, C) : (2^C, C)
genLogInsts _ _ (IsIn c [_, t2@(TCon (TyNum i2 p2))])
        | i2 >= 0 = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2]
        t1 = TCon (TyNum (2 ^ i2) p2)
-}

-- (T, TLog#(T)) : itself
-- (TExp#(T), T) : itself
genLogInsts _ _ p@(IsIn c [t1, t2])
    | (tcon, [arg]) <- splitTAp t2,
      tcon == tLog, arg == t1 = [ mkInst r ([] :=> p) (Just idPrelude) ]
    | (tcon, [arg]) <- splitTAp t1,
      tcon == tExp, arg == t2 = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)

-- XXX Add this?
-- (TExp#(T1), T2) : NumEq(T1,T2) => itself

{-
-- XXX Consider removing this:
-- when satisfyFV, as a last resort:
-- (V, T) : (TExp#(T), V)
--   when V is not bound or dependent and T contains only variables
--        which are bound or dependent
-- XXX Log a b does not have b -> a fundep
-- YYY This should be OK because (in theory)
-- if we get here v is "otherwise unconstrained"
-- otherwise we'd have learned something before
-- dvs reduction kicks in (at the second satisfyFV)
genLogInsts bvs (Just dvs) (IsIn c [tv@(TVar v),t2])
    | v `notElem` dvs,
      checkDVS dvs t2,
      mgu bvs tv t1 /= Nothing =
        [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2]
        t1 = TAp tExp t2
-}

-- when satisfyFV, as a last resort:
-- (T, V) : (T, TLog#(T))
--   when V is not bound or dependent and T contains only variables
--        which are bound or dependent
-- XXX Should this also introduce a NotZero#(T) proviso?
genLogInsts bvs (Just dvs) (IsIn c [t1,tv@(TVar v)])
    | v `notElem` dvs,
      checkDVS dvs t1,
      mgu bvs tv t2 /= Nothing =
        [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2]
        t2 = TAp tLog t1

-- else, no instances to match
genLogInsts _ _ _ = []

-- -------------------------

clsMul :: SymTab -> Class
clsMul symT = Class {
        name = CTypeclass idMul,
        csig = [tvarh1, tvarh2, tvarh3],
        super = [],  -- [IsIn clsSize [TVar tvarh1], IsIn clsSize [TVar tvarh2], IsIn clsSize [TVar tvarh3]]
        genInsts = genMulInsts symT,
        tyConOf = TyCon idMul (Just (Kfun KNum (Kfun KNum (Kfun KNum KStar)))) (TIstruct SClass []),
        funDeps = [[False, False, True], [False, True, False], [True, False, False]],
        funDeps2 = [[Just False, Just False, Just True],
                    [Just False, Just True, Just False],
                    [Just True, Just False, Just False]],
        allowIncoherent = Just False,
        isComm = True,
        pkg_src = Just idPrelude
        }

genMulInsts :: SymTab -> [TyVar] -> Maybe [TyVar] -> Pred -> [Inst]

-- (C1, C2, ?) : (C1, C2, C1*C2)
genMulInsts _ _ _ (IsIn c [t1@(TCon (TyNum n1 p1)), t2@(TCon (TyNum n2 _)), _])
        = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t3]
        t3 = TCon (TyNum (n1 * n2) p1)

-- (C1, ?, C3) : (C1, C3/C1, C3) when C3/C1 has no remainder (and C1 is not 0)
genMulInsts _ _ _ (IsIn c [t1@(TCon (TyNum i1 p1)), _, t3@(TCon (TyNum i3 _))])
        | i1 /= 0 && i3 `mod` i1 == 0 = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t3]
        t2 = TCon (TyNum (i3 `div` i1) p1)

-- (?, C2, C3) : (C3/C2, C2, C3) when C3/C2 has no remainder (and C2 is not 0)
genMulInsts _ _ _ (IsIn c [_, t2@(TCon (TyNum i2 p2)), t3@(TCon (TyNum i3 _))])
        | i2 /= 0 && i3 `mod` i2 == 0 = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t3]
        t1 = TCon (TyNum (i3 `div` i2) p2)

-- (1, T, ?) : (1, T, T)
genMulInsts _ _ _ (IsIn c [t1@(TCon (TyNum 1 _)), t2, _])
        = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t2]

-- (0, T, ?) : (0, T, 0)
genMulInsts _ _ _ (IsIn c [t1@(TCon (TyNum 0 _)), t2, _])
        = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t1]

-- (T, 1, ?) : (T, 1, T)
genMulInsts _ _ _ (IsIn c [t1, t2@(TCon (TyNum 1 _)), _])
        = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t1]

-- (T, 0, ?) : (T, 0, 0)
genMulInsts _ _ _ (IsIn c [t1, t2@(TCon (TyNum 0 _)), _])
        = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t2]

-- (?, T, T) : (1, T, T)
genMulInsts _ _ _ (IsIn c [_, t2, t3])
        | t2 == t3 = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t3]
        t1 = TCon (TyNum 1 (getPosition t2))

-- (T, ?, T) : (T, 1, T)
genMulInsts _ _ _ (IsIn c [t1, _, t3])
        | t1 == t3 = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t3]
        t2 = TCon (TyNum 1 (getPosition t1))

-- (T, T, C) : NumEq(T, sqrt(C)) => itself, when C is a perfect square
genMulInsts symT _ _ p@(IsIn c [t1, t2, TCon (TyNum n npos)])
    | t1 == t2, (Just sqrt_n) <- integerSqrt n
    = [ mkImpliedInst (IsIn clsNumEq [t1, TCon (TyNum sqrt_n npos)]) p ]
  where
    -- look up the class, rather than construct it, for better sharing
    clsNumEq = mustFindClass symT (CTypeclass idNumEq)

-- (T1, T2, TMul#(T1,T2)) : itself
-- (T1, T2, TMul#(T2,T1)) : itself
genMulInsts _ _ _ p@(IsIn c [t1, t2, t3])
    | t3 == cTApplys tMul [t1, t2] ||
      t3 == cTApplys tMul [t2, t1] = [ mkInst r ([] :=> p) (Just idPrelude) ]
 where r = anyTExpr (predToType p)

-- XXX The above rules are simple cases of this:
genMulInsts symT _ _ p@(IsIn c [t1, t2, t3])
    | (equalMulTerms b1 b2) = [ mkInst r ([] :=> p) (Just idPrelude) ]
 where b1 = toMulTerms (TAp (TAp tMul t1) t2)
       b2 = toMulTerms t3
       r = anyTExpr (predToType p)

-- (T1, T1, TMul#(T2, T2)) : NumEq(T1,T2) => itself
genMulInsts symT _ _ p@(IsIn c [t1,t1',t3])
    | t1 == t1', (tcon, [tA, tA']) <- splitTAp t3,
      tcon == tMul, tA == tA'
    = [ mkImpliedInst (IsIn clsNumEq [t1, tA]) p ]
  where
    -- look up the class, rather than construct it, for better sharing
    clsNumEq = mustFindClass symT (CTypeclass idNumEq)

-- XXX Not sure this is useful without a NotZero class
{-
-- (T1, T2, TMul#(T1,T3)) : NumEq(T2,T3) => itself
-- (T1, T2, TMul#(T3,T1)) : NumEq(T2,T3) => itself
--   when T1 /= 0, which can be expressed now as a condition on the structure
--        of T1 (e.g. it's a TyNum that is not 0) but later could be expressed
--        with a NotZero superclass
-- (T1, T2, TMul#(T2,T3)) : NumEq(T1,T3) => itself
-- (T1, T2, TMul#(T3,T1)) : NumEq(T1,T3) => itself
--   when T2 /= 0, which can be expressed now as a condition on the structure
--        of T1 (e.g. it's a TyNum that is not 0) but later could be expressed
--        with a NotZero superclass
genMulInsts symT _ _ p@(IsIn c [t1, t2, t3@(TAp (TAp tc tA) tB)])
    | tc == tMul,
      t1 == tA,
      -- when not zero
      isTNum t1, getTNum t1 /= 0
    = [ mkImpliedInst (IsIn clsNumEq [t2, tB]) p ]
    | tc == tMul,
      t1 == tB,
      -- when not zero
      isTNum t1, getTNum t1 /= 0
    = [ mkImpliedInst (IsIn clsNumEq [t2, tA]) p ]
    | tc == tMul,
      t2 == tA,
      -- when not zero
      isTNum t2, getTNum t2 /= 0
    = [ mkImpliedInst (IsIn clsNumEq [t1, tB]) p ]
    | tc == tMul,
      t2 == tB,
      -- when not zero
      isTNum t2, getTNum t2 /= 0
    = [ mkImpliedInst (IsIn clsNumEq [t1, tA]) p ]
  where
    -- look up the class, rather than construct it, for better sharing
    clsNumEq = mustFindClass symT (CTypeclass idNumEq)
-}

-- XXX The above and below rules could be generalized using MulTerms
-- XXX but we'd have to be careful about non-commutativity of TDiv and
-- XXX non-zeroness when crossing out TMul terms.
-- XXX For now, we settle for just reducing the constant terms.
genMulInsts symT _ _ p@(IsIn c [t1, t2, t3])
    | common_divisor > 1
    = [ mkImpliedInst (IsIn clsNumEq [t12',t3']) p]
 where b1 = toMulTerms (TAp (TAp tMul t1) t2)
       b2 = toMulTerms t3
       common_divisor = constIntersectionMulTerms b1 b2
       b1_rem = constDifferenceMulTerms b1 common_divisor
       b2_rem = constDifferenceMulTerms b2 common_divisor
       t12' = fromMulTerms b1_rem
       t3' = fromMulTerms b2_rem
       -- look up the class, rather than construct it, for better sharing
       clsNumEq = mustFindClass symT (CTypeclass idNumEq)

-- when satisfyFV, as a last resort, though, we can ignore the NotZero
-- requirement and see if things satisfy:
-- (T1, T2, TMul#(T1,T3)) : NumEq(T2,T3) => itself
-- (T1, T2, TMul#(T3,T1)) : NumEq(T2,T3) => itself
-- (T1, T2, TMul#(T2,T3)) : NumEq(T1,T3) => itself
-- (T1, T2, TMul#(T3,T1)) : NumEq(T1,T3) => itself
genMulInsts symT _ (Just _) p@(IsIn c [t1, t2, t3@(TAp (TAp tc tA) tB)])
    | tc == tMul,
      t1 == tA
    = [ mkImpliedInst (IsIn clsNumEq [t2, tB]) p ]
    | tc == tMul,
      t1 == tB
    = [ mkImpliedInst (IsIn clsNumEq [t2, tA]) p ]
    | tc == tMul,
      t2 == tA
    = [ mkImpliedInst (IsIn clsNumEq [t1, tB]) p ]
    | tc == tMul,
      t2 == tB
    = [ mkImpliedInst (IsIn clsNumEq [t1, tA]) p ]
  where
    -- look up the class, rather than construct it, for better sharing
    clsNumEq = mustFindClass symT (CTypeclass idNumEq)

-- when satisfyFV, as a last resort:
-- (T1, T2, V) : (T1, T2, TMul#(T1,T2))
--   when V is not bound or dependent and T1 and T2 contain only variables
--        which are bound or dependent
genMulInsts _ bvs (Just dvs) (IsIn c [t1,t2,tv@(TVar v)])
    | v `notElem` dvs,
      checkDVS dvs (t1, t2),
      mgu bvs tv t3 /= Nothing =
        [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t3]
        t3 = TAp (TAp tMul t1) t2

{-
genMulInsts (Just dvs) (IsIn c [t1,TVar v,t3]) | v `notElem` dvs =
        [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t3]
        t2 = TAp (TAp tDiv t3) t1

genMulInsts (Just dvs) (IsIn c [TVar v,t2,t3]) | v `notElem` dvs =
        [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t3]
        t1 = TAp (TAp tDiv t3) t2
-}

-- else, no instances to match
genMulInsts _ _ _ _ = []

-- -------------------------

-- Basic commutativity rules for Mul/TMul (similar to Add/TAdd).
-- However, since Div/TDiv round, they are not commutative, and are
-- therefore not included in this analysis (like Sub/TSub with Add/TAdd).

-- A bag of non-constant, non-TMul terms which have been multiplied;
-- and a product of constant terms
--  * The constant product may not be needed when the proviso reduces fully;
--    but when the proviso does not reduce, it allows us to make some
--    progress and hopefully report a slightly simpler proviso error.
--    It may also improve efficiency in the fully-reducible case by
--    avoiding having to do multiple steps of reduction.
data MulTerms = MulTerms Integer (B.Bag Type)

unionMulTerms :: MulTerms -> MulTerms -> MulTerms
unionMulTerms (MulTerms i1 mul_b1) (MulTerms i2 mul_b2) =
    MulTerms (i1 * i2) (B.union mul_b1 mul_b2)

singletonMulTerms :: Type -> MulTerms
singletonMulTerms (TCon (TyNum { tynum_value = n })) = MulTerms n B.empty
singletonMulTerms t = MulTerms 1 (B.singleton t)

toMulTerms :: Type -> MulTerms
toMulTerms (TAp (TAp tc t1) t2)
    | tc == tMul = unionMulTerms (toMulTerms t1) (toMulTerms t2)
toMulTerms t = singletonMulTerms t

fromMulTerms :: MulTerms -> Type
fromMulTerms (MulTerms 1 mul_b) =
    mkMulType (B.toList mul_b)
fromMulTerms (MulTerms i mul_b) =
    let it = cTNum i noPosition  -- XXX better position?
    in  mkMulType (it : B.toList mul_b)

mkMulType :: [Type] -> Type
mkMulType [] = cTNum 1 noPosition  -- XXX better position?
mkMulType mul_ts =
    let mkTMul t1 t2 = TAp (TAp tMul t1) t2
    in  foldr1 mkTMul mul_ts

equalMulTerms :: MulTerms -> MulTerms -> Bool
equalMulTerms (MulTerms i1 mul_b1) (MulTerms i2 mul_b2) =
    (i1 == i2) && (mul_b1 == mul_b2)

constIntersectionMulTerms :: MulTerms -> MulTerms -> Integer
constIntersectionMulTerms (MulTerms i1 _) (MulTerms i2 _) =
    gcd i1 i2

constDifferenceMulTerms :: MulTerms -> Integer -> MulTerms
constDifferenceMulTerms (MulTerms i mul_b) c =
    -- doesn't check that the constant is an integral divisor
    MulTerms (i `div` c) mul_b

-- -------------------------

clsDiv :: Class
clsDiv = Class {
        name = CTypeclass idDiv,
        csig = [tvarh1, tvarh2, tvarh3],
        super = [],  -- [IsIn clsSize [TVar tvarh1], IsIn clsSize [TVar tvarh2], IsIn clsSize [TVar tvarh3]]
        genInsts = genDivInsts,
        tyConOf = TyCon idDiv (Just (Kfun KNum (Kfun KNum (Kfun KNum KStar)))) (TIstruct SClass []),
        funDeps = [[False, False, True]],
        funDeps2 = [[Just False, Just False, Just True]],
        allowIncoherent = Just False,
        isComm = False,
        pkg_src = Just idPrelude
        }

genDivInsts :: [TyVar] -> Maybe [TyVar] -> Pred -> [Inst]

-- (C1, C2, ?) : (C1, C2, C1/C2)
genDivInsts _ _ (IsIn c [t1@(TCon (TyNum i1 pos)), t2@(TCon (TyNum i2 _)), _])
        = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t3]
        t3 = TCon (TyNum ((i1+i2-1) `div` i2) pos)

-- (T, 1, ?) : (T, 1, T)
genDivInsts _ _ (IsIn c [t1, t2@(TCon (TyNum 1 _)), _])
        = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t1]

-- XXX Add this?
-- (0, T, ?) : (0, T, 0)

-- (T1, T2, TDiv#(T1,T2)) : itself
genDivInsts _ _ (IsIn c [t1, t2, t3])
    | t3 == cTApplys tDiv [t1, t2] = [ mkInst r ([] :=> p) (Just idPrelude) ]
 where r = anyTExpr (predToType p)
       p = IsIn c [t1, t2, t3]

-- when satisfyFV, as a last resort:
-- (T1, T2, V) : (T1, T2, TDiv#(T1,T2))
--   when V is not bound or dependent and T1 and T2 contain only variables
--        which are bound or dependent
-- XXX need t2 /= 0 as well
genDivInsts bvs (Just dvs) (IsIn c [t1,t2,tv@(TVar v)])
    | v `notElem` dvs,
      checkDVS dvs (t1, t2),
      mgu bvs tv t3 /= Nothing =
        [ mkInst r ([] :=> p) (Just idPrelude) ]
  where r = anyTExpr (predToType p)
        p = IsIn c [t1, t2, t3]
        t3 = TAp (TAp tDiv t1) t2

-- else, no instances to match
genDivInsts _ _ _ = []

-- -------------------------

clsNumEq :: SymTab -> Class
clsNumEq symT =
       Class {
            name = CTypeclass idNumEq,
            csig = [tvarh1, tvarh2],
            super = [],
            genInsts = genNumEqInsts symT,
            tyConOf = TyCon idNumEq (Just kNNS) (TIstruct SClass []),
            funDeps  = [[False, True], [True, False]],
            funDeps2 = [[Just False, Just True], [Just True, Just False]],
            allowIncoherent = Just False,
            isComm = True,
            pkg_src = Just idPrelude
            }

genNumEqInsts :: SymTab ->  [TyVar] -> Maybe [TyVar] -> Pred -> [Inst]
-- safe base-case if t1 and t2 are syntactically equal
genNumEqInsts symT _ _ p@(IsIn c [t1, t2])
    | t1 == t2 = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where p = IsIn c [t1, t1]
        r = anyTExpr (predToType p)

-- reduce a requested equality to a simpler provisos
-- (i.e. fewer type functions)
genNumEqInsts symT _ _ p@(IsIn c [t, t'])
    | tcon == tAdd, [t1, t2] <- args = [ mkImpliedInst (IsIn clsAdd' [t1, t2, tB]) p ]
    | tcon == tSub, [t1, t2] <- args = [ mkImpliedInst (IsIn clsAdd' [t2, tB, t1]) p ]
    | tcon == tMul, [t1, t2] <- args = [ mkImpliedInst (IsIn clsMul' [t1, t2, tB]) p ]
    | tcon == tDiv, [t1, t2] <- args = [ mkImpliedInst (IsIn clsDiv [t1, t2, tB]) p ]
    | tcon == tMax, [t1, t2] <- args = [ mkImpliedInst (IsIn clsMax [t1, t2, tB]) p ]
    | tcon == tMin, [t1, t2] <- args = [ mkImpliedInst (IsIn clsMin [t1, t2, tB]) p ]
    | tcon == tLog, [t1] <- args     = [ mkImpliedInst (IsIn clsLog [t1, tB])     p ]
    -- we do NumEq (TExp a) (TExp b) ==> NumEq a b because more is tricky
    | tcon == tExp, [t1] <- args,
      (tcon2, args2) <- splitTAp tB,
      tcon2 == tExp, [t2] <- args2   = [ mkImpliedInst (IsIn c [t1, t2])       p ]
    | tcon == tSizeOf, [t1] <- args  = [ mkImpliedInst (IsIn clsBits [t1, tB]) p ]
  where clsBits = mustFindClass symT (CTypeclass idBits)
        -- look up the class, rather than construct it, for better sharing
        clsAdd' = mustFindClass symT (CTypeclass idAdd)
        clsMul' = mustFindClass symT (CTypeclass idMul)
        -- tA should have more structure since TAp sorts first
        (tA, tB) = ordPair (t, t')
        (tcon, args) = splitTAp tA

-- If one is a variable and the other has no tyvars, it's safe to unify them
genNumEqInsts _ _ _ (IsIn c [TVar {}, t2]) | null (tv t2)
    = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where p = IsIn c [t2, t2]
        r = anyTExpr (predToType p)
genNumEqInsts symT _ _ (IsIn c [t1, TVar {}]) | null (tv t1)
    = [ mkInst r ([] :=> p) (Just idPrelude) ]
  where p = IsIn c [t1, t1]
        r = anyTExpr (predToType p)

-- reduce away a generated type variable
genNumEqInsts symT bvs (Just dvs) (IsIn c [t1, t2])
    | TVar v <- tB, checkDVS dvs tA, mgu bvs tB tA /= Nothing,
      let p = IsIn c [tA, tA], let r = anyTExpr (predToType p) =
        --trace ("NumEq " ++ ppReadable (r, p)) $
        [ mkInst r ([] :=> p) (Just idPrelude) ]
  where (tA, tB) = ordPair (t1, t2)

genNumEqInsts _ _ _ _ = []

-- -------------------------

tiArrow, tiBit, tiSizeOf, tiInteger, tiReal :: TISort
tiArrow   = TIabstract
tiBit     = TIabstract
tiSizeOf  = TIabstract
tiInteger = TIabstract
tiReal    = TIabstract

tiClock, tiReset, tiInout, tiPrimArray :: TISort
tiClock   = TIabstract -- XXX TIstruct SInterface ... ?
tiReset   = TIabstract -- XXX TIstruct or Bit 1 ?
tiInout   = TIabstract
tiPrimArray = TIabstract

tiPair, tiBool, tiAction, tiRules, tiString, tiChar :: TISort
tiPair    = TIstruct SStruct [idPrimFst, idPrimSnd]
tiBool    = tiEnum [idFalse, idTrue]
tiAction  = TIabstract
tiRules   = TIabstract
tiString  = TIabstract
tiChar    = TIabstract

tiHandle, tiBufferMode, tiMaybe, tiList, tiFmt :: TISort
tiHandle  = TIabstract
tiBufferMode = tiEnum [idNoBuffering, idLineBuffering, idBlockBuffering]
tiMaybe   = tiData [idInvalid, idValid]
tiList    = tiData [idNil noPosition, idCons noPosition]
tiFmt     = TIabstract

tiUnit, tiPosition, tiType, tiName, tiPred, tiSchedPragma :: TISort
tiUnit    = TIstruct SStruct []
tiPosition = TIabstract
tiType = TIabstract
tiName = TIabstract
tiPred = TIabstract
tiSchedPragma = TIabstract

tyiArrow :: TypeInfo
tyiArrow   = TypeInfo (Just (idArrow noPosition)) (Kfun KStar (Kfun KStar KStar)) [] tiArrow (Just idPrelude)
{-
tyiBit     = TypeInfo (Just idBit) (Kfun KNum KStar) [] tiBit (Just idPrelude)
tyiInteger = TypeInfo (Just idInteger) KStar [] tiInteger (Just idPrelude)
-}

-- -------------------------

-- all preTypes should have identifiers (i.e. be non-numeric, non-string) because the usage in MakeSymTab.hs depends on this
preTypes :: [TypeInfo]
preTypes = [
        tyiArrow,
{-
        tyiBit,
        tyiInteger,
        TypeInfo  idString KStar              [] TIabstract (Just idPrelude),
        TypeInfo  idSizeOf (Kfun KStar KNum)  [] TIabstract (Just idPrelude),
-}
        TypeInfo (Just idAdd) (Kfun KNum (Kfun KNum (Kfun KNum KStar))) [v1, v2, v3] (TIstruct SClass []) (Just idPrelude),
        TypeInfo (Just idMax) (Kfun KNum (Kfun KNum (Kfun KNum KStar))) [v1, v2, v3] (TIstruct SClass []) (Just idPrelude),
        TypeInfo (Just idMin) (Kfun KNum (Kfun KNum (Kfun KNum KStar))) [v1, v2, v3] (TIstruct SClass []) (Just idPrelude),
        TypeInfo (Just idMul) (Kfun KNum (Kfun KNum (Kfun KNum KStar))) [v1, v2, v3] (TIstruct SClass []) (Just idPrelude),
        TypeInfo (Just idDiv) (Kfun KNum (Kfun KNum (Kfun KNum KStar))) [v1, v2, v3] (TIstruct SClass []) (Just idPrelude),
        TypeInfo (Just idLog) (Kfun KNum (Kfun KNum KStar)) [v1, v2] (TIstruct SClass []) (Just idPrelude),
        TypeInfo (Just idNumEq) (Kfun KNum (Kfun KNum KStar)) [v1, v2] (TIstruct SClass []) (Just idPrelude)
        ]

preClasses :: SymTab -> [Class]
preClasses symT = [clsNumEq symT,
                   clsAdd symT,
                   clsMax,
                   clsMin,
                   clsLog,
                   clsMul symT,
                   clsDiv ]

isPreClass :: Class -> Bool
isPreClass cl =
    let preClassNames = map name (preClasses (internalError "isPreClass"))
    in  (name cl) `elem` preClassNames

preValues :: [(Id, VarInfo)]
preValues = [
--        (idValueOf, VarInfo VarPrim (idValueOf :>: Forall [KNum] ([] :=> (TGen noPosition 0 `fn` tInteger))) Nothing)
        ]

-- -------------------------
