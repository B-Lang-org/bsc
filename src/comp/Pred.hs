{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
module Pred(
            Qual(..), PredWithPositions(..), Pred(..), Class(..), Inst(..),
            getInsts,
            removePredPositions, getPredPositions, addPredPositions, mkPredWithPositions,
            expandSyn, predToType, qualToType, mkInst,
            Instantiate(..),
            predToCPred, qualTypeToCQType,
            ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Data.List(union, genericSplitAt, genericLength)
import Eval
import ErrorUtil(internalError)
import Position
import Id
import IdPrint
import Type
import NumType
import PFPrint
import CSyntax(CExpr)
import CType
import CVPrint(pvPreds, pvParameterTypes)
import CSyntaxTypes

--import Debug.Trace
--import Util(traces)


--
-- Add position info to the predicates in a scheme, to allow position
-- info to carry on after type checking of implicitly typed definitions.
-- Schemes for other identifiers or purposes will contain empty lists.
--
data Qual t
        = [(PredWithPositions)] :=> t
        deriving (Eq, Ord, Show)

instance PPrint t => PPrint (Qual t) where
    pPrint d p ([] :=> t) = pparen (p>0) $ pPrint d p t
    pPrint d p (ps :=> t) = pparen (p>0) $ text "(" <> sepList (map (ppPred . removePredPositions) ps) (text ",") <> text ") =>" <+> pPrint d 0 t
        where ppPred (IsIn c []) = ppId d (typeclassId $ name c)
              ppPred (IsIn c ts) = ppId d (typeclassId $ name c) <+> sep (map (pPrint d 11) ts)

instance PVPrint t => PVPrint (Qual t) where
    pvPrint d p ([] :=> t) = pvparen (p>0) $ pvPrint d p t
    pvPrint d p (ps :=> t) = pvparen (p>0) $ pvPrint d 0 t <+> pvPreds d (map removePredPositions ps)

instance Types t => Types (Qual t) where
    apSub s (ps :=> t) = apSub s ps :=> apSub s t
    tv      (ps :=> t) = tv ps `union` tv t

instance (Hyper a) => Hyper (Qual a) where
    hyper (ps :=> t) y = hyper2 ps t y

qualTypeToCQType :: Qual Type -> CQType
qualTypeToCQType (pwps :=> t) = CQType ps t
  where ps = map (predToCPred . removePredPositions) pwps

-----

--
-- Allow some Preds to be tagged with position information
--
data PredWithPositions = PredWithPositions Pred [Position]
    deriving (Show)

mkPredWithPositions :: [Position] -> Pred -> PredWithPositions
mkPredWithPositions poss p = PredWithPositions p poss

removePredPositions :: PredWithPositions -> Pred
removePredPositions (PredWithPositions p poss) = p

getPredPositions :: PredWithPositions -> [Position]
getPredPositions (PredWithPositions p poss) = poss

addPredPositions :: PredWithPositions -> [Position] -> PredWithPositions
addPredPositions (PredWithPositions p poss) poss' =
    PredWithPositions p (poss ++ poss')

instance Eq PredWithPositions where
    (==) (PredWithPositions p1 _) (PredWithPositions p2 _) = (p1 == p2)
    (/=) x y = not (x == y)

instance Ord PredWithPositions where
    compare (PredWithPositions p1 _) (PredWithPositions p2 _) = compare p1 p2
    (<) (PredWithPositions p1 _) (PredWithPositions p2 _) = p1 < p2
    (<=) (PredWithPositions p1 _) (PredWithPositions p2 _) = p1 <= p2
    (>=) (PredWithPositions p1 _) (PredWithPositions p2 _) = p1 >= p2
    (>) (PredWithPositions p1 _) (PredWithPositions p2 _) = p1 > p2
    max p1 p2 = if (p1 <= p2) then p2 else p1
    min p1 p2 = if (p1 <= p2) then p1 else p2

instance PPrint PredWithPositions where
    pPrint d p (PredWithPositions pred _) = pPrint d p pred

instance PVPrint PredWithPositions where
    pvPrint d p (PredWithPositions pred _) = pvPrint d p pred

instance Types PredWithPositions where
    apSub s (PredWithPositions p poss) = PredWithPositions (apSub s p) poss
    tv      (PredWithPositions p poss) = tv p

instance Hyper PredWithPositions where
    hyper (PredWithPositions p poss) y = hyper2 p poss y

-----

data Pred
        = IsIn Class [Type]
        deriving (Eq, Ord, Show)

instance PPrint Pred where
    pPrint d p (IsIn c ts) = pparen (p>0) $ ppId d (typeclassId $ name c) <+> sep (map (pPrint d 10) ts)

instance PVPrint Pred where
    pvPrint d p (IsIn c ts) = pvparen (p>0) $ pvpId d (typeclassId $ name c) <> pvParameterTypes d ts

instance Types Pred where
    apSub s (IsIn c ts) = IsIn c $ expandSyn <$> apSub s ts
    tv      (IsIn c ts) = tv ts

instance Hyper Pred where
    hyper (IsIn c ts) y = hyper2 c ts y

predToCPred :: Pred -> CPred
predToCPred (IsIn c ts) = CPred (name c) ts

-----------------------------------------------------------------------------

data Class
        = Class {
            name  :: CTypeclass,
            csig  :: [TyVar],
            super :: [(CTypeclass, Pred)],
            tyConOf :: TyCon,
            funDeps :: [[Bool]],
            funDeps2 :: [[Maybe Bool]],
            genInsts :: [TyVar] -> Maybe [TyVar] -> Pred -> [Inst],
            allowIncoherent :: Maybe Bool, -- Just False = always coherent
                                           -- Just True  = always incoherent
                                           -- Nothing = flag-controlled
            isComm :: Bool -- if the class is commutative (used for Add and Mul)
        }

-- Instances are stored as a function, to support primitive numeric typeclasses
-- with an infinite number of instances (Add, Mul, etc).
-- For finite classes, the function ignores its arguments and just returns
-- the list of instances; so use this function to retrieve those instances.
getInsts :: Class -> [Inst]
getInsts c = genInsts c [] Nothing (IsIn cls [])
    where
      err s = internalError $ "getInsts: no " ++ show s
      cls = Class { name = CTypeclass(dummyId (err "dummyId")),
                    csig = err "csig",
                    super = err "super",
                    genInsts = err "getInsts",
                    tyConOf = err "tyConOf",
                    funDeps = err "funDeps",
                    funDeps2 = err "funDeps2",
                    allowIncoherent = err "allowIncoherent",
                    isComm = err "isComm"
                  }

instance Show Class where
    showsPrec p c =
        showString "(Class " .
                showsPrec 0 (name c) .
                showsPrec 0 (csig c) . showString " " .
                showsPrec 0 (super c) . showString " " .
                showsPrec 0 (funDeps c) .
                showString ")"

instance PPrint Class where
    pPrint d p c =
        text "(Class" <+>
        pPrint d 0 (name c) <>
        pPrint d 0 (csig c) <+>
        pPrint d 0 (super c) <+>
        pPrint d 0 (getInsts c) <+>
        pPrint d 0 (funDeps c) <>
        text ")"

instance PVPrint Class where
    pvPrint d p c = text "(Class" <+>
                pvPrint d 0 (name c) <>
                pvPrint d 0 (csig c) <+>
                pvPrint d 0 (super c) <+>
                pvPrint d 0 (getInsts c) <+>
                pvPrint d 0 (funDeps c) <>
                text ")"

instance Hyper Class where
    hyper (Class x1 x2 x3 x4 x5 x6 x7 x8 x9) y = hyper7 x1 x2 x3 x4 x5 x8 x9 y

instance Eq Class where
    c == c'  =  name c == name c'

instance Ord Class where
    c <= c'  = (name c, csig c) <= (name c', csig c')
    c `compare` c'  = (name c, csig c) `compare` (name c', csig c')

-- someone should comment what all these
-- things are that go into an Inst.
data Inst = Inst CExpr [TyVar] (Qual Pred)

instance Hyper Inst where
    hyper (Inst x1 x2 x3) y = hyper3 x1 x2 x3 y

mkInst :: CExpr -> Qual Pred -> Inst
mkInst e i = Inst e (tv i) i

instance Types Inst where
    apSub s (Inst e _ i) = Inst (apSub s e) [] (apSub s i)
    tv (Inst _ vs _) = vs

{-
instance Match Pred where
    match (IsIn c ts) (IsIn c' ts') | c == c'   = match ts ts'
                                    | otherwise = Nothing
-}

instance PPrint Inst where
    pPrint d p (Inst e _ qp) = text "(Inst" <+> pPrint d 10 e <+> pPrint d 10 qp <> text ")"

instance PVPrint Inst where
    pvPrint d p (Inst e _ qp) = text "(Inst" <+> pvPrint d 10 e <+> pvPrint d 10 qp <> text ")"

-----------------------------------------------------------------------------

expandSyn :: Type -> Type
expandSyn t0 = exp [] t0 []
  where exp syns (TAp f a) as = exp syns f (exp syns a [] : as)
        exp syns tt@(TCon (TyCon i _ (TItype n t))) as | i `elem` syns =
          internalError ("recursive type synonyms: " ++ ppReadable syns)
        exp syns tt@(TCon (TyCon i _ (TItype n t))) as =
            case genericSplitAt n as of
            (as1, as2) -> if genericLength as1 < n then
                              -- We have expanded a synonym that was not fully applied.
                              -- It is all right if `type S v1 ... vn = t vn' and vn doesn't
                              -- occur in t.
                              exp syns' (inst as1 (truncType (n - genericLength as1) (fromInteger n-1) t')) as2
                          else
                              exp syns' (inst as1 t') as2
          where syns' = i:syns
                t' = setTypePosition (getIdPosition i) t
        exp syns tt@(TCon (TyCon i _ _)) as | isTFun i = apTFun tt i as
        exp syns t as = foldl TAp t as

        truncType 0 _ t = t
        truncType k n (TAp t (TGen _ n')) | n == n' && notIn n t = truncType (k-1) (n-1) t
          where notIn _ (TVar _) = True
                notIn _ (TCon _) = True
                notIn v (TAp t1 t2) = notIn v t1 && notIn v t2
                notIn v (TGen _ n) = v /= n
                notIn v (TDefMonad _) = internalError "expandSyn,truncType (TDefMonad)"
        truncType k n t = internalError ("expandSyn,truncType\n" ++ ppReadable (k, n, t0, t))

isTFun :: Id -> Bool
isTFun i = i `elem` numOpNames

apTFun :: Type -> Id -> [Type] -> Type
apTFun _ i [TCon (TyNum x px), TCon (TyNum y py)] | Just n <- opNumT i [x, y] = TCon (TyNum n p')
  where p' = bestPosition px py
apTFun _ i [TCon (TyNum x px)] | Just n <- opNumT i [x] = TCon (TyNum n px)
apTFun t _ as = foldl TAp t as

-----------------------------------------------------------------------------

qualToType :: Qual Type -> Type
qualToType (qs :=> t) = foldr fn t (map (predToType . removePredPositions) qs)

predToType :: Pred -> Type
predToType (IsIn c ts) = cTApplys (TCon (tyConOf c)) ts

-----------------------------------------------------------------------------

class Instantiate t where
    inst  :: [Type] -> t -> t

instance Instantiate Type where
    inst ts (TAp l r) = TAp (inst ts l) (inst ts r)
    inst ts (TGen _ n)  = ts !! n
    inst ts t         = t

instance Instantiate a => Instantiate [a] where
    inst ts = map (inst ts)

instance Instantiate t => Instantiate (Qual t) where
    inst ts (ps :=> t) = inst ts ps :=> inst ts t

instance Instantiate PredWithPositions where
    inst ts (PredWithPositions p poss) = PredWithPositions (inst ts p) poss

instance Instantiate Pred where
    inst ts (IsIn c t) = IsIn c $ expandSyn <$> inst ts t

instance Instantiate Inst where
    inst ts (Inst e ks h) = Inst e [] (inst ts h)
