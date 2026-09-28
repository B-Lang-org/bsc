{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
module Pred(
            Qual(..), PredWithPositions(..), Pred(..), Class(..), Inst(..),
            removePredPositions, getPredPositions, addPredPositions, mkPredWithPositions,
            PredAncestor(..),
            getPredAncestors, mkPredAncestor, addPredAncestors,
            expandSyn, predToType, qualToType, mkInst,
            Instantiate(..),
            predToCPred, qualTypeToCQType,
            pureInputPositions,
            ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Data.List(union, genericSplitAt, genericLength)
import Eval
import Error(ErrMsg(..), internalError, bsErrorReallyUnsafe)
import Position
import Id
import IdPrint
import Type
import TypeOps
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

instance (NFData a) => NFData (Qual a) where
    rnf (ps :=> t) = rnf2 ps t

qualTypeToCQType :: Qual Type -> CQType
qualTypeToCQType (pwps :=> t) = CQType ps t
  where ps = map (predToCPred . removePredPositions) pwps

-----

--
-- Allow some Preds to be tagged with position information and with the
-- reduction chain that produced them
--

-- An ancestor of a residual predicate: a predicate that instance
-- reduction reduced (through an instance's context) to produce this one,
-- captured with the positions it carried at the time of the reduction.
-- The predicate is captured unsubstituted; apply the current substitution
-- (apSub) when rendering it in an error message.
data PredAncestor = PredAncestor Pred [Position]
    deriving (Show)

instance PPrint PredAncestor where
    pPrint d prec (PredAncestor p _) = pPrint d prec p

instance NFData PredAncestor where
    rnf (PredAncestor p poss) = rnf2 p poss

-- The ancestors are ordered nearest-first: the head is the predicate
-- this one was directly reduced from, and the last entry is the
-- user-written root.  The ancestors are carried inert: they are excluded
-- from substitution in the Types instance below, so the solver's
-- substitution application (a known cost center) does not traverse them;
-- apply the final substitution when rendering an error.  They are
-- likewise excluded from equality and comparison, as positions already
-- are.
data PredWithPositions = PredWithPositions Pred [Position] [PredAncestor]
    deriving (Show)

mkPredWithPositions :: [Position] -> Pred -> PredWithPositions
mkPredWithPositions poss p = PredWithPositions p poss []

removePredPositions :: PredWithPositions -> Pred
removePredPositions (PredWithPositions p poss anc) = p

getPredPositions :: PredWithPositions -> [Position]
getPredPositions (PredWithPositions p poss anc) = poss

addPredPositions :: PredWithPositions -> [Position] -> PredWithPositions
addPredPositions (PredWithPositions p poss anc) poss' =
    PredWithPositions p (poss ++ poss') anc

getPredAncestors :: PredWithPositions -> [PredAncestor]
getPredAncestors (PredWithPositions p poss anc) = anc

-- Capture a predicate (with its positions) as an ancestor entry.
mkPredAncestor :: PredWithPositions -> PredAncestor
mkPredAncestor (PredWithPositions p poss anc) = PredAncestor p poss

-- Record the reduction chain a predicate came from (appended after any
-- ancestors it already has, preserving nearest-first order).
addPredAncestors :: PredWithPositions -> [PredAncestor] -> PredWithPositions
addPredAncestors (PredWithPositions p poss anc) anc' =
    PredWithPositions p poss (anc ++ anc')

-- NOTE: the reporting rule for choosing which entry of an ancestry
-- chain to show the user is NOT "the last ancestor": reportedPwp
-- (ContextErrors) reports the root-most non-numeric-class entry, with
-- position merging.  Keep that logic there; do not add a simplistic
-- root accessor here.

instance Eq PredWithPositions where
    (==) (PredWithPositions p1 _ _) (PredWithPositions p2 _ _) = (p1 == p2)
    (/=) x y = not (x == y)

instance Ord PredWithPositions where
    compare (PredWithPositions p1 _ _) (PredWithPositions p2 _ _) = compare p1 p2
    (<) (PredWithPositions p1 _ _) (PredWithPositions p2 _ _) = p1 < p2
    (<=) (PredWithPositions p1 _ _) (PredWithPositions p2 _ _) = p1 <= p2
    (>=) (PredWithPositions p1 _ _) (PredWithPositions p2 _ _) = p1 >= p2
    (>) (PredWithPositions p1 _ _) (PredWithPositions p2 _ _) = p1 > p2
    max p1 p2 = if (p1 <= p2) then p2 else p1
    min p1 p2 = if (p1 <= p2) then p1 else p2

instance PPrint PredWithPositions where
    pPrint d p (PredWithPositions pred _ _) = pPrint d p pred

instance PVPrint PredWithPositions where
    pvPrint d p (PredWithPositions pred _ _) = pvPrint d p pred

instance Types PredWithPositions where
    -- the ancestors are deliberately not substituted (see above)
    apSub s (PredWithPositions p poss anc) = PredWithPositions (apSub s p) poss anc
    tv      (PredWithPositions p poss anc) = tv p

instance NFData PredWithPositions where
    rnf (PredWithPositions p poss anc) = rnf3 p poss anc

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

instance NFData Pred where
    rnf (IsIn c ts) = rnf2 c ts

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
            inputPositions :: [Int],      -- pure-input positions for PredTrie (pureInputPositions funDeps (length csig))
                                          -- empty when all positions are outputs: trie degenerates to a flat list
            genInsts :: [TyVar] -> Maybe [TyVar] -> Pred -> [Inst],
            getInsts :: [Inst],           -- flat list for display/analysis
            allowIncoherent :: Maybe Bool, -- Just False = always coherent
                                           -- Just True  = always incoherent
                                           -- Nothing = flag-controlled
            isComm :: Bool, -- if the class is commutative (used for Add and Mul)
            pkg_src :: Maybe Id, -- package from which this class came
            assocTypes :: [(TyCon, [Int], Int)]
        }

instance Show Class where
    showsPrec p c =
        showString "(Class " .
                showsPrec 0 (name c) .
                showsPrec 0 (csig c) . showString " " .
                showsPrec 0 (super c) . showString " " .
                showsPrec 0 (funDeps c) .
                showsPrec 0 (assocTypes c) .
                showString ")"

instance PPrint Class where
    pPrint d p c =
        text "(Class" <+>
        pPrint d 0 (name c) <>
        pPrint d 0 (csig c) <+>
        pPrint d 0 (super c) <+>
        pPrint d 0 (getInsts c) <+>
        pPrint d 0 (funDeps c) <+>
        pPrint d 0 (assocTypes c) <>
        text ")"

instance PVPrint Class where
    pvPrint d p c = text "(Class" <+>
                pvPrint d 0 (name c) <>
                pvPrint d 0 (csig c) <+>
                pvPrint d 0 (super c) <+>
                pvPrint d 0 (getInsts c) <+>
                pvPrint d 0 (funDeps c) <+>
                pvPrint d 0 (assocTypes c) <>
                text ")"

instance NFData Class where
    rnf c = rnf (name c)            `seq`
            rnf (csig c)            `seq`
            rnf (super c)           `seq`
            rnf (tyConOf c)         `seq`
            rnf (funDeps c)         `seq`
            rnf (inputPositions c)  `seq`
            -- funDeps2, genInsts, getInsts intentionally not forced
            rnf (allowIncoherent c) `seq`
            rnf (isComm c)          `seq`
            rnf (pkg_src c)         `seq`
            rnf (assocTypes c)

instance Eq Class where
    c == c'  =  name c == name c'

instance Ord Class where
    c <= c'  = (name c, csig c) <= (name c', csig c')
    c `compare` c'  = (name c, csig c) `compare` (name c', csig c')

-- | Compute Class.inputPositions from the functional-dependency matrix and arity.
-- Returns positions that are False (input) in ALL fundep directions.
-- When empty (all positions are outputs in some direction), the PredTrie
-- degenerates to a flat list and returns all instances for any query.
pureInputPositions :: [[Bool]] -> Int -> [Int]
pureInputPositions bss n = [ i | i <- [0 .. n - 1], not (any (!! i) bss) ]

-- someone should comment what all these
-- things are that go into an Inst.
data Inst = Inst CExpr [TyVar] (Qual Pred) (Maybe Id)
                                            -- ^ source package (Nothing = current package)

instance NFData Inst where
    rnf (Inst x1 x2 x3 x4) = rnf4 x1 x2 x3 x4

mkInst :: CExpr -> Qual Pred -> Maybe Id -> Inst
mkInst e i pkg = Inst e (tv i) i pkg

instance Types Inst where
    apSub s (Inst e _ i pkg) = Inst (apSub s e) [] (apSub s i) pkg
    tv (Inst _ vs _ _) = vs

{-
instance Match Pred where
    match (IsIn c ts) (IsIn c' ts') | c == c'   = match ts ts'
                                    | otherwise = Nothing
-}

instance PPrint Inst where
    pPrint d p (Inst e _ qp pkg) = text "(Inst" <+> pPrint d 10 e <+> pPrint d 10 qp <+> pPrint d 10 pkg <> text ")"

instance PVPrint Inst where
    pvPrint d p (Inst e _ qp pkg) = text "(Inst" <+> pvPrint d 10 e <+> pvPrint d 10 qp <+> pvPrint d 10 pkg <> text ")"

-----------------------------------------------------------------------------

expandSyn :: Type -> Type
expandSyn t0 = exp [] f as
  where (f, as) = splitTAp t0
        -- All type applications should be split before entering exp
        exp _ f@(TAp _ _) as = internalError $ "expandSyn.exp Unexpected TAp: " ++ ppReadable (f, as)
        exp syns (TCon (TyCon i _ (TItype n t))) as
          -- This probably never happens because recursive type synonyms are caught
          -- when making the symbol table, but it is better to produce a proper error
          -- if something sneaks through.
          | i `elem` syns = bsErrorReallyUnsafe [(getPosition syns, ETypeSynRecursive (map pfpString syns))]
          -- We are implementing LiberalTypeSynonyms, which means expanding type synonyms
          -- like macros as far as possible before doing any consistency checks.
          -- However, expandSyn is only called in contexts (user source code, arguments
          -- to non-synonym type applications) where a concrete type is expected
          -- post-expansion. If we have a partially applied type synonym in such a
          -- context (which includes the eventual return from exp), it is an error.
          | let numArgs = genericLength as,
            numArgs < n = bsErrorReallyUnsafe [(getPosition i, EPartialTypeApp (pfpString i) n numArgs)]
          -- We have a synonym we can expand, so do so.
          | otherwise = let (as1, as2) = genericSplitAt n as
                            t' = setTypePosition (getIdPosition i) t
                            (f', as') = splitTAp $ inst as1 t'
                        in exp (i:syns) f' (as' ++ as2)
        -- Type functions (TIatf) are NOT expanded here; they are handled by
        -- normT via expTFun, which generates the appropriate class constraint.
        exp _ f@(TCon (TyCon i _ _)) as
          | isPrimTFunName i = apTFun f i $ map expandSyn as
        -- f does not contain a TAp or a synonym TCon, so it cannot have synonyms to expand
        exp _ f as = foldl TAp f $ map expandSyn as

apTFun :: Type -> Id -> [Type] -> Type
apTFun _ i [TCon (TyNum x px), TCon (TyNum y py)] | Just n <- opNumT i [x, y] = TCon (TyNum n p')
  where p' = bestPosition px py
apTFun _ i [TCon (TyNum x px)] | Just n <- opNumT i [x] = TCon (TyNum n px)
apTFun _ i [TCon (TyStr x px), TCon (TyStr y py)] | Just s <- opStrT i [x, y] = TCon (TyStr s p')
  where p' = bestPosition px py
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
    -- ancestors are carried inert, as in the Types instance
    inst ts (PredWithPositions p poss anc) = PredWithPositions (inst ts p) poss anc

instance Instantiate Pred where
    inst ts (IsIn c t) = IsIn c $ expandSyn <$> inst ts t

instance Instantiate Inst where
    inst ts (Inst e ks h pkg) = Inst e [] (inst ts h) pkg
