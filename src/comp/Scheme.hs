{-# LANGUAGE CPP #-}
module Scheme(Scheme(..), quantify, toScheme) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import CType
import Type
import Subst
import Pred
import PFPrint
import Position(noPosition, HasPosition(..))
import Eval(NFData(..), rnf2)

-- a scheme is a (possibly qualified) type polymorphic over some type variables
-- referred to as TGen n (where n is the index in the [Kind] list)
data Scheme = Forall [Kind] (Qual Type)
              deriving (Eq, Show)

instance PPrint Scheme where
  pPrint d p (Forall ks qt) = pparen (p>0) $
    foldr (\ (t,k) r -> text "/\\ (" <> pPrint d 0 t <+> text "::" <+> pPrint d 0 k <> text ") ." <+> r) (pPrint d 0 qt)
    (zip (map (TGen noPosition) [0..]) ks)

instance PVPrint Scheme where
  pvPrint d p (Forall ks qt) = pparen (p>0) $
    foldr (\ (t,k) r -> text "/\\ (" <> pPrint d 0 t <+> text "::" <+> pPrint d 0 k <> text ") ." <+> r) (pvPrint d 0 qt)
    (zip (map (TGen noPosition) [0..]) ks)

instance Types Scheme where
    apSub s (Forall ks qt) = Forall ks (apSub s qt)
    tv      (Forall ks qt) = tv qt

instance NFData Scheme where
    rnf (Forall ks qt) = rnf2 ks qt

-- turn a qualified type (qt) into a scheme over some type variables (vs)
-- the reverse of quantify is inst (q.v.)
quantify :: [TyVar] -> Qual Type -> Scheme
quantify vs qt@(ps :=> t) =
        Forall ks (apSub s qt)
  where vs' = [ v | v <- tv qt, v `elem` vs ]
        ks  = map kind vs'
        s   = mkSubst (zipWith (\ v n -> (v, TGen (getPosition v) n)) vs' [0..])

-- turn an unqualified type (t) into a type scheme over no variables
toScheme :: Type -> Scheme
toScheme t = Forall [] ([] :=> t)
