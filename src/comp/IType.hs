{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}

module IType(
  IType(..)
  ,IKind(..)
  ,itArrow
  ,iToCT
  ,iToCK
   )
    where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import ErrorUtil(internalError)
import Id(Id)
import PreIds(idArrow)
import CType(Type(..), CType, TyCon(..), Kind(..),
             TISort, cTApplys, cTVar, cTCon, cTNum)
import StdPrel(tiArrow)
import Eval(Hyper(..),hyper3, hyper2, hyper)
import PPrint
import PFPrint
import Position(noPosition)
import Util(itos)
import qualified Data.Generics as Generic

-- ==============================
-- IKind, IType

data IKind
        = IKStar
        | IKNum
        | IKFun IKind IKind
        deriving (Eq, Ord, Show, Generic.Data, Generic.Typeable)

data IType
        = ITForAll Id IKind IType
        | ITAp IType IType
        | ITVar Id
        | ITCon Id IKind TISort
        | ITNum Integer
        deriving (Show, Generic.Data, Generic.Typeable)

-- --------------------------------
-- Hyper Instances
instance Hyper IType where
    hyper (ITForAll i k t) y = hyper3 i k t y
    hyper (ITAp a b) y = hyper2 a b y
    hyper (ITVar i) y = hyper i y
    hyper (ITCon i k s) y = hyper3 i k s y
    hyper (ITNum i) y = hyper i y

instance Hyper IKind where
    hyper IKStar y = y
    hyper IKNum y = y
    hyper (IKFun a b) y = hyper2 a b y

-- --------------------------------
-- Eq Instances
instance Eq IType where
    x == y  =  cmpT x y == EQ
    x /= y  =  cmpT x y /= EQ

instance Ord IType where
    compare x y = cmpT x y

cmpT :: IType -> IType -> Ordering
cmpT (ITForAll i1 _ t1) (ITForAll i2 _ t2) =  -- kind comparison skipped for speed
        case compare i1 i2 of
        EQ -> cmpT t1 t2
        o  -> o
cmpT (ITForAll _  _  _ ) _                   = LT

cmpT (ITAp _ _)          (ITForAll _  _  _)  = GT
cmpT (ITAp f1 a1)        (ITAp f2 a2)        =
        case cmpT f1 f2 of
        EQ -> cmpT a1 a2
        o  -> o
cmpT (ITAp _  _)         _                   = LT

cmpT (ITVar _)           (ITForAll _  _  _)  = GT
cmpT (ITVar _)           (ITAp _  _)         = GT
cmpT (ITVar i1)          (ITVar i2)          = compare i1 i2
cmpT (ITVar _)           _                   = LT

cmpT (ITCon _  _ _)      (ITForAll _  _  _)  = GT
cmpT (ITCon _  _ _)      (ITAp _ _)          = GT
cmpT (ITCon _  _ _)      (ITVar _)           = GT
cmpT (ITCon i1 _ _)      (ITCon i2 _ _)      = compare i1 i2
cmpT (ITCon _  _ _)      _                   = LT

cmpT (ITNum n1)          (ITNum n2)          = compare n1 n2
cmpT (ITNum _)           _                   = GT

-- -----------------------------------------
-- Pretty Print instances PPrint and PVPrint

instance PPrint IKind where
    pPrint _ _ IKStar = text "*"
    pPrint _ _ IKNum = text "#"
    pPrint d p (IKFun l r) = pparen (p>9) $ pPrint d 9 l <+> text "->" <+> pPrint d 10 r

instance PPrint IType where
    pPrint d p (ITForAll i k t) = ppQuant "\\/" d p i k t
    pPrint d p (ITAp (ITAp arr a) r) | arr == itArrow =
        pparen (p > 8) (sep [pPrint d 9 a <+> text "->", pPrint d 8 r])
    pPrint d p (ITAp e e') = pparen (p>9) $
        sep [pPrint d 9 e, pPrint d 10 e']
    pPrint d p (ITVar i) = pPrint d 0 i
    pPrint d p (ITCon c _ _) = pPrint d 0 c
    pPrint d p (ITNum n) = text (itos n)

instance PVPrint IType where
    -- convert to CType and use the PVPrint instance for that
    pvPrint d p ity =
        let convITyToCTy (ITForAll _ _ t) = convITyToCTy t
            convITyToCTy (ITAp t1 t2)  = cTApplys (convITyToCTy t1)
                                                  [convITyToCTy t2]
            convITyToCTy (ITVar i)     = cTVar i
            convITyToCTy (ITCon i _ _) = cTCon i
            convITyToCTy (ITNum n)     = cTNum n noPosition
        in  pvPrint d p (convITyToCTy ity)

-- ---------------------------------------------------
-- Other utility functions

-- Function type (a -> b)
itArrow :: IType
itArrow = ITCon (idArrow noPosition) (IKFun IKStar (IKFun IKStar IKStar)) tiArrow

-- Pretty print ITForAll
ppQuant :: String -> PDetail -> Int -> Id -> IKind -> IType -> Doc
ppQuant s d p i t e =
    pparen (p>0) (sep [text s <> pparen True (pPrint d 0 i <>text" ::" <+> pPrint d 0 t) <+> text ".", pPrint d 0 e])

-- ---------------------------------------------------
-- Convert ISyntax kinds/types to CType

iToCT :: IType -> CType
iToCT (ITForAll _ _ _) = internalError "IConv.iToCT: ITForAll"
iToCT (ITAp t1 t2) = TAp (iToCT t1) (iToCT t2)
iToCT (ITVar i) = internalError "IConv.iToCT: ITVar"
iToCT (ITCon i k s) = TCon (TyCon i (Just (iToCK k)) s)
iToCT (ITNum n) = TCon (TyNum n noPosition)

iToCK :: IKind -> Kind
iToCK (IKStar) = KStar
iToCK (IKNum) = KNum
iToCK (IKFun k1 k2) = Kfun (iToCK k1) (iToCK k2)
