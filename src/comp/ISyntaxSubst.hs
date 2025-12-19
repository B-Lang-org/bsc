module ISyntaxSubst(
        tSubst,
        eSubst,
        etSubst
) where

import ISyntax
import Eval
import Id
import qualified Data.Set as S

-- ============================================================
-- Single substitution functions moved from ISyntax

-- Type substitution
tSubst :: Id -> IType -> IType -> IType
tSubst v x t = sub t
  where sub tt@(ITForAll i k t)
          | v == i = tt
          | i `S.member` fvx =
              let i' = cloneId (S.toList vs) i
                  t' = tSubst i (ITVar i') t
              in  ITForAll i' k (sub t')
          | otherwise = ITForAll i k (sub t)
        sub (ITAp f a) = normITAp (sub f) (sub a)
        sub tt@(ITVar i) = if i == v then x else tt
        sub tt@(ITCon _ _ _) = tt
        sub tt@(ITNum _) = tt
        sub tt@(ITStr _) = tt
        fvx = fTVars x
        vs = fvx `S.union` aTVars t

eSubst :: Id -> IExpr a -> IExpr a -> IExpr a
eSubst v x e = deepseq e' e'
  where e' = sub e
        sub ee@(ILam i t e)
            | v == i = ee
            | i `S.member` fvx =
              let i' = cloneId (S.toList vs) i
                  e' = eSubst i (IVar i') e
              in  ILam i' t (sub e')
            | otherwise = ILam i t (sub e)
--        sub ee@(IVar i) = if i == v then setPos (getIdPosition i) x else ee
        sub ee@(IVar i) = if i == v then x else ee
        sub (ILAM i k e) = ILAM i k (sub e)
        sub (IAps f ts es) = IAps (sub f) ts (map sub es)
        -- don't sub into ICUndet's optional variable because it doesn't get
        -- populated until after evaluation
        sub ee@(ICon _ _) = ee
        sub ee@(IRefT _ _ _) = ee        -- no free vars inside IRefT
        fvx = fVars x
        vs = fvx `S.union` aVars e
{-
        setPos p (ICon i ci) = ICon (setIdPosition p i) ci
        setPos p (IVar i) = IVar (setIdPosition p i)
--        setPos p (IAps e ts es) = IAps (setPos p e) ts es
        setPos p e = e
-}

-- --------------------

etSubst :: Id -> IType -> IExpr a -> IExpr a
etSubst v x e = sub e
  where sub (ILam i t e) = ILam i (tSubst v x t) (etSubst v x e)
        sub ee@(IVar i) = ee
        sub ee@(ILAM i k e)
            | v == i = ee
            | i `S.member` fvx =
                let i' = cloneId (S.toList vs) i
                    e' = etSubst i (ITVar i') e
                in  ILAM i' k (sub e')
            | otherwise = ILAM i k (sub e)
        sub (IAps f ts es) = IAps (sub f) (map (tSubst v x) ts) (map sub es)
        sub (ICon i ii@(ICUndet { })) = ICon i (ii { iConType = tSubst v x (iConType ii) })
        sub (ICon i ii@(ICVerilog { })) = ICon i (ICVerilog { iConType = tSubst v x (iConType ii),
                                                              isUserImport = isUserImport ii,
                                                              vMethTs = map (map (tSubst v x)) (vMethTs ii),
                                                              vInfo = vInfo ii
                                                            })
        sub (ICon i ii@(ICInt { })) = ICon i (ii { iConType = tSubst v x (iConType ii) })
        sub (ICon i ii@(ICStateVar { })) = ICon i (ii { iConType = tSubst v x (iConType ii) })
        sub (ICon i ii@(ICMethArg { })) = ICon i (ii { iConType = tSubst v x (iConType ii) })
        sub (ICon i ii@(ICModPort { })) = ICon i (ii { iConType = tSubst v x (iConType ii) })
        sub (ICon i ii@(ICModParam { })) = ICon i (ii { iConType = tSubst v x (iConType ii) })
        sub (ICon i ii@(ICForeign { })) = ICon i (ii { iConType = tSubst v x (iConType ii) })
        sub (ICon i ii@(ICType { })) = ICon i (ii { iType = tSubst v x (iType ii) })
        sub ee@(ICon _ _) = ee
        sub ee@(IRefT _ _ _) = ee        -- no free tyvar inside IRef
        fvx = fTVars x
        vs = fvx `S.union` aVars e
