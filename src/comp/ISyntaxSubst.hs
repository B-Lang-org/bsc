{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ISyntaxSubst(
        -- Public API
        tSubst,
        eSubst,
        etSubst,
        tSubstBatch,
        eSubstBatch,
        -- Internal types (exposed for testing/debugging)
        SubstContext(..),
        SomeCtx(..),
        EmptyExpr(..),
        SingleExpr(..),
        BatchExpr(..),
        EmptyType(..),
        SingleType(..),
        BatchType(..),
        ExprSubstCtx,
        TypeSubstCtx,
        eSubstWith
) where

import ISyntax
import Eval
import Id
import Data.Maybe(fromMaybe, isJust)
import qualified Data.Set as S
import qualified Data.Map as M

-- ============================================================
-- Substitution contexts

-- Existential wrapper for when context type changes
data SomeCtx v where
  SomeCtx :: SubstContext ctx v => ctx -> SomeCtx v

-- Type family for batch context types
type family BatchCtx v where
  BatchCtx (IExpr a) = BatchExpr a
  BatchCtx IType = BatchType

-- Typeclass for substitution contexts (unified for expr and type)
class SubstContext ctx v | ctx -> v where
  lookupVar :: Id -> ctx -> Maybe v
  ctxIsEmpty :: ctx -> Bool
  ctxContainsVar :: Id -> ctx -> Bool
  ctxRemove :: Id -> ctx -> SomeCtx v
  ctxAdd :: Id -> v -> ctx -> BatchCtx v

-- Constraint synonyms for clarity
type ExprSubstCtx ctx a = SubstContext ctx (IExpr a)
type TypeSubstCtx ctx = SubstContext ctx IType

-- ============================================================
-- Expression substitution contexts

-- Empty context (size 0)
data EmptyExpr a = EmptyExpr

instance SubstContext (EmptyExpr a) (IExpr a) where
  lookupVar _ _ = Nothing
  ctxIsEmpty _ = True
  ctxContainsVar _ _ = False
  ctxRemove _ _ = SomeCtx (EmptyExpr :: EmptyExpr a)
  ctxAdd _ _ _ = error "ctxAdd on EmptyExpr: impossible (no free vars to cause alpha-conversion)"

-- Single substitution (size 1) - uses direct equality, no Map
data SingleExpr a = SingleExpr !Id !(IExpr a) !(S.Set Id)

instance SubstContext (SingleExpr a) (IExpr a) where
  lookupVar i' (SingleExpr i x _) = if i == i' then Just x else Nothing
  ctxIsEmpty _ = False
  ctxContainsVar i' (SingleExpr _ _ fvs) = i' `S.member` fvs
  ctxRemove i' s@(SingleExpr i _ _) =
    if i == i' then SomeCtx (EmptyExpr :: EmptyExpr a) else SomeCtx s
  ctxAdd i' x' (SingleExpr i x fvs) =
    BatchExpr (M.fromList [(i,x), (i',x')]) (fvs `S.union` fVars x')

-- Batch substitution (size >= 2) - uses Map
data BatchExpr a = BatchExpr !(M.Map Id (IExpr a)) !(S.Set Id)

instance SubstContext (BatchExpr a) (IExpr a) where
  lookupVar i (BatchExpr m _) = M.lookup i m
  ctxIsEmpty _ = False  -- BatchExpr always has size >= 2
  ctxContainsVar i (BatchExpr _ fvs) = i `S.member` fvs
  ctxRemove i (BatchExpr m fvs) =
    let m' = M.delete i m
    in case M.size m' of
         0 -> SomeCtx (EmptyExpr :: EmptyExpr a)
         1 -> let (j, x) = M.findMin m'
              in SomeCtx $ SingleExpr j x fvs
         _ -> SomeCtx $ BatchExpr m' fvs
  ctxAdd i x (BatchExpr m fvs) =
    BatchExpr (M.insert i x m) (fvs `S.union` fVars x)

-- ============================================================
-- Type substitution contexts

-- Empty type context
data EmptyType = EmptyType

instance SubstContext EmptyType IType where
  lookupVar _ _ = Nothing
  ctxIsEmpty _ = True
  ctxContainsVar _ _ = False
  ctxRemove _ _ = SomeCtx EmptyType
  ctxAdd _ _ _ = error "ctxAdd on EmptyType: impossible (no free vars to cause alpha-conversion)"

-- Single type substitution
data SingleType = SingleType !Id !IType !(S.Set Id)

instance SubstContext SingleType IType where
  lookupVar i' (SingleType i t _) = if i == i' then Just t else Nothing
  ctxIsEmpty _ = False
  ctxContainsVar i' (SingleType _ _ fvs) = i' `S.member` fvs
  ctxRemove i' s@(SingleType i _ _) =
    if i == i' then SomeCtx EmptyType else SomeCtx s
  ctxAdd i' t' (SingleType i t fvs) =
    BatchType (M.fromList [(i,t), (i',t')]) (fvs `S.union` fTVars t')

-- Batch type substitution
data BatchType = BatchType !(M.Map Id IType) !(S.Set Id)

instance SubstContext BatchType IType where
  lookupVar i (BatchType m _) = M.lookup i m
  ctxIsEmpty _ = False
  ctxContainsVar i (BatchType _ fvs) = i `S.member` fvs
  ctxRemove i (BatchType m fvs) =
    let m' = M.delete i m
    in case M.size m' of
         0 -> SomeCtx EmptyType
         1 -> let (j, t) = M.findMin m'
              in SomeCtx $ SingleType j t fvs
         _ -> SomeCtx $ BatchType m' fvs
  ctxAdd i t (BatchType m fvs) =
    BatchType (M.insert i t m) (fvs `S.union` fTVars t)

-- ============================================================
-- Type substitution

-- Internal type substitution with context
{-# SPECIALIZE tSubstWith :: EmptyType -> S.Set Id -> IType -> (IType, Bool) #-}
{-# SPECIALIZE tSubstWith :: SingleType -> S.Set Id -> IType -> (IType, Bool) #-}
{-# SPECIALIZE tSubstWith :: BatchType -> S.Set Id -> IType -> (IType, Bool) #-}
tSubstWith :: TypeSubstCtx tctx => tctx -> S.Set Id -> IType -> (IType, Bool)
tSubstWith tctx allIds t
    | ctxIsEmpty tctx = (t, False)
    | otherwise = sub tctx allIds t
  where
    -- sub needs to be polymorphic because the context type can change at
    -- ctxAdd (to batch) or ctxRemove (to single or empty)
    sub :: TypeSubstCtx tctx' => tctx' -> S.Set Id -> IType -> (IType, Bool)
    sub tctx allIds tt@(ITForAll i k t) =
      case lookupVar i tctx of
        Just _ ->
          -- Variable shadowed: remove from context and continue
          -- We reprocess tt because it is possible i is in the free vars
          -- of the context, so we will need alpha-conversion.
          -- We call tSubstWith so that we check if the context is now empty.
          case ctxRemove i tctx of
            SomeCtx tctx' -> tSubstWith tctx' allIds tt
        Nothing ->
          if ctxContainsVar i tctx
          then -- Alpha-conversion needed: add renaming and continue
            let i'      = cloneId (S.toList allIds) i
                tctx'   = ctxAdd i (ITVar i') tctx
                allIds' = S.insert i' allIds
            in (ITForAll i' k (fst $ sub tctx' allIds' t), True)
          else -- No conflict: continue with same context
            let (t', t_changed) = sub tctx allIds t
            in if t_changed
               then (ITForAll i k t', True)
               else (tt, False)
    sub tctx allIds tt@(ITAp f a)
      | changed = (normITAp f' a', True)
      | otherwise = (tt, False)
      where (f', f_changed) = sub tctx allIds f
            (a', a_changed) = sub tctx allIds a
            changed = f_changed || a_changed
    sub tctx _      tt@(ITVar i) = (fromMaybe tt mt, isJust mt)
      where mt = lookupVar i tctx
    sub _    _      tt@(ITCon _ _ _) = (tt, False)
    sub _    _      tt@(ITNum _) = (tt, False)
    sub _    _      tt@(ITStr _) = (tt, False)

-- Public API: single type substitution
{-# INLINE tSubst #-}
tSubst :: Id -> IType -> IType -> IType
tSubst i t ty = fst $ tSubstWith (SingleType i t (fTVars t)) (fTVars t `S.union` aTVars ty) ty

-- Public API: batch type substitution
{-# INLINE tSubstBatch #-}
tSubstBatch :: M.Map Id IType -> IType -> IType
tSubstBatch typeMap t
  | M.null typeMap = t
  | M.size typeMap == 1 =
      let (i, ty) = M.findMin typeMap
      in tSubst i ty t
  | otherwise =
      let ftx = S.unions (M.elems (M.map fTVars typeMap))
          tctx = BatchType typeMap ftx
          allIds = ftx `S.union` aTVars t
      in fst $ tSubstWith tctx allIds t

-- ============================================================
-- Expression and type substitution

-- Helper: apply type substitution function to IConInfo
tSubstIConInfo :: (IType -> (IType, Bool)) -> IConInfo a -> (IConInfo a, Bool)
tSubstIConInfo tsubFn ii@(ICVerilog { })
  | t_changed || vts_changed = (ii { iConType = t', vMethTs = vts' }, True)
  | otherwise = (ii, False)
  where (t', t_changed) = tsubFn (iConType ii)
        (vts', vts_changed) = mapChanged (mapChanged tsubFn) (vMethTs ii)
tSubstIConInfo tsubFn ii@(ICType { })
  | changed = (ii { iType = t' }, True)
  | otherwise = (ii, False)
  where (t', changed) = tsubFn (iType ii)
tSubstIConInfo tsubFn ii
  | changed = (ii { iConType = t' }, True)
  | otherwise = (ii, False)
  where (t', changed) = tsubFn (iConType ii)

-- Internal expression substitution with contexts
{-# SPECIALIZE eSubstWith :: SingleExpr a -> EmptyType -> S.Set Id -> IExpr a -> (IExpr a, Bool) #-}
{-# SPECIALIZE eSubstWith :: EmptyExpr a -> SingleType -> S.Set Id -> IExpr a -> (IExpr a, Bool) #-}
{-# SPECIALIZE eSubstWith :: SingleExpr a -> SingleType -> S.Set Id -> IExpr a -> (IExpr a, Bool) #-}
{-# SPECIALIZE eSubstWith :: BatchExpr a -> EmptyType -> S.Set Id -> IExpr a -> (IExpr a, Bool) #-}
{-# SPECIALIZE eSubstWith :: EmptyExpr a -> BatchType -> S.Set Id -> IExpr a -> (IExpr a, Bool) #-}
{-# SPECIALIZE eSubstWith :: SingleExpr a -> BatchType -> S.Set Id -> IExpr a -> (IExpr a, Bool) #-}
{-# SPECIALIZE eSubstWith :: BatchExpr a -> SingleType -> S.Set Id -> IExpr a -> (IExpr a, Bool) #-}
{-# SPECIALIZE eSubstWith :: BatchExpr a -> BatchType -> S.Set Id -> IExpr a -> (IExpr a, Bool) #-}
eSubstWith :: (ExprSubstCtx ectx a, TypeSubstCtx tctx)
           => ectx -> tctx -> S.Set Id -> IExpr a -> (IExpr a, Bool)
eSubstWith ectx tctx allIds e
    | ctxIsEmpty ectx && ctxIsEmpty tctx = (e, False)
    | otherwise = sub ectx tctx allIds e
  where
    -- sub needs to be polymorphic because the context type can change at
    -- ctxAdd (to batch) or ctxRemove (to single or empty) for both contexts
    sub :: (ExprSubstCtx ectx' a, TypeSubstCtx tctx') => ectx' -> tctx' -> S.Set Id -> IExpr a -> (IExpr a, Bool)
    sub ectx tctx allIds ee@(ILam i t e) =
      case lookupVar i ectx of
        Just _ ->
          -- Variable shadowed: remove from context and continue
          -- We reprocess ee because it is possible i is in the free vars
          -- of the context, so we will need alpha-conversion.
          -- We call eSubstWith so that we check if the context is now empty.
          case ctxRemove i ectx of
            SomeCtx ectx' -> eSubstWith ectx' tctx allIds ee
        Nothing ->
          if ctxContainsVar i ectx
          then -- Alpha-conversion needed: add renaming and continue
            let i'      = cloneId (S.toList allIds) i
                ectx'   = ctxAdd i (IVar i') ectx
                allIds' = S.insert i' allIds
                (t', _) = tSubstWith tctx allIds' t
                (e', _) = sub ectx' tctx allIds' e
            in (ILam i' t' e', True)
          else -- No conflict: continue with same contexts
            let (t', t_changed) = tSubstWith tctx allIds t
                (e', e_changed) = sub ectx tctx allIds e
            in if t_changed || e_changed
               then (ILam i t' e', True)
               else (ee, False)
    sub ectx tctx allIds ee@(ILAM i k e) =
      case lookupVar i tctx of
        Just _ ->
          -- Variable shadowed: remove from context and continue
          -- We reprocess ee because it is possible i is in the free vars
          -- of the context, so we will need alpha-conversion.
          -- We call eSubstWith so that we check if both contexts are now empty.
          case ctxRemove i tctx of
            SomeCtx tctx' -> eSubstWith ectx tctx' allIds ee
        Nothing ->
          if ctxContainsVar i tctx
          then -- Alpha-conversion needed: add renaming and continue
            let i'      = cloneId (S.toList allIds) i
                tctx'   = ctxAdd i (ITVar i') tctx
                allIds' = S.insert i' allIds
                (e', _) = sub ectx tctx' allIds' e
            in (ILAM i' k e', True)
          else -- No conflict: continue with same contexts
            let (e', e_changed) = sub ectx tctx allIds e
            in if e_changed
               then (ILAM i k e', True)
               else (ee, False)
    sub ectx _    _      ee@(IVar i) = case lookupVar i ectx of
                                         Just e' -> (e', True)
                                         Nothing -> (ee, False)
    sub ectx tctx allIds ee@(IAps f ts es) =
        let (f', f_changed) = sub ectx tctx allIds f
            (ts', ts_changed) = mapChanged (tSubstWith tctx allIds) ts
            (es', es_changed) = mapChanged (sub ectx tctx allIds) es
        in if f_changed || ts_changed || es_changed
           then (IAps f' ts' es', True)
           else (ee, False)
    -- Use helper for IConInfo
    sub _    tctx allIds ee@(ICon i ii) =
        let (ii', ii_changed) = tSubstIConInfo tsubFn ii
            tsubFn = tSubstWith tctx allIds
        in if ii_changed
           then (ICon i ii', True)
           else (ee, False)
    sub _    _    _      ee@(IRefT _ _ _) = (ee, False)  -- no free tyvar inside IRef

-- Public API: single expression substitution
{-# INLINE eSubst #-}
eSubst :: Id -> IExpr a -> IExpr a -> IExpr a
eSubst i x e = if changed then deepseq e' e' else e
  where fvx = fVars x
        allIds = fvx `S.union` aVars e
        (e', changed) = eSubstWith (SingleExpr i x fvx) EmptyType allIds e

-- Public API: type substitution in expression
{-# INLINE etSubst #-}
etSubst :: forall a. Id -> IType -> IExpr a -> IExpr a
etSubst i t e = if changed then deepseq e' e' else e
  where ftx = fTVars t
        allIds = ftx `S.union` aVars e
        (e', changed) = eSubstWith (EmptyExpr :: EmptyExpr a) (SingleType i t ftx) allIds e

-- Public API: batch expression and type substitution
{-# INLINE eSubstBatch #-}
eSubstBatch :: forall a. M.Map Id (IExpr a) -> M.Map Id IType -> IExpr a -> IExpr a
eSubstBatch exprMap typeMap e
    | exprSize == 0 && typeSize == 0 = e
    | otherwise = if changed then deepseq e' e' else e
  where
    exprSize = M.size exprMap
    typeSize = M.size typeMap
    (e', changed) = case (exprSize, typeSize) of
          (0, 1) -> let (i, t) = M.findMin typeMap
                        ftx = fTVars t
                    in eSubstWith (EmptyExpr :: EmptyExpr a) (SingleType i t ftx) (ftx `S.union` aVars e) e
          (0, _) -> let ftx = S.unions (M.elems (M.map fTVars typeMap))
                    in eSubstWith (EmptyExpr :: EmptyExpr a) (BatchType typeMap ftx) (ftx `S.union` aVars e) e
          (1, 0) -> let (i, x) = M.findMin exprMap
                        fvx = fVars x
                    in eSubstWith (SingleExpr i x fvx) EmptyType (fvx `S.union` aVars e) e
          (1, 1) -> let (ei, ex) = M.findMin exprMap
                        (ti, tt) = M.findMin typeMap
                        fvx = fVars ex
                        ftx = fTVars tt
                    in eSubstWith (SingleExpr ei ex fvx) (SingleType ti tt ftx) (fvx `S.union` ftx `S.union` aVars e) e
          (1, _) -> let (ei, ex) = M.findMin exprMap
                        fvx = fVars ex
                        ftx = S.unions (M.elems (M.map fTVars typeMap))
                    in eSubstWith (SingleExpr ei ex fvx) (BatchType typeMap ftx) (fvx `S.union` ftx `S.union` aVars e) e
          (_, 0) -> let fvx = S.unions (M.elems (M.map fVars exprMap))
                    in eSubstWith (BatchExpr exprMap fvx) EmptyType (fvx `S.union` aVars e) e
          (_, 1) -> let fvx = S.unions (M.elems (M.map fVars exprMap))
                        (ti, tt) = M.findMin typeMap
                        ftx = fTVars tt
                    in eSubstWith (BatchExpr exprMap fvx) (SingleType ti tt ftx) (fvx `S.union` ftx `S.union` aVars e) e
          (_, _) -> let fvx = S.unions (M.elems (M.map fVars exprMap))
                        ftx = S.unions (M.elems (M.map fTVars typeMap))
                    in eSubstWith (BatchExpr exprMap fvx) (BatchType typeMap ftx) (fvx `S.union` ftx `S.union` aVars e) e

{-# INLINE mapChanged #-}
mapChanged :: (a -> (a, Bool)) -> [a] -> ([a], Bool)
mapChanged _ [] = ([], False)
mapChanged f xs0@(x:xs)
  | not changed = (xs0, False)
  | otherwise   = (x' : xs', True)
  where (x', x_changed) = f x
        (xs', xs_changed) = mapChanged f xs
        changed = x_changed || xs_changed
