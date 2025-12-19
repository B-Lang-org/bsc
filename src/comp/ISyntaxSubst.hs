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
import qualified Data.Set as S
import qualified Data.Map as M

-- ============================================================
-- Changed flag wrapper

-- Changed flag type - Unchanged carries no payload for efficiency
-- Similar to Maybe but with "change tracking" semantics
-- Not an Applicative/Monad because Unchanged has no value to work with:
--   - Can't define: Changed f <*> Unchanged (no value to apply f to)
--   - Can't define: pure/return (unclear if should be Changed or Unchanged)
-- Lazy in 'a' to minimize peak memory residency (deepseq at top level handles forcing)
data Changed a = Changed a | Unchanged

-- Rebuild with 1 Changed argument
{-# INLINE changed1 #-}
changed1 :: (a -> b) -> Changed a -> Changed b
changed1 _ Unchanged = Unchanged
changed1 f (Changed x) = Changed (f x)

-- Get the value from Changed, or use the provided original if Unchanged
{-# INLINE changedOr #-}
changedOr :: a -> Changed a -> a
changedOr orig Unchanged = orig
changedOr _ (Changed x) = x

-- Rebuild with 2 Changed arguments - returns Unchanged only if both unchanged
{-# INLINE changed2 #-}
changed2 :: (a -> b -> c) -> a -> b -> Changed a -> Changed b -> Changed c
changed2 _     _     _ Unchanged    Unchanged    = Unchanged
changed2 f     _ origB (Changed a') Unchanged    = Changed $ f a' origB
changed2 f origA     _ Unchanged    (Changed b') = Changed $ f origA b'
changed2 f     _     _ (Changed a') (Changed b') = Changed $ f a' b'

-- Rebuild with 3 Changed arguments - returns Unchanged only if all unchanged
{-# INLINE changed3 #-}
changed3 :: (a -> b -> c -> d) -> a -> b -> c -> Changed a -> Changed b -> Changed c -> Changed d
changed3 _     _     _     _ Unchanged    Unchanged    Unchanged    = Unchanged
changed3 f     _ origB origC (Changed a') Unchanged    Unchanged    = Changed $ f a' origB origC
changed3 f origA     _ origC Unchanged    (Changed b') Unchanged    = Changed $ f origA b' origC
changed3 f origA origB     _ Unchanged    Unchanged    (Changed c') = Changed $ f origA origB c'
changed3 f     _     _ origC (Changed a') (Changed b') Unchanged    = Changed $ f a' b' origC
changed3 f     _ origB     _ (Changed a') Unchanged    (Changed c') = Changed $ f a' origB c'
changed3 f origA     _     _ Unchanged    (Changed b') (Changed c') = Changed $ f origA b' c'
changed3 f     _     _     _ (Changed a') (Changed b') (Changed c') = Changed $ f a' b' c'

-- ============================================================
-- Substitution contexts

-- Existential wrapper for when context type changes
data SomeCtx v where
  SomeCtx :: SubstContext ctx v => ctx -> SomeCtx v

-- Type family for batch context types
type family BatchCtx v where
  BatchCtx (IExpr a) = BatchExpr a
  BatchCtx IType = BatchType

-- Typeclass for substitution contexts (unified for IExpr and IType)
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
{-# SPECIALIZE tSubstWith :: EmptyType -> S.Set Id -> IType -> Changed IType #-}
{-# SPECIALIZE tSubstWith :: SingleType -> S.Set Id -> IType -> Changed IType #-}
{-# SPECIALIZE tSubstWith :: BatchType -> S.Set Id -> IType -> Changed IType #-}
tSubstWith :: TypeSubstCtx tctx => tctx -> S.Set Id -> IType -> Changed IType
tSubstWith tctx allIds t
    | ctxIsEmpty tctx = Unchanged
    | otherwise = sub tctx allIds t
  where
    -- sub needs to be polymorphic because the context type can change at
    -- ctxAdd (to batch) or ctxRemove (to single or empty)
    sub :: TypeSubstCtx tctx' => tctx' -> S.Set Id -> IType -> Changed IType
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
            in Changed $ ITForAll i' k $ changedOr t (sub tctx' allIds' t)
          else -- No conflict: continue with same context
            changed1 (ITForAll i k) (sub tctx allIds t)
    sub tctx allIds tt@(ITAp f a) =
      changed2 normITAp f a (sub tctx allIds f) (sub tctx allIds a)
    sub tctx _      tt@(ITVar i) = maybe Unchanged Changed (lookupVar i tctx)
    sub _    _      tt@(ITCon _ _ _) = Unchanged
    sub _    _      tt@(ITNum _) = Unchanged
    sub _    _      tt@(ITStr _) = Unchanged

-- Public API: single type substitution
{-# INLINE tSubst #-}
tSubst :: Id -> IType -> IType -> IType
tSubst i t ty = changedOr ty (tSubstWith (SingleType i t (fTVars t)) (fTVars t `S.union` aTVars ty) ty)

-- Public API: batch type substitution
{-# INLINE tSubstBatch #-}
tSubstBatch :: M.Map Id IType -> IType -> IType
tSubstBatch typeMap t
  | M.null typeMap = t
  | M.size typeMap == 1 =
      let (i, ty) = M.findMin typeMap
      in tSubst i ty t
  | otherwise =
      let ftx = S.unions $ M.elems $ M.map fTVars typeMap
          tctx = BatchType typeMap ftx
          allIds = ftx `S.union` aTVars t
      in changedOr t (tSubstWith tctx allIds t)

-- ============================================================
-- Expression and type substitution

-- Helper: apply type substitution function to IConInfo
tSubstIConInfo :: (IType -> Changed IType) -> IConInfo a -> Changed (IConInfo a)
tSubstIConInfo tsubFn ii@(ICVerilog { }) =
  changed2 (\t vts -> ii { iConType = t, vMethTs = vts })
           (iConType ii) (vMethTs ii)
           (tsubFn (iConType ii)) (mapChanged (mapChanged tsubFn) (vMethTs ii))
-- ICType's iConType is always itType (no free variables)
tSubstIConInfo tsubFn ii@(ICType { }) =
  changed1 (\t' -> ii { iType = t' }) (tsubFn (iType ii))
tSubstIConInfo tsubFn ii =
  changed1 (\t' -> ii { iConType = t' }) (tsubFn (iConType ii))

-- Internal expression substitution with contexts
{-# SPECIALIZE eSubstWith :: EmptyExpr a -> EmptyType -> S.Set Id -> IExpr a -> Changed (IExpr a) #-}
{-# SPECIALIZE eSubstWith :: SingleExpr a -> EmptyType -> S.Set Id -> IExpr a -> Changed (IExpr a) #-}
{-# SPECIALIZE eSubstWith :: EmptyExpr a -> SingleType -> S.Set Id -> IExpr a -> Changed (IExpr a) #-}
{-# SPECIALIZE eSubstWith :: SingleExpr a -> SingleType -> S.Set Id -> IExpr a -> Changed (IExpr a) #-}
{-# SPECIALIZE eSubstWith :: BatchExpr a -> EmptyType -> S.Set Id -> IExpr a -> Changed (IExpr a) #-}
{-# SPECIALIZE eSubstWith :: EmptyExpr a -> BatchType -> S.Set Id -> IExpr a -> Changed (IExpr a) #-}
{-# SPECIALIZE eSubstWith :: SingleExpr a -> BatchType -> S.Set Id -> IExpr a -> Changed (IExpr a) #-}
{-# SPECIALIZE eSubstWith :: BatchExpr a -> SingleType -> S.Set Id -> IExpr a -> Changed (IExpr a) #-}
{-# SPECIALIZE eSubstWith :: BatchExpr a -> BatchType -> S.Set Id -> IExpr a -> Changed (IExpr a) #-}
eSubstWith :: (ExprSubstCtx ectx a, TypeSubstCtx tctx)
           => ectx -> tctx -> S.Set Id -> IExpr a -> Changed (IExpr a)
eSubstWith ectx tctx allIds e
    | ctxIsEmpty ectx && ctxIsEmpty tctx = Unchanged
    | otherwise = sub ectx tctx allIds e
  where
    -- sub needs to be polymorphic because the context type can change at
    -- ctxAdd (to batch) or ctxRemove (to single or empty) for both contexts
    sub :: (ExprSubstCtx ectx' a, TypeSubstCtx tctx') => ectx' -> tctx' -> S.Set Id -> IExpr a -> Changed (IExpr a)
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
                t' = changedOr t (tSubstWith tctx allIds' t)
                e' = changedOr e (sub ectx' tctx allIds' e)
            in Changed $ ILam i' t' e'
          else -- No conflict: continue with same contexts
            changed2 (ILam i) t e (tSubstWith tctx allIds t) (sub ectx tctx allIds e)
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
                e' = changedOr e (sub ectx tctx' allIds' e)
            in Changed $ ILAM i' k e'
          else -- No conflict: continue with same contexts
            changed1 (ILAM i k) (sub ectx tctx allIds e)
    sub ectx _    _      ee@(IVar i) = maybe Unchanged Changed (lookupVar i ectx)
    sub ectx tctx allIds ee@(IAps f ts es) =
        changed3 IAps f ts es (sub ectx tctx allIds f) (mapChanged (tSubstWith tctx allIds) ts) (mapChanged (sub ectx tctx allIds) es)
    -- Use helper for IConInfo
    sub _    tctx allIds ee@(ICon i ii) =
        changed1 (ICon i) (tSubstIConInfo (tSubstWith tctx allIds) ii)
    sub _    _    _      ee@(IRefT _ _ _) = Unchanged  -- no free tyvar inside IRef

-- Public API: single expression substitution
{-# INLINE eSubst #-}
eSubst :: Id -> IExpr a -> IExpr a -> IExpr a
eSubst i x e
    | Changed e' <- result = deepseq e' e'
    | otherwise = e
  where fvx = fVars x
        allIds = fvx `S.union` aVars e
        result = eSubstWith (SingleExpr i x fvx) EmptyType allIds e

-- Public API: type substitution in expression
{-# INLINE etSubst #-}
etSubst :: forall a. Id -> IType -> IExpr a -> IExpr a
etSubst i t e
    | Changed e' <- result = deepseq e' e'
    | otherwise = e
  where ftx = fTVars t
        allIds = ftx `S.union` aVars e
        result = eSubstWith (EmptyExpr :: EmptyExpr a) (SingleType i t ftx) allIds e

-- Public API: batch expression and type substitution
{-# INLINE eSubstBatch #-}
eSubstBatch :: forall a. M.Map Id (IExpr a) -> M.Map Id IType -> IExpr a -> IExpr a
eSubstBatch exprMap typeMap e
    | exprSize == 0 && typeSize == 0 = e
    | Changed e' <- result = deepseq e' e'
    | otherwise = e
  where
    exprSize = M.size exprMap
    typeSize = M.size typeMap
    result = case (exprSize, typeSize) of
          (0, 1) -> let (i, t) = M.findMin typeMap
                        ftx = fTVars t
                    in eSubstWith (EmptyExpr :: EmptyExpr a) (SingleType i t ftx) (ftx `S.union` aVars e) e
          (0, _) -> let ftx = S.unions $ M.elems $ M.map fTVars typeMap
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
                        ftx = S.unions $ M.elems $ M.map fTVars typeMap
                    in eSubstWith (SingleExpr ei ex fvx) (BatchType typeMap ftx) (fvx `S.union` ftx `S.union` aVars e) e
          (_, 0) -> let fvx = S.unions $ M.elems $ M.map fVars exprMap
                    in eSubstWith (BatchExpr exprMap fvx) EmptyType (fvx `S.union` aVars e) e
          (_, 1) -> let fvx = S.unions $ M.elems $ M.map fVars exprMap
                        (ti, tt) = M.findMin typeMap
                        ftx = fTVars tt
                    in eSubstWith (BatchExpr exprMap fvx) (SingleType ti tt ftx) (fvx `S.union` ftx `S.union` aVars e) e
          (_, _) -> let fvx = S.unions $ M.elems $ M.map fVars exprMap
                        ftx = S.unions $ M.elems $ M.map fTVars typeMap
                    in eSubstWith (BatchExpr exprMap fvx) (BatchType typeMap ftx) (fvx `S.union` ftx `S.union` aVars e) e

{-# INLINE mapChanged #-}
mapChanged :: (a -> Changed a) -> [a] -> Changed [a]
mapChanged _ [] = Unchanged
mapChanged f xs0@(x:xs) = changed2 (:) x xs (f x) (mapChanged f xs)
