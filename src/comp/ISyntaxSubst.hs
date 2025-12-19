module ISyntaxSubst(
        tSubst,
        eSubst,
        etSubst,
        SubstCtx,
        SubstCtxVars(..),
        ExprSubstCtx,
        TypeSubstCtx,
        emptyCtx,
        isEmptyCtx,
        ctxInsert,
        ctxDelete,
        ctxLookup,
        ctxFreeVarSet,
        tSubstBatch,
        eSubstBatch
) where

import ISyntax
import Eval
import Id
import Data.Maybe(fromMaybe)
import qualified Data.Set as S
import qualified Data.Map as M

-- ============================================================
-- Batch substitution infrastructure

-- Typeclass for computing free variables in substitution contexts
class SubstCtxVars v where
  ctxFreeVars :: v -> S.Set Id

instance SubstCtxVars IType where
  ctxFreeVars = fTVars

instance SubstCtxVars (IExpr a) where
  ctxFreeVars = fVars

-- Substitution context: a map and the free variables of all values
data SubstCtx v = SubstCtx (M.Map Id v) (S.Set Id)

-- Type aliases for clarity
type ExprSubstCtx a = SubstCtx (IExpr a)
type TypeSubstCtx = SubstCtx IType

-- Create an empty substitution context
emptyCtx :: SubstCtx v
emptyCtx = SubstCtx M.empty S.empty

-- Check if a context is empty
isEmptyCtx :: SubstCtx v -> Bool
isEmptyCtx (SubstCtx m _) = M.null m

-- Insert a binding into the context
ctxInsert :: SubstCtxVars v => Id -> v -> SubstCtx v -> SubstCtx v
ctxInsert i v (SubstCtx m fvs) = SubstCtx (M.insert i v m) (fvs `S.union` ctxFreeVars v)

-- Delete a binding from the context
-- We keep the free variables (conservative but safe - might do extra
-- alpha-conversions but won't miss needed ones)
ctxDelete :: Id -> SubstCtx v -> SubstCtx v
ctxDelete i (SubstCtx m fvs) = SubstCtx (M.delete i m) fvs

-- Lookup a variable in the context
ctxLookup :: Id -> SubstCtx v -> Maybe v
ctxLookup i (SubstCtx m _) = M.lookup i m

-- Get the free variable set from the context
ctxFreeVarSet :: SubstCtx v -> S.Set Id
ctxFreeVarSet (SubstCtx _ fvs) = fvs

-- ============================================================
-- Batch type substitution

-- Batch type substitution (internal interface)
tSubstBatch' :: TypeSubstCtx -> S.Set Id -> IType -> IType
tSubstBatch' tctx allIds t
    | isEmptyCtx tctx = t
    | otherwise = sub tctx allIds t
  where
    sub tctx allIds tt@(ITForAll i k t) =
        case ctxLookup i tctx of
            Just _ ->
                -- Variable shadowed: remove from context and continue
                -- We reprocess tt because it is possible i is in the free vars
                -- of the context, so we will need alpha-conversion.
                -- We go back to tSubstBatch' so that we check if tctx' is empty.
                let tctx' = ctxDelete i tctx
                in tSubstBatch' tctx' allIds tt
            Nothing ->
                if i `S.member` ctxFreeVarSet tctx
                   then -- Alpha-conversion needed: add renaming and continue
                        let i'      = cloneId (S.toList allIds) i
                            tctx'   = ctxInsert i (ITVar i') tctx
                            allIds' = S.insert i' allIds
                        in ITForAll i' k (sub tctx' allIds' t)
                   else -- No conflict: continue with same context
                        ITForAll i k (sub tctx allIds t)
    sub tctx allIds (ITAp f a) = normITAp (sub tctx allIds f) (sub tctx allIds a)
    sub tctx _      tt@(ITVar i) = fromMaybe tt (ctxLookup i tctx)
    sub _    _      tt@(ITCon _ _ _) = tt
    sub _    _      tt@(ITNum _) = tt
    sub _    _      tt@(ITStr _) = tt

-- Batch type substitution (public API)
tSubstBatch :: M.Map Id IType -> IType -> IType
tSubstBatch typeMap t
    | M.null typeMap = t
    | otherwise =
        let ftx     = S.unions (M.elems (M.map fTVars typeMap))
            tctx    = SubstCtx typeMap ftx
            allIds  = ftx `S.union` aTVars t
        in tSubstBatch' tctx allIds t

-- Single type substitution (wrapper around batch version)
tSubst :: Id -> IType -> IType -> IType
tSubst v x t = tSubstBatch (M.singleton v x) t

-- ============================================================
-- Batch expression and type substitution

-- Helper: apply type substitution function to IConInfo
tSubstIConInfo :: (IType -> IType) -> IConInfo a -> IConInfo a
tSubstIConInfo tsubFn ii@(ICUndet { }) =
    ii { iConType = tsubFn (iConType ii) }
tSubstIConInfo tsubFn ii@(ICVerilog { }) =
    ii { iConType = tsubFn (iConType ii),
         vMethTs = map (map tsubFn) (vMethTs ii) }
tSubstIConInfo tsubFn ii@(ICInt { }) =
    ii { iConType = tsubFn (iConType ii) }
tSubstIConInfo tsubFn ii@(ICStateVar { }) =
    ii { iConType = tsubFn (iConType ii) }
tSubstIConInfo tsubFn ii@(ICMethArg { }) =
    ii { iConType = tsubFn (iConType ii) }
tSubstIConInfo tsubFn ii@(ICModPort { }) =
    ii { iConType = tsubFn (iConType ii) }
tSubstIConInfo tsubFn ii@(ICModParam { }) =
    ii { iConType = tsubFn (iConType ii) }
tSubstIConInfo tsubFn ii@(ICForeign { }) =
    ii { iConType = tsubFn (iConType ii) }
tSubstIConInfo tsubFn ii@(ICType { }) =
    ii { iType = tsubFn (iType ii) }
tSubstIConInfo _ ii = ii  -- No types to substitute in other cases

-- Batch expression and type substitution (internal interface, no deepseq)
eSubstBatch' :: ExprSubstCtx a -> TypeSubstCtx -> S.Set Id -> IExpr a -> IExpr a
eSubstBatch' ectx tctx allIds e
    | isEmptyCtx ectx && isEmptyCtx tctx = e
    | otherwise = sub ectx tctx allIds e
  where
    sub ectx tctx allIds ee@(ILam i t e) =
        case ctxLookup i ectx of
            Just _ ->
                -- Variable shadowed: remove from context and continue
                -- We reprocess ee because it is possible i is in the free vars
                -- of the context, so we will need alpha-conversion.
                -- We go back to eSubstBatch' because we want to recheck if both contexts are empty.
                let ectx' = ctxDelete i ectx
                in eSubstBatch' ectx' tctx allIds ee
            Nothing ->
                if i `S.member` ctxFreeVarSet ectx
                   then -- Alpha-conversion needed: add renaming and continue
                        let i'      = cloneId (S.toList allIds) i
                            ectx'   = ctxInsert i (IVar i') ectx
                            allIds' = S.insert i' allIds
                        in ILam i' (tSubstBatch' tctx allIds' t) (sub ectx' tctx allIds' e)
                   else -- No conflict: continue with same contexts
                        ILam i (tSubstBatch' tctx allIds t) (sub ectx tctx allIds e)
    sub ectx tctx allIds ee@(ILAM i k e) =
        case ctxLookup i tctx of
            Just _ ->
                -- Variable shadowed: remove from context and continue
                -- We reprocess ee because it is possible i is in the free vars
                -- of the context, so we will need alpha-conversion.
                -- We go back to eSubstBatch' because we want to recheck if both contexts are empty.
                let tctx' = ctxDelete i tctx
                in eSubstBatch' ectx tctx' allIds ee
            Nothing ->
                if i `S.member` ctxFreeVarSet tctx
                   then -- Alpha-conversion needed: add renaming and continue
                        let i'      = cloneId (S.toList allIds) i
                            tctx'   = ctxInsert i (ITVar i') tctx
                            allIds' = S.insert i' allIds
                        in ILAM i' k (sub ectx tctx' allIds' e)
                   else -- No conflict: continue with same contexts
                        ILAM i k (sub ectx tctx allIds e)
    sub ectx _    _      ee@(IVar i)    = fromMaybe ee (ctxLookup i ectx)
    sub ectx tctx allIds (IAps f ts es) = IAps (sub ectx tctx allIds f)
                                               (map (tSubstBatch' tctx allIds) ts)
                                               (map (sub ectx tctx allIds) es)
    -- Use helper for IConInfo
    sub _    tctx allIds (ICon i ii)    = ICon i (tSubstIConInfo tsubFn ii)
      where tsubFn = tSubstBatch' tctx allIds
    sub _    _    _      ee@(IRefT _ _ _) = ee        -- no free tyvar inside IRef

-- Batch expression and type substitution (public API, with deepseq)
eSubstBatch :: M.Map Id (IExpr a) -> M.Map Id IType -> IExpr a -> IExpr a
eSubstBatch exprMap typeMap e
    | M.null exprMap && M.null typeMap = e
    | otherwise = deepseq e' e'
  where
    fvx     = S.unions (M.elems (M.map fVars  exprMap))
    ftx     = S.unions (M.elems (M.map fTVars typeMap))
    ectx    = SubstCtx exprMap fvx
    tctx    = SubstCtx typeMap ftx
    allIds  = fvx `S.union` ftx `S.union` aVars e
    e'      = eSubstBatch' ectx tctx allIds e

-- Single expression substitution (wrapper around batch version)
eSubst :: Id -> IExpr a -> IExpr a -> IExpr a
eSubst v x e = eSubstBatch (M.singleton v x) M.empty e

-- Type substitution in expression (wrapper around batch version)
etSubst :: Id -> IType -> IExpr a -> IExpr a
etSubst v x e = eSubstBatch M.empty (M.singleton v x) e

