-- Source type observations are annotations, not hardware liveness roots.
module ATypePropagation (propagateSourceTypes, muxDataChildren) where

import Data.List (foldl')
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import ASyntax
import ASyntaxUtil (aType)
import ASourceTypes (SourceTypeInfo, sourceTypeKey)
import Prim (PrimOp(..))

-- Propagate interpretations only along explicitly justified value edges.
-- A shared expression must be revisited when another interpretation reaches
-- it: a boolean visited set would lose candidates at CSE joins.
propagateSourceTypes :: (AExpr -> [AExpr]) -> [ADef] ->
                        SourceTypeInfo -> SourceTypeInfo
propagateSourceTypes dataChildren defs observations = M.elems (go M.empty initial)
  where
    defmap = M.fromList [(i, e) | ADef i _ e _ <- defs]
    initial = M.fromListWith combine
        [(sourceTypeKey e, (e, ts)) | (e, ts) <- observations, not (S.null ts)]
    children e = filter (sameValueWidth e) $ aliases e ++ dataChildren e
    -- An unspecified mux default is not a shared value. Giving it a type
    -- would conflate independent don't-cares of the same width downstream.
    sameValueWidth _ (ASAny {}) = False
    sameValueWidth e child = aType e == aType child
    aliases (ASDef _ i) = maybe [] (:[]) (M.lookup i defmap)
    aliases _ = []
    -- Normalize indexing only. Retain an original expression as the payload
    -- so these annotations do not unnecessarily discard source-location IDs.
    combine (_, incoming) (original, old) =
        let joined = incoming `S.union` old
        in joined `seq` (original, joined)
    enqueue ts pending e = M.insertWith combine (sourceTypeKey e) (e, ts) pending
    go seen pending = case M.minViewWithKey pending of
        Nothing -> seen
        Just ((key, (e, incoming)), rest) ->
            let old = maybe S.empty snd (M.lookup key seen)
                delta = incoming `S.difference` old
            in if S.null delta
               then go seen rest
               else let joined = old `S.union` delta
                        seen' = joined `seq` M.insert key (e, joined) seen
                        pending' = foldl' (enqueue delta) rest (children e)
                    in seen' `seq` pending' `seq` go seen' pending'

-- Both mux forms use alternating selector/value pairs, including the default.
-- Never assign the result's source type to a selector.
muxDataChildren :: AExpr -> [AExpr]
muxDataChildren (APrim _ _ op args)
    | op == PrimMux || op == PrimPriMux = values args
  where
    values (_ : value : rest) = value : values rest
    values _ = []
muxDataChildren _ = []
