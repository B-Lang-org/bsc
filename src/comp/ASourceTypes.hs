-- Source-type observations are metadata, never hardware liveness roots.
-- Keep their expression equivalence independent of compiler CSE and of the
-- source-location IDs retained by AExpr's derived Ord instance.
module ASourceTypes(SourceTypeInfo, sourceTypeKey, canonicalSourceExpr,
                    sourceTypeLookup, anchorSourceTypes,
                    namedSourceTypes, anchorASPackage) where

import qualified Data.Map as M
import qualified Data.Map.Strict as MS
import qualified Data.Set as S
import ASyntax
import Id(getIdString)
import ISyntax(IType)

type SourceTypeInfo = [(AExpr, S.Set IType)]

sourceTypeKey :: AExpr -> AExpr
sourceTypeKey (APrim _ t op es) = APrim defaultAId t op (map sourceTypeKey es)
sourceTypeKey (ASInt _ t v) = ASInt defaultAId t v
sourceTypeKey (ASReal _ t v) = ASReal defaultAId t v
sourceTypeKey (ASStr _ t v) = ASStr defaultAId t v
sourceTypeKey (AMethCall t i m es) = AMethCall t i m (map sourceTypeKey es)
sourceTypeKey (ATuple t es) = ATuple t (map sourceTypeKey es)
sourceTypeKey (ATupleSel t e n) = ATupleSel t (sourceTypeKey e) n
sourceTypeKey (ANoInlineFunCall t i f es) =
    ANoInlineFunCall t i f (map sourceTypeKey es)
sourceTypeKey (AFunCall t i f c es) = AFunCall t i f c (map sourceTypeKey es)
sourceTypeKey (ASAny t e) = ASAny t (fmap sourceTypeKey e)
sourceTypeKey (ASClock t (AClock osc gate)) =
    ASClock t (AClock (sourceTypeKey osc) (sourceTypeKey gate))
sourceTypeKey (ASReset t (AReset e)) = ASReset t (AReset (sourceTypeKey e))
sourceTypeKey (ASInout t (AInout e)) = ASInout t (AInout (sourceTypeKey e))
sourceTypeKey e = e

-- Follow only top-level aliases. Rewriting every nested ASDef would expand
-- the expression DAG; the lazy memo shares each alias class's canonical RHS.
canonicalSourceExpr :: [ADef] -> AExpr -> AExpr
canonicalSourceExpr defs = canonical
  where memo = M.fromList [(i, definition i t e) | ADef i t e _ <- defs]
        -- An unspecified value is a fresh choice, not a shared expression.
        -- Keep the defining signal's identity, including for a compound RHS
        -- containing such a choice. Real aliases still resolve to that same
        -- identity. Bare unknown observations cannot match every unknown def.
        definition i t e | containsAny e = ASDef t i
        definition _ _ e = canonical e
        canonical e@(ASDef _ i) = M.findWithDefault e i memo
        canonical e = sourceTypeKey e

containsAny :: AExpr -> Bool
containsAny (ASAny {}) = True
containsAny (APrim _ _ _ es) = any containsAny es
containsAny (AMethCall _ _ _ es) = any containsAny es
containsAny (ATuple _ es) = any containsAny es
containsAny (ATupleSel _ e _) = containsAny e
containsAny (ANoInlineFunCall _ _ _ es) = any containsAny es
containsAny (AFunCall _ _ _ _ es) = any containsAny es
containsAny (ASClock _ (AClock osc gate)) = containsAny osc || containsAny gate
containsAny (ASReset _ (AReset e)) = containsAny e
containsAny (ASInout _ (AInout e)) = containsAny e
containsAny _ = False

sourceTypeLookup :: [ADef] -> [(AExpr, S.Set IType)] -> AExpr -> S.Set IType
sourceTypeLookup _ [] = const S.empty
sourceTypeLookup defs observations = \e ->
    M.findWithDefault S.empty (canonical e) index
  where canonical = canonicalSourceExpr defs
        index = MS.fromListWith S.union
            [(canonical e, ts) | (e, ts) <- observations]

-- Anchor equivalent observations to existing definitions before their RHSs
-- change or their original aliases disappear. These references are excluded
-- from use-count and reachability analysis. Deduplicate on metadata keys only;
-- distinct ASDef anchors must survive even when they currently have one RHS.
anchorSourceTypes :: [ADef] -> [(AExpr, S.Set IType)] -> [(AExpr, S.Set IType)]
anchorSourceTypes _ [] = []
anchorSourceTypes defs observations = M.elems $ MS.fromListWith combine
    [(sourceTypeKey e, (e, ts)) | (e, ts) <- observations ++ anchors,
                                 not (S.null ts)]
  where lookupTypes = sourceTypeLookup defs observations
        anchors = [(e, ts) | ADef i t _ _ <- defs,
                             let e = ASDef t i
                                 ts = lookupTypes e,
                             not (S.null ts)]
        combine (_, newTypes) (oldExpr, oldTypes) =
            let ts = S.union newTypes oldTypes
            in ts `seq` (oldExpr, ts)

-- All named aliases of the final expressions, plus observed input/state
-- port leaves. The caller restricts this map to actual emitted declarations.
namedSourceTypes :: [ADef] -> [(AExpr, S.Set IType)] -> M.Map String (S.Set IType)
namedSourceTypes _ [] = M.empty
namedSourceTypes defs observations = MS.fromListWith S.union (defined ++ ports)
  where lookupTypes = sourceTypeLookup defs observations
        canonical = canonicalSourceExpr defs
        defined = [(getIdString i, ts) | ADef i t _ _ <- defs,
                                         let ts = lookupTypes (ASDef t i),
                                         not (S.null ts)]
        ports = [(getIdString i, ts) | (e, ts) <- observations,
                                      ASPort _ i <- [canonical e],
                                      not (S.null ts)]

anchorASPackage :: ASPackage -> ASPackage
anchorASPackage pkg = pkg {
    aspkg_expr_types = anchorSourceTypes
        (aspkg_values pkg ++ aspkg_inout_values pkg) (aspkg_expr_types pkg) }
