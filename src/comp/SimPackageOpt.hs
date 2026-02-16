module SimPackageOpt ( simPackageOpt ) where

import Flags
import SimPackage
import ASyntax
import ASyntaxUtil
import AOpt(aExpandDynSel, aInsertCaseDef)
import Prim
import IntLit
import IntegerUtil(aaaa)
import Util(mapSndM, map_mapM)
import Error(internalError, ErrMsg(..), ErrorHandle, bsError)
import Id(isFromRHSId, dummy_id, mkIdCanFire, mkIdWillFire)
import Position(noPosition)
import Data.Maybe
import PPrint

import qualified Data.Map as M
import qualified Data.Set as S
import Util(map_insertManyWith)

-- import Debug.Trace

-- -------------------------

simPackageOpt :: ErrorHandle -> Flags -> SimSystem -> IO SimSystem
simPackageOpt errh flags ss = do
  let pkgs0 = M.toList (ssys_packages ss)
  pkgs1 <- mapSndM (pkgOpt errh flags) pkgs0
  return $ ss { ssys_packages = M.fromList pkgs1 }

pkgOpt :: ErrorHandle -> Flags -> SimPackage -> IO SimPackage
pkgOpt errh flags pkg0 = do
  -- Replace dynamic array selection with case expressions.
  -- This needs to be done before aInsertCase, which can merge adjacent
  -- case/if expressions.
  let pkg1A = expandDynSel pkg0

  -- Before any inlining, use aInsertCase to infer case expression.
  -- It only infers in defs, so it needs to be applied before any inlining.
  -- Note: This can leave unused defs, so we rely on the later opts
  -- to remove unused defs.
  let pkg1B = insertCase pkg1A

  -- remove occurrences of ASAny
  --
  -- replace occurrences of ASAny with a user-specified value;
  -- this is monadic because it can error if the user specified X or Z
  pkg2 <- convertASAny errh flags pkg1B

  -- inline defs (that were created in anticipation of CSE that didn't happen)
  -- and remove unused defs
  let pkg3 = inlineDefs pkg2

  -- combine nested concats and constants exposed by converting ASAny,
  -- and optimize wide concats for Bluesim codegen
  let pkg4 = optimizeConcats pkg3

  return pkg4

-- -------------------------

data UseInfo = None | Only AId | Multiple
  deriving (Eq,Show)

instance PPrint UseInfo where
  pPrint _ _ None     = text "None"
  pPrint d _ (Only x) = (text "Only") <+> pPrint d 0 x
  pPrint _ _ Multiple = text "Multiple"

combine_uses :: UseInfo -> UseInfo -> UseInfo
combine_uses None     x        = x
combine_uses x        None     = x
combine_uses (Only _) (Only _) = Multiple
combine_uses Multiple  _       = Multiple
combine_uses _        Multiple = Multiple

collectUses :: DefMap -> [AId] -> M.Map AId UseInfo
collectUses defmap used_vars = collectUses' use_map0 S.empty used_vars
  where -- consider the vars we start with as "multiple"
        use_map0 = M.fromList [ (v, Multiple) | v <- used_vars ]
        collectUses' m s [] = m
        collectUses' m s (v:vs) | (S.member v s) =
            -- we've already visited this def
            collectUses' m s vs
        collectUses' m s (v:vs) =
            -- some vars are not defs
            case (M.lookup v defmap) of
              Nothing -> collectUses' m s vs
              Just d@(ADef i _ _ _) ->
                  let new_vs = aVars d
                      new_uses = [ (new_v, Only i) | new_v <- new_vs ]
                      m' = map_insertManyWith combine_uses new_uses m
                      s' = S.insert v s
                  in  collectUses' m' s' (new_vs ++ vs)

-- This is inlining defs that were created during AConv.
--   In AConv, expressions are added to a map in an attempt to CSE.
--   If the expr doesn't already exist in the map, then a new name is
--   created, with the FromRHS Id property.  If that expression is
--   seen again, then the same name is used; but if the expression
--   doesn't appear again, then the new name was not necessary.
--   This code checks for FromRHS property on defs that are used
--   only once, and inlines them.
-- This code also eliminates unused defs (which might have resulted
-- from the "insertCase" step).
--
inlineDefs :: SimPackage -> SimPackage
inlineDefs pkg =
  let
      def_map0 = sp_local_defs pkg
      defs0 = M.toList def_map0

      used_in_rule = concatMap aVars (sp_rules pkg)
      used_in_method = concatMap aVars (sp_interface pkg)
      -- We don't extract the uses in state instantiations
      -- because we assume that those exprs have been inlined
      --used_in_state = concatMap aVars (sp_instances pkg)
      -- we want to make sure to preserve the CF/WF signals
      used_in_sched =
          let sched_ids = map arule_id (sp_rules pkg) ++
                          concatMap aIfaceSchedNames (sp_interface pkg)
          in  concat [ [mkIdCanFire i, mkIdWillFire i] | i <- sched_ids ]
      used_vars = used_in_rule ++ used_in_method ++ used_in_sched

      use_map = collectUses def_map0 used_vars

      isTaskOrForeignFunc (ADef _ _ (AFunCall {}) _)   = True
      isTaskOrForeignFunc (ADef _ _ (ATaskValue {}) _) = True
      isTaskOrForeignFunc _                          = False
      -- case-expr becomes case-stmt, which needs a def name to assign to
      isCase (ADef _ _ (APrim _ _ PrimCase _) _) = True
      isCase _ = False
      -- is an unsized string or an array of unsized strings
      isUnsized (ATString Nothing) = True
      isUnsized (ATArray _ t) = isUnsized t
      isUnsized _ = False
      isNotOk d
        | isUnsized (adef_type d)         = True
        | (aSize d > 64)                  = True
        | isTupleType (adef_type d)       = True
        | isTaskOrForeignFunc d           = True
        | isCase d                        = True
        | otherwise                       = False
      dangerous = [ i | (i,d) <- defs0, isNotOk d ]

      -- don't inline these
      keep = S.fromList (used_vars ++ dangerous)

      -- construct a substitution
      subst = M.fromList [ (i, adef_expr (fromJust md))
                         | (i,(Only _)) <- M.toList use_map
                         , isFromRHSId i
                         , not (i `S.member` keep)
                         , let md = M.lookup i (sp_local_defs pkg)
                         , isJust md
                         ]

      defs1 = mapMaybe (processDef use_map subst) defs0
  in pkg { sp_local_defs = M.fromList defs1 }

processDef :: M.Map AId UseInfo -> M.Map AId AExpr ->
              (AId, ADef) -> Maybe (AId, ADef)
processDef use_map subst (name,def) =
  let has_subst = name `M.member` subst
      has_use = name `M.member` use_map
      doSubst (ASDef _ i) = (\e -> exprMap doSubst e) <$> M.lookup i subst
      doSubst _           = Nothing
      opt d@(ADef _ _ e _) = d { adef_expr = exprMap doSubst e }
  in if has_subst
     then Nothing
     else if has_use
     then Just (name, opt def)
     else Nothing

-- -------------------------

optimizeConcats :: SimPackage -> SimPackage
optimizeConcats pkg =
   let optConcat p@(APrim pid pty PrimConcat args) =
          let -- flatten sub-concats into this one
              flatten ((APrim _ _ PrimConcat es):rest) = (flatten es) ++ (flatten rest)
              flatten (x:xs)                           = x:(flatten xs)
              flatten []                               = []
              -- combine adjacent constants (this can happen because ASAny
              -- was only replaced with a value at the start of the Bluesim
              -- backend
              combine_constants (0,_) [] = []
              combine_constants (w,n) [] = [ ASInt dummy_id (ATBit w) (ilSizedBin w n) ]
              combine_constants (w,n) ((ASInt _ (ATBit w') (IntLit _ _ n')):es) =
                combine_constants (w+w', n*(2^w') + n') es
              combine_constants (0,_) (e:es) =
                [e] ++ (combine_constants (0,0) es)
              combine_constants (w,n) (e:es) =
                [ASInt dummy_id (ATBit w) (ilSizedBin w n),e] ++ (combine_constants (0,0) es)
              -- this is the optimized concat arguments regardless of width
              args' = map optConcat $ combine_constants (0,0) $ flatten args
          in if ((aSize pty) <= 64)
             then -- for non-wide concats, we have no optimizations
                  -- beyond the basic ones
                  case args' of
                    []  -> internalError "SimPackageOpt: optimizeConcats has empty arg list"
                    [e] -> e
                    _   -> APrim pid pty PrimConcat args'
             else -- restructure wide concats into chunks aligned on
                  -- 32-bit boundaries
                  let extract (APrim aid (ATBit sz) PrimExtract [e,_,ASInt _ _ (IntLit _ _ base)]) nbits lo =
                        APrim aid (ATBit nbits) PrimExtract [e, aNat (base + lo + nbits - 1), aNat (base + lo) ]
                      extract e nbits lo =
                        APrim dummy_id (ATBit nbits) PrimExtract [e, aNat (lo + nbits - 1), aNat lo]
                      restructure grp sz []     = [grp]
                      restructure grp sz (e:es) =
                        let bits_left_in_dword = if ((sz /= 0) && ((sz `rem` 32) == 0)) then 32 else (sz `rem` 32);
                            e_sz = aSize e
                        in if e_sz <= bits_left_in_dword
                           then restructure (grp ++ [e]) (sz - e_sz) es
                           else -- need to break e across word boundary
                                let ehi = extract e bits_left_in_dword (e_sz - bits_left_in_dword)
                                    elo = extract e (e_sz - bits_left_in_dword) 0
                                in (grp ++ [ehi]):(restructure [] (sz - bits_left_in_dword) (elo:es))
                      args'' = [ case grp of
                                    []  -> internalError "SimPackageOpt: optimizeConcats has empty arg group"
                                    [e] -> e
                                    _   -> APrim dummy_id (ATBit (sum (map aSize grp))) PrimConcat grp
                               | grp <- restructure [] (aSize pty) args'
                               ]
                  in case args'' of
                       []  -> internalError "SimPackageOpt: optimizeConcats has empty arg list"
                       [e] -> e
                       _   -> APrim pid pty PrimConcat args''
       -- recurse for other
       optConcat (APrim i t o as) = APrim i t o (map optConcat as)
       optConcat (AMethCall t o m as) = AMethCall t o m (map optConcat as)
       -- XXX There is maybe an opportunity to optimize tuple construction here,
       -- since that basically turns into a concat as well.
       optConcat (ATuple t as) = ATuple t (map optConcat as)
       optConcat (ATupleSel t e idx) = ATupleSel t (optConcat e) idx
       optConcat (AFunCall t i f isC as) = AFunCall t i f isC (map optConcat as)
       optConcat e = e
   in mapAExprs optConcat pkg

-- -------------------------

-- Replace dynamic array selection with case-expressions.
-- Note: This can inline defs, causing there to be unused defs;
--       we rely on "inlineUses" to remove them.
--
expandDynSel :: SimPackage -> SimPackage
expandDynSel pkg =
  let
      defmap0 = sp_local_defs pkg
      findFn i = adef_expr (findDef defmap0 i)

      defmap1 = M.map (aExpandDynSel True findFn) defmap0

      -- because method return values are not lifted to local defs,
      -- we need to expand dynamic array selection there, too
      ifc1 = aExpandDynSel True findFn (sp_interface pkg)

      -- and they have been inlined into instantiation arguments
      -- XXX Until there is a way to codegen case statements for submodule
      -- XXX instantiation arguments (see mkStateInitList?)
      ss1 = aExpandDynSel False findFn (sp_state_instances pkg)
  in
      pkg { sp_local_defs = defmap1,
            sp_interface = ifc1,
            sp_state_instances = ss1 }

-- -------------------------

-- Convert nested if-expressions into case-expressions in some situations
-- (using the same "aInsertCaseDef" function from the Verilog backend)
-- Note: This can inline defs, causing there to be unused defs;
--       we rely on "inlineUses" to remove them.
--
insertCase :: SimPackage -> SimPackage
insertCase pkg =
  let
      defmap0 = sp_local_defs pkg
      findFn i = adef_expr (findDef defmap0 i)

      defmap1 = M.map (aInsertCaseDef True findFn) defmap0

      -- because method return values are not lifted to local defs,
      -- we need to infer case expressions there, too
      aInsertCaseIfc ai@(AIDef { aif_value = d }) =
          ai { aif_value = aInsertCaseDef True findFn d }
      aInsertCaseIfc ai@(AIActionValue { aif_value = d }) =
          ai { aif_value = aInsertCaseDef True findFn d }
      aInsertCaseIfc ai = ai

      ifc0 = sp_interface pkg
      ifc1 = map aInsertCaseIfc ifc0
  in
      pkg { sp_local_defs = defmap1,
            sp_interface = ifc1 }

-- -------------------------

-- This is monadic because it can report an error
--
convertASAny :: ErrorHandle -> Flags -> SimPackage -> IO SimPackage
convertASAny errh flags apkg = do
  let
      tgt :: String
      tgt = unSpecTo flags

      mkVal :: Integer -> IO AExpr
      mkVal n = do
        v <- case tgt of
               "0" -> return $ 0
               "1" -> return $ (2^n) - 1
               "A" -> return $ aaaa n
               _   -> -- this situation should have been rejected when
                      -- we checked command-line flags
                      bsError errh [(noPosition, EBluesimNoXZ tgt)]
        return $ ASInt dummy_id (ATBit n) (ilSizedHex n v)

      cvtASAnyExpr :: AExpr -> IO AExpr
      cvtASAnyExpr (ASAny ty _) = mkVal (aSize ty)
      cvtASAnyExpr (APrim aid ty op args) =
        do args' <- mapM cvtASAnyExpr args
           return $ APrim aid ty op args'
      cvtASAnyExpr (AMethCall ty aid mid args) =
        do args' <- mapM cvtASAnyExpr args
           return $ AMethCall ty aid mid args'
      cvtASAnyExpr (ATuple ty elems) =
        do elems' <- mapM cvtASAnyExpr elems
           return $ ATuple ty elems'
      cvtASAnyExpr (ATupleSel ty exp idx) =
        do exp' <- cvtASAnyExpr exp
           return $ ATupleSel ty exp' idx
      cvtASAnyExpr (ANoInlineFunCall ty aid fun args) =
        do args' <- mapM cvtASAnyExpr args
           return $ ANoInlineFunCall ty aid fun args'
      cvtASAnyExpr (AFunCall ty aid fun isC args) =
        do args' <- mapM cvtASAnyExpr args
           return $ AFunCall ty aid fun isC args'
      cvtASAnyExpr expr = return expr

  -- convert in the state, rules, ifc, and defs
  -- XXX consider an instance of mapMAExprs for SimPackage?
  --
  let ss = sp_state_instances apkg
      rs = sp_rules apkg
      ifc = sp_interface apkg
      dmap = sp_local_defs apkg

  ss' <- mapMAExprs cvtASAnyExpr ss
  rs' <- mapMAExprs cvtASAnyExpr rs
  ifc' <- mapMAExprs cvtASAnyExpr ifc
  dmap' <- map_mapM (mapMAExprs cvtASAnyExpr) dmap

  return $ apkg { sp_state_instances = ss'
                , sp_rules = rs'
                , sp_interface = ifc'
                , sp_local_defs = dmap' }

-- -------------------------
