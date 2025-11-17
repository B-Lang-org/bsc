module TypeCheck(cTypeCheck,
                 cCtxReduceDef, cCtxReduceIO,
                 topExpr,
                 qualifyClassDefaults
                ) where

import Data.List
import Data.Maybe(catMaybes)
import Control.Monad(when)
import qualified Data.Map as M
import qualified Data.Set as S

import PFPrint
import Id
import Error(internalError, EMsg, WMsg, ErrMsg(..),
             ErrorHandle, bsError, bsErrorNoExit, bsErrorUnsafe, bsWarning)
import ContextErrors
import Flags(Flags, enablePoisonPills, allowIncoherentMatches)
import CSyntax
import PoisonUtils
import Type
import Subst
import TIMonad
import TCMisc
import TCheck
import CtxRed
import SymTab
import Assump
import CSubst(cSubstN)
import CFreeVars(getFVC, getFTCC)
import Util(separate, apFst, quote, fst3)

cTypeCheck :: ErrorHandle -> Flags -> SymTab -> CPackage -> IO (CPackage, Bool, S.Set Id)
cTypeCheck errh flags symtab (CPackage name exports imports impsigs fixs defns includes) = do
    (typecheckedDefns, typeWarns, usedPkgs, haveErrors) <- tiDefns errh symtab flags defns

    -- Issue type warnings
    when (not (null typeWarns)) $ bsWarning errh typeWarns

    return (CPackage name exports imports impsigs fixs typecheckedDefns includes,
            haveErrors,
            usedPkgs)


-- type check top-level definitions in parallel (since they are independent)
tiDefns :: ErrorHandle -> SymTab -> Flags -> [CDefn] -> IO ([CDefn], [WMsg], S.Set Id, Bool)
tiDefns errh s flags ds = do
  let ai = allowIncoherentMatches flags
  let checkDef d = (defErr, warns, usedPkgs)
        where (result, warns, usedPkgs) = runTI flags ai s $ tiOneDef d
              defErr = case result of
                          (Left emsgs)  -> Left emsgs
                          (Right cdefn) -> rmFreeTypeVars cdefn
  let checked = map checkDef ds
  let (checks, wss, pkgss) = unzip3 checked
  let (errors, ds') = apFst concat $ separate checks
  let have_errors = not (null errors)
  let mkErrorDef (Left _)  (CValueSign (CDef i t _)) = Just (mkPoisonedCDefn i t)
      mkErrorDef (Left _)  (Cclass {}) = Nothing
      mkErrorDef (Left _)  (CValue {}) = Nothing -- Can't recover from missing signature error.
      mkErrorDef (Left _)  d = internalError ("tiDefns - not CValueSign or Cclass: " ++ ppReadable d)
      mkErrorDef (Right _) _ = Nothing
  let error_defs = catMaybes (zipWith mkErrorDef checks ds)
  let checked_error_defs = map checkDef error_defs
  let (double_error_msgs, error_defs') =
          apFst concat $ separate $ map fst3 checked_error_defs
  -- Accumulate all used packages (only from the first round, poison pills don't use new symbols)
  let allUsedPkgs = S.unions pkgss
  -- XXX: we give up - some type signatures are bogus
  when ((not (null double_error_msgs)) || (have_errors && not (enablePoisonPills flags))) $
      bsError errh (nub errors) -- the underyling error should be in errors
  when (have_errors && enablePoisonPills flags) $ bsErrorNoExit errh errors
  return (ds' ++ error_defs', concat wss, allUsedPkgs, have_errors)

nullAssump :: [Assump]
nullAssump = []

tiOneDef :: CDefn -> TI CDefn
tiOneDef d@(CValueSign (CDef i t s)) = do
        --trace ("TC " ++ ppReadable i) $ return ()
        (rs, ~(CLValueSign d' _)) <- tiExpl nullAssump (i, t, s, [])
        checkTopPreds d rs
        s <- getSubst'
        clearSubst
        return (CValueSign (apSub s d'))
tiOneDef d@(Cclass incoh cps ik is fd fs) = do
    let -- we can assume that the current class is available, so make it
        -- as a pred
        ts :: [CType]
        ts = map cTVar is -- XXX no kind?
        this_p :: CPred
        this_p = CPred (CTypeclass (iKName ik)) ts
        tiF :: CField -> TI CField
        tiF f@(CField { cf_default = [] }) = return f
        tiF f@(CField fid _ (CQType fps fty) fcs _) = do
          let -- we don't need to include the superclasses ("cps")
              fps' = [this_p] ++ fps
              fqt' = CQType fps' fty
          (rs, ~(CLValueSign (CDefT _ _ _ fcs') _))
               <- tiExpl nullAssump (fid, fqt', fcs, [])
          checkTopPreds fid rs
          clearSubst
          return (f { cf_default = fcs' })
    fs' <- mapM tiF fs
    -- XXX We could return the mangled typechecked clauses here if
    -- XXX * we typecheck Cclass first and re-insert into the symt
    -- XXX * typecheck the rest of the pkg (which may use those defaults)
    -- XXX   and have "tiExpl" of structs not re-typecheck defaults
    -- XXX * have "genSign" use the symt containing the typechecked defaults
    -- XXX Until then, "genSign" inserts qualifiers, to preserve the scope
    -- traceM ("Cclass: " ++ ppReadable fs')
    return d
tiOneDef d@(CValue i s) = errorAtId ENoTopTypeSign i
tiOneDef d = return d

-- Force the substitution to make sure we don't drag around cruft.
getSubst' :: TI Subst
getSubst' = do
        s <- getSubst
        if s == s then return s else internalError "TypeCheck.getSubst': s /= s (WTF!?)"

-- Any predicates at the top level should be reported as an error
checkTopPreds :: (HasPosition a, PPrint a) => a -> [VPred] -> TI ()
checkTopPreds _ [] = return ()
checkTopPreds a ps = do
    -- reduce the predicates as much as possible
    (ps', ls) <- satisfy [] ps
    if null ps' then
        -- they shouldn't reduce away completely
        internalError ("checkTopPreds " ++ ppReadable (a, ps))
     else do
        addExplPreds []  -- add en empty context
        handleContextReduction (getPosition a) ps'

-- typecheck an expression as a top-level object
-- returning any unsatisfied preds
topExpr :: CType -> CExpr -> TI ([VPred], CExpr)
topExpr td e = do
  (ps, e') <- tiExpr [] td e
  (ps', ls) <- satisfy [] ps
  s <- getSubst
  return (apSub s (ps', Cletrec ls e'))

------

qualifyClassDefaults :: ErrorHandle -> SymTab -> [CDefn] -> [CDefn]
qualifyClassDefaults errh symt ds =
    let
        mkCQual c =
            case (findCon symt c) of
              Just [ConInfo { ci_assump = (qc :>: _) }] -> (c, qc)
              Just ds ->
                  let msg = "The signature file generation for typeclass " ++
                            "defaults cannot disambiguate the constructor " ++
                            quote (getIdString c) ++ ".  Perhaps adding " ++
                            "a package qualifier will help."
                  in  bsErrorUnsafe errh [(getPosition c, EGeneric msg)]
              Nothing ->
                  -- it could be a struct/interface (or an alias of one?)
                  case (findType symt c) of
                    Just (TypeInfo (Just qc) _ _ _ _) -> (c, qc)
                    _ -> internalError ("qualifyClassDefaults: " ++
                                        "constructor not found: " ++
                                        ppReadable c)
        mkTQual t =
            case (findType symt t) of
              Just (TypeInfo (Just qt) _ _ _ _) -> (t, qt)
              Just (TypeInfo Nothing _ _ _ _) ->
                  internalError ("qualifyClassDefaults: " ++
                                 "unexpected numeric or string type: " ++ ppReadable t)
              Nothing -> internalError ("qualifyClassDefaults: " ++
                                        "type not found: " ++ ppReadable t)
        mkVQual v =
            case (findVar symt v) of
              Just (VarInfo _ (qv :>: _) _ _) -> (v, CVar qv)
              Nothing -> internalError ("qualifyClassDefaults: " ++
                                        "var not found: " ++ ppReadable v)
        qualDef (Cclass incoh cps ik is deps fs) =
            let qualField (CField fi fps fqt fdefaults foqt) =
                    let (csets, vsets) = unzip $ map getFVC fdefaults
                        cset = S.unions csets
                        vset = S.unions vsets
                        tset = S.unions (map getFTCC fdefaults)
                        -- make the mappings
                        cmap = M.fromList (map mkCQual (S.toList cset))
                        vmap = M.fromList (map mkVQual (S.toList vset))
                        tmap = M.fromList (map mkTQual (S.toList tset))
                        -- substitute into the clauses
                        fdefaults' = cSubstN (tmap,cmap,vmap,M.empty) fdefaults
                    in  (CField fi fps fqt fdefaults' foqt)
            in  (Cclass incoh cps ik is deps (map qualField fs))
        qualDef d = d
    in
        map qualDef ds

------

-- remove free type variables from toplevel definitions:
--  - substitute vars of kind * with ()
--  - report unknown size on remaining free vars of kind #
-- crash on free type variables of other kinds (presumed typecheck bug)
rmFreeTypeVars :: CDefn -> Either [EMsg] CDefn
rmFreeTypeVars defn
    | null typeVars = Right defn
    | not (null unresolvedTypeVarsNum) = Left msgs
    | null typeVarsBad =
        Right (apSub substitution defn)
    | otherwise = internalError ("Typecheck.rmFreeD: toplevel type vars with" ++
                                 " kind neither * nor #:\n" ++
                                 ppReadable [(var, kind var) | var <- typeVarsBad] ++
                                 ppReadable defn)
    where typeVars = getFree defn
          (unresolvedTypeVarsNum, typeVars') = partition ((== KNum) . kind) typeVars
          (typeVarsStar, typeVarsBad) = partition ((== KStar) . kind) typeVars'
          substitution = mkSubst (zip typeVarsStar (repeat tPrimUnit))
          msgs = [(getPosition var, EUnknownSize) | var <- unresolvedTypeVarsNum]

-- get free type variables and hints about unknown size bit vectors
getFree :: CDefn -> [TyVar]
getFree (CValueSign (CDefT i vs qt cs)) = concatMap (getFreeC vs) cs
getFree d = []

getFreeC :: [TyVar] -> CClause -> [TyVar]
getFreeC vs (CClause ps qs e) = concatMap (getFreeQ vs) qs ++ getFreeE vs e

getFreeQ :: [TyVar] -> CQual -> [TyVar]
getFreeQ vs (CQGen t p e) = getFreeT vs t ++ getFreeE vs e
getFreeQ vs (CQFilter e) = getFreeE vs e

getFreeE :: [TyVar] -> CExpr -> [TyVar]
--getFreeE vs (CLam i e) = getFreeE vs e
--getFreeE vs (CLamT i _ e) = getFreeE vs e
getFreeE vs (Cletseq ds e) = concatMap (getFreeD vs) ds ++ getFreeE vs e
getFreeE vs (Cletrec ds e) = concatMap (getFreeD vs) ds ++ getFreeE vs e
getFreeE vs (CSelectT ti i) = []
getFreeE vs (CConT t i es) = concatMap (getFreeE vs) es
--getFreeE vs (Ccase _ _ _) =
getFreeE vs (CStructT t fs) = getFreeT vs t ++ concatMap (getFreeE vs . snd) fs
getFreeE vs e@(CAny {}) = []
getFreeE vs e@(CVar _) = []
getFreeE vs e@(CApply f es) = getFreeE vs f ++ concatMap (getFreeE vs) es
-- task application is the same as a normal application here
-- except checking the type for free variables (as CmoduleVerilogT does)
getFreeE vs e@(CTaskApplyT f t es) = getFreeT vs t ++ getFreeE vs f ++ concatMap (getFreeE vs) es
getFreeE vs e@(CLit _) = []
--getFreeE vs (CBinOp _ _ _) =
--getFreeE vs (CHasType _ _) =
--getFreeE vs (Cif _ _ _ _) =
--getFreeE vs (Csub _ _) =
getFreeE vs (Crules _ rs) = concatMap (getFreeR vs) rs
getFreeE vs (CTApply e ts) = getFreeE vs e ++ concatMap (getFreeT vs) ts
--getFreeE vs (CmoduleVerilog e _ _ _ ses _ _ _) =
getFreeE vs (CmoduleVerilogT t e es _ _ ses _ _ _) =
   getFreeT vs t ++ getFreeE vs e ++ concatMap (getFreeE vs . snd) ses
--getFreeE vs (CForeignFuncC _ cqt) =
getFreeE vs (CForeignFuncCT _ t) = getFreeT vs t
getFreeE vs e@(CLitT t _) = getFreeT vs t
getFreeE vs e@(CAnyT _ _ t) = getFreeT vs t
getFreeE vs e@(Cattributes _) = []
getFreeE vs e = internalError ("TypeCheck.getFreeE: " ++ ppReadable e ++ "\nshowing " ++ show e )

getFreeD :: [TyVar] -> CDefl -> [TyVar]
getFreeD vs (CLValueSign (CDefT i vs' qt cs) qs) =
        let vs'' = vs' ++ vs
        in  getFreeQT vs'' qt ++ concatMap (getFreeC vs'') cs ++ concatMap (getFreeQ vs) qs
getFreeD vs _ = internalError "TypeCheck.getFreeD: not CLValueSign"

getFreeT :: [TyVar] -> CType -> [TyVar]
getFreeT vs (TVar v) | v `notElem` vs = [v]
getFreeT vs (TAp t1 t2) = getFreeT vs t1 ++ getFreeT vs t2
getFreeT vs t = []

getFreeQT :: [TyVar] -> CQType -> [TyVar]
getFreeQT vs (CQType ps t) = getFreeT vs t                -- XXX ps

getFreeR :: [TyVar] -> CRule -> [TyVar]
getFreeR vs (CRule _ mi qs e) = getFreeME vs mi ++ concatMap (getFreeQ vs) qs ++ getFreeE vs e
getFreeR vs (CRuleNest _ mi qs rs) = getFreeME vs mi ++ concatMap (getFreeQ vs) qs ++ concatMap (getFreeR vs) rs

getFreeME :: [TyVar] -> Maybe CExpr -> [TyVar]
getFreeME vs Nothing = []
getFreeME vs (Just e) = getFreeE vs e
