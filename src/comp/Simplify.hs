module Simplify(simplify) where
import Data.List(partition)
import Util(mapSnd)
import ListMap(lookupWithDefault)
import qualified Data.Set as S
import qualified Data.Map as M
import PPrint(PPrint, ppReadable, ppString)
import ErrorUtil(internalError)
import Id(Id, isKeepId, isDictId)
import CSyntax
import CSyntaxTypes()
import CFreeVars(getFVE, getPV, getFVD)
import Subst
import CType(getCQArrows)
import SCC
import Util(tracep)
import IOUtil(progArgs)
import Flags(Flags, simplifyCSyntax)
--import Debug.Trace

--import Util(traces)

trace_simplify :: Bool
trace_simplify = "-trace-simplify" `elem` progArgs

traced :: (PPrint a, PPrint b) => String -> a -> b -> b
traced name orig result =
    let message = "Simplify trace: " ++ name ++ ":\n" ++ ppReadable orig ++
                  "=====>\n" ++ ppReadable result
    in  tracep trace_simplify message result

-- XXX not updated for let/letrec split

simplify :: Flags -> CPackage -> CPackage
simplify flags pkg@(CPackage mi exps imps impsigs fixs ds includes)
    | simplifyCSyntax flags =
        let (env, _) = selectSimple [] [ d | CValueSign d <- ds ]
        in  CPackage mi exps imps impsigs fixs (simp env ds) includes
    | otherwise = pkg

cLetRec :: [CDefl] -> CExpr -> CExpr
cLetRec [] e = e
-- turns
--   (let) i :: _ = e in i  (i not in freevars of e)
-- into
--   e
cLetRec orig@[CLValueSign (CDefT i [] _ [CClause [] [] e]) []] (CVar i')
    | i == i' && not (isKeepId i) && not (S.member i (snd (getFVE e))) =
        traced "Simplify.cLetRec" orig e
cLetRec ds e = Cletrec (map optBind ds) e

-- turns
--   let i .v1 ... .vn p1 ... pn :: qt = let i' p1' ... pn' :: qt' = e in i'
--       (i' not in free vars of e)
-- into
--   let i .v1 ... .vn p1 .. pn p1' .. pn' :: qt = e
optBind :: CDefl -> CDefl
optBind orig@(CLValueSign (CDefT i vs qt [CClause ps [] (Cletrec [CLValueSign (CDefT i' [] _ [CClause ps' [] e]) []] (CVar i''))]) [])
        | i' == i'' && not (isKeepId i') && not (S.member i' (snd (getFVE e))) =
            (traced "Simplify.optBind" orig
             (CLValueSign (CDefT i vs qt [CClause (ps++ps') [] e]) []))

optBind b = b

isSimple :: CExpr -> Bool
isSimple (CAnyT {}) = True
isSimple (CVar _) = True
isSimple (CConT _ _ []) = True
isSimple (CTApply e _) = isSimple e
isSimple _ = False

{- never used
isSimpleL :: CDefl -> Bool
isSimpleL (CLValueSign (CDefT _ _ _ [CClause [] [] e]) []) = isSimple e
isSimpleL _ = False
-}

class Simp a where
    simp :: Env -> a -> a

type Env = [(Id, (CExpr, CQType))]

-- drop substitutions that replace identifiers from is
dropIs :: [Id] -> Env -> Env
dropIs is substs = filter ((`notElem` is) . fst) substs

-- sep substitutions whose RHSs have free vars in is
--   returns (captured, noncaptured) environments
sepCaptures :: [Id] -> Env -> (Env, Env)
sepCaptures is substs =
    let isCapture (from, (to, _)) =
            let fvs = snd (getFVE to) in any (`S.member` fvs) is
    in  partition isCapture substs

instance (Simp a) => Simp [a] where
    simp r xs = map (simp r) xs

instance Simp CDefn where
    simp r (CValueSign d) = CValueSign (simp r d)
    simp r d = d

instance Simp CDef where
    -- turns
    --   (let) i .v1 ... .vn p1 .. pn :: t =
    --            let i' .v1' ... .vn' p1' ... pn' = e' when q1' ... qn'
    --                i' .v1' ... .vn' p1'' ... pn'' = e'' when q1'' .. qn''
    --                ...
    --            in  i'
    --         when q1 ... qn
    -- into
    --   (let) i .v1 ... .vn p1 ... pn p1' ... pn' = e'
    --             when q1 .. qn, q1' .. qn'
    --         i .v1 ... .vn p1 ... pn p1'' ... pn'' = e''
    --             when q1 .. qn, q1'' .. qn''
    --         ...
    simp r def@(CDefT i vs t cs) =
        case simp r cs of
        [CClause ps qs (Cletrec [CLValueSign (CDefT i' vs' _ cs) []] (CVar i''))]
            | i' == i'' && not (isKeepId i') ->
                CDefT i vs t [CClause (ps ++ ps') (qs ++ qs') e | CClause ps' qs' e <- cs]
        cs -> CDefT i vs t cs
    simp r def@(CDef _ _ _) = internalError "Simplify.Simp(CDef).simp: CDef"

-- XXX susceptible to bug #168
instance Simp CClause where
    simp r clause@(CClause ps qs e)
        | null captures = CClause ps (simp r' qs) (simp r' e)
        | otherwise =
            internalError ("Simplify.simp:CClause: pattern-captured free " ++
                           "vars (bug #168):\n  pattern vars: " ++
                           ppString patternVars ++ "\n" ++
                           concat ["  captured: " ++
                                   ppString v ++ " = " ++ ppString e ++ "\n"
                                   | (v,(e,_)) <- captures])
        where patternVars = concatMap (S.toList . getPV) ps
              r' = dropIs patternVars r
              (captures, _) = sepCaptures patternVars r'

instance Simp CRule where
    simp r (CRule rps mi qs e) = CRule rps (simp r mi) (simp r qs) (simp r e)
    simp r (CRuleNest rps mi qs rs) = CRuleNest rps (simp r mi) (simp r qs) (simp r rs)

instance Simp CQual where
    simp r (CQGen t p e) = CQGen t p (simp r e)
    simp r (CQFilter e) = CQFilter (simp r e)

instance Simp CExpr where
    -- let i = e
    -- in  let i' = i
    --     in  e'
    --  ==>  when i' not in FV(e), i not in FV(e)
    -- let i' = e in e' [i'/i]
    simp r orig@(Cletrec [CLValueSign (CDefT i [] qtype [CClause [] [] e]) []]
                 (Cletrec [CLValueSign
                        (CDefT i' [] qtype' [CClause [] [] (CVar i'')]) []]
                  e'))
        | i == i''
          && not (isKeepId i ||
                  i' `S.member` snd (getFVE e) ||
                  i `S.member` snd (getFVE e)) =
              let r' = (i, (CVar i', qtype)):r -- new environment
                  result = cLetRec [CLValueSign
                                 (CDefT i' [] qtype'
                                  [CClause [] [] (simp r' e)]) []]
                           (simp r' e')
              in  traced "Simplify.Simp(CExpr).simp[1]" orig result
--  simp r (CLam i e) = CLam i (simp (dropIs [i] r) e)
    -- turns
    --   let f x1 x2 x3 = e in f e1 e2 e3
    -- into
    --   e where x1 bound to e1 etc
    -- XXX is this susceptible to #166?  analyze!
    simp r orig@(Cletrec [CLValueSign (CDefT i [] qtype [CClause ps [] e]) []]
                 (CApply (CVar i') es))
        | (i == i' && not (isKeepId i) && length ps == length es
           && length argTypes == length es && all isCPVar ps
           && not (i `S.member` snd (getFVE e))) =
          traced "Simplify.Simp(CExpr).simp[2]" orig $
          simp (zip [ x | CPVar x <- ps ] ets ++ r) e
       where (argTypes, _) = getCQArrows qtype
             ets = zip es argTypes
    -- turns
    --   let f .a1 .a2 .a3 x1 x2 x3 = e in f .t1 .t2 .t3 e1 e2 e3
    -- into
    --   e where .t1 substituted for a1, x1 bound to e1, etc
    -- where f has type variables
    -- XXX is this susceptible to #166?  analyze!
    simp r orig@(Cletrec [CLValueSign (CDefT i vs qtype [CClause ps [] e]) []]
                 (CApply (CTApply (CVar i') ts) es))
        | (i == i' && not (isKeepId i) && length vs == length ts
           && length ps == length es && all isCPVar ps
           && not (i `S.member` snd (getFVE e))) =
          traced "Simplify.Simp(CExpr).simp[3]" orig $
          simp (zip [ x | CPVar x <- ps ] ets ++ r)
                    (apSub typeVarSubst e)
       where (argTypes, _) = getCQArrows qtype
             ets = zip es (map (apSub typeVarSubst) argTypes)
             typeVarSubst = mkSubst (zip vs ts)
    simp r orig@(Cletrec ds e) =
        let capturedVars :: [Id]
            capturedVars = S.toList $ S.unions $ map capturedVarsCDefl ds
            -- drop substitutions of vars shadowed by let-bindings
            rd = dropIs capturedVars r
            -- let for environment bindings whose RHSs have free vars
            -- captured by ds (avoids bug #166)
            (captures, rd') = sepCaptures capturedVars rd
            capturedDefs = [CLValueSign (CDefT var [] t [CClause [] [] e]) []
                            | (var, (e, t)) <- captures]
            -- sep substitutions with any capturedVars free on the RHS
            (r', ds') = selectSimpleL rd' (simp rd' ds)
            blurb =("simp[4]:\n* capturedVars =\n" ++ ppReadable capturedVars ++
                    "* r =\n" ++ ppReadable r ++
                    "* rd =\n" ++ ppReadable rd ++
                    "* captures=\n" ++ ppReadable captures ++
                    "* rd' =\n" ++ ppReadable rd' ++
                    "* r' =\n" ++ ppReadable r')
         in traced ("Simplify.Simp(CExpr).simp[4]\n"++blurb++"\n") orig $
            cLetRec capturedDefs (cLetRec ds' (simp r' e))
    simp r (CSelectT ti i) = CSelectT ti i
    simp r (CConT t i es) = CConT t i (simp r es)
--  simp r (Ccase _ _ _) =
    simp r (CStructT i fs) = CStructT i (mapSnd (simp r) fs)
    simp r e@(CAny {}) = e
    simp r orig@(CVar i)
         | isSame = result
         | otherwise = traced "Simplify.Simp(CExpr).simp[5]" orig result
        where err = internalError "Simplify.Simp.simp: CVar"
              result = fst (lookupWithDefault r (orig, err) i)
              isSame = case result of
                         CVar i' -> (i == i')
                         _ -> False

    simp r orig@(CApply (CApply f es) es') =
        traced "Simplify.Simp(CExpr).simp[6]" orig $
        simp r (CApply f (es ++ es'))
    simp r orig@(CApply f []) = simp r f
    simp r (CApply f es) = CApply (simp r f) (simp r es)
-- CTaskApply should be gone after type-checking
--    simp r (CTaskApply task es) = (CTaskApply (simp r task) (simp r es))
    simp r (CTaskApplyT task t es) = (CTaskApplyT (simp r task) t (simp r es))
    simp r e@(CLit _) = e
--  simp r (CBinOp _ _ _) =
--  simp r (CHasType _ _) =
--  simp r (Cif _ _ _ _) =
--  simp r (Csub _ _) =
    simp r (Crules ps rs) = Crules ps (map (simp r) rs)
    simp r orig@(CTApply (CTApply e ts) ts') =
        traced "Simplify.Simp(CExpr).simp[7]" orig $
        simp r (CTApply e (ts ++ ts'))
    simp r (CTApply e []) = simp r e
    simp r (CTApply e ts) = CTApply (simp r e) ts
    simp r e@(CLitT _ _) = e
    simp r e@(CAnyT {}) = e
--  simp r (CmoduleVerilog m ui c rs ses fs sch ps) =
    simp r (CmoduleVerilogT t m ui c rs ses fs sch ps) =
        CmoduleVerilogT t (simp r m) ui c rs (mapSnd (simp r) ses) fs sch ps
--  simp r e@(CForeignFuncC { }) =
    simp r e@(CForeignFuncCT { }) = e
    simp r e@(Cattributes _) = e
    simp r e = internalError ("Simplify.Simp(CExpr).simp: " ++ ppReadable e)

instance Simp CDefl where
    simp r defl@(CLValueSign d me) =
        CLValueSign (simp r d) (simp r me)
    simp r (CLValue _ _ _) = internalError "Simplify.Simp(CDefl).simp: CLValue"
    simp r (CLMatch _ _) = internalError "Simplify.Simp(CDefl).simp: CLMatch"

instance (Simp a) => Simp (Maybe a) where
    simp r Nothing = Nothing
    simp r (Just x) = Just (simp r x)

selectSimple :: Env -> [CDef] -> (Env, [CDef])
selectSimple env defs =
    let defNames = S.fromList (map getDName defs)
        defMap = M.fromList [(getDName def, def) | def <- defs]
        defDeps = [(name, S.toList (S.delete name
                                    (snd (getFVD def) `S.intersection` defNames)))
                   | def <- defs, let name = getDName def]
        defDepMap = M.fromList defDeps
        defSCCs = scc defDeps
        isSingleton [_] = True
        isSingleton _ = False
        (defSimple, defLoops) = partition isSingleton defSCCs
        orderedSimpleDefs =
            case tsort [(name,
                         (M.findWithDefault (errLook name) name defDepMap))
                        | name <- concat defSimple] of
                Right order -> [M.findWithDefault (errLook name) name defMap
                                | name <- order]
                Left loops -> errSort loops
        loopyDefs = [M.findWithDefault (errLook name) name defMap
                     | name <- concat defLoops]
        errSort ls = internalError ("Simplify.selectSimple: tsort failed: " ++
                                    ppReadable ls ++ "\n    defDeps = " ++
                                    ppReadable defDeps ++ "\n    defSCCs = " ++
                                    ppReadable defSCCs)
        errLook i = internalError ("Simplify.selectSimple: lookup failed: " ++
                                   ppString i ++ "\n    defDeps = " ++
                                   ppReadable defDeps ++ "\n    defSCCs = " ++
                                   ppReadable defSCCs)
        (newEnv, simplifiedDefs) = selectSimple' env [] orderedSimpleDefs
    in  (newEnv, simplifiedDefs ++ loopyDefs)

selectSimple' :: Env -> [CDef] -> [CDef] -> (Env, [CDef])
selectSimple' r rds [] =
    --traces "selectSimple returns" $
    (r, reverse rds)
-- (let) i :: _ = e
--   ==> [e/i]
selectSimple' r rds (CDefT i [] t [CClause [] [] e] : ds)
    | not (isKeepId i) && (isDictId i || isSimple e) =
    --traces ("simple "++ ppReadable (i,e)) $
    selectSimple' ((i, (e, t)) : [(i', (simp r' e', t')) | (i', (e', t')) <- r])
                     (simp r' rds) (simp r' ds)
    where r' = [(i, (e, t))]
selectSimple' r rds (d:ds) = selectSimple' r (d:rds) ds

selectSimpleL :: Env -> [CDefl] -> (Env, [CDefl])
selectSimpleL r lds =
    --traces ("selectSimpleL " ++ show (length r) ++ "\nr=" ++ ppReadable r ++ "\nlds=" ++ ppReadable lds) $
    case selectSimple r [ d | CLValueSign d [] <- lds ] of
    (r', ds) -> (r', map (flip CLValueSign []) ds ++ [ ld | ld@(CLValueSign _ (_ : _)) <- lds ])
--    traces ("selectSimpleL returns:\nr=" ++ ppReadable r' ++
--                            "\nnoquals:\n" ++
--                            ppReadable (map (flip CLValueSign []) ds) ++
--                            "\nwithquals:\n" ++ ppReadable [ ld | ld@(CLValueSign _ (_ : _)) <- lds ] ++ "\n") $

isCPVar :: CPat -> Bool
isCPVar (CPVar _) = True
isCPVar _ = False

-- collect variables captured in a let arm
-- different from *bound* variables, e.g., consider:
--   let f x y = ... in ...
-- where the *bound* variables are [f] and *captured* variables are [f, x, y]
capturedVarsCDefl :: CDefl -> S.Set Id
capturedVarsCDefl (CLValueSign def _) = capturedVarsCDef def
capturedVarsCDefl (CLMatch pat e) = getPV pat
capturedVarsCDefl (CLValue var clauses _) =
    S.unions (S.singleton var : map capturedVarsClause clauses)

capturedVarsCDef :: CDef -> S.Set Id
capturedVarsCDef (CDefT var _ _ clauses) =
    S.unions (S.singleton var : map capturedVarsClause clauses)
capturedVarsCDef (CDef _ _ _) = internalError "Simplify.capturedVarsCDef: CDef"

capturedVarsClause :: CClause -> S.Set Id
capturedVarsClause (CClause pats _ _) = S.unions (map getPV pats)
