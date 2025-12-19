> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

> module Parser.BSV.CVParserImperative where

> import Data.List
> import Data.Maybe
> import Control.Monad
> import Control.Monad.State
> import qualified Data.Set as S
> import qualified Data.Map as M

> import Parsec hiding (getPosition)

> import Parser.BSV.CVParserCommon
> import Parser.BSV.CVParserAssertion
> import Parser.BSV.CVParserUtil
> import CSyntax hiding (cLetSeq, cLetRec)
> import CSyntaxUtil

> import Id
> import Position
> import CFreeVars
> import PVPrint
> import Type
> import VModInfo
> import SchedInfo
> import Pragma
> import Error(internalError, ErrMsg(..), EMsg)
> import PreIds
> import FStringCompat
> import PreStrings
> import SEMonad
> import Util

The list of identifiers x1,x2,... at position p:

> newIds :: Position -> [Id]
> newIds p = map (\ s -> mk_dangling_id s p) (newIdsN 1)
> newIdsN :: Integer -> [String]
> newIdsN n = ("x" ++ itos n):(newIdsN (n+1))


convert declarations + assignments to lets
make sure variables are not used in between declaration and assignment
id is function or method name when defining the function/method

> imperativeToCExpr :: Position -- start of block
>                   -> ImperativeFlags
>                   -> [ImperativeStatement] -- statements
>                   -> SV_Parser CExpr -- resulting parser
> imperativeToCExpr pos flags stmts =
>  do  cs <- emptyISConvState
>      let newVars = maybe [] (\t -> (Nothing, fst t) : snd t)
>                    (functionNameArgs flags)
>          declareAndAssign var =
>             do let v = snd var
>                    t = fst var
>                declare (getIdPosition v) v t []
>                assign (getIdPosition v) v ATNormal
>          convPipe = do mapM_ declareAndAssign newVars
>                        checkedStmts <- checkImperativeStmts (stmtContext flags) stmts
>                        convImperativeStmtsToCExpr pos flags True checkedStmts
>          initState = cs { issFunction = [functionNameArgs flags] }
>      -- mapM_ (\stmt -> traceM ("DEBUG: " ++ show stmt)) stmts >>
>      semToParser initState convPipe

helper function that lets us check how to wrap a split block by looking for
return statements
we accept any return instead of just looking for a terminal one because it
seems likely that will be closer to "the right thing" even if we become
more liberal about where return is allowed
we might need to start recursing into loops, though, if the parser becomes
more liberal

> hasISReturn :: ImperativeStatement -> Bool
> hasISReturn (ISReturn _ _) = True
> hasISReturn (ISAction _ _) = False
> hasISReturn (ISActionValue _ stmts) = any hasISReturn stmts
> hasISReturn (ISIf _ _ stmts1 mstmts2) = any hasISReturn stmts1 ||
>                                         fromMaybe False (fmap (any hasISReturn) mstmts2)
> hasISReturn (ISCase _ _ arms mdefault) = any (any hasISReturn) (map thd arms) ||
>                                          fromMaybe False (fmap ((any hasISReturn) . snd) mdefault)
> hasISReturn (ISCaseTagged _ _ arms mdefault) = any (any hasISReturn) (map fth4 arms) ||
>                                                fromMaybe False (fmap ((any hasISReturn) . snd) mdefault)
> hasISReturn (ISBeginEnd _ stmts) = any hasISReturn stmts
> hasISReturn _ = False

this function "imperativeToCExprForSplitAttribute" is used to wrap an
imperative statement in a splitDeep or nosplitDeep function.  see
pImperativeStmt

> imperativeToCExprForSplitAttribute :: Position
>                             -> ImperativeFlags
>                             -> [ImperativeStatement]
>                             -> SV_Parser CExpr
> imperativeToCExprForSplitAttribute pos flags stmts = do
>     cs <- emptyISConvState
>     semToParser cs
>                 (do
>                     let isAV = any hasISReturn stmts
>                     let wrapper = if isAV then ISActionValue else ISAction
>                     let a = [wrapper pos stmts]
>                     checkedStmts <- checkImperativeStmts (stmtContext flags) a
>                     convImperativeStmtsToCExpr pos flags True a
>                 )

When assigning or binding to a tuple of variables, see if we have type info
for all of the variables -- that is, were those variables declared with types.
If we have types for all the variables, then we can construct a type for the
tuple.  If any field is missing, we can't construct a partial type.
(This also reports an error if any of the Ids have not been declared.)
XXX If CType supported partial type information (such as adding a CTUnknown),
XXX then we could return a tuple with types where we know them.

> getIdOrTupleType :: IdOrTuple -> ISConvMonad (Maybe CQType)
> getIdOrTupleType vars =
>   let pos = getIdOrTuplePosition vars
>       getIdType i = do
>           inf <- getDeclInfo i
>           case inf of
>             Nothing -> cvtErr (getPosition i) (EExternalVarAssign (pvpString i))
>             Just mtps -> return mtps
>   in  case vars of
>         Right i -> do mtps <- getIdType i
>                       case mtps of
>                         (Nothing, _) -> return Nothing
>                         (Just t, ps) -> return $ Just (CQType ps t)
>         Left mis ->
>             if (all (isRight) mis)
>             then do mtpss <- mapM getIdType (getIdOrTupleNames vars)
>                     if all (isJust . fst) mtpss
>                       then let ts = map (fromJust . fst) mtpss
>                                ps = concatMap snd mtpss
>                            in  return $ Just (CQType ps (tMkTuple pos ts))
>                       else return Nothing
>             else return Nothing

For the following few functions the type a is either CExpr or CStmts.
Updates use a recursive call structure based around the following types to
build the update "from the outside in":

A LetFn adds a set of bindings to a CExpr or CStmts.

> type LetFn a = [CDefl] -> a -> a

An UpdateFn takes an expression which is the "right-hand-side" of the
update, a monadic value which represents the computation within
the scope of the update, and a LetFn.  It produces a monadic value
representing the computation including the update.

> type UpdateFn a = CExpr -> ISConvMonad a -> LetFn a -> ISConvMonad a

mkUpdate yields an UpdateFn given a list of variables to be bound.  It
is normally used by supplying the list of variables plus all three
arguments to the UpdateFn.

> mkUpdate :: IdOrTuple -> UpdateFn a
> mkUpdate vars expr doRest letFn =
>  do
>   mqt <- getIdOrTupleType vars
>   let pos = getIdOrTuplePosition vars
>       hasType = isJust mqt
>       qualType = fromJust mqt
>   let bs = case vars of
>              Right var ->
>                let cls = [CClause [] [] expr]
>                    def = CDef var qualType cls
>                in  if hasType
>                    then [CLValueSign def []]
>                    else -- XXX This has the possibility of assigning a value of
>                         -- XXX type different from the previous value
>                         [CLValue var cls []]
>
>              Left mis ->
>                let names = getIdOrTupleNames vars
>                    var_tuple = case names of
>                                  [] -> mkAcute (dummyId pos)
>                                  _  -> foldr1 mkConcatId (map mkAcute names)
>                    def_tuple = CDef var_tuple qualType [CClause [] [] expr]
>                in  if hasType
>                    then [CLValueSign def_tuple [],
>                          CLMatch (mkIdOrTupleCPat pos vars) (CVar var_tuple)]
>                    else -- XXX This has the possibility of assigning a value of
>                         -- XXX type different from the previous value
>                         [CLMatch (mkIdOrTupleCPat pos vars) expr]
>   body <- doRest
>   return $ letFn bs body

The following function recursively converts "s.a.b.c.d = e" to "s.a.b.c =
s.a.b.c{d = e}" if possible, returning Nothing otherwise. It also handles
square-bracketted suffixes and ranges, converting them to calls to primUpdateFn
and primUpdateRangeFn, respectively

maybeUpdateFn takes a position and expression and produces either Just
UpdateFn or Nothing.  The Nothing value is returned when an error is
encountered because selection is applied to a value that does not
support it.  It is up to the primary caller of maybeUpdateFn to detect
the Nothing returned and issue an appropriate error message.

Here is an example of how maybeUpdateFn handles a nested array update
like:
  arr[i][j] <- mkRegU();
On the first call, the CExpr will be a subscript of (arr[i]) with the
subscript j.  It will make a recursive call to produce an update
function for (arr[i]).  This will again make a recursive call to produce
an update function for the variable arr.  That call will yield an update
function "mkUpdate [arr]".  Using that function, the middle call
will construct a function which performs an update for arr[i].  The
outer call then uses that function construct a function which performs
an update for arr[i][j].  The original caller can then use that function
along with an expression for the right-hand-side to complete the update.

This function also accumulates a list of elements describing the complete
update sequence, such as ["6", "2", "arr"], used for naming bound
instances.

> maybeUpdateFn :: Position -> CExpr -> Maybe (CExpr, UpdateFn a)
> maybeUpdateFn p (CVar var) = Just (mkNameExpr var, mkUpdate (Right var))
> maybeUpdateFn p (CSelect expr id) =
>   case maybeUpdateFn p expr of
>     Nothing -> Nothing
>     Just (n,fn) -> Just (n', g) where
>        pos = getPosition id
>        n' = CApply (CVar (idPrimJoinNamesAt pos)) [n, mkNameExpr id]
>        g e doRest =
>          let e' = CStructUpd expr [(id, e)]
>          in fn e' doRest
> maybeUpdateFn p (CSub pos ev ei) =
>   case maybeUpdateFn p ev of
>     Nothing -> Nothing
>     Just (n,fn) -> Just (n', g) where
>        -- XXX should we share ei with a temporary?
>        n' = CApply (CVar (idPrimExtNameIdxAt pos)) [n, ei]
>        g e doRest =
>          let e' = (CApply (CVar (idPrimUpdateFn pos)) [posLiteral pos, ev, ei, e])
>          in fn e' doRest
> maybeUpdateFn pos (CSub2 expr_vec expr_hi expr_lo) =
>   case maybeUpdateFn pos expr_vec of
>          Nothing -> Nothing
>          -- the statename can't be used on a range-update
>          Just (n,fn) -> Just (n, g) where
>             g expr_rhs doRest =
>               let e' = CSubUpdate pos expr_vec (expr_hi, expr_lo) expr_rhs
>               in  fn e' doRest
> maybeUpdateFn _ _ = Nothing

> makeResultCExpr :: Position -> [Id] -> CExpr -> CExpr
>                 -> SEM [Error.EMsg] ISConvState CExpr
> makeResultCExpr pos updatedVars inside rest =
>     do let resultId = idTheResult pos
>            patVars = pMkTuple pos $ map CPVar updatedVars
>            processDeclInfo (Just (Just t, [])) = Just t
>            processDeclInfo _ = Nothing
>        maybeVarTypes <- mapM getDeclInfo updatedVars >>=
>                         return . sequence . map processDeclInfo
>        let makeResultLet Nothing =
>                CLValue resultId [CClause [] [] inside] []
>            makeResultLet (Just varTs) =
>                let t = CQType [] (tMkTuple pos varTs)
>                in  CLValueSign (CDef resultId t [CClause [] [] inside]) []
>            resultLet = makeResultLet maybeVarTypes
>        return (cLetSeq [resultLet]
>                (cLetSeq [CLMatch patVars $ CVar resultId] rest))

> convImperativeStmtsToCExpr :: ExprConverter
> convImperativeStmtsToCExpr blockPos flags atEnd (ISPatEq pos pat expr : rest) =
>     do body <- convImperativeStmtsToCExpr blockPos flags atEnd rest
>        return (cLetSeq [CLMatch pat expr] body)
> convImperativeStmtsToCExpr blockPos flags atEnd (ISEqual pos vars expr : rest) =
>     do mfname <- isFunctionNameIdOrTuple vars
>        case (mfname, rest) of
>          (Just _, []) | atEnd -> return expr
>          (Just var, _) -> cvtErr pos (ENonTerminalFunctionAssign (pvpString var) (endKeyword flags))
>          (Nothing, _) ->
>              do mkUpdate vars expr (convImperativeStmtsToCExpr blockPos flags atEnd rest) cLetSeq
> convImperativeStmtsToCExpr blockPos flags atEnd (ISUpdate pos struct expr : rest) =
>     do case maybeUpdateFn pos struct of
>          Nothing    -> cvtErr pos (EBadStructUpdate ("1:"++pvpString struct))
>          Just (_,f) -> f expr (convImperativeStmtsToCExpr blockPos flags atEnd rest) cLetSeq

> convImperativeStmtsToCExpr blockPos flags True ([ISBeginEnd pos stmts]) =
>     do pushState
>        let newFlags = flags { stmtContext = ISCExpression,
>                               endKeyword = Just "end" }
>        expr <- (checkImperativeStmts ISCExpression stmts
>                 >>= convImperativeStmtsToCExpr pos newFlags True)
>        popState
>        return expr

> convImperativeStmtsToCExpr blockPos flags atEnd (s@(ISBeginEnd pos stmts) : rest) =
>     do pushState
>        let updatedVars = S.toList $ getUFVISs stmts
>            resultExp = mkTuple pos $ map CVar updatedVars
>            newFlags = flags { stmtContext = ISCExpression,
>                               endKeyword = Just "end" }
>        inside <- (checkImperativeStmts ISCExpression (stmts++[ISNakedExpr pos resultExp])
>                   >>= convImperativeStmtsToCExpr pos newFlags False)
>        popState
>        mapM_ (\ v -> assign pos v ATNormal) updatedVars
>        body <- convImperativeStmtsToCExpr blockPos flags atEnd rest
>        makeResultCExpr pos updatedVars inside body

> convImperativeStmtsToCExpr blockPos flags True ([ISAction pos stmts]) =
>     do pushState
>        inside <- (checkImperativeStmts ISCAction stmts
>                   >>= convImperativeStmtsToCStmts (ISCAction,Nothing,Nothing) True)
>        popState
>        return (Caction pos inside)
> convImperativeStmtsToCExpr blockPos flags True ([ISActionValue pos stmts]) =
>     do pushState
>        inside <- (checkImperativeStmts ISCActionValue stmts
>                   >>= convImperativeStmtsToCStmts (ISCActionValue,Nothing,Nothing) True)
>        when (not (endsWithReturn inside)) (cvtErr pos EActionValueWithoutValue)
>        popState
>        return (Cdo False inside)
> convImperativeStmtsToCExpr blockPos flags atEnd (ISAction pos stmts : rest) =
>     do cvtErr pos (ENonTerminalAction (endKeyword flags))
> convImperativeStmtsToCExpr blockPos flags atEnd (ISActionValue pos stmts : rest) =
>     do cvtErr pos (ENonTerminalActionValue (endKeyword flags))

> convImperativeStmtsToCExpr blockPos flags True ([ISIf pos conds consStmts altStmts]) =
>     do pushState
>        when (isNothing altStmts) (cvtErr pos EExprBlockWithoutValue)
>        consExpr <- (checkImperativeStmts (stmtContext flags) consStmts
>                      >>= convImperativeStmtsToCExpr pos flags True)
>        altExpr  <- (checkImperativeStmts (stmtContext flags) (fromJust altStmts)
>                      >>= convImperativeStmtsToCExpr pos flags True)
>        popState
>        return (mkIf pos conds consExpr altExpr)

> convImperativeStmtsToCExpr blockPos flags atEnd (ISIf pos conds consStmts altStmts : rest) =
>     do pushState
>        let altStmtsUpdVars = maybe S.empty getUFVISs altStmts
>            updatedVars = S.toList (getUFVISs consStmts `S.union` altStmtsUpdVars)
>            resultExpr = mkTuple pos $ map CVar updatedVars
>            resultStmts = [ISNakedExpr pos resultExpr]
>            altStmtsWithResult = maybe resultStmts (++ resultStmts) altStmts
>        checkedConsStmts <- checkImperativeStmts (stmtContext flags) (consStmts ++ resultStmts)
>        consExpr <- convImperativeStmtsToCExpr pos flags False checkedConsStmts
>        checkedAltStmts <- checkImperativeStmts (stmtContext flags) altStmtsWithResult
>        altExpr <- convImperativeStmtsToCExpr pos flags False checkedAltStmts
>        let inside = mkIf pos conds consExpr altExpr
>        popState
>        body <- convImperativeStmtsToCExpr blockPos flags atEnd rest
>        makeResultCExpr pos updatedVars inside body

> -- XXX special case when all arms are constants
> -- XXX (should turn into a pattern-matching case-expression)

XXX perhaps should see whether the following few clauses could share code

> convImperativeStmtsToCExpr blockPos flags True ([ISCase casePos subject arms dfltArm]) =
>     do pushState
>        let convArm (armPos, tests, conseq) =
>                do pushState
>                   let conseqPos = getListPosWithDefault conseq armPos
>                   conseqExpr <-
>                       convImperativeStmtsToCExpr conseqPos flags True conseq
>                   let pattern = CPAny armPos
>                       filters = if null tests then []
>                                 else [CQFilter $ COper $ intersperse (CRator 2 (idOrAt armPos))
>                                       [CRand $
>                                        COper [CRand subject,
>                                                  CRator 2 (idEqualAt armPos),
>                                                  CRand test]
>                                        | test <- tests]]
>                   popState
>                   return (CCaseArm { cca_pattern = pattern,
>                                      cca_filters = filters,
>                                      cca_consequent = conseqExpr })
>            convDfltArm (armPos, conseq) = convArm (armPos, [], conseq)
>        caseArms <- mapM convArm arms
>        dfltArms <- mapM convDfltArm (maybeToList dfltArm)
>        let allArms = caseArms ++ dfltArms
>            subject = CStruct (Just True) (idPrimUnitAt casePos) []
>        popState
>        return (Ccase casePos subject allArms)

> convImperativeStmtsToCExpr blockPos flags atEnd (ISCase casePos subject arms dfltArm : rest) =
>     do pushState
>        let rightHandSides = concat ([conseq | (pos, tests, conseq) <- arms] ++
>                                     [conseq | (pos, conseq) <- maybeToList dfltArm])
>            updatedVars = S.toList (getUFVISs rightHandSides)
>            resultExpr = mkTuple casePos $ map CVar updatedVars
>            convArm (armPos, tests, conseq) =
>                do pushState
>                   let conseqPos = getListPosWithDefault conseq armPos
>                   checkedConseq <- checkImperativeStmts (stmtContext flags)
>                                    (conseq ++ [ISNakedExpr conseqPos resultExpr])
>                   conseqExpr <- convImperativeStmtsToCExpr conseqPos flags atEnd
>                                 checkedConseq
>                   let pattern = CPAny armPos
>                       filters = if null tests then []
>                                 else [CQFilter $ COper $ intersperse (CRator 2 (idOrAt armPos))
>                                       [CRand $
>                                        COper [CRand subject,
>                                                  CRator 2 (idEqualAt armPos),
>                                                  CRand test]
>                                        | test <- tests]]
>                   popState
>                   return (CCaseArm { cca_pattern = pattern,
>                                      cca_filters = filters,
>                                      cca_consequent = conseqExpr })
>            convMDfltArm Nothing = convArm (casePos, [], [])
>            convMDfltArm (Just (armPos, conseq)) = convArm (armPos, [], conseq)
>        caseArms <- mapM convArm arms
>        dfltArms <- mapM convMDfltArm [dfltArm]
>        let allArms = caseArms ++ dfltArms
>            subject = CStruct (Just True) (idPrimUnitAt casePos) []
>        popState
>        body <- convImperativeStmtsToCExpr blockPos flags atEnd rest
>        makeResultCExpr casePos updatedVars (Ccase casePos subject allArms) body

> convImperativeStmtsToCExpr blockPos flags True ([ISCaseTagged casePos subject arms dfltArm]) =
>     do pushState
>        let convArm (armPos, pat, tests, conseq) =
>                do pushState
>                   let -- XXX before removing updatedVars' and friends, convince yourself
>                       -- XXX that they *really* don't belong here...
>                       -- rightHandSides =
>                       --        concat ([conseq | (pos, pat, tests, conseq) <- arms] ++
>                        --                [conseq | (pos, conseq) <- maybeToList dfltArm])
>                       -- updatedVarList = S.toList updatedVars
>                       -- variables bound in the patterns
>                       -- allPatternVars =
>                       --    S.unions [getPV pat | (pos, pat, tests, conseq) <- arms]
>                       -- pattern vars which are updated in some places -- must not capture
>                       -- updatedVars = getUFVISs rightHandSides
>                       -- capturedVars = S.intersection allPatternVars updatedVars
>                       -- capturedPatternVars = capturedVars `S.intersection` getPV pat
>                       -- updatedVars' = [if var `S.member` capturedPatternVars
>                       --              then mkAcute var -- shadowed, preserve old value
>                       --              else var         -- not shadowed, allow updates
>                       --              | var <- updatedVarList]
>                       conseqPos = getListPosWithDefault conseq armPos
>                   checkedConseq <- checkImperativeStmts (stmtContext flags) conseq
>                   conseqExpr
>                       <- convImperativeStmtsToCExpr conseqPos flags True checkedConseq
>                   popState
>                   return (CCaseArm { cca_pattern = pat,
>                                      cca_filters = map CQFilter tests,
>                                      cca_consequent = conseqExpr })
>            convDfltArm (armPos, conseq) =
>                convArm (armPos, CPAny armPos, [], conseq)
>        -- bindings to avoid capturing any of capturedVars
>        --capturedVarBindings <- mapM mkCapturedBinding (S.toList capturedVars)
>        caseArms <- mapM convArm arms
>        dfltArms <- mapM convDfltArm (maybeToList dfltArm)
>        let allArms = caseArms ++ dfltArms
>        popState
>        return (Ccase casePos subject allArms)

> convImperativeStmtsToCExpr blockPos flags atEnd (ISCaseTagged casePos subject
>                                            arms dfltArm : rest) =
>     do pushState
>        let rightHandSides = concat ([conseq
>                                      | (pos, pat, tests, conseq) <- arms] ++
>                                     [conseq
>                                      | (pos, conseq) <- maybeToList dfltArm])
>            updatedVars = getUFVISs rightHandSides
>            updatedVarList = S.toList updatedVars
>            -- variables bound in the patterns
>            allPatternVars = S.unions
>                             [getPV pat | (pos, pat, tests, conseq) <- arms]
>            -- pattern vars which are updated in some places -- must not capture
>            capturedVars = S.intersection allPatternVars updatedVars
>            -- make bindings to avoid capturing an assigned pattern variable
>            mkCapturedBinding var =
>                do info <- getDeclInfo var
>                   when (isNothing info)
>                            (cvtErr (getPosition var)
>                             (EExternalVarAssign (pvpString var)))
>                   let var' = mkAcute var
>                       (mtyp,ps) = fromJust info
>                       typ = CQType ps (fromJust mtyp)
>                       cls = [CClause [] [] (CVar var)]
>                   return (if isNothing mtyp
>                            then CLValue var' cls []
>                            else CLValueSign (CDef var' typ cls) [])
>            convArm (armPos, pat, tests, conseq) =
>                do pushState
>                   let capturedPatternVars = capturedVars `S.intersection` getPV pat
>                       updatedVars' = [if var `S.member` capturedPatternVars
>                                       then mkAcute var -- shadowed, preserve old value
>                                       else var         -- not shadowed, allow updates
>                                       | var <- updatedVarList]
>                       resultExpr = mkTuple armPos $ map CVar updatedVars'
>                       conseqPos = getListPosWithDefault conseq armPos
>                   checkedConseq <- checkImperativeStmts (stmtContext flags)
>                                    (conseq ++ [ISNakedExpr conseqPos resultExpr])
>                   conseqExpr
>                       <- convImperativeStmtsToCExpr conseqPos flags atEnd checkedConseq
>                   popState
>                   return (CCaseArm { cca_pattern = pat,
>                                      cca_filters = map CQFilter tests,
>                                      cca_consequent = conseqExpr })
>            convMDfltArm Nothing = convArm (casePos, CPAny casePos, [], [])
>            convMDfltArm (Just (armPos, conseq)) =
>                convArm (armPos, CPAny armPos, [], conseq)
>        -- bindings to avoid capturing any of capturedVars
>        capturedVarBindings <- mapM mkCapturedBinding (S.toList capturedVars)
>        caseArms <- mapM convArm arms
>        dfltArms <- mapM convMDfltArm [dfltArm]
>        let allArms = caseArms ++ dfltArms
>        popState
>        body <- convImperativeStmtsToCExpr blockPos flags atEnd rest
>        resultCExpr <- (makeResultCExpr casePos updatedVarList
>                        (Ccase casePos subject allArms) body)
>        return (cLetSeq capturedVarBindings resultCExpr)

> convImperativeStmtsToCExpr blockPos flags atEnd wh@(ISWhile pos cond whbody : rest) =
>     do pushState
>        let updatedVars = S.toList $ getUFVISs whbody
>            f = idF pos
>            resultExp = mkTuple pos $ map CVar updatedVars
>            patVars = pMkTuple pos $ map CPVar updatedVars
>            call = CApply (CVar f) [resultExp]
>        info <- mapM getDeclInfo updatedVars
>        -- report external assigned variables
>        let xs = [v | (Nothing,v) <- zip info updatedVars]
>        when (not (null xs))
>             (cvtErrs [(getPosition var, EExternalVarAssign (pvpString var)) | var <- xs])
>        let mtpss = map fromJust info
>        -- report variables without type signature
>        let xs2 = [v | (Nothing,v) <- zip (map fst mtpss) updatedVars]
>        when (not (null xs2))
>             (cvtErrs [(getPosition var, ETypesRequired (pvpString var)) | var <- xs2])
>        inside <- (checkImperativeStmts (stmtContext flags)
>                   (whbody++[ISNakedExpr pos call])
>                       >>= convImperativeStmtsToCExpr pos (flags { stmtContext = ISCExpression }) False)
>        popState
>        let typeTuple = tMkTuple pos $ map (fromJust . fst) mtpss
>            fnQType = CQType (concat(map snd mtpss)) $ fn typeTuple typeTuple
>            loop = (cLetRec [CLValueSign (CDef f fnQType [CClause [patVars] [] $
>                              Cif pos cond inside resultExp]) [] ]
>                    call)
>        mapM_ (\ v -> assign pos v ATNormal) updatedVars
>        body <- convImperativeStmtsToCExpr blockPos flags atEnd rest
>        makeResultCExpr pos updatedVars loop body

> convImperativeStmtsToCExpr blockPos flags atEnd (ISFunction pos [] def : rest) =
>     do body <- convImperativeStmtsToCExpr blockPos flags atEnd rest
>        return (cLetRec [def] body)
> convImperativeStmtsToCExpr blockPos flags atEnd (ISFunction pos prags def : rest) =
>     internalError ("convImperativeStmtsToCExpr: ISFunction with pragmas at " ++ pvpString pos)
> convImperativeStmtsToCExpr blockPos flags atEnd (ISModule pos name (Just pragma)
>                                            moduleType definition : rest) =
>     -- User attributes are only allowed on top-level modules,
>     -- so error if any are found.  Compiler-added PPparam pragmas
>     -- can just be ignored here, so we filter them before the check.
>     case (filterPPparam pragma) of
>       Nothing -> convImperativeStmtsToCExpr blockPos flags atEnd
>                    (ISModule pos name Nothing moduleType definition : rest)
>       Just pragma' -> cvtErr (getPosition pragma') ENestedModulePragma
> convImperativeStmtsToCExpr blockPos flags atEnd (ISModule pos name Nothing
>                                            moduleType definition : rest) =
>     do let def = CDef name moduleType [definition]
>        body <- convImperativeStmtsToCExpr blockPos flags atEnd rest
>        return (cLetSeq [CLValueSign def []] body)
> convImperativeStmtsToCExpr blockPos flags _ [ISReturn pos (Just expr)] = return expr
> convImperativeStmtsToCExpr blockPos flags _ (ISReturn pos expr : rest) =
>     cvtErr pos (ENonTerminalReturn (endKeyword flags))
> convImperativeStmtsToCExpr blockPos flags atEnd stmts@(ISMethod pos _ : rest)
>     | atEnd && all isISMethod rest =
>         do let methods = [method | ISMethod _ method <- stmts]
>            return (Cinterface pos Nothing methods)
>     | otherwise =
>         cvtErr pos (ENonTerminalMethodsOrSubinterfaces (endKeyword flags))
> convImperativeStmtsToCExpr blockPos flags atEnd stmts@(ISRule pos _ _ _ : rest)
>     | atEnd && all isISRule rest =
>         do let rules = [rule | ISRule _ _ _ rule <- stmts]
>                prags = concat [ps | ISRule _ _ ps _ <- stmts]
>            return (Crules prags rules)
>     | otherwise = cvtErr pos (ENonTerminalRules (endKeyword flags))
> convImperativeStmtsToCExpr blockPos flags _ [ISNakedExpr pos expr] = return expr
> convImperativeStmtsToCExpr blockPos flags _ (ISNakedExpr pos expr : rest) =
>     cvtErr pos (ENonTerminalNakedExpr (endKeyword flags))
> -- XXX noPosition
> convImperativeStmtsToCExpr blockPos flags atEnd []
>     | atEnd && (stmtContext flags) == ISCInterface = do return (Cinterface blockPos Nothing [])
>     | atEnd && (stmtContext flags) == ISCRules = do return (Crules [] [])
>     | atEnd && (stmtContext flags) == ISCInstance = -- "never looked at"
>         do return (CVar (internalError "CVParserImperative.convImperativeStmtsToCExpr N/E ISCInst"))
>     | otherwise = cvtErr blockPos EExprBlockWithoutValue

This next one is triggered by
(* split *)  or (* nosplit *)
let x=10;
...etc

The scope of a (* split *) or (* nosplit *) is supposed to be only the
next statement.  "let" statements superficially appear to be a single
statement, so in the above example, the attribute should be harmlessly
dropped.  However, because of rewriting into functional style, the
scope of the attribute extends to every statement afterwards, not what
we want.

> {-
> convImperativeStmtsToCExpr _ _ _ ((ISDecl pos _ _ _):_) =
>     cvtErr pos EDeclarationForbiddenImperativeToCExpr
> -}
> convImperativeStmtsToCExpr blockPos flags _ (stmt : stmts) =
>     internalError ("convImperativeStmtsToCExpr: " ++ (show stmt)
>                    ++ " at " ++ pvpString (getPosition stmt))

-- ---------------------------------

The purpose of the second and third elements of the tuple (first
argument) ought to be documented.

> imperativeToCStmts :: (ISContext, Maybe CType, Maybe CExpr) ->
>                          [ImperativeStatement] -> SV_Parser [CStmt]
> imperativeToCStmts cmtme@(ctxt,_,_) stmts =
>  do cs <- emptyISConvState
>     let convPipe = checkImperativeStmts ctxt stmts >>= convImperativeStmtsToCStmts cmtme True
>     semToParser cs convPipe

> sletFn :: [CDefl] -> [CStmt] -> [CStmt]
> sletFn defs ss = csLetseq defs ++ ss

> isInstNameAttrib :: (Position,PProp) -> Bool
> isInstNameAttrib (_, PPinst_name _) = True
> isInstNameAttrib _ = False

> convInstPProps :: Position -> [(Position,PProp)] ->
>                   ISConvMonad (Maybe Id, [(Position,PProp)])
> convInstPProps pos pprops = do
>     let (inst_pprops, rest_pprops) = partition isInstNameAttrib pprops
>     when (length inst_pprops > 1)
>          (cvtErr pos EUniqueInst)
>     let maybeInst_name = case inst_pprops of
>                              [(_, PPinst_name i)] -> Just i
>                              _ -> Nothing
>     return (maybeInst_name, rest_pprops)

> makeResultCStmts :: Position -> [Id] -> CExpr -> [IdProp]
>                  -> SEM [EMsg] ISConvState [CStmt]
> makeResultCStmts pos updatedVars inside props =
>     do let resultId = addIdProps (idTheResult pos) props
>            patVars = pMkTuple pos $ map CPVar updatedVars
>            processDeclInfo (Just (Just t, [])) = Just t
>            processDeclInfo _ = Nothing
>        maybeRetType <- mapM getDeclInfo updatedVars >>=
>                        (return . fmap (tMkTuple pos) .
>                         sequence . map processDeclInfo)
>        let makeBind Nothing = CSBind (CPVar resultId) Nothing [] inside
>            makeBind (Just t) =
>                CSBindT (CPVar resultId) Nothing [] (CQType [] t) inside
>        return (makeBind maybeRetType :
>                csLetseq [CLMatch patVars $ CVar resultId])

> convImperativeStmtsToCStmts ::
>     (ISContext, Maybe CType, Maybe CExpr) -> Bool
>           -> [ImperativeStatement] -> ISConvMonad [CStmt]

the next one is triggered by the following code

function int foo (int x) ;
        (* split *)
        if (x==10)
        return 20;
        else
        return 30;
endfunction


> convImperativeStmtsToCStmts (ISCExpression,_,_) atEnd stmts =
>     cvtErr (getPosition stmts) EExpressionStatementContext
> convImperativeStmtsToCStmts (ISCToplevel,_,_) atEnd stmts =
>     internalError ("CVParserImperative.convImperativeStmtsToCStmts: toplevel statement context (" ++ pvpString stmts ++ ")")
> convImperativeStmtsToCStmts (ISCIsModule,t,_) True [] = do
>     let it = case t of
>               Nothing -> Nothing
>               Just t  -> leftCon t
>     when (isNothing it) (cvtErr (getPosition t) EBadInterface)
>     return [CSExpr Nothing (CApply (CVar (idReturn noPosition)) [Cinterface noPosition it []])]
> convImperativeStmtsToCStmts ((ISCModule _),t,_) True [] = do
>     let it = case t of
>               Nothing -> Nothing
>               Just t  -> leftCon t
>     when (isNothing it) (cvtErr (getPosition t) EBadInterface)
>     return [CSExpr Nothing (CApply (CVar (idReturn noPosition)) [Cinterface noPosition it []])]
> convImperativeStmtsToCStmts _ _ [] = return []
> convImperativeStmtsToCStmts c_mt_me atEnd (ISPatEq pos pat expr : rest) =
>     do body <- convImperativeStmtsToCStmts c_mt_me atEnd rest
>        return (csLetseq [CLMatch pat expr] ++ body)
> convImperativeStmtsToCStmts c_mt_me@(context,_,_) atEnd (ISPatBind pos pat expr : rest) =
>     do body <- convImperativeStmtsToCStmts c_mt_me atEnd rest
>        -- let maybeNameExpr = if (isModuleContext context) then (Just (createPatternNameExpr pat pos)) else Nothing
>        let maybeNameExpr = Nothing
>        return ((CSBind pat  maybeNameExpr [] expr) : body)
> convImperativeStmtsToCStmts c_mt_me@(c,mt,me) atEnd (ISEqual pos vars expr : rest) =
>     do mfname <- isFunctionNameIdOrTuple vars
>        case (mfname, rest) of
>          (Just var, []) -> cvtErr pos (EForbiddenFunctionAssign (pvpString var) (pvpString c))
>          (Just var, _)  -> cvtErr pos (ENonTerminalFunctionAssign (pvpString var) Nothing)
>          (Nothing, _) -> mkUpdate vars expr (convImperativeStmtsToCStmts c_mt_me atEnd rest) sletFn

> convImperativeStmtsToCStmts c_mt_me atEnd (ISUpdate pos struct expr : rest) =
>     do case maybeUpdateFn pos struct of
>          Nothing    -> cvtErr pos (EBadStructUpdate ("2:"++pvpString struct))
>          Just (_,f) -> f expr (convImperativeStmtsToCStmts c_mt_me atEnd rest) sletFn

> convImperativeStmtsToCStmts c_mt_me@(context,_,_) atEnd ce@(ISUpdateBind pos pprops struct expr : rest) =
>     case maybeUpdateFn pos struct of
>       Nothing -> cvtErr pos (EBadStructUpdate ("3:"++pvpString struct))
>       Just (nameExpr,f) ->
>         do let c = idC pos
>            tail <- f (CVar c)
>                      (convImperativeStmtsToCStmts c_mt_me atEnd rest)
>                      sletFn
>            (maybeInst_name, rest_pprops) <- convInstPProps pos pprops
>            let maybeStateName =
>                  -- this should only be Just if it's a module context
>                  case maybeInst_name of
>                    Just i -> Just (mkNameExpr i)
>                    Nothing ->
>                      -- don't inject the state-naming for actionvalues
>                      if not (isModuleContext context)
>                      then Nothing
>                      else Just nameExpr
>                the_bind = CSBind (CPVar c) maybeStateName rest_pprops expr
>            return (the_bind : tail)

> convImperativeStmtsToCStmts c_mt_me atEnd (ISUpdateReg pos struct expr : rest) = do
>   stmts <- convImperativeStmtsToCStmts c_mt_me atEnd rest
>   -- traceM("ISUpdateReg: " ++ pvpReadable (struct, expr))
>   return ((CSExpr Nothing (Cwrite pos struct expr)) : stmts)

> convImperativeStmtsToCStmts c_mt_me@(context,_,_) True [ISBeginEnd pos stmts] =
>     do pushState
>        inside <- (checkImperativeStmts context stmts
>                       >>= convImperativeStmtsToCStmts c_mt_me True)
>        let cvtStmts | (context == ISCAction) = [CSExpr Nothing (Caction pos inside)]
>                     | isMonadicContext context = [CSExpr Nothing (Cdo False inside)]
>                     | otherwise = internalError "CVParserImperative.convImperativeToCStmts: ISBeginEnd"
>        popState
>        return cvtStmts
> convImperativeStmtsToCStmts c_mt_me@(context,_,_) atEnd (s@(ISBeginEnd pos stmts) : rest) =
>   if stmtIsNonMonadic s
>    then
>     do e <- convImperativeStmtsToCExpr pos
>                                        expressionFlags
>                                        False
>                                        [s, ISReturn pos (Just (anyExprAt pos))]
>        cvtRest <- convImperativeStmtsToCStmts c_mt_me atEnd rest
>        case e of
>          (Cletseq ds _) -> return (CSletseq ds : cvtRest)
>          _ -> internalError ("convImperativeStmtsToCStmts ISBeginEnd: " ++ show e)
>    else
>     do pushState
>        let updatedVars = S.toList $ getUFVISs stmts
>            resultExp = mkTuple pos $ map CVar updatedVars
>        varTypes <- mapM getDeclInfo updatedVars
>--        let resultType = CQType [] $ tMkTuple pos $ map fromJust varTypes
>        inside <- (checkImperativeStmts context (stmts ++ [ISReturn pos (Just resultExp)])
>                       >>= convImperativeStmtsToCStmts c_mt_me False)
>        standardResultStmts <-
>            makeResultCStmts pos updatedVars (Cdo False inside) []
>        let cvtStmts | null updatedVars && isActionContext context =
>                         [CSExpr Nothing (Caction pos inside)] -- optimized
>                     | otherwise = standardResultStmts
>        popState
>        mapM_ (\ v -> assign pos v ATNormal) updatedVars
>        cvtRest <- convImperativeStmtsToCStmts c_mt_me atEnd rest
>        return (cvtStmts ++ cvtRest)
> convImperativeStmtsToCStmts (ISCActionValue,_,_) True [ISAction pos stmts] =
>     cvtErr pos ETerminalAction
> convImperativeStmtsToCStmts c_mt_me@(context,_,_) atEnd (ISAction pos stmts : rest)
>     | isActionContext context =
>         do pushState
>            let updatedVars = S.toList $ getUFVISs stmts
>                resultExp = mkTuple pos $ map CVar updatedVars
>                stmtsWithTail | null updatedVars = stmts
>                              | otherwise = stmts ++ [ISReturn pos (Just resultExp)]
>            varTypes <- mapM getDeclInfo updatedVars
>--            let resultType = CQType [] $ tMkTuple pos $ map fromJust varTypes
>            inside <- (checkImperativeStmts context stmtsWithTail
>                       >>= convImperativeStmtsToCStmts c_mt_me False)
>            standardResultStmts <-
>                makeResultCStmts pos updatedVars (Cdo False inside) []
>            let cvtStmts | null updatedVars = [CSExpr Nothing $ Caction pos inside]
>                         | otherwise = standardResultStmts
>            popState
>            mapM_ (\ v -> assign pos v ATNormal) updatedVars
>            cvtRest <- convImperativeStmtsToCStmts c_mt_me atEnd rest
>            return (cvtStmts ++ cvtRest)
>       | otherwise = cvtErr pos (EForbiddenAction (pvpString context))
> -- XXX is this right, given runtime eval?  what's up with empty actionvalues?
> convImperativeStmtsToCStmts c_mt_me@(ISCActionValue,_,_) True [ISActionValue pos stmts] =
>     do pushState
>        inside <- (checkImperativeStmts ISCActionValue stmts
>                   >>= convImperativeStmtsToCStmts c_mt_me True)
>        when (not (endsWithReturn inside)) (cvtErr pos EActionValueWithoutValue)
>        let cvtStmts = [CSExpr Nothing (Cdo False inside)]
>        popState
>        return cvtStmts
> convImperativeStmtsToCStmts c_mt_me atEnd (ISActionValue pos stmts : rest) =
>     cvtErr pos (ENonTerminalActionValue Nothing)
> convImperativeStmtsToCStmts c_mt_me@(context,_,_) atEnd (ISWhile pos cond whbody : rest)
>     | not (isMonadicContext context) = cvtErr pos (EForbiddenWhile (pvpString context))
> convImperativeStmtsToCStmts
>        c_mt_me@(context,_,_) atEnd (w@(ISWhile pos cond whbody) : rest) =
>   if stmtIsNonMonadic w
>    then
>     do e <- convImperativeStmtsToCExpr pos
>                                        expressionFlags
>                                        False
>                                        [w, ISReturn pos (Just (anyExprAt pos))]
>        body <- convImperativeStmtsToCStmts c_mt_me atEnd rest
>        case e of
>          (Cletseq ds _) -> return (CSletseq ds : body)
>          _ -> internalError ("convImperativeStmtsToCStmts ISWhile: " ++ show e)
>    else
>     do pushState
>        let updatedVars = S.toList $ getUFVISs whbody
>            f = idF pos
>            (mVar, preds) = contextMonadInfo pos context
>            resultExp = mkTuple pos $ map CVar updatedVars
>            patVars = pMkTuple pos $ map CPVar updatedVars
>            call = CApply (CVar f) [resultExp]
>        info <- mapM getDeclInfo updatedVars
>        let xs = [v | (Nothing,v) <- zip info updatedVars]
>        when (not (null xs))
>             (cvtErrs [(getPosition var, EExternalVarAssign (pvpString var)) | var <- xs])
>        let mtpss = map fromJust info
>        let xs2 = [v | (Nothing,v) <- zip (map fst mtpss) updatedVars]
>        when (not (null xs2))
>             (cvtErrs [(getPosition var, ETypesRequired (pvpString var)) | var <- xs2])
>
>        inside <- (checkImperativeStmts context
>                   (whbody++[ISNakedExpr pos call])
>                       >>= convImperativeStmtsToCStmts c_mt_me False) --True)
>        popState
>        let typeTuple = tMkTuple pos $ map (fromJust . fst) mtpss
>            fnQType = CQType (preds ++(concat(map snd mtpss))) $ fn typeTuple (TAp mVar typeTuple)
>            ifConseq | null updatedVars && isActionContext context = Caction pos inside
>                     | otherwise = Cdo False inside
>            ifAlter | null updatedVars && isActionContext context = Caction pos []
>                    | otherwise = Cdo False [CSExpr Nothing (cVApply (idReturn pos) [resultExp])]
>            loop = (csLetrec [CLValueSign (CDef f fnQType [CClause [patVars] [] $
>                                                        Cif pos cond ifConseq ifAlter]) []])
>        standardResultStmts <- makeResultCStmts pos updatedVars call
>                               [IdP_keep, (IdPDisplayName fsLoop)]
>        let postLoop | null updatedVars && isActionContext context =
>                         [CSExpr Nothing call] -- optimized
>                     | otherwise = standardResultStmts
>        mapM_ (\ v -> assign pos v ATNormal) updatedVars
>        body <- convImperativeStmtsToCStmts c_mt_me atEnd rest
>        return (loop ++ postLoop ++ body)

> convImperativeStmtsToCStmts c_mt_me@(context,_,_) True [ISIf pos conds consStmts altStmts] =
>     do pushState
>        checkedConsStmts <- checkImperativeStmts context consStmts
>        consCStmts <- convImperativeStmtsToCStmts c_mt_me True checkedConsStmts
>        checkedAltStmts <- checkImperativeStmts context (maybe [] (\x->x) altStmts)
>        altCStmts <- convImperativeStmtsToCStmts c_mt_me True checkedAltStmts
>        let cvtStmt | context==ISCAction =
>                        -- XXX pos should be different for cons and alt
>                        [CSExpr Nothing $ mkIf pos conds (Caction pos consCStmts) (Caction pos altCStmts)]
>                    | otherwise = [CSExpr Nothing (mkIf pos conds (Cdo False consCStmts) (Cdo False altCStmts))]
>        popState
>        return cvtStmt

> convImperativeStmtsToCStmts c_mt_me@(context,_,_) atEnd (s@(ISIf pos conds consStmts altStmts) : rest) =
>   if stmtIsNonMonadic s
>    then
>     do e <- convImperativeStmtsToCExpr pos
>                                        expressionFlags
>                                        False
>                                        [s, ISReturn pos (Just (anyExprAt pos))]
>        body <- convImperativeStmtsToCStmts c_mt_me atEnd rest
>        case e of
>          (Cletseq ds _) -> return (CSletseq ds : body)
>          _ -> internalError ("convImperativeStmtsToCStmts ISIf: " ++ show e)
>    else
>     do pushState
>        let altStmtsUpdVars = maybe S.empty getUFVISs altStmts
>            updatedVars = S.toList (getUFVISs consStmts `S.union` altStmtsUpdVars)
>            resultExpr = mkTuple pos $ map CVar updatedVars
>            consStmtsWithResult = consStmts ++ [ISReturn pos (Just resultExpr)]
>            altStmtsWithResult = (maybe [] (\x->x) altStmts)++ [ISReturn pos (Just resultExpr)]
>        checkedConsStmts <- checkImperativeStmts context consStmtsWithResult
>        consCStmts <- convImperativeStmtsToCStmts c_mt_me False checkedConsStmts
>        checkedAltStmts <- checkImperativeStmts context altStmtsWithResult
>        altCStmts <- convImperativeStmtsToCStmts c_mt_me False checkedAltStmts
>        standardResultStmts <-
>            makeResultCStmts pos updatedVars (mkIf pos conds (Cdo False consCStmts) (Cdo False altCStmts)) []
>        let cvtStmt | null updatedVars && context==ISCAction =
>                        -- XXX pos should be different for cons and alt
>                        [CSExpr Nothing $ mkIf pos conds (Caction pos consCStmts) (Caction pos altCStmts)]
>                    | otherwise = standardResultStmts
>        popState
>        body <- convImperativeStmtsToCStmts c_mt_me atEnd rest
>        return (cvtStmt ++ body)

> convImperativeStmtsToCStmts c_mt_me@(context,_,_) True [ISCase casePos subject arms dfltArm] =
>     do pushState
>        let convArm (armPos, tests, conseq) =
>                do pushState
>                   checkedConseq <- checkImperativeStmts context conseq
>                   conseqCStmts <- convImperativeStmtsToCStmts c_mt_me True checkedConseq
>                   let conseqExpr =
>                        if context==ISCAction
>                         then Caction armPos conseqCStmts
>                         else Cdo False conseqCStmts
>                       pattern = CPAny armPos
>                       filters = if null tests then []
>                                 else [CQFilter $ COper $ intersperse (CRator 2 (idOrAt armPos))
>                                       [CRand $
>                                        COper [CRand subject,
>                                                  CRator 2 (idEqualAt armPos),
>                                                  CRand test]
>                                        | test <- tests]]
>                   popState
>                   return (CCaseArm { cca_pattern = pattern,
>                                      cca_filters = filters,
>                                      cca_consequent = conseqExpr })
>            convDfltActionArm Nothing                 = convArm (casePos, [], [ISAction casePos []])
>            convDfltActionArm (Just (armPos, conseq)) = convArm (armPos, [], conseq)
>            convDfltArm (armPos, conseq) = convArm (armPos, [], conseq)
>        caseArms <- mapM convArm arms
>        dfltArms <- (if context==ISCAction
>                      then mapM convDfltActionArm [dfltArm]
>                      else mapM convDfltArm (maybeToList dfltArm))
>        let allArms = caseArms ++ dfltArms
>            subject = CStruct (Just True) (idPrimUnitAt casePos) []
>        popState
>        return [CSExpr Nothing (Ccase casePos subject allArms)]

> convImperativeStmtsToCStmts c_mt_me@(context,_,_) atEnd
>                             (s@(ISCase casePos subject arms dfltArm) : rest) =
>   if stmtIsNonMonadic s
>    then
>     do e <- convImperativeStmtsToCExpr casePos
>                                        expressionFlags
>                                        False
>                                        [s, ISReturn casePos (Just (anyExprAt casePos))]
>        body <- convImperativeStmtsToCStmts c_mt_me atEnd rest
>        case e of
>          (Cletseq ds _) -> return (CSletseq ds : body)
>          _ -> internalError ("convImperativeStmtsToCStmts ISCase: " ++ show e)
>    else
>     do pushState
>        let rightHandSides = concat ([conseq | (pos, tests, conseq) <- arms]
>                                     ++ [conseq | (pos, conseq)
>                                                  <- maybeToList dfltArm])
>            updatedVars = S.toList (getUFVISs rightHandSides)
>            resultExpr = mkTuple casePos $ map CVar updatedVars
>            convArm (armPos, tests, conseq) =
>                do pushState
>                   let conseqPos = getListPosWithDefault conseq armPos
>                   checkedConseq <- checkImperativeStmts context
>                                    (conseq ++ [ISReturn conseqPos (Just resultExpr)])
>                   conseqCStmts <- convImperativeStmtsToCStmts c_mt_me atEnd
>                                   checkedConseq
>                   let conseqExpr = Cdo False conseqCStmts
>                       pattern = CPAny armPos
>                       filters = if null tests then []
>                                 else [CQFilter $ COper $
>                                       intersperse (CRator 2 (idOrAt armPos))
>                                       [CRand $
>                                        COper [CRand subject,
>                                                  CRator 2 (idEqualAt armPos),
>                                                  CRand test]
>                                        | test <- tests]]
>                   popState
>                   return (CCaseArm { cca_pattern = pattern,
>                                      cca_filters = filters,
>                                      cca_consequent = conseqExpr })
>            convMDfltArm Nothing = convArm (casePos, [], [])
>            convMDfltArm (Just (armPos, conseq)) = convArm (armPos, [], conseq)
>        caseArms <- mapM convArm arms
>        dfltArms <- mapM convMDfltArm [dfltArm]
>        let allArms = caseArms ++ dfltArms
>            subject = CStruct (Just True) (idPrimUnitAt casePos) []
>        popState
>        body <- convImperativeStmtsToCStmts c_mt_me atEnd rest
>        resultStmts <-
>            makeResultCStmts casePos updatedVars (Ccase casePos subject allArms) []
>        return (resultStmts ++ body)

> convImperativeStmtsToCStmts c_mt_me@(context,_,_) True
>                                 [ISCaseTagged casePos subject arms dfltArm] =
>     do pushState
>        let convArm (armPos, pat, tests, conseq) =
>                do pushState
>                   checkedConseq <- checkImperativeStmts context conseq
>                   conseqStmts
>                       <- convImperativeStmtsToCStmts c_mt_me True checkedConseq
>                   let conseqExpr = Cdo False conseqStmts
>                   popState
>                   return (CCaseArm { cca_pattern = pat,
>                                      cca_filters = map CQFilter tests,
>                                      cca_consequent = conseqExpr })
>            convDfltArm (armPos, conseq) =
>                convArm (armPos, CPAny armPos, [], conseq)
>            convDfltActionArm Nothing    =
>                convArm (casePos, CPAny casePos, [], [ISAction casePos []])
>            convDfltActionArm (Just (armPos, conseq)) =
>                convArm (armPos, CPAny armPos, [], conseq)
>        caseArms <- mapM convArm arms
>        dfltArms <- (if context==ISCAction
>                      then mapM convDfltActionArm [dfltArm]
>                      else mapM convDfltArm (maybeToList dfltArm))
>        let allArms = caseArms ++ dfltArms
>        popState
>        return [CSExpr Nothing (Ccase casePos subject allArms)]

> convImperativeStmtsToCStmts c_mt_me@(context,_,_) atEnd
>                                 (s@(ISCaseTagged casePos subject arms dfltArm)
>                                  : rest) =
>   if stmtIsNonMonadic s
>    then
>     do e <- convImperativeStmtsToCExpr casePos
>                                        expressionFlags
>                                        False
>                                        [s, ISReturn casePos (Just (anyExprAt casePos))]
>        body <- convImperativeStmtsToCStmts c_mt_me atEnd rest
>        case e of
>          (Cletseq ds _) -> return (CSletseq ds : body)
>          _ -> internalError ("convImperativeStmtsToCStmts ISCaseTagged: " ++ show e)
>    else
>     do pushState
>        let rightHandSides = concat ([conseq | (pos, pat, tests, conseq) <- arms] ++
>                                     [conseq | (pos, conseq) <- maybeToList dfltArm])
>            updatedVars = getUFVISs rightHandSides
>            updatedVarList = S.toList updatedVars
>            -- variables bound in the patterns
>            allPatternVars = S.unions [getPV pat | (pos, pat, tests, conseq) <- arms]
>            -- pattern vars which are updated in some places -- must not capture
>            capturedVars = S.intersection allPatternVars updatedVars
>            -- make bindings to avoid capturing an assigned pattern variable
>            mkCapturedBinding var =
>                do info <- getDeclInfo var
>                   when (isNothing info) (cvtErr (getPosition var) (EExternalVarAssign (pvpString var)))
>                   let var' = mkAcute var
>                       (mtyp,ps) = fromJust info
>                       typ = CQType ps (fromJust mtyp)
>                       cls = [CClause [] [] (CVar var)]
>                   return (if isNothing mtyp
>                            then CLValue var' cls []
>                            else CLValueSign (CDef var' typ cls) [])
>            convArm (armPos, pat, tests, conseq) =
>                do pushState
>                   let capturedPatternVars = capturedVars `S.intersection` getPV pat
>                       updatedVars' = [if var `S.member` capturedPatternVars
>                                       then mkAcute var -- shadowed, preserve old value
>                                       else var         -- not shadowed, allow updates
>                                       | var <- updatedVarList]
>                       resultExpr = mkTuple armPos $ map CVar updatedVars'
>                   checkedConseq <- checkImperativeStmts context
>                                    (conseq ++ [ISReturn armPos (Just resultExpr)])
>                   conseqStmts <- convImperativeStmtsToCStmts c_mt_me atEnd
>                                   checkedConseq
>                   let conseqExpr = Cdo False conseqStmts
>                   popState
>                   return (CCaseArm { cca_pattern = pat,
>                                      cca_filters = map CQFilter tests,
>                                      cca_consequent = conseqExpr })
>            convMDfltArm Nothing = convArm (casePos, CPAny casePos, [], [])
>            convMDfltArm (Just (armPos, conseq)) =
>                convArm (armPos, CPAny armPos, [], conseq)
>        -- bindings to avoid capturing any of capturedVars
>        capturedVarBindings <- mapM mkCapturedBinding (S.toList capturedVars)
>        caseArms <- mapM convArm arms
>        dfltArms <- mapM convMDfltArm [dfltArm]
>        let allArms = caseArms ++ dfltArms
>        popState
>        body <- convImperativeStmtsToCStmts c_mt_me atEnd rest
>        resultStmts <- makeResultCStmts casePos updatedVarList (Ccase casePos subject allArms) []
>        return (csLetseq capturedVarBindings ++ resultStmts ++ body)

> convImperativeStmtsToCStmts c_mt_me atEnd (ISBind pos pprops vars expr : rest) =
>     do mqt <- getIdOrTupleType vars
>        let pos = getIdOrTuplePosition vars
>            hasType = isJust mqt
>            qualType = fromJust mqt
>            pat = mkIdOrTupleCPat pos vars
>        (maybeInst_name, rest_pprops) <- convInstPProps pos pprops
>        let -- propagate state name if we're on a module monad and binding only one thing
>            maybeStateName =
>               case maybeInst_name of
>                      Just i -> Just i
>                      Nothing -> case (isModuleContext (fst3 c_mt_me), vars) of
>                                   (True, Right var) -> Just var
>                                   (True, Left [Right var]) -> Just var
>                                   _ -> Nothing
>            maybeNameExpr = fmap mkNameExpr maybeStateName
>        let s = if hasType
>                then CSBindT pat maybeNameExpr rest_pprops qualType expr
>                else -- XXX This has the possibility of assigning a value of
>                     -- XXX type different from the previous value
>                     CSBind pat maybeNameExpr rest_pprops expr
>        body <- convImperativeStmtsToCStmts c_mt_me atEnd rest
>        return (s:body)

> convImperativeStmtsToCStmts c_mt_me atEnd (ISFunction pos [] def : rest) =
>     do body <- convImperativeStmtsToCStmts c_mt_me atEnd rest
>        return (csLetrec [def] ++ body)
> convImperativeStmtsToCStmts c_mt_me atEnd (ISFunction pos prags def : rest) =
>     internalError "convImperativeStmtsToCStmts: ISFunction with pragmas"

> convImperativeStmtsToCStmts c_mt_me atEnd (ISModule pos name (Just pragma)
>                                            moduleType definition : rest) =
>     -- User attributes are only allowed on top-level modules,
>     -- so error if any are found.  Compiler-added PPparam pragmas
>     -- can just be ignored here, so we filter them before the check.
>     case (filterPPparam pragma) of
>       Nothing -> convImperativeStmtsToCStmts c_mt_me atEnd
>                    (ISModule pos name Nothing moduleType definition : rest)
>       Just pragma' -> cvtErr (getPosition pragma') ENestedModulePragma
> convImperativeStmtsToCStmts c_mt_me atEnd (ISModule pos name Nothing
>                                            moduleType definition : rest) =
>     do let def = CDef name moduleType [definition]
>        body <- convImperativeStmtsToCStmts c_mt_me atEnd rest
>        return (csLetseq [CLValueSign def []] ++ body)

> convImperativeStmtsToCStmts c_mt_me atEnd
>   (ISInst pos pprops ifcVar stateVar ifcType maybeCk maybeRt maybePr constructor : rest) =
>     do let qualType = CQType [] (fromJust ifcType)
>            pat = CPVar ifcVar
>            theModule = (if isNothing maybeCk && isNothing maybeRt && isNothing maybePr
>                          then constructor
>                          else cVApply (idChangeSpecialWires (getPosition constructor))
>                                       [mkMaybe maybeCk,
>                                        mkMaybe maybeRt,
>                                        mkMaybe maybePr,
>                                        constructor])
>        body <- convImperativeStmtsToCStmts c_mt_me atEnd rest
>        return (if isNothing ifcType
>                 then CSBind pat (Just (mkNameExpr stateVar)) pprops theModule : body
>                 else CSBindT pat (Just (mkNameExpr stateVar)) pprops qualType theModule : body)

> convImperativeStmtsToCStmts c_mt_me atEnd (ISRegWrite pos reg expr : rest) =
>     do body <- convImperativeStmtsToCStmts c_mt_me atEnd rest
>        return (CSExpr Nothing (CBinOp reg (mkId pos fsAssign) expr) : body)

> convImperativeStmtsToCStmts  c_mt_me@(context,_,_) atEnd all@(ISNakedExpr pos expr : rest)
>                              | (isModuleContext context) =
>     let getIdDef (CApply (CVar id_def) _) =  if (getIdBase id_def /= fsF) then (Just id_def) else Nothing
>         getIdDef (CVar id_def)            =  if (getIdBase id_def /= fsF) then (Just id_def) else Nothing
>         getIdDef _                        =  Nothing
>     in do body <- convImperativeStmtsToCStmts c_mt_me atEnd rest
>           let id_def  = getIdDef expr
>           let name = case (id_def) of
>                       Nothing -> Nothing
>                       Just id -> let display_name = getIdBase id
>                                      id'           = (setNakedInstId
>                                                        (setKeepId
>                                                          (setIdBase id (concatFString [mkFString "_inst", fsUnderscore, getIdBase id]))))
>                                  in Just (mkNameExpr (setIdDisplayName id' display_name))
>           return (CSExpr name expr : body)

> convImperativeStmtsToCStmts  c_mt_me atEnd (ISNakedExpr pos expr : rest) =
>     do body <- convImperativeStmtsToCStmts c_mt_me atEnd rest
>        return (CSExpr Nothing expr : body)

> convImperativeStmtsToCStmts _ _ [ISReturn pos (Just expr)] =
>     return [CSExpr Nothing (cVApply (idReturn pos) [expr])]
> convImperativeStmtsToCStmts _ _ (ISReturn pos _ : _) =
>     cvtErr pos (ENonTerminalReturn Nothing)

> convImperativeStmtsToCStmts c_mt_me@(context,_,_) atEnd (ISRule pos name ps rule : rest)
>                             | (isModuleContext context) =
>     do let addRules = CVar (idAddRulesAt pos)
>            isRule (ISRule _ _ _ _)  = True
>            isRule _                 = False
>            theRPs (ISRule _ _ p r) = (r,p)
>            theRPs _ = undefined -- guarded by "span" (next line below)
>            (isrules,new_rest) = span isRule rest
>            (rules,pragss) = unzip ((rule,ps) : map theRPs isrules)
>        body <- convImperativeStmtsToCStmts c_mt_me atEnd new_rest
>        let id_name = setHideId (mkId pos (mkFString "_add_rules"))
>        let nameExpr = mkNameExpr id_name
>        return (CSExpr (Just nameExpr) (cApply 14 addRules [Crules (concat pragss) rules]) : body)

> convImperativeStmtsToCStmts c_mt_me atEnd (ISRule pos name ps rule : rest) =
>     do let addRules = CVar (idAddRulesAt pos)
>            isRule (ISRule _ _ _ _)  = True
>            isRule _                 = False
>            theRPs (ISRule _ _ p r) = (r,p)
>            theRPs _ = undefined -- guarded by "span" (next line below)
>            (isrules,new_rest) = span isRule rest
>            (rules,pragss) = unzip ((rule,ps) : map theRPs isrules)
>        body <- convImperativeStmtsToCStmts c_mt_me atEnd new_rest
>        return (CSExpr Nothing (cApply 14 addRules [Crules (concat pragss) rules]) : body)

> convImperativeStmtsToCStmts (c,mt,me) atEnd stmts@(ISMethod pos def : rest)
>     | atEnd && all isISMethod rest =
>         do let it = case mt of
>                       Nothing -> Nothing
>                       Just t  -> leftCon t
>            when (isNothing it) (cvtErr (getPosition mt) EBadInterface)
>            let methods = [method | ISMethod _ method <- stmts]
>                ifc = Cinterface pos it methods
>            return [CSExpr Nothing (cVApply (idReturn pos) [ifc])]
>     | otherwise = cvtErr pos (ENonTerminalMethodsOrSubinterfaces Nothing)

> convImperativeStmtsToCStmts (_,mty,mf) True stmts@(ISBVI pos _ : rest) =
>     do let isbvi (ISBVI _ _) = True
>            isbvi _ = False
>            isDefaultClock (ISBVI _ (BVI_default_clock _)) = True
>            isDefaultClock _ = False
>            isDefaultReset (ISBVI _ (BVI_default_reset _)) = True
>            isDefaultReset _ = False
>            isInputClock (ISBVI _ (BVI_input_clock _)) = True
>            isInputClock _ = False
>            isOutputClock (ISBVI _ (BVI_output_clock _)) = True
>            isOutputClock _ = False
>            isAncestor (ISBVI _ (BVI_ancestor _)) = True
>            isAncestor _ = False
>            isFamily (ISBVI _ (BVI_family _)) = True
>            isFamily _ = False
>            isInputReset (ISBVI _ (BVI_input_reset _)) = True
>            isInputReset _ = False
>            isOutputReset (ISBVI _ (BVI_output_reset _)) = True
>            isOutputReset _ = False
>            isMethod (ISBVI _ (BVI_method _)) = True
>            isMethod _ = False
>            isInterface (ISBVI _ (BVI_interface _)) = True
>            isInterface _ = False
>            isArg (ISBVI _ (BVI_arg _)) = True
>            isArg _ = False
>            isSchedule (ISBVI _ (BVI_schedule _)) = True
>            isSchedule _ = False
>            isPath (ISBVI _ (BVI_path _)) = True
>            isPath _ = False
>            isUnsync (ISBVI _ (BVI_unsync _)) = True
>            isUnsync _ = False

>            mkVMethodConflictInfo :: [([Id], MethodConflictOp, [Id])] -> VMethodConflictInfo
>            mkVMethodConflictInfo scheds =
>             let f b = [(i1,i2)
>                          | (i1s,bb,i2s) <- scheds, b==bb, i1<-i1s, i2<-i2s]
>                 g b = [i2s
>                          | (i1s,bb,i2s) <- scheds, b==bb]
>                 h b = [i2
>                          | (i1s,bb,i2s) <- scheds, b==bb, i2<-i2s]
>             in MethodConflictInfo (f CF) (f SB) (g ME) (f P) (f SBR) (f C) (h EXT)
>            mkVSchedInfo :: [([Id], MethodConflictOp, [Id])] -> [Id] -> VSchedInfo
>            mkVSchedInfo scheds unsync_meths =
>             let mci = mkVMethodConflictInfo scheds
>                 -- XXX the user cannot specify these in an import
>                 rms = []
>                 rbm = []
>                 -- we have an undocumented statement to specify unsync methods
>                 ccm = unsync_meths
>             in SchedInfo mci rms rbm ccm

Extract the BVI statements

>        let (bvis0, afters) = span isbvi stmts
>        when (not (null afters)) $
>            cvtErr (getPosition (head afters)) EBVISeparated

Find the default clock (or create one if needed)
(We label it "0" because it may be unnamed and will need to be named)

>        (default_clock0, bvis0_0) <-
>            case (partition isDefaultClock bvis0) of
>              ([], ss) ->
>                  let -- unnamed clocks are uniquely determined by their pos
>                      unnamed_i = setIdPosition noPosition emptyId
>                      clk_inf = (unnamed_i, Just (VName "CLK",
>                                                  Right (VName "CLK_GATE")))
>                      arg_inf = (ClockArg unnamed_i,
>                                 CVar idExposeCurrentClock,
>                                 True)
>                      ss' = ( ISBVI pos (BVI_input_clock clk_inf)
>                            : ISBVI pos (BVI_arg arg_inf)
>                            : ss )
>                  in  return (unnamed_i, ss')
>              ([ISBVI _ (BVI_default_clock i)], ss) ->
>                  return (i, ss)
>              (clks@(_:clk2:_), _) ->
>                  cvtErr (getPosition clk2) ETooManyDefaultClocks
>              _ -> internalError
>                       "convImperativeStmtsToCStmts: BVI default_clock"

Fixup the unnamed clocks
XXX checks for valid clock names could be done here rather than later

>        (default_clock, unnamed_clks, bvis0_1) <- do
>          let old_bvis = bvis0_0
>          let findClkNames (cset, cposs) (BVI_input_clock (i,_)) =
>                  if (isEmptyId i)
>                  then (cset, ((getIdPosition i):cposs))
>                  else (S.insert i cset, cposs)
>              findClkNames (cset, cposs) (BVI_output_clock (i,_)) =
>                  (S.insert i cset, cposs)
>              findClkNames accum (BVI_interface (_,_,ss)) = foldl findClkNamesIS accum ss
>              findClkNames accum _ = accum
>              findClkNamesIS accum (ISBVI _ s) = findClkNames accum s
>              findClkNamesIS accum _ = accum
>          -- get the empty names (uniquified by their position)
>          -- and the real names, to avoid clash when we create names
>          let (clk_set, uclk_poss_rev) =
>                  foldl findClkNamesIS (S.empty, []) old_bvis
>              uclk_poss = reverse uclk_poss_rev
>          -- new name source without clash
>          let new_clk_names =
>                  take (length uclk_poss) $
>                      filter isOKClk $ map (addIdSuffix idClk) [1..]
>                where isOKClk i = S.notMember i clk_set
>          -- map from old name to new name
>          let uclk_map = M.fromList (zip uclk_poss new_clk_names)
>          -- function to update clock names
>          let updClk :: Id -> Id
>              updClk i | isEmptyId i =
>                  let pos = getIdPosition i
>                  in  case (M.lookup pos uclk_map) of
>                        Just i' -> setIdPosition pos i'
>                        Nothing -> internalError ("CVParserImperative updClk: " ++
>                                                  pvpReadable (pos, uclk_poss, new_clk_names))
>              updClk i = i
>          -- function to update BVI statements
>          let updISBVI :: BVIStmt -> BVIStmt
>              updISBVI (BVI_default_clock i) = (BVI_default_clock (updClk i))
>              updISBVI (BVI_input_clock (i, inf))
>                                             = (BVI_input_clock ((updClk i), inf))
>              updISBVI (BVI_arg (ClockArg i, e, b))
>                                             = (BVI_arg (ClockArg (updClk i), e, b))
>              updISBVI s = s
>          let updIS :: ImperativeStatement -> ImperativeStatement
>              updIS (ISBVI pos s) = (ISBVI pos (updISBVI s))
>              updIS s = s
>          -- check that the user didn't serendipitously refer to one of the new names
>          when (not (isEmptyId default_clock0)) $ do
>            let dclk_str = getIdString default_clock0
>            when (dclk_str /= "no_clock" &&
>                  default_clock0 `elem` new_clk_names) $
>                cvtErr (getPosition default_clock0) (EUndeclaredClock dclk_str)
>          -- return the updated defaults and statements
>          return (updClk default_clock0,
>                  new_clk_names,
>                  map updIS old_bvis)

Find the default reset (or create one if needed)
(We label it "0" because it may be unnamed and will need to be named)

>        (default_reset0, bvis0_2) <-
>            case (partition isDefaultReset bvis0_1) of
>              ([], ss) ->
>                  let -- unnamed resets are uniquely determined by their pos
>                      unnamed_i = setIdPosition noPosition emptyId
>                      -- Nothing for clock means use the default clock
>                      rst_inf = (unnamed_i, (Just (VName "RST"), Nothing))
>                      arg_inf = (ResetArg unnamed_i,
>                                 CVar idExposeCurrentReset,
>                                 True)
>                      ss' = ( ISBVI pos (BVI_input_reset rst_inf)
>                            : ISBVI pos (BVI_arg arg_inf)
>                            : ss )
>                  in  return (unnamed_i, ss')
>              ([ISBVI _ (BVI_default_reset i)], ss) ->
>                  return (i, ss)
>              (rsts@(_:rst2:_), _) ->
>                  cvtErr (getPosition rst2) ETooManyDefaultResets
>              _ -> internalError
>                       "convImperativeStmtsToCStmts: BVI default_reset"

Fixup the unnamed resets
XXX checks for valid reset names could be done here rather than later

>        (default_reset, unnamed_rsts, bvis0_3) <- do
>          let old_bvis = bvis0_2
>          let findRstNames (rset, rposs) (BVI_input_reset (i,_)) =
>                  if (isEmptyId i)
>                  then (rset, ((getIdPosition i):rposs))
>                  else (S.insert i rset, rposs)
>              findRstNames (rset, rposs) (BVI_output_reset (i,_)) =
>                  (S.insert i rset, rposs)
>              findRstNames accum (BVI_interface (_,_,ss)) = foldl findRstNamesIS accum ss
>              findRstNames accum _ = accum
>              findRstNamesIS accum (ISBVI _ s) = findRstNames accum s
>              findRstNamesIS accum _ = accum
>          -- get the empty names (uniquified by their position)
>          -- and the real names, to avoid clash when we create names
>          let (rst_set, urst_poss_rev) =
>                  foldl findRstNamesIS (S.empty, []) old_bvis
>              urst_poss = reverse urst_poss_rev
>          -- new name source without clash
>          let new_rst_names =
>                  take (length urst_poss) $
>                      filter isOKRst $ map (addIdSuffix idRst) [1..]
>                where isOKRst i = S.notMember i rst_set
>          -- map from old name to new name
>          let urst_map = M.fromList (zip urst_poss new_rst_names)
>          -- function to update reset names
>          let updRst :: Id -> Id
>              updRst i | isEmptyId i =
>                  let pos = getIdPosition i
>                  in  case (M.lookup pos urst_map) of
>                        Just i' -> setIdPosition pos i'
>                        Nothing -> internalError ("CVParserImperative updRst: " ++
>                                                  pvpReadable (pos, urst_poss, new_rst_names))
>              updRst i = i
>          -- function to update BVI statements
>          let updISBVI :: BVIStmt -> BVIStmt
>              updISBVI (BVI_default_reset i) = (BVI_default_reset (updRst i))
>              updISBVI (BVI_input_reset (i, inf))
>                                             = (BVI_input_reset ((updRst i), inf))
>              updISBVI (BVI_arg (ResetArg i, e, b))
>                                             = (BVI_arg (ResetArg (updRst i), e, b))
>              updISBVI s = s
>          let updIS :: ImperativeStatement -> ImperativeStatement
>              updIS (ISBVI pos s) = (ISBVI pos (updISBVI s))
>              updIS s = s
>          -- check that the user didn't serendipitously refer to one of the new names
>          when (not (isEmptyId default_reset0)) $ do
>            let drst_str = getIdString default_reset0
>            when (drst_str /= "no_reset" &&
>                  default_reset0 `elem` new_rst_names) $
>                cvtErr (getPosition default_reset0) (EUndeclaredReset drst_str)
>          -- return the updated defaults and statements
>          return (updRst default_reset0,
>                  new_rst_names,
>                  map updIS old_bvis)

Create a separate bind statement for module arguments assigned with "<-"

>        let foldFn (ISBVI p (BVI_arg (i,e,True))) (bindings,bvis,idNo) =
>              let id = enumId "bv" p idNo
>              in ((CSBind (CPVar id) Nothing [] e):bindings,
>                  (ISBVI p (BVI_arg (i, CVar id, False))):bvis,
>                  idNo+1)
>            foldFn bvi (bindings,bvis,idNo) = (bindings, bvi:bvis, idNo)
>
>        let (bindings, bvis1, _) = foldr foldFn ([],[],0) bvis0_3

check for wiring problems with the input and output ports
we're allowed to share output ports, but not input ports
some of these restrictions could be lifted if we made the compiler more clever
(e.g. sharing input port between methods that conflict)

>        let addOutputPort pos port (inputs, outputs, errs) = (inputs, outputs', errs')
>              where outputs' = S.insert port outputs
>                    errs' = if (port `S.member` inputs) then
>                               (pos, EBVIInputOutputOverlap str):errs
>                            else errs
>                    str = getVNameString port
>            addInput pos name (inputs, outputs, errs) = (inputs', outputs, errs'')
>              where inputs' = S.insert name inputs
>                    errs' = if (name `S.member` inputs) then
>                               (pos, EBVIInputOverlap str):errs
>                            else errs
>                    errs'' = if (name `S.member` outputs) then
>                                (pos, EBVIInputOutputOverlap str):errs'
>                             else errs'
>                    str = getVNameString name
>            chkBVIPorts (ISBVI pos (BVI_input_clock inf)) ioerrs =
>              case (snd inf) of
>                Nothing -> ioerrs
>                Just (osc, Left _) -> addInput pos osc ioerrs
>                Just (osc, Right gate) -> addInput pos gate (addInput pos osc ioerrs)
>            chkBVIPorts (ISBVI pos (BVI_output_clock inf)) ioerrs =
>               case (snd inf) of
>                 Nothing -> ioerrs
>                 Just (osc, Nothing) -> addOutputPort pos osc ioerrs
>                 Just (osc, Just (gate,_)) -> addOutputPort pos gate (addOutputPort pos osc ioerrs)
>            chkBVIPorts (ISBVI pos (BVI_input_reset inf)) ioerrs =
>                case (fst (snd inf)) of
>                  Nothing -> ioerrs
>                  Just rst -> addInput pos rst ioerrs
>            chkBVIPorts (ISBVI pos (BVI_output_reset inf)) ioerrs =
>                case (fst (snd inf)) of
>                  Nothing -> ioerrs
>                  Just rst -> addOutputPort pos rst ioerrs
>            chkBVIPorts (ISBVI pos (BVI_arg (inf, _, _))) ioerrs =
>                case inf of
>                  Param name -> addInput pos name ioerrs
>                  Port (name, _) _ _ -> addInput pos name ioerrs
>                  _ -> ioerrs
>            chkBVIPorts (ISBVI pos (BVI_method (_,inf@(Method {}),_))) ioerrs = ioerrs3
>                where ioerrs1 = case (vf_output inf) of
>                                  Just (name, _) -> addOutputPort pos name ioerrs
>                                  _ -> ioerrs
>                      ioerrs2 = case (vf_enable inf) of
>                                  Just (name, _) -> addInput pos name ioerrs1
>                                  _ -> ioerrs1
>                      ioerrs3 = foldr (\port iers -> addInput pos (fst port) iers)
>                                      ioerrs2
>                                      (vf_inputs inf)
>            chkBVIPorts (ISBVI pos (BVI_interface (_,_,stmts))) ioerrs = ioerrs'
>               where ioerrs' = foldr chkBVIPorts ioerrs stmts
>            chkBVIPorts _ ioerrs = ioerrs
>        let (_,_,errs) = foldr chkBVIPorts (S.empty, S.empty, []) bvis1
>        when (not (null errs)) $ cvtErrs errs

Extract each type of statement, making sure to preserve the order

>        let (bvi_in_clocks, bvis2) = partition isInputClock bvis1
>            in_clocks = [ c | (ISBVI _ (BVI_input_clock c)) <- bvi_in_clocks ]
>
>            (bvi_out_clocks, bvis3) = partition isOutputClock bvis2
>            out_clocks = [ c | (ISBVI _ (BVI_output_clock c)) <- bvi_out_clocks ]
>
>            (bvi_ancestors, bvis4) = partition isAncestor bvis3
>            ancestors = [ a | (ISBVI _ (BVI_ancestor a)) <- bvi_ancestors ]
>
>            (bvi_familys, bvis5) = partition isFamily bvis4
>            familys = [ f | (ISBVI _ (BVI_family f)) <- bvi_familys ]
>
>            (bvi_in_resets, bvis6) =partition isInputReset bvis5
>            in_resets = [ r | (ISBVI _ (BVI_input_reset r)) <- bvi_in_resets ]
>
>            (bvi_out_resets, bvis7) = partition isOutputReset bvis6
>            out_resets = [ r | (ISBVI _ (BVI_output_reset r)) <- bvi_out_resets ]
>
>            -- parameters in particular need to remain in order,
>            -- because instantiaion in v95 syntax uses positional args
>            (bvi_args, bvis8) = partition isArg bvis7
>            args = [ a | (ISBVI _ (BVI_arg a)) <- bvi_args ]
>
>            (bvi_methods, bvis9) = partition isMethod bvis8
>            methods = [ m | (ISBVI _ (BVI_method m)) <- bvi_methods ]
>
>            (bvi_ifcs, bvis10) = partition isInterface bvis9
>            ifcs = [ i | (ISBVI _ (BVI_interface i)) <- bvi_ifcs ]
>
>            (bvi_schedules, bvis11) = partition isSchedule bvis10
>            schedules = [ (p, s) | (ISBVI p (BVI_schedule s)) <- bvi_schedules ]
>
>            (bvi_paths, bvis12) = partition isPath bvis11
>            paths = [ p | (ISBVI _ (BVI_path p)) <- bvi_paths ]
>
>            (bvi_unsyncs, bvis13) = partition isUnsync bvis12
>            unsyncs = [ u | (ISBVI _ (BVI_unsync u)) <- bvi_unsyncs ]
>
>        when (not (null bvis13))
>            (internalError "convImperativeStmtsToCStmts:ISBVI(2)")

>        let fname = case mf of
>                     (Just e) -> e
>                     _ -> (internalError "convImperativeStmtsToCStmts:ISBVI(3)")
>            itype = case mty of
>                     Just ty -> CQType [] ty
>                     _ -> internalError "convImperativeStmtsToCStmts:ISBVI(4)"

>            second (a,b,c) = b
>            third  (a,b,c) = c
>
>            sepFn (ISBVI _ stmt) e0@(cs, rs, ms) =
>                case stmt of
>                   (BVI_output_clock c) -> (c:cs, rs,   ms)
>                   (BVI_output_reset r) -> (cs,   r:rs, ms)
>                   (BVI_method m)       -> (cs,   rs,   m:ms)
>                   (BVI_interface (_,_,ss)) -> foldr sepFn e0 ss
>                   _ -> internalError "convImperativeStmtsToCStmts:ISBVI(6a)"
>            sepFn _ _ = internalError "convImperativeStmtsToCStmts:ISBVI(6b)"

>            isReservedClk clk_name = (getIdString clk_name == "no_clock") ||
>                                     (getIdString clk_name == "default_clock")

>            isReservedRst rst_name = (getIdString rst_name == "no_reset") ||
>                                     (getIdString rst_name == "default_reset")

>            -- if there is no associated clock (for a method, port, or reset),
>            -- use the default clock;
>            -- and replace the special clock "no_clock" with Nothing
>            -- (and don't use the default clock if it's "no_clock"!)
>            handleClk (Just c) = if (getIdString c == "no_clock")
>                                 then Nothing
>                                 else if (getIdString c == "default_clock")
>                                      then handleClk (Just default_clock)
>                                      else (Just c)
>            handleClk Nothing  = handleClk (Just default_clock)

>            -- if there is no associated reset (with a method),
>            -- use the default reset;
>            -- and replace the special reset "no_reset" with Nothing
>            -- (and don't use the default reset if it's "no_reset"!)
>            handleRst (Just c) = if (getIdString c == "no_reset")
>                                 then Nothing
>                                 else if (getIdString c == "default_reset")
>                                      then handleRst (Just default_reset)
>                                      else (Just c)
>            handleRst Nothing  = handleRst (Just default_reset)

>            -- get nested output interface clocks, resets, inouts and methods
>            (ncs,nrs,nms) = foldr sepFn ([],[],[]) (concat (map third ifcs))

>        -- clocks and nested clocks
>        let alloutclocks = ncs ++ out_clocks
>            allinclocks = in_clocks
>            allclockids = map fst alloutclocks ++ map fst allinclocks
>            alluserclockids = allclockids \\ unnamed_clks

>        -- handle the clock associated with a reset
>        -- and report an error if the clock is undeclared
>        let defaultResetInfClk (i, (mp, mc)) = do
>              case mc of
>                (Just c) | (not (isReservedClk c)) &&
>                           (not (c `elem` alluserclockids)) ->
>                    cvtErr (getPosition c) (EUndeclaredClock (getIdString c))
>                _ -> return (i, (mp, handleClk mc))

>        -- resets and nested resets
>        -- (this also checks that the associated clock names are valid)
>        alloutresets <- mapM defaultResetInfClk (nrs ++ out_resets)
>        allinresets <- mapM defaultResetInfClk in_resets
>        let allresetids = map fst alloutresets ++ map fst allinresets
>            alluserresetids = allresetids \\ unnamed_rsts

>        -- methods and nested methods
>        -- (this means all BVI_method statements, which includes
>        -- clocks, resets, and inouts in the interface -- it might
>        -- be better called "fields")
>        let allmethods = nms ++ methods

>        -- check for reserved clock names
>        let bad_clockids = filter isReservedClk alluserclockids
>        case (bad_clockids) of
>            [] -> return ()
>            (badid:_) -> cvtErr (getPosition badid)
>                                (EReservedClock (getIdString badid))

>        -- check for reserved reset names
>        let bad_resetids = filter isReservedRst alluserresetids
>        case (bad_resetids) of
>            [] -> return ()
>            (badid:_) -> cvtErr (getPosition badid)
>                                (EReservedReset (getIdString badid))

>        let dclk_str = getIdString default_clock
>        when (dclk_str /= "no_clock" &&
>              not (default_clock `elem` allclockids)) $
>            cvtErr (getPosition default_clock) (EUndeclaredClock dclk_str)
>        let drst_str = getIdString default_reset
>        when (drst_str /= "no_reset" &&
>              not (default_reset `elem` allresetids)) $
>            cvtErr (getPosition default_reset) (EUndeclaredReset drst_str)

>        let checkClkRst mclk mrst = do
>              -- before replacing with an unnamed default, check if the
>              -- user given name is legal
>              mclk' <- case (mclk, handleClk mclk) of
>                         (Just i, _) | (not (isReservedClk i)) &&
>                                       (i `notElem` alluserclockids) ->
>                             cvtErr (getPosition i)
>                                        (EUndeclaredClock (getIdString i))
>                         (_, res) -> return res
>              mrst' <- case (mrst, handleRst mrst) of
>                         (Just i, _) | (not (isReservedRst i)) &&
>                                       (i `notElem` alluserresetids) ->
>                             cvtErr (getPosition i)
>                                        (EUndeclaredReset (getIdString i))
>                         (_, res) -> return res
>              return (mclk', mrst')

>        let
>            -- for ports: update the clock and reset fields for ports,
>            --            check that the clock/reset names are valid, and
>            -- for inouts: also update and check the clock/reset
>            --             and insert a cast (rather than pack)
>            -- for all: sanity check that the expr is bound with "=", not "<-"
>            updateArg ((Port vp mclk mrst), e, False) = do
>                (clk, rst) <- checkClkRst mclk mrst
>                let new_p   = Port vp clk rst
>                return (new_p, e)
>            updateArg (p@(InoutArg vn mclk mrst), e, False) = do
>                (clk, rst) <- checkClkRst mclk mrst
>                let new_e = cVApply idPrimInoutCast0 [e]
>                    new_p = InoutArg vn clk rst
>                return (new_p, new_e)
>            updateArg (a, e, False) = return (a, e)
>            updateArg _ = internalError "convImperativeStmtsToCStmts:ISBVI(5)"

>        updated_args <- mapM updateArg args

>        -- this updates the clocked_by and reset_by of methods,
>        -- to add the default clock/reset if the field was left blank,
>        -- and leaving it as Nothing if "no_clock"/"no_reset" was specified
>        -- (or the default is "no_clock" or "no_reset")
>        let addClockAndReset (_,m@(Clock i),_) = return m
>            -- the clocked_by of resets (and inouts) is handled elsewhere
>            addClockAndReset (_,m@(Reset i),_) = return m
>            addClockAndReset (_,m@(Inout i vn mclk mrst),_) = do
>                (clk, rst) <- checkClkRst mclk mrst
>                return (Inout i vn clk rst)
>            addClockAndReset (_,Method a mclk mrst d e f g, _) = do
>                (clk, rst) <- checkClkRst mclk mrst
>                return (Method a clk rst d e f g)

>        let mkPatArgs is =
>              take (length is) (map CPVar (newIds lastPos))
>            mkArgs is =
>              take (length is) (map (\ i -> (cVApply idPack [CVar i])) (newIds lastPos))
>            mkBasicDef f id sid is b =
>              let qual = if b
>                         then [CQFilter (cVApply idUnpack
>                                                 [(CSelect (CVar bviMname) (mkRdyId id))])]
>                         else []
>              in CLValue sid [CClause (mkPatArgs is) []
>                               (f (CApply (CSelect (CVar bviMname) id) (mkArgs is)))]
>                             qual

>            mkBSVMethod (si, Clock i, _) =
>                     CLValue si [CClause [] [] (CSelect (CVar bviMname) i)] []
>            mkBSVMethod (si, Reset i, _) =
>                     CLValue si [CClause [] [] (CSelect (CVar bviMname) i)] []
>            mkBSVMethod (si, Inout i _ _ _, _) =
>                     CLValue si [CClause [] []
>                                   (cVApply idPrimInoutUncast0 [(CSelect (CVar bviMname) i)])] []
>            -- the following case will generate an error in chkBSVMethod below:
>            mkBSVMethod (sn, Method n _ _ _ is Nothing Nothing, b) = -- ... mo me needsReady
>               mkBasicDef (\ e -> e) n sn is b
>            mkBSVMethod (sn, Method n _ _ _ is (Just _) Nothing, b) = -- ... mo me needsReady
>               mkBasicDef (\ e -> cVApply idUnpack [e]) n sn is b
>            mkBSVMethod (sn, Method n _ _ _ is Nothing (Just _), b) = -- ... mo me needsReady
>               mkBasicDef (\ e -> cVApply idFromActionValue_ [e]) n sn is b
>            mkBSVMethod (sn, Method n _ _ _ is (Just _) (Just _), b) = -- ... mo me needsReady
>               mkBasicDef (\ e -> cVApply idFromActionValue_ [e]) n sn is b

>            mkBSVIfc (name,constr,ss) =
>               let ms = [ m | (ISBVI _ (BVI_method m)) <- ss ]
>                   is = [ i | (ISBVI _ (BVI_interface i)) <-ss ]
>                   mcs = methodClauses ms
>                   ics = map mkBSVIfc is
>                   clss = mcs++ics
>                in CLValue name [CClause [][] (Cinterface lastPos (Just constr) clss)] []
>
>            isRealMethod (_,Method i _ _ _ _ _ _,_) = not (isRdyId i)
>            isRealMethod _ = True
>            methodClauses ms = (map mkBSVMethod (filter isRealMethod ms))
>            ifcClauses = map mkBSVIfc

>            lastPos = getPosition (last stmts)
>            bviMname = idM lastPos
>            chkBSVMethod (Method n _ _ _ _ Nothing Nothing) = -- mo me
>               cvtErr (getPosition n) (EForeignModOutputOrEnable (pvpReadable n))
>            chkBSVMethod m = return ()
>            theFamilies cs as fs = do
>               let dup_cs = findSame cs
>               when (not (null dup_cs)) $
>                   cvtErrs [ (getPosition c, EDuplicateClocks (getIdString c))
>                                 | (c:_) <- dup_cs ]
>               let sings = map (\i -> [i]) cs
>                   -- XXX this could give a better error if any of the statements
>                   -- XXX include reserved clock names
>                   unify fams (x,y) = do
>                      let (f1s, rs0) = partition (elem x) fams
>                      when ((null f1s) || (x `elem` unnamed_clks)) $
>                          cvtErr (getPosition x) (EUndeclaredClock (getIdString x))

>                      let f1 = case f1s of
>                                [x]-> x
>                                _  -> internalError "duplicate clocks"
>                          already = y `elem` f1
>                          (f2s, rs) = partition (elem y) rs0
>                      when ((not already && null f2s) || (y `elem` unnamed_clks)) $
>                          cvtErr (getPosition y) (EUndeclaredClock (getIdString y))
>                      let f2 = case f2s of
>                                [x]-> x
>                                _  -> internalError "duplicate clocks"
>                      return (if already then fams
>                               else ((f1 `union` f2):rs))
>               res0 <- foldM unify sings as
>               foldM unify res0 fs

>        mapM_ chkBSVMethod (map second allmethods)
>        methods' <- mapM addClockAndReset allmethods

>        -- check for an Action or ActionValue method which is
>        -- clocked by no_clock and issue a warning
>        let msgs = [ (getIdString n, getPosition n)
>                   | (Method n Nothing _ _ _ _ (Just _)) <- methods'
>                   ]
>        when (not (null msgs)) (cvtWarn pos (WBVIActionMethodNoClock msgs))

>        let methodClock nam = do
>               let mis = [ c | (Method n c r m i o e) <- methods', n==nam]
>               (when (null mis) (cvtErr (getPosition nam) EInvalidMethod))
>               let c = case mis of
>                        [Nothing] -> idNoClock
>                        [Just ci] -> ci
>                        _  -> internalError ("multiple method clocks | " ++
>                                             show nam ++ " | " ++ show mis)
>               return c
>            checkScheduleClocks fs (p,(i2s,CF,i1s)) = do (return ())
>            checkScheduleClocks fs (p,(i2s,_,i1s)) = do
>               cs <- mapM methodClock (i1s ++ i2s)
>               (when (null cs) (internalError ("empty cs at "++show p)))
>               (when (any (==idNoClock) cs) (cvtErr p EScheduleNoClock))
>               let c1 = head cs
>               let fs0 = filter (elem c1) fs
>               (when (null fs0) (internalError ("empty fs0 at "++show p ++
>                                                "| c1 = " ++ show c1)))
>               let f = head fs0
>               (when (not (all (\ x -> x `elem` f) cs))
>                     (cvtErr p EScheduleUnrelatedClocks))
>               return ()
>
>        fams <- theFamilies allclockids ancestors familys
>        -- theFamilies checks for duplicate clock ids,
>        -- so do the same here for resets
>        let dup_rs = findSame allresetids
>        when (not (null dup_rs)) $
>            cvtErrs [ (getPosition r, EDuplicateResets (getIdString r))
>                          | (r:_) <- dup_rs ]
>        -- and check for duplicate names of other interface fields
>        let dup_is = findSame $ filter (not . isRdyId) $ map vf_name methods'
>        when (not (null dup_is)) $
>            cvtErrs [ (getPosition i, EDuplicateIfcField (getIdString i))
>                          | (i:_) <- dup_is ]

> -- We want to treat read methods in the same clock family as CF
> -- and all methods in different clock families as CF, unless
> -- a user has supplied an annotation already.
> -- We also want to keep the annotations dense (ie., not using N^2
> -- annotations when a single annotation with two lenght-N lists will do).
>        let mfams = [Nothing]:[map Just cs | cs <- fams]
>            readMethods cs = [ n | (Method n c _ _ _ _ Nothing) <- methods', c `elem` cs ]
>            rdyMethods cs = filter isRdyId (readMethods cs)
>            nonRdyReadMethods cs = filter (not . isRdyId) (readMethods cs)
>            actionMethods cs = [ n | Method n c _ _ _ _ (Just _) <- methods', c `elem` cs ]
>            allMethods cs = [ n | (Method n c _ _ _ _ _) <- methods', c `elem` cs ]
>            cfDifferentFam = [(pos,(allMethods f1,CF,allMethods f2)) | f1<-mfams, f2<-mfams, f1 < f2]
>            cfReadsSameFam = [(pos,(readMethods f,CF,readMethods f)) | f<-mfams]
>            cActionSameFam = [(pos,(actionMethods f, C, actionMethods f)) | f <- mfams, f /= [Nothing]]
>            cfActionNoClock = (pos,(actionMethods [Nothing], CF, actionMethods [Nothing]))
>            sbReadActionSameFam = [(pos,(nonRdyReadMethods f, SB, actionMethods f)) | f <- mfams, f /= [Nothing]]
>            cfReadActionNoClock = (pos,(nonRdyReadMethods [Nothing], CF, actionMethods [Nothing]))
>            cfRdyActionSameFam =  [(pos,(rdyMethods f, CF, actionMethods f)) | f <- mfams]
>            notDegenerate (_,(xs,_,ys)) = (not (null xs)) && (not (null ys))
>            cfDifferentFam' = filter notDegenerate (cfActionNoClock:cfReadActionNoClock:cfDifferentFam)
>            cfReadsSameFam' = filter notDegenerate cfReadsSameFam
>            cActionSameFam' = filter notDegenerate cActionSameFam
>            sbReadActionSameFam' = filter notDegenerate sbReadActionSameFam
>            cfRdyActionSameFam' = filter notDegenerate cfRdyActionSameFam
> -- all annotations in cfDifferentFam', cfReadsSameFam', cActionSameFam', etc. are disjoint,
> -- so we only need to consider overlap with user-supplied annotations,
> -- not each other.
>            commonEl l1 l2 = not (null (intersect l1 l2))
>            remove (_,(xs,_,ys)) (p,(as,r,bs))=
>                if (commonEl as xs) && (commonEl bs ys)
>                   then let (as_x, as') = partition (\x -> x `elem` xs) as
>                            (_   , bs') = partition (\y -> y `elem` ys) bs
>                        in case (as',bs') of
>                            ([],[])   -> []
>                            ([],_)    -> [(p,(as,r,bs'))]
>                            (_ ,[])   -> [(p,(as',r,bs))]
>                            otherwise -> [(p,(as',r,bs)), (p,(as_x,r,bs'))]
>                   else [(p,(as,r,bs))]
>            removeList l (s:rest) = removeList (concatMap (remove s) l) rest
>            removeList l []       = l
>            bothOrders = schedules ++ (map (\(p,(xs,r,ys))->(p,(ys,r,xs))) schedules)
>            cfReadsSameFam''      = cfReadsSameFam' `removeList` bothOrders
>            cfDifferentFam''      = cfDifferentFam' `removeList` bothOrders
>            cActionSameFam''      = cActionSameFam' `removeList` bothOrders
>            sbReadActionSameFam'' = sbReadActionSameFam' `removeList` bothOrders
>            -- XXX users probably can't/shouldn't put scheduling annotations on ready signals anyway
>            cfRdyActionSameFam'' = cfRdyActionSameFam' `removeList` bothOrders
>            schedules' = schedules ++
>                         cfReadsSameFam'' ++
>                         cfDifferentFam'' ++
>                         cActionSameFam'' ++
>                         sbReadActionSameFam'' ++
>                         cfRdyActionSameFam''
>            mkSchedWarn (pos, (ms1, op, ms2)) =
>                mkSchedWarn' (pos, ((filter (not . isRdyId) ms1),
>                                    op,
>                                    (filter (not . isRdyId) ms2)))
>            mkSchedWarn' (pos,([],_,_)) = []
>            mkSchedWarn' (pos,(_,_,[])) = []
>            mkSchedWarn' (pos, (ms1, CF, ms2)) = [(pos, WNoSchedulingAnnotation
>                                                         (map getIdString ms1)
>                                                         "conflict-free"
>                                                         (map getIdString ms2))]
>            mkSchedWarn' (pos, (ms1, SB, ms2)) = [(pos, WNoSchedulingAnnotation
>                                                         (map getIdString ms1)
>                                                         "sequenced-before"
>                                                         (map getIdString ms2))]
>            mkSchedWarn' (pos, (ms1, C, ms2))  = [(pos, WNoSchedulingAnnotation
>                                                         (map getIdString ms1)
>                                                         "conflict"
>                                                         (map getIdString ms2))]
>            mkSchedWarn' (_,(ms1, op, ms2)) =
>                internalError ("CVParserImperative: Unexpected scheduling assumption " ++
>                               show (ms1, op, ms2))
>        -- don't include cfRdyActionSameFam'' because we'd just filter it out
>        cvtWarns (concatMap mkSchedWarn (cfReadsSameFam'' ++
>                                         cActionSameFam'' ++
>                                         sbReadActionSameFam''))
>        mapM_ (checkScheduleClocks fams) schedules'
>        let checkScheduleDups ss =
>                let check i1 i2 = nub (checkForw i1 i2 ++ checkBack i1 i2)
>                    checkForw (p1,(xs,r1,ys)) (p2,(as,r2,bs)) =
>                        if (r1 /= r2) && (commonEl as xs) && (commonEl bs ys)
>                        then let as_x = filter (\x -> x `elem` xs) as
>                                 bs_y = filter (\y -> y `elem` ys) bs
>                             in  [(p2, EBVIDuplicateSchedule p1 (show r1)
>                                           (map getIdString as_x)
>                                           (map getIdString bs_y))]
>                        else []
>                    isRevOp C = True
>                    isRevOp CF = True
>                    isRevOp SB = True
>                    isRevOp SBR = True
>                    isRevOp op = internalError ("isRevOp: " ++ show op)
>                    checkBack (p1,(xs,r1,ys)) (p2,(as,r2,bs)) =
>                        if ((r1 /= r2) || not (isRevOp r1)) &&
>                           (commonEl as ys) && (commonEl bs xs)
>                        then let as_y = filter (\y -> y `elem` ys) as
>                                 bs_x = filter (\x -> x `elem` xs) bs
>                             in  [(p2, EBVIDuplicateSchedule p1 (show r1)
>                                           (map getIdString bs_x)
>                                           (map getIdString as_y))]
>                        else []
>                    checkList (s:rest) =
>                        concatMap (check s) rest ++ checkList rest
>                    checkList [] = []
>                    errs = checkList ss
>                in  if (null errs)
>                    then return ()
>                    else cvtErrs errs
>        -- just check the user specified relationships
>        checkScheduleDups schedules
>        let vsi = mkVSchedInfo (map snd schedules') (concat unsyncs)
>            mod = CmoduleVerilog
>                    fname
>                    True -- is a user import
>                    (ClockInfo allinclocks alloutclocks ancestors familys)
>                    (ResetInfo allinresets alloutresets)
>                    updated_args
>                    methods'
>                    vsi
>                    (VPathInfo paths)
>            mod' = cVApply idLiftModule [mod]
>            ifc = Cinterface pos Nothing ((methodClauses methods)++(ifcClauses ifcs))
>        -- (*A*) Note: this next expression is recognised by GenWrap and the
>        -- interface type itype is replaced there.  See comment (*A*) in GenWrap.hs.
>        return (bindings ++
>                [CSBindT (CPVar bviMname) (Just (mkNameExpr bviMname)) [] itype mod',
>                 CSExpr Nothing (cVApply (idReturn lastPos) [ifc])])

> convImperativeStmtsToCStmts c_mt_me False stmts@(ISBVI pos _ : rest) =
>     internalError "atEnd not True for ISBVI stmt"

> convImperativeStmtsToCStmts context atEnd stmts@(ISSequence pos seq : rest) =
>  do    --checking has been deferred to this point
>    let (nm, params, _ {-provisos-}, vardecls, body) = seq
>    pushState
>    mapM_ (addParam pos) params
>    vs <- mapM (mapM (checkImperativeStmt miInvalid)) vardecls
>    -- let vars' = map concat vs
>    checkRecursionSP [nm] body
>    bChecked <- checkSPBody body
>    convImperativeStmtsToCStmts context atEnd rest
> convImperativeStmtsToCStmts context atEnd stmts@(ISProperty pos prop : rest) =
>  do
>    let (nm, params, _ {-provisos-}, vardecls, body) = prop
>    pushState
>    mapM_ (addParam pos) params
>    vs <- mapM (mapM (checkImperativeStmt miInvalid)) vardecls
>    --  let vars' = map concat vs
>    checkRecursionSP [nm] body
>    bChecked <- checkSPBody body
>    convImperativeStmtsToCStmts context atEnd rest
> convImperativeStmtsToCStmts context@(ctxt,_,_) atEnd stmts@(ISAssertStmt pos as : rest) =
>  do
>     let (bl, body) = as
>     setupAssertFunctions
>     bChecked <- checkAssertBody body
>     new <- transAssertStmt pos (bl, bChecked)
>--     traceM "Before Checking"
>--     traceM "======================="
>--     traceM $ unlines (map show new)
>--     traceM $ unlines (map pvpString new)
>     bFinal <- checkImperativeStmts ctxt new
>--     traceM "After Checking"
>--     traceM "======================="
>--     traceM $ unlines (map show bFinal)
>--     traceM $ unlines (map pvpString bFinal)
>     convImperativeStmtsToCStmts context atEnd (bFinal ++ rest)

> convImperativeStmtsToCStmts _ _ (stmt : rest) =
>     cvtErr (getPosition stmt) EForbiddenStatement

> setupAssertFunctions :: ISConvMonad ()
> setupAssertFunctions = modify $ \state ->
>      state { issStmtChecker = checkImperativeStmts,
>              issStmtConverter = convImperativeStmtsToCStmts,
>              issExprConverter = convImperativeStmtsToCExpr}

The following function turns a [CExpr] into a CExpr denoting the (BSV) list of the original expressions.

> mkBSVList :: Position -> [CExpr] -> CExpr
> mkBSVList pos =
>     let f e bes = (CCon (idCons pos) [e, bes])
>     in foldr f (CCon (idNil pos) [])

> mkBSVNil :: Position -> CExpr
> mkBSVNil pos = mkBSVList pos []

> imperativeToStmtSeq :: ISContext -> [ImperativeStatement] -> SV_Parser CExpr
> imperativeToStmtSeq ISCSequence stmts =
>  do cs <- emptyISConvState
>     let convPipe = convImperativeStmtsToStmtSeq stmts -- XXX no checking at present
>     fmap (mkBSVList noPosition) $ semToParser cs convPipe

> imperativeToStmtSeq _ stmts =
>     internalError("CVParserImperative.convImperativeToStmtSeq: improper call (" ++ pvpString stmts ++ ")")

-- ----

This next function converts a Position into a String Literal of form
"_l<nn>c<nn>", where the <nn> are the line and column positions.  The string is
intended to be used as a suffix to rule names (which are strings in Classic)
to uniquify them.

> posToString :: Position -> CExpr
> posToString pos@(Position _ l c _) =
>     let s = "_l" ++ (itos l) ++ "c" ++ (itos c)
>     in stringLiteralAt pos s

> convImperativeStmtsToStmtSeq :: [ImperativeStatement] -> ISConvMonad [CExpr]
> convImperativeStmtsToStmtSeq [] = return []

> convImperativeStmtsToStmtSeq act@(ISAction pos stmts : rest) =
>     do pushState
>        inside <- (checkImperativeStmts ISCAction stmts
>                   >>= convImperativeStmtsToCStmts (ISCAction,Nothing,Nothing) False)
>        popState
>        remainder <- convImperativeStmtsToStmtSeq rest
>        let ps = posToString pos
>        return ((CCon (idSAction pos) [ps, Caction pos inside, (CCon (idNothing pos) [])]) : remainder)

> convImperativeStmtsToStmtSeq act@(ISActionValue pos stmts : rest) =
>     do pushState
>        inside <- (checkImperativeStmts ISCAction stmts
>                   >>= convImperativeStmtsToCStmts (ISCActionValue,Nothing,Nothing) False)
> --     when (not (endsWithReturn inside)) (cvtErr pos EActionValueWithoutValue)
>        popState
>        remainder <- convImperativeStmtsToStmtSeq rest
>        let ps = posToString pos
>        return ((CCon (idSActionValue pos) [ps, Cdo False inside]) : remainder)

> convImperativeStmtsToStmtSeq act@(ISRegWrite pos reg expr : rest) =
>     do let inside = CBinOp reg (mkId pos fsAssign) expr
>        remainder <- convImperativeStmtsToStmtSeq rest
>        let ps = posToString pos
>        return ((CCon (idSAction pos) [ps, inside, (CCon (idNothing pos) [])]) : remainder)

> convImperativeStmtsToStmtSeq act@(ISUpdateReg pos struct expr : rest) =
>     do let inside = Cwrite pos struct expr
>        remainder <- convImperativeStmtsToStmtSeq rest
>        let ps = posToString pos
>        return ((CCon (idSAction pos) [ps, inside, (CCon (idNothing pos) [])]) : remainder)

> convImperativeStmtsToStmtSeq exp@(ISNakedExpr pos expr : rest) =
>     do remainder <- convImperativeStmtsToStmtSeq rest
>        let ps = posToString pos
>        return ((cVApply (idStmtify pos) [ps, expr]) : remainder)

> -- if we want to support other functions and still give reasonable errors,
> -- we could define a typeclass for "<-" in sequence context
> convImperativeStmtsToStmtSeq exp@(ISBind pos pprops (Right var) expr@(CApply func@(CVar funcId) arg_list) : rest)
>     | funcId == (idCallServer noPosition) =
>     do let ps = posToString pos
>        let added_args = [(CApply (CVar idAsIfc) [(CVar var)]), ps]
>        let new_args   = arg_list ++ added_args
>        let expr' = (CApply func new_args)
>        convImperativeStmtsToStmtSeq (ISNakedExpr pos expr' : rest)
> convImperativeStmtsToStmtSeq exp@(ISBind pos _ _ expr : rest) =
>     cvtErr pos ESequenceBind
> convImperativeStmtsToStmtSeq exp@(ISUpdateBind pos pprops struct expr@(CApply func@(CVar funcId) arg_list) : rest)
>     | funcId == (idCallServer noPosition) =
>     do let ps = posToString pos
>        -- XXX we can't use PrimUpdatable, so we just pass the interface
>        let added_args = [(CApply (CVar idAsIfc) [struct]), ps]
>        let new_args   = arg_list ++ added_args
>        let expr' = (CApply func new_args)
>        convImperativeStmtsToStmtSeq (ISNakedExpr pos expr' : rest)
> convImperativeStmtsToStmtSeq exp@(ISUpdateBind pos _ _ _ : rest) =
>     cvtErr pos ESequenceBind

> convImperativeStmtsToStmtSeq (ISIf _ [] _ _ : _) =
>     internalError ("CVParserImperative: convImperativeStmtsToStmtSeq: " ++
>                    "ISIf _ [] _ _ ...")
> convImperativeStmtsToStmtSeq ifs@(ISIf pos conds consStmts altStmts
>                               : rest) | all isCQFilter conds =
>     do pushState
>        let hasAlt = isJust altStmts
>            cond = joinWithAnd [e | CQFilter e <- conds]
>        -- XXX no checking at present
>        consEs <- convImperativeStmtsToStmtSeq consStmts
>        let consExpr = case consEs of
>                           [x] -> x
>                           _ -> internalError ("if arm in sequence not singleton")
>        altEs <- maybe (return []) convImperativeStmtsToStmtSeq altStmts
>        let altExpr = if not hasAlt then consExpr -- its value is irrelevant
>                      else case altEs of
>                           [x] -> x
>                           _ -> internalError ("else arm in sequence not singleton")
>        let ps = posToString pos
>        let inside = if hasAlt
>                      then CCon (idSIf2 pos) [ps, cond, consExpr, altExpr]
>                      else CCon (idSIf1 pos) [ps, cond, consExpr]

>        popState
>        remainder <- convImperativeStmtsToStmtSeq rest
>        return (inside : remainder)
> convImperativeStmtsToStmtSeq (ISIf pos conds consStmts altStmts : rest) =
>     cvtErr pos ESequenceIfPattern

> convImperativeStmtsToStmtSeq (ISAbtIf _ [] _ _ : _) =
>     internalError ("CVParserImperative: convImperativeStmtsToStmtSeq: " ++
>                    "ISAbtIf _ [] _ _ ...")
> convImperativeStmtsToStmtSeq ifs@(ISAbtIf pos conds consStmts altStmts
>                               : rest) | all isCQFilter conds =
>     do pushState
>        let hasAlt = isJust altStmts
>            cond = joinWithAnd [e | CQFilter e <- conds]
>        -- XXX no checking at present
>        consEs <- convImperativeStmtsToStmtSeq consStmts
>        let consExpr = case consEs of
>                           [x] -> x
>                           _ -> internalError ("abortif arm in sequence not singleton")
>        altEs <- maybe (return []) convImperativeStmtsToStmtSeq altStmts
>        let altExpr = if not hasAlt then consExpr -- its value is irrelevant
>                      else case altEs of
>                           [x] -> x
>                           _ -> internalError ("else arm in sequence not singleton")
>        let ps = posToString pos
>        let inside = if hasAlt
>                      then CCon (idSAbtIf2 pos) [ps, cond, consExpr, altExpr]
>                      else CCon (idSAbtIf1 pos) [ps, cond, consExpr]
>        popState
>        remainder <- convImperativeStmtsToStmtSeq rest
>        return (inside : remainder)
> convImperativeStmtsToStmtSeq (ISAbtIf pos conds consStmts altStmts : rest) =
>     cvtErr pos ESequenceIfPattern

> convImperativeStmtsToStmtSeq (ISRepeat pos countExpr bodyStmts : rest) =
>     do pushState
>        -- XXX no checking at present
>        bodyEs <- convImperativeStmtsToStmtSeq bodyStmts
>        let bodyExpr = case bodyEs of
>                           [x] -> x
>                           _ -> internalError ("repeat body in sequence not singleton")
>        let ps = posToString pos
>        let inside = CCon (idSRepeat pos) [ps, countExpr, bodyExpr]
>        popState
>        remainder <- convImperativeStmtsToStmtSeq rest
>        return (inside: remainder)


> convImperativeStmtsToStmtSeq whi@(ISWhile pos testExpr bodyStmts : rest) =
>     do pushState
>        -- XXX no checking at present
>        bodyEs <- convImperativeStmtsToStmtSeq bodyStmts
>        let bodyExpr = case bodyEs of
>                           [x] -> x
>                           _ -> internalError ("while body in sequence not singleton")
>        let ps = posToString pos
>        let inside = CCon (idSWhile pos) [ps, testExpr, bodyExpr, (CCon (idNothing pos) []), (CCon (idNothing pos) []), (CCon (idNothing pos) [])]
>        popState
>        remainder <- convImperativeStmtsToStmtSeq rest
>        return (inside: remainder)

> convImperativeStmtsToStmtSeq forit@(ISFor pos initStmts testExpr incrStmts bodyStmts : rest) =
>     do pushState
>        -- XXX no checking at present
>        initEs <- convImperativeStmtsToStmtSeq initStmts
>        let initExpr = case initEs of
>                           [x] -> x
>                           _ -> internalError ("for inits in sequence not singleton")
>        bodyEs <- convImperativeStmtsToStmtSeq bodyStmts
>        let bodyExpr = case bodyEs of
>                           [x] -> x
>                           _ -> internalError ("for body in sequence not singleton")
>        incrEs <- convImperativeStmtsToStmtSeq incrStmts
>        let incrExpr = case incrEs of
>                           [x] -> x
>                           _ -> internalError ("for incs in sequence not singleton")
>        let ps = posToString pos
>        let inside = CCon (idSFor pos) [ps, initExpr, testExpr, incrExpr, bodyExpr]
>        popState
>        remainder <- convImperativeStmtsToStmtSeq rest
>        return (inside : remainder)

> convImperativeStmtsToStmtSeq sseq@(ISSeq pos stmts : rest) =
>     do pushState
>        -- XXX no checking at present
>        inside <- convImperativeStmtsToStmtSeq stmts
>        popState
>        remainder <- convImperativeStmtsToStmtSeq rest
>        let ps = posToString pos
>        return ((CCon (idSSeq pos) [ps, mkBSVList pos inside]) : remainder)

> convImperativeStmtsToStmtSeq sseq@(ISPar pos stmts : rest) =
>     do pushState
>        -- XXX no checking at present
>        inside <- convImperativeStmtsToStmtSeq stmts
>        popState
>        remainder <- convImperativeStmtsToStmtSeq rest
>        let ps = posToString pos
>        return ((CCon (idSPar pos) [ps, mkBSVList pos inside]) : remainder)

> convImperativeStmtsToStmtSeq (ISBreak pos : rest) =
>     do remainder <- convImperativeStmtsToStmtSeq rest
>        let ps = posToString pos
>        return ((CCon (idSBreak pos) [ps]) : remainder)

> convImperativeStmtsToStmtSeq (ISContinue pos : rest) =
>     do remainder <- convImperativeStmtsToStmtSeq rest
>        let ps = posToString pos
>        return ((CCon (idSContinue pos) [ps]) : remainder)

> convImperativeStmtsToStmtSeq x@(ISReturn pos (Just expr) : rest) =
>       convImperativeStmtsToStmtSeq ((ISActionValue pos x) : rest)

> convImperativeStmtsToStmtSeq x@(ISReturn pos Nothing : rest) =
>     do remainder <- convImperativeStmtsToStmtSeq rest
>        let ps = posToString pos
>        return ((CCon (idSReturn pos) [ps]) : remainder)

> convImperativeStmtsToStmtSeq (ISGoto pos id : rest) =
>     do remainder <- convImperativeStmtsToStmtSeq rest
>        let ps = posToString pos
>        return ((CCon (idSJump pos) [ps, (stringLiteralAt (getIdPosition id) (getIdString id))]) : remainder)

> convImperativeStmtsToStmtSeq (ISLabel pos id : rest) =
>     do remainder <- convImperativeStmtsToStmtSeq rest
>        let ps = posToString pos
>        return ((CCon (idSLabel pos) [ps, (stringLiteralAt (getIdPosition id) (getIdString id)), (CCon idFalse []), (CCon (idNothing pos) [])]) : remainder)

> convImperativeStmtsToStmtSeq (ISNamed pos id stmts : rest) =
>     do pushState
>        -- XXX no checking at present
>        inside <- convImperativeStmtsToStmtSeq stmts
>        popState
>        remainder <- convImperativeStmtsToStmtSeq rest
>        let ps = posToString pos
>        return ((CCon (idSNamed pos) [ps, (stringLiteralAt (getIdPosition id) (getIdString id)), mkBSVList pos inside]) : remainder)

> convImperativeStmtsToStmtSeq sseq@(ISDecl pos _ _ _ : rest) =
>     cvtErr pos (EForbiddenDeclaration "statement sequence")

> convImperativeStmtsToStmtSeq (ISCase pos _ _ _ : rest) =
>     cvtErr pos (EUnsupportedCaseStmt "statement sequence")

> convImperativeStmtsToStmtSeq (ISCaseTagged pos _ _ _ : rest) =
>     cvtErr pos (EUnsupportedCaseStmt "statement sequence")

> convImperativeStmtsToStmtSeq stmts =
>     internalError ("CVParserImperative.convImperativeStmtsToStmtSeq: nonexhaustive cases (" ++ pvpString stmts ++ ")")

-- ---------------------------------

> cstmtsToCMStmts :: [CSchedulePragma] -> [CStmt] -> SV_Parser [CMStmt]
> cstmtsToCMStmts prags cstmts =
>   do if null cstmts then return []
>       else do
>        let (stmts1, ifcss) = (init cstmts, last cstmts)
>            addRules = CVar (idAddRulesAt noPosition)
>            stmts' = if null prags then stmts1
>                     else (stmts1 ++ [CSExpr Nothing (cApply 14 addRules [Crules prags []])])
>        case ifcss of
>          CSExpr Nothing (CApply (CVar i) [ifc])-> -- i==(idReturn noPosition) ->
>              return (map CMStmt stmts' ++ [CMinterface ifc])
>          e@(CSExpr Nothing _) ->
>              return (map CMStmt (stmts' ++ [e]))
>          x -> failWithErr (getPosition x, EBadInterface)
>       -- XXX make above errors "internal"?

> imperativeToCDefns ::  [ImperativeStatement] -> SV_Parser [CDefn]
> imperativeToCDefns stmts = -- called only for top-level of package
>  do cs <- emptyISConvState
>     let convPipe = checkImperativeStmts ISCToplevel stmts >>= convImperativeStmtsToCDefns
>     semToParser cs convPipe

> convImperativeStmtsToCDefns :: [ImperativeStatement] -> ISConvMonad [CDefn]
> convImperativeStmtsToCDefns [] = return []
> convImperativeStmtsToCDefns (ISTypedef pos defns : rest) =
>     do restDefns <- convImperativeStmtsToCDefns rest
>        return (defns ++ restDefns)
> convImperativeStmtsToCDefns (ISTypeclass pos name provisos dependencies parameters functions : rest) =
>     do let defn = Cclass Nothing provisos name parameters dependencies functions
>        restDefns <- convImperativeStmtsToCDefns rest
>        return (defn : restDefns)
> convImperativeStmtsToCDefns (ISTypeclassInstance pos classType functions : rest) =
>     do let defn = Cinstance classType functions
>        restDefns <- convImperativeStmtsToCDefns rest
>        return (defn : restDefns)
> convImperativeStmtsToCDefns (ISInterface pos name ifcPragmas params methods : rest) =
>     do let derivedClasses = []
>            defn = Cstruct True (SInterface ifcPragmas) name params methods derivedClasses
>        restDefns <- convImperativeStmtsToCDefns rest
>        return (defn : restDefns)
> convImperativeStmtsToCDefns (ISModule pos name maybePragma
>                              moduleType definition : rest) =
>     do let pragmas = map CPragma (maybeToList maybePragma)
>            defn = CValueSign (CDef name moduleType [definition])
>        restDefns <- convImperativeStmtsToCDefns rest
>        return (pragmas ++ [defn] ++ restDefns)
> convImperativeStmtsToCDefns (ISForeignModule pos name modType definition pragmas : rest) =
>     do let defn = CValueSign (CDef name modType [definition])
>            pdefns = map CPragma pragmas
>        restDefns <- convImperativeStmtsToCDefns rest
>        return (pdefns ++ [defn] ++ restDefns)
> convImperativeStmtsToCDefns (ISForeignFunction pos src_id link_id src_type : rest) =
>     do let expr = CForeignFuncC link_id src_type
>            clause = CClause [] [] expr
>            defn = CValueSign (CDef src_id src_type [clause])
>            -- this pragma communicates to a later pass that a module should
>            -- be generated for this foreign import (similar to PPverilog)
>            pragma = CPragma (Pproperties src_id [PPforeignImport link_id])
>        restDefns <- convImperativeStmtsToCDefns rest
>        return (pragma : defn : restDefns)
> convImperativeStmtsToCDefns (ISFunction pos prags (CLValueSign def [])
>                              : rest) =
>     do let pragmas = map CPragma prags
>            defn = (CValueSign def)
>        restDefns <- convImperativeStmtsToCDefns rest
>        return (pragmas ++ [defn] ++ restDefns)
> convImperativeStmtsToCDefns (ISFunction pos prags _ : rest) =
>     cvtErr pos EForbiddenLetFn
> convImperativeStmtsToCDefns (ISEqual pos (Right var) value : rest) =
>     do di <- getDeclInfo var
>        let (mdeclType, ps) = fromJustOrErr "convImperativeStmtsToCDefns" di
>            qualType = CQType ps (fromJust mdeclType)
>            cls = [CClause [] [] value]
>            def = if isNothing mdeclType
>                   then CValue var cls
>                   else CValueSign (CDef var qualType cls)
>        restDefns <- convImperativeStmtsToCDefns rest
>        return (def : restDefns)
> convImperativeStmtsToCDefns (ISEqual pos (Left _) _ : _) =
>        cvtErr pos EForbiddenTuple
> convImperativeStmtsToCDefns (ISClassicDefns pos defns : rest) =
>     do restDefns <- convImperativeStmtsToCDefns rest
>        return (defns ++ restDefns)
> convImperativeStmtsToCDefns (stmt : rest) =
>     cvtErr (getPosition stmt) EForbiddenStatement

 >     internalError ("CVParserImperative.convImperativeToCStmts: " ++ pvpString stmt ++ " at " ++ pvpString (getPosition stmt))



> endsWithReturn :: [CStmt] -> Bool
> endsWithReturn [CSExpr _ (CApply (CVar f) [body])] | f == idSplitDeepAV ||
>                                                      f == idNosplitDeepAV =
>  case body of
>    Cdo _ sts -> endsWithReturn sts
>    Caction _ sts -> endsWithReturn sts
>    _ -> False
> endsWithReturn [CSExpr _ (CApply (CVar f) [_])] = f == idReturn noPosition
> endsWithReturn [CSExpr _ (Cdo _ sts)] = endsWithReturn sts
> endsWithReturn [CSExpr _ (Caction _ sts)] = endsWithReturn sts
> endsWithReturn [CSExpr _ (Cif _ _ (Cdo _ sts1) (Cdo _ sts2))] =
>     endsWithReturn sts1 && endsWithReturn sts2
> endsWithReturn [CSExpr _ (Cif _ _ (Caction _ sts1) (Caction _ sts2))] =
>     endsWithReturn sts1 && endsWithReturn sts2
> endsWithReturn [CSExpr _ (Ccase _ _ arms)] = and(map armEndsWithReturn arms)
> endsWithReturn (stmt:stmts) = endsWithReturn stmts
> endsWithReturn _ = False

> armEndsWithReturn :: CCaseArm -> Bool
> armEndsWithReturn (CCaseArm { cca_consequent = Cdo _ consequent_stmts }) =
>     endsWithReturn consequent_stmts
> armEndsWithReturn _ = False

Check for use of unassigned variables; if any are found, report errors

> detectUnassignedUses :: CExpr -> ISConvMonad ()
> detectUnassignedUses expr = mapM_ detectUnassignedUse (S.toList (snd (getFVE expr)))
> detectUnassignedUse :: Id -> ISConvMonad ()
> detectUnassignedUse var =
>     do declared <- isDeclared var
>        assigned <- isAssigned var
>        uninitialized <- isUninitialized var
>        when (declared && (not assigned || uninitialized))
>                 (cvtErr (getIdPosition var) (EUseBeforeAssign (pvpString var)))

> getPatVars :: [CQual] -> S.Set Id
> getPatVars qs = S.unions [getPV pat | (CQGen _ pat _) <- qs]

> declareAndAssignVarsInPattern :: CPat -> ISConvMonad ()
> declareAndAssignVarsInPattern pat =
>     do let pvs = getPV pat
>            declAndAssign pv = do declare (getPosition pv) pv Nothing []
>                                  assign (getPosition pv) pv ATNormal
>        mapM_ declAndAssign (S.toList pvs)
> detectUnassignedUsesQuals :: [CQual] -> ISConvMonad ()
> detectUnassignedUsesQuals [] = return ()
> detectUnassignedUsesQuals (CQFilter expr : qs) =
>     do detectUnassignedUses expr
>        detectUnassignedUsesQuals qs
> detectUnassignedUsesQuals (CQGen _ pat expr : qs) =
>     do detectUnassignedUses expr
>        --pushState
>        declareAndAssignVarsInPattern pat
>        detectUnassignedUsesQuals qs
>        --popState

> detectUnassignedUsesClause :: CClause -> SEM [EMsg] ISConvState ()
> detectUnassignedUsesClause (CClause pat quals body) =
>     do pushState
>        detectUnassignedUsesQuals quals
>        detectUnassignedUses body
>        popState

> detectUnassignedUsesDef :: CDef -> ISConvMonad ()
> detectUnassignedUsesDef (CDef name typ clauses) =
>     mapM_ detectUnassignedUsesClause clauses
> detectUnassignedUsesDef (CDefT name _ _ _) =
>     internalError ("CVParserImperative.detectUnassignedUsesDef: CDefT before tcheck (\""
>                    ++ pvpString name ++ "\"")

> detectUnassignedUsesDefl :: CDefl -> ISConvMonad ()
> detectUnassignedUsesDefl (CLValueSign def quals) =
>     do pushState
>        detectUnassignedUsesQuals quals
>        detectUnassignedUsesDef def
>        popState
> detectUnassignedUsesDefl (CLValue name clauses quals) =
>     do pushState
>        detectUnassignedUsesQuals quals
>        mapM_ detectUnassignedUsesClause clauses
>        popState
> detectUnassignedUsesDefl (CLMatch pat expr) = detectUnassignedUses expr

> detectUnassignedUsesRule :: CRule -> ISConvMonad ()
> detectUnassignedUsesRule (CRule _ cond quals body) =
>     do pushState
>        mapM_ detectUnassignedUses (maybeToList cond)
>        detectUnassignedUsesQuals quals
>        detectUnassignedUses body
>        popState
> detectUnassignedUsesRule (CRuleNest _ cond qual rules) =
>     do pushState
>        mapM_ detectUnassignedUses (maybeToList cond)
>        detectUnassignedUsesQuals qual
>        mapM_ detectUnassignedUsesRule rules
>        popState

> detectBadStruct :: Position -> CExpr -> ISConvMonad ()
> detectBadStruct pos lhs =
>     do when (isNothing (structVar lhs))
>             (cvtErr pos (EBadStructUpdate ("5:"++pvpString lhs)))

> detectUndeclaredVarOrFunction :: Id -> ISConvMonad ()
> detectUndeclaredVarOrFunction var =
>     do funname <- isFunctionName var
>        when (not funname) (detectUndeclaredVar var)

> detectUndeclaredVar :: Id -> ISConvMonad ()
> detectUndeclaredVar var =
>     do declared <- isDeclared var
>        when (not declared)
>                 (cvtErr (getIdPosition var) (EAssignBeforeDecl (pvpString var)))

> detectUndeclaredProperty :: Id -> ISConvMonad ()
> detectUndeclaredProperty var =
>  do
>    declared <- isProperty var
>    when (not declared) (detectUndeclaredSequence var)

> detectUndeclaredProperties :: CExpr -> ISConvMonad ()
> detectUndeclaredProperties expr = mapM_ detectUndeclaredProperty (S.toList (snd (getFVE expr)))

> detectUndeclared :: CExpr -> ISConvMonad ()
> detectUndeclared expr = mapM_ detectUndeclaredAll (S.toList (snd (getFVE expr)))

> detectUndeclaredAll :: Id -> ISConvMonad ()
> detectUndeclaredAll var =
>  do
>     dec <- isDeclared var
>     seq <- isSequence var
>     prop <- isProperty var
>     return ()
>     --when (not dec && not seq && not prop)
>     --            (cvtErr (getIdPosition var) (EUnboundVar (pvpString var)))

> detectUndeclaredSequences :: CExpr -> ISConvMonad ()
> detectUndeclaredSequences expr = mapM_ detectUndeclaredSequence (S.toList (snd (getFVE expr)))

> detectUndeclaredSequence :: Id -> ISConvMonad ()
> detectUndeclaredSequence var =
>  do
>    declared <- isSequence var
>    when (not declared) (detectUndeclaredVarOrFunction var)

> warnShadowClause :: CClause -> ISConvMonad ()
> warnShadowClause clause@(CClause args quals body) =
>     do pushState
>        sequence_ [declare pos arg Nothing [] >> assign pos arg ATNormal
>                   | arg <- S.toList (getPVs args), let pos = getPosition arg]
>        popState

> warnShadowDef :: CDef -> ISConvMonad ()
> warnShadowDef (CDef name typ clauses) = mapM_ warnShadowClause clauses
> warnShadowDef (CDefT name _ _ _) =
>     internalError ("CVParserImperative.warnShadowDef: CDefT before tcheck (\""
>                    ++ pvpString name ++ "\"")

> warnShadowDefl :: CDefl -> ISConvMonad ()
> warnShadowDefl (CLValueSign def quals) = warnShadowDef def
> warnShadowDefl (CLValue name clauses quals) =
>     mapM_ warnShadowClause clauses
> warnShadowDefl (CLMatch pat expr) =
>     do pushState
>        sequence_ [declare pos arg Nothing [] >> assign pos arg ATNormal
>                   | arg <- S.toList (getPV pat), let pos = getPosition arg]
>        popState

> checkImperativeStmts :: ISContext -> [ImperativeStatement]
>                      -> ISConvMonad [ImperativeStatement]
> checkImperativeStmts context stmts =
>     do let mInfo pos = case context of
>                ISCModule t -> (t,[])
>                _           -> defaultModuleMonadInfo pos
>        stmtss' <- mapM (checkImperativeStmt mInfo) stmts
>        declaredVars <- getDeclaredVars
>        normallyAssignedVars <- getNormallyAssignedVars
>        let unassignedVars =
>                S.toList (declaredVars `S.difference` normallyAssignedVars)
>        cvtWarns [(getPosition v, WNeverAssigned (pvpString v))
>                  | v <- unassignedVars]
>        return (concat stmtss')

The next (monadic) function replaces the identifiers in [ImperativeStatement]
by their current versions, as held in the monadic state.  It is defined (at
present) only for those statements allowed in the expression context.

XXX   Detecting function argument collisions TBD

> undoTuple :: Type -> Maybe [Type]
> undoTuple (TAp x t) =
>     case (undoTuple x) of
>                Nothing -> Nothing
>                Just ts  -> Just (ts++[t])
> undoTuple (TCon (TyCon i _ _)) | take 5 (getIdBaseString i) == "Tuple" = Just []
> undoTuple _ = Nothing

> getMaybeType :: CDefl -> (Maybe CType)
> getMaybeType (CLValueSign (CDef _ (CQType _ t) _) _) = Just t
> getMaybeType _ = Nothing

> substMonadType :: (Position -> (CType,[CPred])) -> CType -> (CType,[CPred])
> substMonadType tc (TDefMonad pos) = tc pos
> substMonadType tc (TAp t1 t2) =
>     let (t1', ps1) = substMonadType tc t1
>         (t2', ps2) = substMonadType tc t2
>     in (TAp t1' t2', ps1++ps2)
> substMonadType _ t = (t, [])

> substMonadCDefl :: (Position -> (CType,[CPred])) -> CDefl -> CDefl
> substMonadCDefl tc (CLValueSign (CDef i (CQType ps ty) cs) cqs) =
>     let (ty1,ps1) = substMonadType tc ty
>     in (CLValueSign (CDef i (CQType (ps1++ps) ty1) cs) cqs)
> substMonadCDefl _ cd = cd

> -- note that RegWrite assignments do not go into the environment, since they're instances
> checkImperativeStmt :: (Position -> (CType,[CPred])) -> ImperativeStatement
>             -> ISConvMonad [ImperativeStatement]
> checkImperativeStmt mi (ISDecl pos vars Nothing _) =
>     do mapIdOrTupleM_ (\v -> declare pos v Nothing []) vars
>        return []
> checkImperativeStmt mi (ISDecl pos (Right var) (Just ty) preds) =
>     do let (ty1,ps) = substMonadType mi ty
>        declare pos var (Just ty1) (ps++preds)
>        return []
> checkImperativeStmt mi (ISDecl pos (Left vars) (Just typ) preds) = do
>     case undoTuple typ of
>        Nothing -> (cvtErr pos EForbiddenTuple)
>        Just ts -> do
>          when (length ts /= length vars)
>            (cvtErr pos EForbiddenTuple)
>          let f (Left _)  _ = return ()
>              f (Right v) t = do
>               let (t1,ps) = substMonadType mi t
>               declare pos v (Just t1) (ps++preds)
>          zipWithM_ f vars ts
>          return []

> checkImperativeStmt mi stmt@(ISPatEq pos pat expr) =
>     do detectUnassignedUses expr
>        let vars = S.toList (getPV pat)
>            atype = getCExprAssignmentType expr
>        mapM_ (\v -> declare pos v Nothing []) vars
>        mapM_ (\v -> assign  pos v atype) vars
>        return [stmt]

> checkImperativeStmt mi stmt@(ISPatBind pos pat expr) =
>     do detectUnassignedUses expr
>        let vars = S.toList (getPV pat)
>            atype = getCExprAssignmentType expr
>        mapM_ (\v -> declare pos v Nothing []) vars
>        mapM_ (\v -> assign  pos v atype) vars
>        return [stmt]

> checkImperativeStmt mi stmt@(ISEqual pos vars expr) =
>     do mapIdOrTupleM_ detectUndeclaredVarOrFunction vars
>        detectUnassignedUses expr
>        varsWithProps <- mapIdOrTupleM updateIdProps vars
>        let atype = getCExprAssignmentType expr
>        mapIdOrTupleM_ (\ v -> assign pos v atype) varsWithProps
>        return [ISEqual pos varsWithProps expr]

> checkImperativeStmt mi stmt@(ISUpdate pos (CSub2 lhs hi lo) rhs) =
>     do detectBadStruct pos lhs
>        let var = fromJust (structVar lhs)
>        detectUndeclaredVarOrFunction var
>        detectUnassignedUses rhs
>        let atype = getCExprAssignmentType rhs
>        assigned <- isAssigned var -- needed for dummy init
>        uninitialized <- isUninitialized var -- needed for dummy init
>        assign pos var atype
>        -- do this after recording the assignment, since var being unassigned
>        -- does not matter.
>        detectUnassignedUses lhs
>        -- XXX hack to permit assigning to subscripts of a bit variable
>        -- XXX (This is now done by handling undefined in the evaluator,
>        -- XXX so can we remove this?)
>        let needsDummyInit = not assigned || uninitialized
>            dummyDecl = (ISEqual pos (Right var) (anyExprAt pos))
>        return (if needsDummyInit then [dummyDecl,stmt] else [stmt])
> checkImperativeStmt mi stmt@(ISUpdate pos expr' expr) =
>     do detectBadStruct pos expr'
>        let var = fromJust (structVar expr')
>        detectUndeclaredVarOrFunction var
>        detectUnassignedUses expr
>        let atype = getCExprAssignmentType expr
>        assign pos var atype
>        detectUnassignedUses expr'
>        return [stmt]

> checkImperativeStmt mi stmt@(ISUpdateBind pos pprops lhs_sub@(CSub2 lhs hi lo) rhs) =
>     do detectBadStruct pos lhs
>        let var = fromJust (structVar lhs)
>        detectUndeclaredVarOrFunction var
>        detectUnassignedUses rhs
>        let atype = getCExprAssignmentType rhs
>        assign pos var atype
>        detectUnassignedUses lhs
>        return [stmt]
> checkImperativeStmt mi stmt@(ISUpdateBind pos pprops expr' expr) =
>     do detectBadStruct pos expr'
>        let var = fromJust (structVar expr')
>        detectUndeclaredVarOrFunction var
>        detectUnassignedUses expr
>        let atype = getCExprAssignmentType expr
>        assign pos var atype
>        detectUnassignedUses expr'
>        return [stmt]

> checkImperativeStmt mi stmt@(ISUpdateReg pos lhs_sub@(CSub2 lhs hi lo) rhs) =
>     do detectBadStruct pos lhs
>        detectUnassignedUses lhs
>        detectUnassignedUses rhs
>        return [stmt]
>
> checkImperativeStmt mi stmt@(ISUpdateReg pos expr' expr) =
>     do detectBadStruct pos expr'
>        detectUnassignedUses expr'
>        detectUnassignedUses expr
>        return [stmt]

> checkImperativeStmt mi stmt@(ISBind pos pprops vars expr) =
>     do mapIdOrTupleM_ detectUndeclaredVar vars
>        detectUnassignedUses expr
>        let atype = getCExprAssignmentType expr
>        varsWithProps <- mapIdOrTupleM updateIdProps vars
>        mapIdOrTupleM_ (\ v -> assign pos v atype) varsWithProps
>        return [ISBind pos pprops varsWithProps expr]
> checkImperativeStmt mi stmt@(ISReturn pos (Just expr)) =
>     do detectUnassignedUses expr
>        return [stmt]
> checkImperativeStmt mi stmt@(ISNakedExpr pos expr) =
>     do detectUnassignedUses expr
>        return [stmt]
> checkImperativeStmt mi stmt@(ISInst pos pprops ifcVar instVar maybeTyp maybeCk maybeRt maybePr expr) =
>     do detectUnassignedUses expr
>        when (isJust maybeCk) (detectUnassignedUses $ fromJust maybeCk)
>        when (isJust maybeRt) (detectUnassignedUses $ fromJust maybeRt)
>        when (isJust maybePr) (detectUnassignedUses $ fromJust maybePr)
>        declare pos ifcVar maybeTyp []
>        assign pos ifcVar ATNormal
>        -- XXX missing decl type info should be appropriate module type
>        -- declare pos instVar Nothing [] -- instVar isn't really a variable
>        assign pos instVar ATNormal
>        return [stmt]
> checkImperativeStmt mi stmt@(ISFunction pos prags defl) =
>     do let defl' = substMonadCDefl mi defl
>        detectUnassignedUsesDefl defl'
>        -- XXX missing declaration type should be function type
>        declare pos (getLName defl') (getMaybeType defl') []
>        assign pos (getLName defl') ATNormal
>        warnShadowDefl defl'
>        return [ISFunction pos prags defl']
> checkImperativeStmt mi stmt@(ISMethod pos defl) =
>     do let defl' = substMonadCDefl mi defl
>        detectUnassignedUsesDefl defl'
>        -- XXX missing declaration type should be method type
>        declare pos (getLName defl') Nothing []
>        assign pos (getLName defl') ATNormal
>        pushState
>        warnShadowDefl defl'
>        popState
>        return [ISMethod pos defl']
> checkImperativeStmt mi stmt@(ISRule pos name prags rule@(CRule _ _ _ _)) =
>     do detectUnassignedUsesRule rule
>        declare pos name (Just (tRulesAt pos)) []
>        assign pos name ATNormal
>        return [stmt]
> checkImperativeStmt mi stmt@(ISRule pos name prags (CRuleNest _ _ quals rules)) =
>     do pushState
>        detectUnassignedUsesQuals quals
>        mapM_ detectUnassignedUsesRule rules
>        declare pos name (Just (tRulesAt pos)) []
>        assign pos name ATNormal
>        popState
>        return [stmt]
> checkImperativeStmt mi stmt@(ISRegWrite pos (CVar regName) src) =
>     do declared <- isDeclared regName
>        assigned <- isAssigned regName
>        uninitialized <- isUninitialized regName
>        when (declared && (not assigned || uninitialized))
>             (cvtErr pos
>              (ERegAssignToUninitializedLocal (pvpString regName)))
>        detectUnassignedUses src
>        return [stmt]
> checkImperativeStmt mi stmt@(ISRegWrite pos dest src) =
>     do detectUnassignedUses dest
>        detectUnassignedUses src
>        return [stmt]
> checkImperativeStmt mi stmt@(ISBeginEnd pos body) =
>     do let assignedFreeVars = S.toList (getUFVISs body)
>        mapM_ detectUndeclaredVarOrFunction assignedFreeVars
>        mapM_ (\var -> assign pos var ATNormal) assignedFreeVars
>        return [stmt]
> checkImperativeStmt mi stmt@(ISAction pos body) =
>     do let assignedFreeVars = S.toList (getUFVISs body)
>        mapM_ detectUndeclaredVarOrFunction assignedFreeVars
>        mapM_ (\var -> assign pos var ATNormal) assignedFreeVars
>        return [stmt]
> checkImperativeStmt mi stmt@(ISActionValue pos body) =
>     do let assignedFreeVars = S.toList (getUFVISs body)
>        mapM_ detectUndeclaredVarOrFunction assignedFreeVars
>        mapM_ (\var -> assign pos var ATNormal) assignedFreeVars
>        return [stmt]
> checkImperativeStmt mi stmt@(ISWhile pos cond _) =
>     do detectUnassignedUses cond
>        return [stmt]
> checkImperativeStmt mi stmt@(ISFor pos inits cond incs forbody) =
>   checkImperativeStmt mi (ISBeginEnd pos (inits ++ [ISWhile pos cond (forbody ++ incs)]))
> checkImperativeStmt mi stmt@(ISIf pos cond conseq alter) =
>     do pushState --(jes)
>        detectUnassignedUsesQuals cond
>        let assignedFreeVarSetConseq = getUFVISs conseq
>            assignedFreeVarSetAlter = maybe S.empty getUFVISs alter
>            assignedFreeVarSetIntersection = (assignedFreeVarSetConseq
>                                              `S.intersection`
>                                              assignedFreeVarSetAlter)
>            assignedFreeVarSetUnion = (assignedFreeVarSetConseq
>                                       `S.union`
>                                       assignedFreeVarSetAlter)
>            assignedFreeVarSetOneBranch = (assignedFreeVarSetUnion
>                                           `S.difference`
>                                           assignedFreeVarSetIntersection)
>            detectUnassigned var =
>                do assigned <- isAssigned var
>                   uninitialized <- isUninitialized var
>                   when (not assigned)
>                            (cvtErr pos (EAssignNotInAllPaths (pvpString var)))
>                   when (assigned && uninitialized)
>                            (cvtWarn pos (EAssignNotInAllPaths (pvpString var)))
>        -- XXX does not detect variables assigned only in one branch
>        mapM_ detectUndeclaredVarOrFunction
>              (S.toList assignedFreeVarSetUnion)
>        mapM_ detectUnassigned (S.toList assignedFreeVarSetOneBranch)
>        mapM_ (\var -> assign pos var ATNormal)
>              (S.toList assignedFreeVarSetUnion)
>        popState --(jes)
>        mapM_ (\var -> assign pos var ATNormal)
>              (S.toList (assignedFreeVarSetUnion `S.difference` (getPatVars cond)))
>        return [stmt]
> checkImperativeStmt mi stmt@(ISCase pos subject [] Nothing) =
>     cvtErr pos EEmptyCase
> checkImperativeStmt mi stmt@(ISCase pos subject arms dfltArm) =
>     do detectUnassignedUses subject
>        mapM_ detectUnassignedUses (concat [test | (pos, test, conseq) <- arms])
>        let assignedFreeVarSets = [getUFVISs conseq | (pos, test, conseq) <- arms] ++
>                                  [getUFVISs conseq | (pos, conseq) <- maybeToList dfltArm]
>            assignedFreeVarSetUnion = S.unions assignedFreeVarSets
>            assignedFreeVarSetIntersection = set_intersectMany assignedFreeVarSets
>            assignedFreeVarSetNotAllPaths = (assignedFreeVarSetUnion
>                                             `S.difference`
>                                             assignedFreeVarSetIntersection)
>            detectUnassigned var =
>                do assigned <- isAssigned var
>                   uninitialized <- isUninitialized var
>                   when (not assigned) (cvtErr pos (EAssignNotInAllPaths (pvpString var)))
>                   when (assigned && uninitialized) (cvtWarn pos (EAssignNotInAllPaths (pvpString var)))
>        mapM_ detectUndeclaredVarOrFunction (S.toList assignedFreeVarSetUnion)
>        mapM_ detectUnassigned (S.toList assignedFreeVarSetNotAllPaths)
>        mapM_ (\var -> assign pos var ATNormal) (S.toList assignedFreeVarSetUnion)
>        return [stmt]
> checkImperativeStmt mi stmt@(ISCaseTagged pos subject [] Nothing) =
>     cvtErr pos EEmptyCase
> checkImperativeStmt mi stmt@(ISCaseTagged pos subject arms dfltArm) =
>     do detectUnassignedUses subject
>        mapM_ (mapM_ detectUnassignedUses) [tests | (_, _, tests, _) <- arms]
>        let assignedFreeVarSets = [getUFVISs conseq `S.difference` getPV pat
>                                   | (_, pat, _, conseq) <- arms] ++
>                                  [getUFVISs conseq
>                                   | (_, conseq) <- maybeToList dfltArm]
>            assignedFreeVarSetUnion = S.unions assignedFreeVarSets
>            assignedFreeVarSetIntersection = set_intersectMany assignedFreeVarSets
>            assignedFreeVarSetNotAllPaths = (assignedFreeVarSetUnion
>                                             `S.difference`
>                                             assignedFreeVarSetIntersection)
>            detectUnassigned var = do assigned <- isAssigned var
>                                      uninitialized <- isUninitialized var
>                                      when (not assigned)
>                                               (cvtErr pos
>                                                (EAssignNotInAllPaths
>                                                 (pvpString var)))
>                                      when (assigned && uninitialized)
>                                               (cvtWarn pos
>                                                (EAssignNotInAllPaths
>                                                 (pvpString var)))
>            warnShadowPatternVars (pos, pat, _, conseq) =
>               do pushState
>                  declareAndAssignVarsInPattern pat
>                  mapM_ detectUndeclaredVarOrFunction (S.toList $ getUFVISs conseq)
>                  popState
>        mapM_ warnShadowPatternVars arms
>        -- mapM_ detectUndeclaredVarOrFunction (S.toList assignedFreeVarSetUnion)
>        mapM_ detectUnassigned (S.toList assignedFreeVarSetNotAllPaths)
>        mapM_ (\var -> assign pos var ATNormal) (S.toList assignedFreeVarSetUnion)
>        return [stmt]
> checkImperativeStmt mi stmt@(ISTypeclass pos name provisos dependencies params functions) =
>     do return [stmt]
> checkImperativeStmt mi stmt@(ISTypeclassInstance pos classType functions) =
>     do mapM_ detectUnassignedUsesDefl functions
>        mapM_ warnShadowDefl functions
>        return [stmt]
> checkImperativeStmt mi stmt@(ISInterface pos name maybePragma params methods) =
>     do return [stmt]
> checkImperativeStmt mi stmt@(ISModule pos name pragma moduleType definition) =
>     do detectUnassignedUsesClause definition
>        -- XXX missing module type is CQType, not CType
>        declare pos name Nothing []
>        assign pos name ATNormal
>        warnShadowClause definition
>        return [stmt]
> checkImperativeStmt mi stmt@(ISForeignModule pos name moduleType definition pragmas) =
>     do detectUnassignedUsesClause definition
>        assign pos name ATNormal
>        warnShadowClause definition
>        return [stmt]
> checkImperativeStmt mi stmt@(ISBVI pos (BVI_arg (_, e, _))) =
>     do detectUnassignedUses e
>        return [stmt]
> checkImperativeStmt mi stmt@(ISBVI _ _) =
>     do return [stmt]
> checkImperativeStmt mi stmt@(ISForeignFunction pos bsv_name maybe_link_name bsv_type) =
>     do return [stmt]
> checkImperativeStmt mi stmt@(ISTypedef pos defns) =
>     do return [stmt]
> checkImperativeStmt mi stmt@(ISClassicDefns pos defns) =
>     do return [stmt]

ASSERTIONS

> -- Just add the sequences/properties to the environment
> -- The rest will be done in convImperativeStmtToCStmt
> checkImperativeStmt mi stmt@(ISSequence _ (nm, _,_,_,_)) =
>     do
>        addSequence nm stmt
>        return [stmt]
> checkImperativeStmt mi stmt@(ISProperty pos (nm, _,_,_,_)) =
>     do
>        addProperty nm stmt
>        return [stmt]
> checkImperativeStmt mi stmt@(ISAssertStmt pos (bl, body)) =

xxx should do fixUnboundProp on body's body!

>     do
>        return [stmt]

> checkImperativeStmt mi stmt =
>     do internalError ("CVParserImperative.checkImperativeStmt: unhandled " ++ show stmt)


==========
ASSERTIONS

value of mi supplied to checkImperativeStmt when checking statements which
should never contain us of "module" as a type.

> miInvalid :: Position -> (CType,[CPred])
> miInvalid pos = internalError "TDefMonad used in assertion etc."

Code which checks sequences and properties
Ensures that variables are declared, etc.

> addParam :: Position -> (Maybe CType, Id) -> ISConvMonad ()
> addParam pos (t, nm) =
>  do
>    declare pos nm t []
>    assign pos nm ATNormal

> checkSeqExpr, checkPropExpr :: CExpr -> ISConvMonad ()
> checkSeqExpr e = detectUndeclared e
> checkPropExpr e = detectUndeclared e

> checkSPBody :: SVA_SP -> ISConvMonad SVA_SP
> checkSPBody (SVA_SP_DelayU d rest sq) =
>  do
>    checkDelay d
>    s' <- checkSPBody sq
>    r' <- mapM checkSPBody rest
>    return (SVA_SP_DelayU d r' s')
> checkSPBody (SVA_SP_Delay d rest s1 s2) =
>  do
>    s1' <- checkSPBody s1
>    checkDelay d
>    s2' <- checkSPBody s2
>    r' <- mapM checkSPBody rest
>    return (SVA_SP_Delay d r' s1' s2')
> checkSPBody s@(SVA_SP_Expr exp rep) =
>  do
>    checkSeqExpr exp
>    checkRep rep
>    return s
> checkSPBody (SVA_SP_Match sq asns rep) =
>  do
>    s' <- checkSPBody sq
>    as' <- mapM (mapM (checkImperativeStmt miInvalid)) asns
>    let asns' = map concat as'
>    checkRep rep
>    return (SVA_SP_Match s' asns' rep)
> checkSPBody (SVA_SP_Or s1 s2) =
>  do
>    s1' <- checkSPBody s1
>    s2' <- checkSPBody s2
>    return (SVA_SP_Or s1' s2')
> checkSPBody (SVA_SP_And s1 s2) =
>  do
>    s1' <- checkSPBody s1
>    s2' <- checkSPBody s2
>    return (SVA_SP_And s1' s2')
> checkSPBody (SVA_SP_Intersect s1 s2) =
>  do
>    s1' <- checkSPBody s1
>    s2' <- checkSPBody s2
>    return (SVA_SP_Intersect s1' s2')
> checkSPBody (SVA_SP_Within s1 s2) =
>  do
>    s1' <- checkSPBody s1
>    s2' <- checkSPBody s2
>    return (SVA_SP_Within s1' s2')
> checkSPBody (SVA_SP_Throughout s1 s2) =
>  do
>    s1' <- checkSPBody s1
>    s2' <- checkSPBody s2
>    return (SVA_SP_Throughout s1' s2')
> checkSPBody (SVA_SP_Parens sq rep) =
>  do
>    s' <- checkSPBody sq
>    checkRep rep
>    return (SVA_SP_Parens s' rep)
> checkSPBody (SVA_SP_FirstMatch sq asns rep) =
>  do
>    s' <- checkSPBody sq
>    as' <- mapM (mapM (checkImperativeStmt miInvalid)) asns
>    let asns' = map concat as'
>    checkRep rep
>    return (SVA_SP_FirstMatch s' asns' rep)
> checkSPBody (SVA_SP_Not p) =
>  do
>    p' <- checkSPBody p
>    return (SVA_SP_Not p')
> checkSPBody (SVA_SP_Implies s p) =
>  do
>    s' <- checkSPBody s
>    p' <- checkSPBody p
>    return (SVA_SP_Implies s' p')
> checkSPBody (SVA_SP_ImpliesD s p) =
>  do
>    s' <- checkSPBody s
>    p' <- checkSPBody p
>    return (SVA_SP_ImpliesD s' p')
> checkSPBody (SVA_SP_If exp p f) =
>  do
>    checkPropExpr exp
>    p' <- checkSPBody p
>    f' <- case f of
>      Nothing -> return Nothing
>      Just z -> do
>        z' <- checkSPBody z
>        return (Just z')
>    return (SVA_SP_If exp p' f')

> checkAssertBody :: SVA_STMT -> ISConvMonad SVA_STMT
> checkAssertBody (SVA_STMT_Assert mn p pass fail) =
>  do
>    p' <- checkSPBody p
>    pass' <- mapM (checkImperativeStmt miInvalid) pass
>    fail' <- mapM (checkImperativeStmt miInvalid) fail
>    return (SVA_STMT_Assert mn p' (concat pass') (concat fail'))
> checkAssertBody (SVA_STMT_Assume mn p) =
>  do
>    p' <- checkSPBody p
>    return (SVA_STMT_Assume mn p')
> checkAssertBody (SVA_STMT_Cover mn p pass) =
>  do
>    p' <- checkSPBody p
>    pass' <- mapM (checkImperativeStmt miInvalid) pass
>    return (SVA_STMT_Cover mn p' (concat pass'))
> checkAssertBody (SVA_STMT_Expect mn p pass fail) =
>  do
>    p' <- checkSPBody p
>    pass' <- mapM (checkImperativeStmt miInvalid) pass
>    fail' <- mapM (checkImperativeStmt miInvalid) fail
>    return (SVA_STMT_Expect mn p' (concat pass') (concat fail'))

> checkRep :: SVA_REP -> ISConvMonad ()
> checkRep (SVA_REP_None) = return ()
> checkRep (SVA_REP_Cons d) = checkDelay d
> checkRep (SVA_REP_NonCons d) = checkDelay d
> checkRep (SVA_REP_Goto d) = checkDelay d

> checkDelay :: SVA_Delay -> ISConvMonad ()
> checkDelay (SVA_Delay_Unbound exp) = checkSeqExpr exp
> checkDelay (SVA_Delay_Const exp) = checkSeqExpr exp
> checkDelay (SVA_Delay_Range e1 e2) =
>  do
>    checkSeqExpr e1
>    checkSeqExpr e2

==============
END ASSERTIONS

> cLetRec :: LetFn CExpr
> cLetRec [] body = body
> cLetRec defs body = Cletrec defs body

> cLetSeq :: LetFn CExpr
> cLetSeq [] body = body
> cLetSeq defs (Cletseq defs' body) = Cletseq (defs ++ defs') body
> cLetSeq defs body = Cletseq defs body

detect whether assignment is to the fake "uninitialized" value

> getCExprAssignmentType :: CExpr -> AssignmentType
> getCExprAssignmentType (CApply (CVar name) _)
>    | name == idPrimUninitialized = ATUninitialized
> getCExprAssignmentType _ = ATNormal

> createPatternNameExpr :: CPat -> Position -> CExpr
> createPatternNameExpr (CPCon _ [CPVar l, CPVar r]) pos = nameExpr
>    where id_concat = setIdPosition pos (mkPairId l r)
>          nameExpr = mkNameExpr id_concat
> createPatternNameExpr (CPCon _ [CPVar l0, (CPCon _ [CPVar l1, CPVar l2])]) pos = nameExpr
>    where id_concat = setIdPosition pos (mkPairId l0 (mkPairId l1 l2))
>          nameExpr = mkNameExpr id_concat
> createPatternNameExpr (CPCon _ _) pos = nameExpr
>    where id_name = (mkId pos (mkFString "tuple"))
>          nameExpr = mkNameExpr id_name
> createPatternNameExpr _ pos = nameExpr
>    where id_name = (mkId pos (mkFString "pat"))
>          nameExpr = mkNameExpr id_name


> mkPairId :: Id -> Id -> Id
> mkPairId a b
>    | a_pkg /= b_pkg =
>        internalError ("CVParserImperative.mkPairId: " ++ show (getIdFStrings a) ++
>                       " and " ++ show (getIdFStrings b))
>    | otherwise = mkQId (getPosition a) a_pkg (concatFString [a_name, (mkFString "__"), b_name])
>    where (a_pkg, a_name) = getIdFStrings a
>          (b_pkg, b_name) = getIdFStrings b
