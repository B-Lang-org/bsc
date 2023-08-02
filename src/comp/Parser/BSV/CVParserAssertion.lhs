> module Parser.BSV.CVParserAssertion where

Main Assertions Handler

This file handles most of the transformation of SVA assertions.
Beyond this file, code related to assertions can be found in:

* CVParser.lhs (parser, pSequence, pProperty, pAssertion, etc)
* CVParserImperative.lhs (checkers and code that calls this file. ConvImperativeStmtsToCStmt,
  checkImperativeStmts, checkSeqBody, etc)
* CVParserCommon.lhs (Data structure definition and pretty-printing)
* Error.hs (Error messages)
* Flags.hs ( -ignore-assertions flag)

Adding a new backend to SVA will probably re-use code up to the deSugar functions.
Look at transAssertStmt for a template.

> import Data.Maybe
> import Control.Monad
> import Control.Monad.Except
> import Control.Monad.State
> import qualified Data.Map as M

> import Parser.BSV.CVParserCommon
> import CSyntax
> import CSyntaxUtil
> import Id
> import Position
> import PVPrint
> import FStringCompat
> import IntLit
> import Error(internalError, ErrMsg(..))
> import SEMonad
> import PreIds
> import PreStrings
> import Util(itos, unconsOrErr)

These functions unroll the sequences and properties
and inline all parameters and sequences

> unrollSEQPROP :: Position -> Bool -> SVA_SP -> ISConvMonad (Either SVA_SEQ SVA_PROP)
> unrollSEQPROP pos allowProp orig@(SVA_SP_Expr e@(CApply (CVar nm) params) rep) =
>  do
>    isSEQ <- isSequence nm
>    if (isSEQ)
>      then do
>        res <- unrollSEQ pos orig
>        return (Left res)
>      else do
>        -- XXX These tests are too restrictive:
>        ss <- filterM isSequenceParam params
>        when (not (null ss)) $ cvtErr pos (EForbiddenSequenceDecl "parameter1" (pvpString ss))
>        ps <- filterM isPropertyParam params
>        when (not (null ps)) $ cvtErr pos (EForbiddenPropertyDecl "parameter1" (pvpString ps))
>        isPROP <- isProperty nm
>        if (not isPROP)
>          then do
>            rep1 <- fixUnboundRep rep
>            return (Left (SVA_SEQ_Expr e rep1))
>          else do
>            (when (not allowProp)) $ cvtErr pos (EForbiddenPropertyDecl "sequence2" (pvpString nm))
>            res <- findPropM nm
>            case res of
>              Just (ISProperty po body) -> do
>                paramed <- replaceParamsProp pos body params
>                unrolled <- unrollPROP pos paramed
>                return $ Right unrolled
>              _ -> internalError $ "CVParserImperative.unrollSEQPROP: " ++ (pvpString nm) ++ " : " ++ pvpString res
>  where
>    isSequenceParam (CVar nm) = isSequence nm
>    isSequenceParam z = return False
>    isPropertyParam (CVar nm) = isProperty nm
>    isPropertyParam z = return False
> unrollSEQPROP pos b (SVA_SP_Expr (CVar nm) rep) =
>   unrollSEQPROP pos b (SVA_SP_Expr (CApply (CVar nm) []) rep) --re-use above code
> unrollSEQPROP pos b (SVA_SP_Expr exp rep) =
>  do
>    rep1 <- fixUnboundRep rep
>    return $ Left (SVA_SEQ_Expr exp rep1)
> unrollSEQPROP pos b (SVA_SP_Or s1 s2) =
>  do
>    res1 <- unrollSEQPROP pos b s1
>    res2 <- unrollSEQPROP pos b s2
>    case res1 of
>      (Left s1') -> case res2 of
>        (Left s2') -> return (Left (SVA_SEQ_Or s1' s2'))
>        (Right p2') -> return (Right (SVA_PROP_Or (SVA_PROP_Seq s1') p2'))
>      (Right p1') -> case res2 of
>        (Left s2') -> return (Right (SVA_PROP_Or p1' (SVA_PROP_Seq s2')))
>        (Right p2') -> return (Right (SVA_PROP_Or p1' p2'))
> unrollSEQPROP pos b (SVA_SP_And s1 s2) =
>  do
>    res1 <- unrollSEQPROP pos b s1
>    res2 <- unrollSEQPROP pos b s2
>    case res1 of
>      (Left s1') -> case res2 of
>        (Left s2') -> return (Left (SVA_SEQ_And s1' s2'))
>        (Right p2') -> return (Right (SVA_PROP_And (SVA_PROP_Seq s1') p2'))
>      (Right p1') -> case res2 of
>        (Left s2') -> return (Right (SVA_PROP_And p1' (SVA_PROP_Seq s2')))
>        (Right p2') -> return (Right (SVA_PROP_And p1' p2'))
> unrollSEQPROP pos _ sp =
>  do
>    -- all prop possibilities have been tried by now:
>    res <- unrollSEQ pos sp
>    return (Left res)

 > unrollSEQPROP pos True sp =
 >  do
 >    cvtErr pos (EForbiddenPropertyDecl "seqprop1" (show sp))
 >    p <- unrollPROP pos sp
 >    final <- case p of
 >      (SVA_PROP_Seq s) -> return (Left s)
 >      x                -> return (Right x)
 >    return final

> unrollSEQ :: Position -> SVA_SP -> ISConvMonad SVA_SEQ
> unrollSEQ pos orig@(SVA_SP_Expr exp@(CApply (CVar nm) params) rep) =
>  do
>    -- These tests are too restrictive:
>    ss <- filterM isSequenceParam params
>    when (not (null ss)) $ cvtErr pos (EForbiddenSequenceDecl "parameter2" (pvpString ss))
>    ps <- filterM isPropertyParam params
>    when (not (null ps)) $ cvtErr pos (EForbiddenPropertyDecl "parameter3" (pvpString ps))
>    isPROP <- isProperty nm
>    when (isPROP) $ cvtErr pos (EForbiddenPropertyDecl "sequence4" (pvpString nm))
>    rep1 <- fixUnboundRep rep
>    isSEQ <- isSequence nm
>    if (not isSEQ) then return (SVA_SEQ_Expr exp rep1) else do
>      res <- findSeqM nm
>      case res of
>        Just (ISSequence po body) -> do
>          paramed <- replaceParamsSeq pos body params
>          unrolled <- unrollSEQ pos paramed
>          return (SVA_SEQ_Parens unrolled rep1)
>        _ -> internalError $ "CVParserImperative.unrollSEQ: " ++ (pvpString nm) ++ " : " ++ pvpString res
>  where
>    isSequenceParam (CVar nm) = isSequence nm
>    isSequenceParam z = return False
>    isPropertyParam (CVar nm) = isProperty nm
>    isPropertyParam z = return False
> unrollSEQ pos (SVA_SP_Expr (CVar nm) rep) =
>   unrollSEQ pos (SVA_SP_Expr (CApply (CVar nm) []) rep) --re-use above code
> unrollSEQ pos (SVA_SP_Expr exp rep) =
>  do
>   rep1 <- fixUnboundRep rep
>   return (SVA_SEQ_Expr exp rep1)
> unrollSEQ pos (SVA_SP_DelayU d rest sq) =
>  do
>    s' <- unrollSEQ pos sq
>    r' <- mapM (unrollSEQ pos) rest
>    return (SVA_SEQ_DelayU d r' s')
> unrollSEQ pos (SVA_SP_Delay d rest s1 s2) =
>  do
>    s1' <- unrollSEQ pos s1
>    s2' <- unrollSEQ pos s2
>    r' <- mapM (unrollSEQ pos) rest
>    return (SVA_SEQ_Delay d r' s1' s2')
> unrollSEQ pos (SVA_SP_Match sq matches rep) =
>  do
>    rep1 <- fixUnboundRep rep
>    s' <- unrollSEQ pos sq
>    return (SVA_SEQ_Match s' matches rep1)
> unrollSEQ pos (SVA_SP_Or s1 s2) =
>  do
>    s1' <- unrollSEQ pos s1
>    s2' <- unrollSEQ pos s2
>    return (SVA_SEQ_Or s1' s2')
> unrollSEQ pos (SVA_SP_And s1 s2) =
>  do
>    s1' <- unrollSEQ pos s1
>    s2' <- unrollSEQ pos s2
>    return (SVA_SEQ_And s1' s2')
> unrollSEQ pos (SVA_SP_Intersect s1 s2) =
>  do
>    s1' <- unrollSEQ pos s1
>    s2' <- unrollSEQ pos s2
>    return (SVA_SEQ_Intersect s1' s2')
> unrollSEQ pos (SVA_SP_Within s1 s2) =
>  do
>    s1' <- unrollSEQ pos s1
>    s2' <- unrollSEQ pos s2
>    return (SVA_SEQ_Within s1' s2')
> unrollSEQ pos (SVA_SP_Throughout s1 s2) =
>  do
>    s1' <- unrollSEQ pos s1
>    s2' <- unrollSEQ pos s2
>    return (SVA_SEQ_Throughout s1' s2')
> unrollSEQ pos (SVA_SP_Parens sq rep) =
>  do
>    rep1 <- fixUnboundRep rep
>    sq' <- unrollSEQ pos sq
>    return (SVA_SEQ_Parens sq' rep1)
> unrollSEQ pos (SVA_SP_FirstMatch sq matches rep) =
>  do
>    rep1 <- fixUnboundRep rep
>    s' <- unrollSEQ pos sq
>    return (SVA_SEQ_FirstMatch s' matches rep1)
> unrollSEQ pos pr = cvtErr pos (EForbiddenPropertyDecl "sequence5" (pvpString pr))


> unrollPROP :: Position -> SVA_SP -> ISConvMonad SVA_PROP
> unrollPROP pos (SVA_SP_Not p) =
>  do
>    p' <- unrollPROP pos p
>    return (SVA_PROP_Not p')
> unrollPROP pos (SVA_SP_Implies sq p2) =
>  do
>    s' <- unrollSEQ pos sq
>    p' <- unrollPROP pos p2
>    return (SVA_PROP_Implies s' p')
> unrollPROP pos (SVA_SP_ImpliesD sq p2) =
>  do
>    s' <- unrollSEQ pos sq
>    p' <- unrollPROP pos p2
>    return (SVA_PROP_ImpliesD s' p')
> unrollPROP pos (SVA_SP_If exp p1 (Just p2)) =
>  do
>    p1' <- unrollPROP pos p1
>    p2' <- unrollPROP pos p2
>    return (SVA_PROP_If exp p1' (Just p2'))
> unrollPROP pos (SVA_SP_If exp p1 Nothing) =
>  do
>    p1' <- unrollPROP pos p1
>    return (SVA_PROP_If exp p1' Nothing)
> unrollPROP pos sq =
>  do
>    res <- unrollSEQPROP pos True sq
>    case res of
>       (Left seq) -> return (SVA_PROP_Seq seq)
>       (Right prop) -> return prop

These fix an ambiguity in the parser's handling of $

> fixUnboundRep :: SVA_REP ->ISConvMonad SVA_REP
> fixUnboundRep (SVA_REP_None) =
>    return SVA_REP_None
> fixUnboundRep (SVA_REP_Cons d) =
>    SVA_REP_Cons <$> fixUnboundDelay d
> fixUnboundRep (SVA_REP_NonCons d) =
>    SVA_REP_NonCons <$> fixUnboundDelay d
> fixUnboundRep (SVA_REP_Goto d) =
>    SVA_REP_Goto <$> fixUnboundDelay d

> fixUnboundDelay :: SVA_Delay -> ISConvMonad SVA_Delay
> fixUnboundDelay (SVA_Delay_Range e1 e2) =
>    if isUnbound e1
>      then cvtErr noPosition (EIllegalAssertExpr "" "lower range")
>      else if isUnbound e2
>        then return (SVA_Delay_Unbound e1)
>        else return (SVA_Delay_Range e1 e2)
> fixUnboundDelay (SVA_Delay_Const exp) =
>    if isUnbound exp
>      then cvtErr noPosition (EIllegalAssertExpr "" "constant delay")
>      else return (SVA_Delay_Const exp)
> fixUnboundDelay x = return x

> isUnbound :: CExpr -> Bool
> isUnbound (CTaskApply (CVar i) []) | getIdBaseString i == "$" = True
> isUnbound x = False

The following functions check for (mutual) recursion among properties and
sequences. Currently we do not support either. Eventually limited support
for recursive properties may be allowed.

> checkRecursionSP :: [Id] -> SVA_SP -> ISConvMonad ()

> checkRecursionSP calls (SVA_SP_Not p) =
>    checkRecursionSP calls p
> checkRecursionSP calls (SVA_SP_Or p1 p2) =
>  do
>    checkRecursionSP calls p1
>    checkRecursionSP calls p2
> checkRecursionSP calls (SVA_SP_And p1 p2) =
>  do
>    checkRecursionSP calls p1
>    checkRecursionSP calls p2
> checkRecursionSP calls (SVA_SP_Implies sq p) =
>  do
>    checkRecursionSP calls sq
>    checkRecursionSP calls p
> checkRecursionSP calls (SVA_SP_ImpliesD sq p) =
>  do
>    checkRecursionSP calls sq
>    checkRecursionSP calls p
> checkRecursionSP calls (SVA_SP_If exp p1 (Just p2)) =
>  do
>    checkRecursionSP calls p1
>    checkRecursionSP calls p2
> checkRecursionSP calls (SVA_SP_If exp p1 Nothing) =
>    checkRecursionSP calls p1
> checkRecursionSP calls (SVA_SP_Expr exp rep) =
>    checkRecursionExpr calls exp
> checkRecursionSP calls (SVA_SP_DelayU d rest sq) =
>  do
>    checkRecursionSP calls sq
>    mapM_ (checkRecursionSP calls) rest
> checkRecursionSP calls (SVA_SP_Delay d rest s1 s2) =
>  do
>    checkRecursionSP calls s1
>    checkRecursionSP calls s2
>    mapM_ (checkRecursionSP calls) rest
> -- checkRecursionSP calls (SVA_SP_Delay d res s1 s2) =
> --  do
> --    checkRecursionSP calls s1
> --    checkRecursionSP calls s2
> checkRecursionSP calls (SVA_SP_Match sq matches rep) =
>    checkRecursionSP calls sq
> checkRecursionSP calls (SVA_SP_Intersect s1 s2) =
>  do
>    checkRecursionSP calls s1
>    checkRecursionSP calls s2
> checkRecursionSP calls (SVA_SP_Within s1 s2) =
>  do
>    checkRecursionSP calls s1
>    checkRecursionSP calls s2
> checkRecursionSP calls (SVA_SP_Throughout s1 s2) =
>  do
>    checkRecursionSP calls s1
>    checkRecursionSP calls s2
> checkRecursionSP calls (SVA_SP_Parens sq rep) =
>    checkRecursionSP calls sq
> checkRecursionSP calls (SVA_SP_FirstMatch sq matches rep) =
>    checkRecursionSP calls sq

> checkRecursionExpr :: [Id] -> CExpr -> ISConvMonad ()
> checkRecursionExpr calls e@(CVar nm) =
>    if nm `elem` calls
>      then cvtErr (getPosition e) (EUnsupportedMutualRecursion (map show (nm : calls)))
>      else do
>        isSEQ <- isSequence nm
>        isPROP <- isProperty nm
>        if isSEQ
>         then do
>           mISSeq <- findSeqM nm
>           let seq = case mISSeq of
>                 (Just (ISSequence _ (_,_,_,_,s))) -> s
>                 _ -> internalError "CVParserAssertion.checkRecursionExpr: ISSeq"
>           checkRecursionSP (nm:calls) seq
>           return ()
>         else if (isPROP)
>           then do
>             mISProp <- findPropM nm
>             let seq = case mISProp of
>                   (Just (ISProperty _ (_,_,_,_,s))) -> s
>                   _ -> internalError "CVParserAssertion.checkRecursionExpr: ISProp"
>             checkRecursionSP (nm:calls) seq
>             return ()
>           else return ()
> checkRecursionExpr calls e@(CApply fun args) =
>  do
>    checkRecursionExpr calls fun
>    mapM_ (checkRecursionExpr calls) args
> checkRecursionExpr calls (CBinOp e1 nm e2) =
>  do
>    checkRecursionExpr calls e1
>    checkRecursionExpr calls e2
> checkRecursionExpr calls exp =
>    return ()

These functions replace all parameters with their passed-in values.

> replaceParamsSeq :: Position -> SVA_Sequence -> [CExpr] -> ISConvMonad SVA_SP
> replaceParamsSeq pos (nm, ps, provisos, vs, body) args =
>  do
>    when (length ps /= length args) $ cvtErr pos (EWrongParamNumber (length ps) (length args))
>    let zips = zip (map snd ps) args
>    foldM (replaceParamSP pos) body zips

> replaceParamsProp :: Position -> SVA_Property -> [CExpr] -> ISConvMonad SVA_SP
> replaceParamsProp pos (nm, ps, provisos, vs, body) args =
>  do
>    when (length ps /= length args) $ cvtErr pos (EWrongParamNumber (length ps) (length args))
>    let zips = zip (map snd ps) args
>    foldM (replaceParamSP pos) body zips

> replaceParamSP :: Position -> SVA_SP -> (Id, CExpr) -> ISConvMonad SVA_SP

 > replaceParamSP pos (SVA_SP_Seq sq) pm =
 >  do
 >    s' <- replaceParamSP pos sq pm
 >    return (SVA_SP_Seq s')

> replaceParamSP pos (SVA_SP_Not p) pm =
>  do
>    p' <- replaceParamSP pos p pm
>    return (SVA_SP_Not p')
> replaceParamSP pos (SVA_SP_Implies sq p) pm =
>  do
>    s' <- replaceParamSP pos sq pm
>    p' <- replaceParamSP pos p pm
>    return (SVA_SP_Implies s' p')
> replaceParamSP pos (SVA_SP_ImpliesD sq p) pm =
>  do
>    s' <- replaceParamSP pos sq pm
>    p' <- replaceParamSP pos p pm
>    return (SVA_SP_ImpliesD s' p')
> replaceParamSP pos (SVA_SP_If exp p1 (Just p2)) pm =
>  do
>    p1' <- replaceParamSP pos p1 pm
>    p2' <- replaceParamSP pos p2 pm
>    return (SVA_SP_If exp p1' (Just p2'))
> replaceParamSP pos (SVA_SP_If exp p1 Nothing) pm =
>  do
>    p1' <- replaceParamSP pos p1 pm
>    return (SVA_SP_If exp p1' Nothing)
> replaceParamSP pos (SVA_SP_DelayU d rest sq) p =
>  do
>    d' <- replaceParamDelay pos d p
>    rs' <- mapM (flip (replaceParamSP pos) p) rest
>    sq' <- replaceParamSP pos sq p
>    return (SVA_SP_DelayU d' rs' sq')
> replaceParamSP pos (SVA_SP_Delay d rest s1 s2) p =
>  do
>    d' <- replaceParamDelay pos d p
>    rs' <- mapM (flip (replaceParamSP pos) p) rest
>    s1' <- replaceParamSP pos s1 p
>    s2' <- replaceParamSP pos s2 p
>    return (SVA_SP_Delay d' rs' s1' s2')
> replaceParamSP pos (SVA_SP_Expr exp rep) p =
>  do
>    e' <- replaceParamExpr pos exp p
>    r' <- replaceParamRep pos rep p
>    return (SVA_SP_Expr e' r')
> replaceParamSP pos (SVA_SP_Match sq matches rep) p =
>  do
>    s' <- replaceParamSP pos sq p
>    m' <- mapM (mapM (flip (replaceParamAsgn pos) p)) matches
>    r' <- replaceParamRep pos rep p
>    return (SVA_SP_Match s' m' r')
> replaceParamSP pos (SVA_SP_Or s1 s2) p =
>  do
>    s1' <- replaceParamSP pos s1 p
>    s2' <- replaceParamSP pos s2 p
>    return (SVA_SP_Or s1' s2')
> replaceParamSP pos (SVA_SP_And s1 s2) p =
>  do
>    s1' <- replaceParamSP pos s1 p
>    s2' <- replaceParamSP pos s2 p
>    return (SVA_SP_And s1' s2')
> replaceParamSP pos (SVA_SP_Intersect s1 s2) p =
>  do
>    s1' <- replaceParamSP pos s1 p
>    s2' <- replaceParamSP pos s2 p
>    return (SVA_SP_Intersect s1' s2')
> replaceParamSP pos (SVA_SP_Within s1 s2) p =
>  do
>    s1' <- replaceParamSP pos s1 p
>    s2' <- replaceParamSP pos s2 p
>    return (SVA_SP_Within s1' s2')
> replaceParamSP pos (SVA_SP_Throughout s1 s2) p =
>  do
>    s1' <- replaceParamSP pos s1 p
>    s2' <- replaceParamSP pos s2 p
>    return (SVA_SP_Throughout s1' s2')
> replaceParamSP pos (SVA_SP_Parens sq rep) p =
>  do
>    sq' <- replaceParamSP pos sq p
>    r' <- replaceParamRep pos rep p
>    return (SVA_SP_Parens sq' r')
> replaceParamSP pos (SVA_SP_FirstMatch sq matches rep) p =
>  do
>    s' <- replaceParamSP pos sq p
>    m' <- mapM (mapM (flip (replaceParamAsgn pos) p)) matches
>    r' <- replaceParamRep pos rep p
>    return (SVA_SP_FirstMatch s' m' r')

> replaceParamRep :: Position -> SVA_REP -> (Id, CExpr) -> ISConvMonad SVA_REP
> replaceParamRep pos (SVA_REP_None) p = return SVA_REP_None
> replaceParamRep pos (SVA_REP_Cons d) p =
>  do
>    d' <- replaceParamDelay pos d p
>    return (SVA_REP_Cons d')
> replaceParamRep pos (SVA_REP_NonCons d) p =
>  do
>    d' <- replaceParamDelay pos d p
>    return (SVA_REP_NonCons d')
> replaceParamRep pos (SVA_REP_Goto d) p =
>  do
>    d' <- replaceParamDelay pos d p
>    return (SVA_REP_Goto d')

> replaceParamDelay :: Position -> SVA_Delay -> (Id, CExpr) -> ISConvMonad SVA_Delay
> replaceParamDelay pos (SVA_Delay_Unbound exp) p =
>  do
>    e' <- replaceParamExpr pos exp p
>    return (SVA_Delay_Unbound e')
> replaceParamDelay pos (SVA_Delay_Range e1 e2) p =
>  do
>    e1' <- replaceParamExpr pos e1 p
>    e2' <- replaceParamExpr pos e2 p
>    return (SVA_Delay_Range e1' e2')
> replaceParamDelay pos (SVA_Delay_Const exp) p =
>  do
>    e' <- replaceParamExpr pos exp p
>    return (SVA_Delay_Const e')

> replaceParamAsgn :: Position -> ImperativeStatement -> (Id, CExpr) -> ISConvMonad ImperativeStatement
> replaceParamAsgn pos (ISEqual po ids exp) p =
>  do
>    ids' <- mapIdOrTupleM (flip (replaceParamId pos) p) ids
>    e' <- replaceParamExpr pos exp p
>    return (ISEqual po ids' e')
> replaceParamAsgn pos (ISUpdate po e1 e2) p =
>  do
>    e1' <- replaceParamExpr pos e1 p
>    e2' <- replaceParamExpr pos e2 p
>    return (ISUpdate po e1' e2')
> replaceParamAsgn pos (ISNakedExpr po exp) p =
>  do
>    e' <- replaceParamExpr pos exp p
>    return (ISNakedExpr po e')
> replaceParamAsgn pos z p = cvtErr pos (EIllegalAssertStmt "sequence")

> replaceParamExpr :: Position -> CExpr -> (Id, CExpr) -> ISConvMonad CExpr
> replaceParamExpr pos (CVar nm) p =
>  do
>    res <- replaceParamIdToExpr pos nm p
>    case res of
>      Nothing -> return (CVar nm)
>      Just e -> return e
> replaceParamExpr pos (CApply nm args) p =
>  do
>    nm' <- replaceParamExpr pos nm p
>    args' <- mapM (flip (replaceParamExpr pos) p) args
>    return (CApply nm' args')
> replaceParamExpr pos (CTaskApply nm args) p =
>  do
>    nm' <- replaceParamExpr pos nm p
>    args' <- mapM (flip (replaceParamExpr pos) p) args
>    return (CTaskApply nm' args')
> replaceParamExpr pos (CBinOp e1 nm e2) p =
>  do
>    e1' <- replaceParamExpr pos e1 p
>    --nm' <- replaceParamId pos nm p
>    e2' <- replaceParamExpr pos e2 p
>    return (CBinOp e1' nm e2')
> replaceParamExpr pos (CLit nm) p =
>    return (CLit nm)
> replaceParamExpr pos (CHasType expr typ) p =
>  do
>    e' <- replaceParamExpr pos expr p
>    return (CHasType e' typ)
> replaceParamExpr pos (CSub pos_e e1 e2) p =
>  do
>    e1' <- replaceParamExpr pos e1 p
>    e2' <- replaceParamExpr pos e2 p
>    return (CSub pos_e e1' e2')
> replaceParamExpr pos (CSub2 e1 e2 e3) p =
>  do
>    e1' <- replaceParamExpr pos e1 p
>    e2' <- replaceParamExpr pos e2 p
>    e3' <- replaceParamExpr pos e3 p
>    return (CSub2 e1' e2' e3')
> replaceParamExpr pos exp p = cvtErr (getPosition exp) (EIllegalAssertExpr (show exp) "sequence")

> replaceParamIdToExpr :: Position -> Id -> (Id, CExpr) -> ISConvMonad (Maybe CExpr)
> replaceParamIdToExpr pos from (to, new) | from == to = return (Just new)
> replaceParamIdToExpr pos from (to, new) = return Nothing

> replaceParamId :: Position -> Id -> (Id, CExpr) -> ISConvMonad Id
> replaceParamId pos from (to, (CVar new)) | from == to = return new
> replaceParamId pos from (to, (CVar new)) = return from
> replaceParamId pos from (to, var) = cvtErr (getPosition var) (EIllegalAssertExpr (show var) "restricted assertion")

BACK END

These functions transform SVA_SEQ and SVA_PROP
into SVA_CORE_SEQ and SVA_CORE_PROP - the core temporal
logic behind SVA.

The transformation itself comes from the SystemVerilog LRM,
Appendix H, section 2.3

XXX Check for negative ranges... probably bad...

> deSugarProp :: SVA_PROP -> ISConvMonad SVA_CORE_PROP
> deSugarProp (SVA_PROP_Seq sq) =
>  do
>    s' <- deSugarSeq sq
>    return (SVA_CORE_PROP_Seq s')
> deSugarProp (SVA_PROP_Not p) =
>  do
>    p' <- deSugarProp p
>    return (SVA_CORE_PROP_Not p')
> deSugarProp (SVA_PROP_Or p1 p2) =
>  do
>    p1' <- deSugarProp p1
>    p2' <- deSugarProp p2
>    return (SVA_CORE_PROP_Or p1' p2')
> deSugarProp (SVA_PROP_And p1 p2) =
>  do
>    p1' <- deSugarProp p1
>    p2' <- deSugarProp p2
>    return (SVA_CORE_PROP_And p1' p2')
> deSugarProp (SVA_PROP_Implies sq p) =
>  do
>    s' <- deSugarSeq sq
>    p' <- deSugarProp p
>    return (SVA_CORE_PROP_Implies s' p')
> deSugarProp (SVA_PROP_ImpliesD sq p) =
>  do
>    aT <- assertTrue
>    s' <- deSugarSeq sq
>    p' <- deSugarProp p
>    del <- deSugarSeq (SVA_SEQ_Expr aT SVA_REP_None)
>    return (SVA_CORE_PROP_Implies (SVA_CORE_SEQ_Concat s' del) p')
> deSugarProp (SVA_PROP_If b p1 Nothing) =
>  do
>    p' <- deSugarProp p1
>    s' <- deSugarSeq (SVA_SEQ_Expr b SVA_REP_None)
>    return (SVA_CORE_PROP_Implies s' p')
> deSugarProp (SVA_PROP_If b p1 (Just p2)) =
>  do
>    p1' <- deSugarProp p1
>    p2' <- deSugarProp p2
>    let s1 = SVA_CORE_SEQ_Expr b
>    let s2 = SVA_CORE_SEQ_Expr (assertNot b)
>    return (SVA_CORE_PROP_And (SVA_CORE_PROP_Implies s1 p1') (SVA_CORE_PROP_Implies s2 p2'))


> deSugarSeq :: SVA_SEQ -> ISConvMonad SVA_CORE_SEQ
> -- b
> deSugarSeq (SVA_SEQ_Expr exp SVA_REP_None) =
>    return (SVA_CORE_SEQ_Expr exp)
> -- b [*0]
> -- The isOne check is added because somehow nulls were (incorrectly) getting wrapped around alwaysTrues.
> deSugarSeq (SVA_SEQ_Expr exp (SVA_REP_Cons (SVA_Delay_Const n))) | isZero n =
>    if (isOne exp)
>       then return (SVA_CORE_SEQ_Expr exp)
>       else return (SVA_CORE_SEQ_Null (SVA_CORE_SEQ_Expr exp))
> -- b [*1]
> deSugarSeq (SVA_SEQ_Expr exp (SVA_REP_Cons (SVA_Delay_Const n))) | isOne n =
>    return (SVA_CORE_SEQ_Expr exp)
> -- b [*n]

 > deSugarSeq (SVA_SEQ_Expr exp (SVA_REP_Cons (SVA_Delay_Const n))) =
 >  do
 >    n' <- decrExpr n
 >    let s1 = (SVA_SEQ_Expr exp SVA_REP_None)
 >    let s2 = (SVA_SEQ_Expr exp (SVA_REP_Cons (SVA_Delay_Const n')))
 >    deSugarSeq (delay1 s1 s2)

> -- b [*1:$]
> -- The isOne check is added because also unbounds were (incorrectly) getting wrapped around alwaysTrues.
> deSugarSeq (SVA_SEQ_Expr exp (SVA_REP_Cons (SVA_Delay_Unbound low))) | isOne low =
>    if (isOne exp)
>       then return (SVA_CORE_SEQ_Expr exp)
>       else return (SVA_CORE_SEQ_Unbound (SVA_CORE_SEQ_Expr exp))
> -- b [*0:$]
> deSugarSeq (SVA_SEQ_Expr exp (SVA_REP_Cons (SVA_Delay_Unbound low))) | isZero low =
>  do
>    let s1 = (SVA_SEQ_Expr exp (SVA_REP_Cons (SVA_Delay_Const (assertLit 0))))
>    let s2 = (SVA_SEQ_Expr exp (SVA_REP_Cons (SVA_Delay_Unbound (assertLit 1))))
>    deSugarSeq (SVA_SEQ_Or s1 s2)

 > -- b [*m:$]
 > deSugarSeq (SVA_SEQ_Expr exp (SVA_REP_Cons (SVA_Delay_Unbound low))) =
 >  do
 >    l' <- decrExpr low
 >    let s1 = (SVA_SEQ_Expr exp (SVA_REP_Cons (SVA_Delay_Const l')))
 >    let s2 = (SVA_SEQ_Expr exp (SVA_REP_Cons (SVA_Delay_Unbound (assertLit 1))))
 >    let d = (SVA_Delay_Const (assertLit 1))
 >    deSugarSeq (SVA_SEQ_Delay d [] s1 s2)

> -- b [*n:n]  (base case)
> deSugarSeq (SVA_SEQ_Expr exp (SVA_REP_Cons (SVA_Delay_Range low high))) | low `assertEq` high =
>    deSugarSeq (SVA_SEQ_Expr exp (SVA_REP_Cons (SVA_Delay_Const low)))

 > -- b [*m:n]  (recursive case)
 > deSugarSeq (SVA_SEQ_Expr exp (SVA_REP_Cons (SVA_Delay_Range low high))) =
 >      if (low > high)
 >       then cvtErr (getPosition low)
 >          (EIllegalAssertDelayRange
 >            ""
 >           "The lower bound cannot be greater than the upper bound.")
 >       else do
 >          l' <- incrExpr low
 >          let s1 = (SVA_SEQ_Expr exp (SVA_REP_Cons (SVA_Delay_Const low)))
 >          let s2 = (SVA_SEQ_Expr exp (SVA_REP_Cons (SVA_Delay_Range l' high)))
 >           -- let d = (SVA_Delay_Const (assertLit 1))
 >           deSugarSeq (SVA_SEQ_Or s1 s2)

> deSugarSeq (SVA_SEQ_Expr exp d@(SVA_REP_Cons _)) =
>    return (SVA_CORE_SEQ_Rep (SVA_CORE_SEQ_Expr exp) d)

> -- b [->n], b [->m:n], b [->m:$]
> deSugarSeq (SVA_SEQ_Expr exp (SVA_REP_Goto d)) =
>  do
>    let s1 = (SVA_SEQ_Expr (assertNot exp) (SVA_REP_Cons (SVA_Delay_Unbound (assertLit 0))))
>    let s2 = (SVA_SEQ_Expr exp SVA_REP_None)
>    let sq = (delay1 s1 s2)
>    deSugarSeq (SVA_SEQ_Parens sq (SVA_REP_Cons d))
> -- b [=n], b [=m:n], b [=m:$]
> deSugarSeq (SVA_SEQ_Expr exp (SVA_REP_NonCons d)) =
>  do
>    let s1 = (SVA_SEQ_Expr exp (SVA_REP_Goto d))
>    let s2 = (SVA_SEQ_Expr (assertNot exp) (SVA_REP_Cons (SVA_Delay_Unbound (assertLit 0))))
>    deSugarSeq (delay1 s1 s2)
> -- Unary x S1 ...
> deSugarSeq (SVA_SEQ_DelayU d rest sq) =
>  do
>    aT <- assertTrue
>    let del = (SVA_SEQ_Expr aT (SVA_REP_Cons d))
>    s' <- deSugarSeq (delay1 del sq)
>    r' <- mapM deSugarSeq rest
>    fuseRest s' r'
> -- S1 0 S2
> deSugarSeq (SVA_SEQ_Delay (SVA_Delay_Const r) [] s1 s2) | isZero r =
>  do
>    s1' <- deSugarSeq s1
>    s2' <- deSugarSeq s2
>    return (SVA_CORE_SEQ_Fuse s1' s2')
> -- S1 1 S2
> deSugarSeq (SVA_SEQ_Delay (SVA_Delay_Const r) [] s1 s2) | isOne r =
>  do
>    s1' <- deSugarSeq s1
>    s2' <- deSugarSeq s2
>    return (SVA_CORE_SEQ_Concat s1' s2')
> -- S1 [0:0] S2
> deSugarSeq (SVA_SEQ_Delay (SVA_Delay_Range low high) [] s1 s2) | isZero low && isZero high =
>  do
>    s1' <- deSugarSeq s1
>    s2' <- deSugarSeq s2
>    return (SVA_CORE_SEQ_Fuse s1' s2')
> -- S1 [1:1] S2
> deSugarSeq (SVA_SEQ_Delay (SVA_Delay_Range low high) [] s1 s2) | isOne low && isOne high =
>  do
>    s1' <- deSugarSeq s1
>    s2' <- deSugarSeq s2
>    return (SVA_CORE_SEQ_Concat s1' s2')
> -- S1 [0:n] S2
> deSugarSeq (SVA_SEQ_Delay (SVA_Delay_Range low high) [] s1 s2) | isZero low =
>  do
>    let del = (SVA_SEQ_Delay (SVA_Delay_Range (assertLit 1) high) [] s1 s2)
>    deSugarSeq (SVA_SEQ_Or (delay0 s1 s2) del)
> -- S1 [0:$] S2
> deSugarSeq (SVA_SEQ_Delay (SVA_Delay_Unbound low) [] s1 s2) | isZero low =
>  do
>    let del = (delay1 s1 s2)
>    deSugarSeq (SVA_SEQ_Or (delay0 s1 s2) del)
> deSugarSeq (SVA_SEQ_Delay d rest s1 s2) =
>  do
>    s1' <- deSugarSeq s1
>    s2' <- deSugarSeq s2
>    rest' <- mapM deSugarSeq rest
>    return (SVA_CORE_SEQ_Delay d rest' s1' s2')


 > --  **** lets try to do this differently (by generating ORs of CONCATS instead of CONCATS of ORS (which seem to work better)

 > deSugarSeq (SVA_SEQ_Delay (SVA_Delay_Range low high) [] s1 s2) | low `assertEq` high =
 >  do
 >    l' <- decrExpr low
 >    s1' <- (deSugarSeq s1)
 >    rest <- deSugarSeq (SVA_SEQ_Delay (SVA_Delay_Range l' l') [] alwaysTrue s2)
 >    return (SVA_CORE_SEQ_Concat s1' rest)
 > --
 > deSugarSeq (SVA_SEQ_Delay (SVA_Delay_Range low high) [] s1 s2) =
 >  do
 >    if (low > high)
 >       then cvtErr (getPosition low)
 >          (EIllegalAssertDelayRange
 >            ""
 >           "The lower bound cannot be greater than the upper bound.")
 >       else do
 > ---             traceM("BBB " ++ (pvpReadable low) ++ " " ++ (pvpReadable high))
 >             l' <- incrExpr low
 >              first <- deSugarSeq (SVA_SEQ_Delay (SVA_Delay_Range low low) [] s1 s2)
 >              rest <- deSugarSeq (SVA_SEQ_Delay (SVA_Delay_Range l' high) [] s1 s2)
 >              return (SVA_CORE_SEQ_Or first rest)
 > --All other delays
 > deSugarSeq (SVA_SEQ_Delay d rest s1 s2) =
 >  do
 >    d' <- decrDelay d
 >    let del = (SVA_SEQ_Expr assertTrue (SVA_REP_Cons d'))
 >    s' <- deSugarSeq (delay1 s1 (delay1 del s2))
 >    r' <- mapM deSugarSeq rest
 >    fuseRest s' r'

> -- S1 or S2
> deSugarSeq (SVA_SEQ_Or s1 s2) =
>  do
>    s1' <- deSugarSeq s1
>    s2' <- deSugarSeq s2
>    return (SVA_CORE_SEQ_Or s1' s2')
> -- S1 and S2
> deSugarSeq (SVA_SEQ_And sq1 sq2) =
>  do
>    awT <- alwaysTrue
>    let s1A = delay1 sq1 awT
>    s1 <- deSugarSeq (SVA_SEQ_Intersect s1A sq2)
>    let s2B = delay1 sq2 awT
>    s2 <- deSugarSeq (SVA_SEQ_Intersect sq1 s2B)
>    return (SVA_CORE_SEQ_Or s1 s2)
> -- S1 intersect S2
> deSugarSeq (SVA_SEQ_Intersect s1 s2) =
>  do
>    s1' <- deSugarSeq s1
>    s2' <- deSugarSeq s2
>    return (SVA_CORE_SEQ_Intersect s1' s2')
> -- S1 within S2
> deSugarSeq (SVA_SEQ_Within s1 s2) =
>  do
>    -- s1' <- deSugarSeq s1
>    s2' <- deSugarSeq s2
>    let n = getLongestPathSeq s2'
>    s1' <-  createOneWithinSequence 2 n s1
> --   traceM("JJJJ " ++ (itos n))
>    return (SVA_CORE_SEQ_Intersect s1' s2')
> -- S1 throughout S2
> deSugarSeq (SVA_SEQ_Throughout s1 s2) =
>  do
>    let sq = (SVA_SEQ_Parens s1 (SVA_REP_Cons (SVA_Delay_Unbound (assertLit 0))))
>    deSugarSeq (SVA_SEQ_Intersect sq s2)
> -- This case should never come up...
> deSugarSeq (SVA_SEQ_Match sq [] rep) =
>    deSugarSeq (SVA_SEQ_Parens sq rep)
> -- (1, v = x)
> deSugarSeq (SVA_SEQ_Match sq [match] SVA_REP_None) | isTrue sq =
>    return (SVA_CORE_SEQ_Asgn match)
> -- (S, v = x)
> deSugarSeq (SVA_SEQ_Match sq [match] SVA_REP_None) =
>  do
>    s' <- deSugarSeq sq
>    return (SVA_CORE_SEQ_Fuse s' (SVA_CORE_SEQ_Asgn match))
> -- (S, v1 = x, v2 = y...)
> deSugarSeq (SVA_SEQ_Match sq (m:matches) SVA_REP_None) =
>  do
>    aT <- assertTrue
>    let s' = (SVA_SEQ_Match sq [m] SVA_REP_None)
>    deSugarSeq (delay0 s' (SVA_SEQ_Match (SVA_SEQ_Expr aT SVA_REP_None) matches SVA_REP_None))
> -- (S, v1 = x...) [x]
> deSugarSeq (SVA_SEQ_Match sq matches rep) =
>    deSugarSeq (SVA_SEQ_Parens (SVA_SEQ_Match sq matches SVA_REP_None) rep)
> -- first_match(S)
> deSugarSeq (SVA_SEQ_FirstMatch sq [] SVA_REP_None) =
>  do
>    s' <- deSugarSeq sq
>    return  (SVA_CORE_SEQ_FirstMatch s')
> -- first_match(S) [x]
> deSugarSeq (SVA_SEQ_FirstMatch sq [] rep) =
>    deSugarSeq (SVA_SEQ_Parens (SVA_SEQ_FirstMatch sq [] SVA_REP_None) rep)
> -- first_match(S, v1 = x, v2 = y...) [x]
> deSugarSeq (SVA_SEQ_FirstMatch sq matches rep) =
>    deSugarSeq (SVA_SEQ_Match (SVA_SEQ_FirstMatch sq [] SVA_REP_None) matches rep)
> -- (S)
> deSugarSeq (SVA_SEQ_Parens sq SVA_REP_None) =
>    deSugarSeq sq
> -- (S) [x]
> deSugarSeq (SVA_SEQ_Parens sq rep) =
>    distributeRep sq rep
> --death
> -- deSugarSeq sq =
> --  do
> --    internalError ("CVParserImperative:deSugarSeq " ++ (pvpString sq))

>
> -- createWithinSequence :: Integer -> SVA_SEQ -> ISConvMonad SVA_CORE_SEQ
> -- createWithinSequence max s =
>
> createOneWithinSequence :: Integer -> CExpr -> SVA_SEQ -> ISConvMonad SVA_CORE_SEQ
> createOneWithinSequence 0 max s =
>  do
>    aT <- assertTrue
>    s' <- deSugarSeq s
>    let post = (SVA_SEQ_Expr aT (SVA_REP_Cons (SVA_Delay_Range (assertLit 0)
>                                                               (max))))
>    post' <- deSugarSeq post
>    return (SVA_CORE_SEQ_Concat s' post')
>
> createOneWithinSequence n max s =
>  do
>    aT <- assertTrue
>    s' <- deSugarSeq s
>    let pre = (SVA_SEQ_Expr aT (SVA_REP_Cons (SVA_Delay_Const (assertLit n))))
>    let post = (SVA_SEQ_Expr aT (SVA_REP_Cons (SVA_Delay_Range (assertLit 0)
>                                                               (max))))
>    pre' <- deSugarSeq pre
>    post' <- deSugarSeq post
>    return (SVA_CORE_SEQ_Fuse pre' (SVA_CORE_SEQ_Fuse s' post'))

Distributes a repetition.
Per the LRM, any repetition may follow a boolean expression,
but after a general sequence only consecutive repetition is allowed.

> distributeRep :: SVA_SEQ -> SVA_REP -> ISConvMonad SVA_CORE_SEQ
> distributeRep (SVA_SEQ_Expr exp SVA_REP_None) r = deSugarSeq (SVA_SEQ_Expr exp r)
> distributeRep seq (SVA_REP_None) = deSugarSeq seq
> distributeRep seq (SVA_REP_Cons d) = consRep seq d
> distributeRep seq (SVA_REP_NonCons d) = cvtErr (getPosition d) (EIllegalRepetition "non-consecutive repetition [= ]")
> distributeRep seq (SVA_REP_Goto d) = cvtErr (getPosition d) (EIllegalRepetition "goto repetition [-> ]")
> -- distributeRep seq rep = internalError $ "CVParserImperative:distributeRep " ++ (show seq) ++ (show rep)

Consecutive repetition is just repeating a sequence back to back.

> consRep :: SVA_SEQ -> SVA_Delay -> ISConvMonad SVA_CORE_SEQ
> consRep (SVA_SEQ_Expr exp SVA_REP_None) d =
>   deSugarSeq (SVA_SEQ_Expr exp (SVA_REP_Cons d))
> consRep seq (SVA_Delay_Const n) | isZero n =
>  do
>    s' <- deSugarSeq seq
>    return (SVA_CORE_SEQ_Null s')
> consRep seq (SVA_Delay_Const n) | isOne n =
>    deSugarSeq seq
> consRep seq (SVA_Delay_Const n) =
>  do
>    n' <- decrExpr n
>    s' <- deSugarSeq seq
>    s2 <- consRep seq (SVA_Delay_Const n')
>    return (SVA_CORE_SEQ_Concat s' s2)
> consRep seq (SVA_Delay_Range low high) | low `assertEq` high =
>    consRep seq (SVA_Delay_Const low)
> consRep seq (SVA_Delay_Range low high) =
>  do
>    l' <- incrExpr low
>    s1 <- deSugarSeq seq
>    s2 <- consRep seq (SVA_Delay_Range l' high)
>    return (SVA_CORE_SEQ_Or s1 s2)
> consRep seq (SVA_Delay_Unbound low) | isZero low =
>  do
>    s' <- deSugarSeq seq
>    let s1 = SVA_CORE_SEQ_Null s'
>    let s2 = SVA_CORE_SEQ_Unbound s'
>    return (SVA_CORE_SEQ_Or s1 s2)
> consRep seq (SVA_Delay_Unbound low) | isOne low =
>  do
>    s' <- deSugarSeq seq
>    return (SVA_CORE_SEQ_Unbound s')
> consRep seq (SVA_Delay_Unbound low) =
>  do
>    l' <- decrExpr low
>    s1 <- consRep seq (SVA_Delay_Const l')
>    s2 <- consRep seq (SVA_Delay_Unbound (assertLit 1))
>    return (SVA_CORE_SEQ_Concat s1 s2)

ASSERTION Helper functions

> fuseRest ::  SVA_CORE_SEQ -> [SVA_CORE_SEQ] -> ISConvMonad SVA_CORE_SEQ
> fuseRest sq [] = return sq
> fuseRest sq [s] =
>    return (SVA_CORE_SEQ_Fuse sq s)
> fuseRest sq (s:ss) =
>  do
>    s2 <- fuseRest s ss
>    return (SVA_CORE_SEQ_Fuse sq s2)

> assertEq :: CExpr -> CExpr -> Bool
> -- XXX This relies on Eq of CExpr to ignore positions
> assertEq s1 s2 = s1 == s2

> zero :: CExpr
> zero = (CLit (CLiteral noPosition (LInt (ilDec 0))))

> one :: CExpr
> one = (CLit (CLiteral noPosition (LInt (ilDec 1))))

> minus1 :: CExpr
> minus1 = (CLit (CLiteral noPosition (LInt (ilDec (-1)))))

> incrExpr :: CExpr -> ISConvMonad CExpr
> incrExpr (CLit (CLiteral p (LInt (IntLit w b n)))) =
>   return (CLit (CLiteral p (LInt (IntLit w b (n+1)))))
> incrExpr e = return (CBinOp e idPlus one)

 > incrExpr e =
 >    cvtErr (getPosition e) (EIllegalAssertExpr (show e) "range")

> decrExpr :: CExpr -> ISConvMonad CExpr
> decrExpr (CLit (CLiteral p (LInt (IntLit w b n)))) =
>   return (CLit (CLiteral p (LInt (IntLit w b (n-1)))))
> decrExpr e = return (CBinOp e idMinus one)

 > decrExpr e =
 >    cvtErr (getPosition e) (EIllegalAssertExpr (show e) "range")

> isTrue :: SVA_SEQ -> Bool
> isTrue (SVA_SEQ_Expr exp rep) | isOne exp = True
> isTrue _ = False

> isZero :: CExpr -> Bool
> isZero (CLit (CLiteral _ (LInt (IntLit _ _ 0)))) = True
> isZero exp = False

> isOne :: CExpr -> Bool
> isOne (CLit (CLiteral _ (LInt (IntLit _ _ 1)))) = True
> isOne exp = False

> delayN :: Integer -> SVA_SEQ -> SVA_SEQ -> SVA_SEQ
> delayN n s1 s2 = (SVA_SEQ_Delay (SVA_Delay_Const (assertLit n)) [] s1 s2)

> delay1, delay0 :: SVA_SEQ -> SVA_SEQ -> SVA_SEQ
> delay1 = delayN 1
> delay0 = delayN 0

> assertLit :: Integer -> CExpr
> assertLit n = CLit (CLiteral noPosition (LInt (ilSizedDec 32 n)))

> assertTrue :: ISConvMonad CExpr
> assertTrue =
>  do pt <- passThrough
>     return (if pt then CCon idTrue [] else assertLit 1)

> alwaysTrue :: ISConvMonad SVA_SEQ
> alwaysTrue =
>  do aT <- assertTrue
>     return (SVA_SEQ_Expr aT (SVA_REP_Cons (SVA_Delay_Unbound (assertLit 0))))

> assertNot :: CExpr -> CExpr
> assertNot (CApply (CVar id) [f]) | isNot (getIdBaseString id) = f
>  where
>    isNot str = str == "!" || str == "not"
> assertNot exp = (CApply fnot [exp])
>  where
>    fnot = (CVar (mkQId noPosition (mkFString "Prelude") (mkFString "not")))

> decrDelay :: SVA_Delay -> ISConvMonad SVA_Delay
> decrDelay (SVA_Delay_Const e) =
>  do
>    e' <- decrExpr e
>    return (SVA_Delay_Const e')
> decrDelay (SVA_Delay_Unbound e) =
>  do
>    e' <- decrExpr e
>    return (SVA_Delay_Unbound e')
> decrDelay (SVA_Delay_Range e1 e2) =
>  do
>    e1' <- decrExpr e1
>    e2' <- decrExpr e2
>    return (SVA_Delay_Range e1' e2')

Does final cleanup before hardware generation

Currently fixes Unbounds to work with the library Unbound
Also transforms away vacuous CORE_SEQ_Null

> cleanupProp :: SVA_CORE_PROP -> ISConvMonad SVA_CORE_PROP
> cleanupProp (SVA_CORE_PROP_Seq s) =
>  do
>    s' <- cleanupSeq s
>    return (SVA_CORE_PROP_Seq s')
> cleanupProp (SVA_CORE_PROP_Not p) =
>  do
>    p' <- cleanupProp p
>    return (SVA_CORE_PROP_Not p')
> cleanupProp (SVA_CORE_PROP_Or p1 p2) =
>  do
>    p1' <- cleanupProp p1
>    p2' <- cleanupProp p2
>    return (SVA_CORE_PROP_Or p1' p2')
> cleanupProp (SVA_CORE_PROP_And p1 p2) =
>  do
>    p1' <- cleanupProp p1
>    p2' <- cleanupProp p2
>    return (SVA_CORE_PROP_And p1' p2')
> cleanupProp (SVA_CORE_PROP_Implies s p) =
>  do
>    s' <- cleanupSeq s
>    p' <- cleanupProp p
>    return (SVA_CORE_PROP_Implies s' p')


> cleanupSeq :: SVA_CORE_SEQ -> ISConvMonad SVA_CORE_SEQ
> cleanupSeq (SVA_CORE_SEQ_Concat (SVA_CORE_SEQ_Unbound s1) s2) =
>  do
>    s1' <- cleanupSeq s1
>    s2' <- cleanupSeq s2
>    return (SVA_CORE_SEQ_Fuse (SVA_CORE_SEQ_Unbound s1') s2')
> cleanupSeq (SVA_CORE_SEQ_Concat s1 s2) =
>  do
>    s1' <- cleanupSeq s1
>    s2' <- cleanupSeq s2
>    return (SVA_CORE_SEQ_Concat s1' s2')
> cleanupSeq (SVA_CORE_SEQ_Fuse s1 s2) =
>  do
>    s1' <- cleanupSeq s1
>    s2' <- cleanupSeq s2
>    return (SVA_CORE_SEQ_Fuse s1' s2')
> cleanupSeq (SVA_CORE_SEQ_Expr e) =
>    return (SVA_CORE_SEQ_Expr e)
> cleanupSeq (SVA_CORE_SEQ_Asgn is) =
>    return (SVA_CORE_SEQ_Asgn is)
> cleanupSeq (SVA_CORE_SEQ_FirstMatch s1) =
>  do
>    s1' <- cleanupSeq s1
>    return (SVA_CORE_SEQ_FirstMatch s1')
> cleanupSeq (SVA_CORE_SEQ_Intersect s1 s2) =
>  do
>    s1' <- cleanupSeq s1
>    s2' <- cleanupSeq s2
>    return (SVA_CORE_SEQ_Intersect s1' s2')
> -- do some simple reduction (x Or-ed with True is x)
> cleanupSeq (SVA_CORE_SEQ_Or s1 s2@(SVA_CORE_SEQ_Expr (CLit (CLiteral _ (LInt (IntLit _ _ 1)))))) =
>    cleanupSeq s1
> cleanupSeq (SVA_CORE_SEQ_Or s1@(SVA_CORE_SEQ_Expr (CLit (CLiteral _ (LInt (IntLit _ _ 1))))) s2) =
>    cleanupSeq s2
> cleanupSeq (SVA_CORE_SEQ_Or s1 s2) =
>  do
>    s1' <- cleanupSeq s1
>    s2' <- cleanupSeq s2
>    return (SVA_CORE_SEQ_Or s1' s2')
> cleanupSeq z = return z

> passThrough :: ISConvMonad Bool
> passThrough = issPassThrough <$> getISCState

> transAssertStmt :: Position -> SVA_Statement -> ISConvMonad [ImperativeStatement]
> transAssertStmt p s =
>  do pt <- passThrough
>     (if pt then transAssertStmtPT else transAssertStmtFSM) p s

PASSTHROUGH ASSERTIONS

This is the "backend" which causes assertions to be passed through to the generated RTL

> transAssertStmtPT :: Position -> SVA_Statement -> ISConvMonad [ImperativeStatement]
> transAssertStmtPT pos (isAlways, (SVA_STMT_Assert mname prop onPass onFail)) =
>  do
>    nm <- newAssertName pos
>    bUnrolled <- unrollPROP pos prop
>    bDeSugared <- deSugarProp bUnrolled
>    bClean <- cleanupProp bDeSugared
>    let (rName, bName, aName) = ruleNames pos
>    let assStr = getIdBaseString (fromMaybe aName mname)
>    let theTask = consAssertion pos assStr bName bClean
>    passExpr <- mkAction onPass
>    failExpr <- mkAction onFail
>    return
>     [(ISDecl pos (Right bName) (Just (TAp (TCon (TyCon idReg (Just KStar) TIabstract))
>                                (TCon (TyCon idBool (Just KStar) TIabstract))))) [],
>      (ISBind pos [] (Right bName) (CVar (idMkRegU pos))),
>      (ISRule pos rName []
>       (CRule [] (Just (stringLiteralAt pos (getIdBaseString rName)))
>              [CQFilter (CCon idTrue [])]
>              (Caction pos [CSExpr Nothing theTask,
>                            CSExpr Nothing (Cif pos (CVar bName) passExpr failExpr)])))]
> transAssertStmtPT pos (_, z) = --unsupported errors go here
>    internalError ("CVParserImperative:transAssertStmtPT at " ++ show pos)

> consAssertion :: Position -> String -> Id -> SVA_CORE_PROP -> CExpr
> consAssertion pos idstr idb p =
>     let (s, es) = ppProp p []
>     in (CTaskApply (CVar idSVA)
>         ((CLit (CLiteral pos (LString idstr))):
>          (CLit (CLiteral pos (LString s))) :
>          reverse((boolParam pos (CVar idb)):es)))

> ruleNames :: Position -> (Id,Id,Id)
> ruleNames pos =
>     let sl = itos(getPositionLine pos)
>         sc = itos(getPositionColumn pos)
>         ids = "L"++sl++"C"++sc
>         rid = "svaRule_"++ids
>         bid = "svaBool_"++ids
>         aid = "svaAssertion_"++ids
>     in (mk_dangling_id rid pos, mk_dangling_id bid pos, mk_dangling_id aid pos)

> svaParam :: Id -> Position -> CExpr -> CExpr
> svaParam i pos e =
>     let rid = idTheResult pos
>     in (Ccase pos (CCon i [e])
>         [CCaseArm {cca_pattern = CPCon i [CPVar rid],
>                    cca_filters = [],
>                    cca_consequent = CVar rid}])

> boolParam :: Position -> CExpr -> CExpr
> boolParam = svaParam idSvaBool
> numParam :: Position -> CExpr -> CExpr
> numParam p n = svaParam idSvaNumber p (CApply (CVar (idFromInteger p)) [n])

> ppDel :: SVA_Delay -> [CExpr] -> (String, [CExpr])
> ppDel (SVA_Delay_Const e) es = ("%n", ((numParam noPosition e):es))
> ppDel (SVA_Delay_Unbound e) es = ("%n:$", ((numParam noPosition e):es))
> ppDel (SVA_Delay_Range e1 e2) es = ("%n:%n", ((numParam noPosition e2):
>                                               (numParam noPosition e1):es))

> ppRep :: SVA_REP -> [CExpr] -> (String, [CExpr])
> ppRep (SVA_REP_Cons d) es =
>     let (s,es1) = ppDel d es in ("*"++s, es1)
> ppRep (SVA_REP_NonCons d) es =
>     let (s,es1) = ppDel d es in ("="++s, es1)
> ppRep (SVA_REP_Goto d) es =
>     let (s,es1) = ppDel d es in ("->"++s, es1)
> ppRep (SVA_REP_None) es = internalError ("SVA_REP_None")

> ppSeq :: SVA_CORE_SEQ -> [CExpr] -> (String, [CExpr])

> ppSeq (SVA_CORE_SEQ_Expr exp) es = ("(%b)", ((boolParam noPosition exp):es))

> ppSeq (SVA_CORE_SEQ_Concat s1 s2) es =
>     let (st1, es1) = ppSeq s1 es
>         (st2, es2) = ppSeq s2 es1
>     in ("(" ++ st1 ++ ")##1(" ++ st2 ++ ")", es2)
> ppSeq (SVA_CORE_SEQ_Fuse s1 s2) es =
>     let (st1, es1) = ppSeq s1 es
>         (st2, es2) = ppSeq s2 es1
>     in ("(" ++ st1 ++ ")##0(" ++ st2 ++ ")", es2)
> ppSeq (SVA_CORE_SEQ_Asgn asns) es =
>     internalError("ppSeq: local variables not yet implemented")
> ppSeq (SVA_CORE_SEQ_Or s1 s2) es =
>     let (st1, es1) = ppSeq s1 es
>         (st2, es2) = ppSeq s2 es1
>     in ("(" ++ st1 ++ ")or(" ++ st2 ++ ")", es2)
> ppSeq (SVA_CORE_SEQ_Intersect s1 s2) es =
>     let (st1, es1) = ppSeq s1 es
>         (st2, es2) = ppSeq s2 es1
>     in ("(" ++ st1 ++ ")intersect(" ++ st2 ++ ")", es2)
> ppSeq (SVA_CORE_SEQ_FirstMatch seq) es =
>     let (st1, es1) = ppSeq seq es
>     in ("(first_match(" ++ st1 ++ "))", es1)
> ppSeq (SVA_CORE_SEQ_Null seq) es =
>     let (st1, es1) = ppSeq seq es
>     in ("((" ++ st1 ++ ")[*0])", es1)
> ppSeq (SVA_CORE_SEQ_Unbound seq) es =
>     let (st1, es1) = ppSeq seq es
>     in ("((" ++ st1 ++ ")[*1:$])", es1)

> ppSeq (SVA_CORE_SEQ_Delay del rest s1 s2) es =
>     let (st1, es1) = ppSeq s1 es
>         (ns,  es2) = ppDel del es1
>         (st2, es3) = ppSeq s2 es2
>         f (pst,pes) sq =
>           let (s, pes1) = ppSeq sq pes in (pst++"##0("++s++")", pes1)
>         (fst, fes) = foldl f ("",es3) rest
>     in ("(" ++ st1 ++ ")##"++ns++"(" ++ st2 ++ ")"++fst, fes)

> ppSeq (SVA_CORE_SEQ_Rep exp rep) es =
>     let (st1, es1) = ppSeq exp es
>         (st2, es2) = ppRep rep es1
>     in ("((" ++ st1 ++ ")["++st2++"])", es2)

> ppProp :: SVA_CORE_PROP -> [CExpr] -> (String, [CExpr])
> ppProp (SVA_CORE_PROP_Seq seq) es =
>     let (st1, es1) = ppSeq seq es
>     in ("(" ++ st1 ++ ")", es1)
> ppProp (SVA_CORE_PROP_Not prop) es =
>     let (st1, es1) = ppProp prop es
>     in ("(not(" ++ st1 ++ "))", es1)
> ppProp (SVA_CORE_PROP_And p1 p2) es =
>     let (st1, es1) = ppProp p1 es
>         (st2, es2) = ppProp p2 es1
>     in ("(" ++ st1 ++ ")and(" ++ st2 ++ ")", es2)
> ppProp (SVA_CORE_PROP_Or p1 p2) es =
>     let (st1, es1) = ppProp p1 es
>         (st2, es2) = ppProp p2 es1
>     in ("(" ++ st1 ++ ")or(" ++ st2 ++ ")", es2)
> ppProp (SVA_CORE_PROP_Implies p1 p2) es =
>     let (st1, es1) = ppSeq p1 es
>         (st2, es2) = ppProp p2 es1
>     in ("(" ++ st1 ++ ")|->(" ++ st2 ++ ")", es2)



TRANSLATION TO BSV

This is the "backend" which generates a FSM to check the assertions

These functions do the important job of turning the assertion into actual hardware
IE modules in the SVA.bs library.

Main translation function

> transAssertStmtFSM :: Position -> SVA_Statement -> ISConvMonad [ImperativeStatement]
> transAssertStmtFSM pos (isAlways, (SVA_STMT_Assert _ prop onPass onFail)) =
>  do
>    nm <- newAssertName pos
>    bUnrolled <- unrollPROP pos prop
>    bDeSugared <- deSugarProp bUnrolled
>    bClean<- cleanupProp bDeSugared
>    (defs, top) <- transAssertBody isAlways bClean
>    let nmId = mkId pos (mkFString nm)
>    let ifcId = mkIdPre fs_the_ (unQualId nmId)        -- XXX filename gen in top only!!!
>    passExpr <- mkAction onPass
>    failExpr <- mkAction onFail
>    assertMod <- instAssertMod isAlways bClean (top, passExpr, failExpr)
>    let assertType = TCon assertCon
>    let inst = ISInst pos [] nmId ifcId (Just assertType) Nothing Nothing Nothing assertMod
>    rule_st <- mkRule nmId
>    return $ defs ++ [inst, rule_st]
> transAssertStmtFSM pos (_, z) = --unsupported errors go here
>    internalError ("CVParserImperative:transAssertStmtFSM at " ++ show pos)

> assertCon :: TyCon
> assertCon = TyCon (mkQId noPosition (mkFString "SVA") (mkFString "Assertion")) (Just KStar) TIabstract

Instantiate the assertion module itself

> instAssertMod :: Bool -> SVA_CORE_PROP -> (CExpr, CExpr, CExpr) -> ISConvMonad CExpr
> instAssertMod False prop (p_mod, passExpr, failExpr) =
>    return (CApply (mkAssertMod "mkAssert") [p_mod, passExpr, failExpr])
> instAssertMod True prop (lst, passExpr, failExpr) =
>    return (CApply (mkAssertMod "mkAssertAlways") [lst, passExpr, failExpr])

> mkAction :: [ImperativeStatement] -> ISConvMonad CExpr
> mkAction [] =
>   return $ cVar (mkId noPosition (mkFString "noAction"))
> mkAction as = do
>  convExpr <- gets issExprConverter
>  convExpr noPosition actionFlags { stmtContext = ISCExpression } True as


Creates the rule which is added to the module which uses assertions to
call the advance method on every clock cycle.

> mkRule :: Id -> ISConvMonad ImperativeStatement
> mkRule nm =
>  do
>    let methNm = mkQId noPosition (mkFString "SVA") (mkFString "advance")
>    let select = CSelect (cVar nm) methNm
>    let body = CApply select []
>    let tr = [CQFilter (CCon (idTrueAt noPosition) [])]
>    let ruleNm = mkIdPost nm fs__fire
>    let ruleNmExp = stringLiteralAt noPosition ((getIdString nm) ++ s__fire)
>    let rule = CRule [RPfireWhenEnabled, RPnoImplicitConditions] (Just ruleNmExp) tr body
>    let imp = (ISRule noPosition ruleNm [] rule)
>    return imp

> newAssertName :: Position -> ISConvMonad String
> newAssertName (Position f l _ _) = do
>  state <- get
>  let s = takeWhile (/='.') $ reverse $ takeWhile (/='/') $ reverse $ getFString f
>      n = issAssertNum state
>      mkStr = "assertion_" ++ s ++ "_" ++ (show l) ++ "__" ++ (show n)
>
>  put $ state {issFile = s, issLine = l,
>               issAssertNum = n + 1, issAssertSubNum = 0, issAssertDecls = []}
>  return mkStr

> curAssertName :: ISConvMonad String
> curAssertName = do
>   state <- get
>   let s = issFile state
>       l = issLine state
>       n = issAssertNum state
>       mkStr = "assertion_" ++ s ++ "_" ++ (show l) ++ "__" ++ (show n)
>   return mkStr

We do a stack of decls in case we decide to turn a bunch of them into
a sub-module definition

> pushDecls :: ISConvMonad ()
> pushDecls = modify $ \s -> s {issAssertDecls = [] : issAssertDecls s}

> popDecls :: ISConvMonad [ImperativeStatement]
> popDecls = do
>   state <- get
>   let decls = issAssertDecls state
>       (decls', res) = case decls of
>         [] -> ([[]], [])
>         [x] -> ([[]], x)
>         z -> (tail decls, head decls)
>   put $ state {issAssertDecls = decls'}
>   return res

Makes a sub-module for mkPropImplies. This submodule can then be replicated

> mkSubModule :: [ImperativeStatement] -> ISConvMonad CExpr
> mkSubModule body = do
>   state <- get
>   let propType =
>         CQType [(CPred (CTypeclass (idIsModuleAt noPosition))
>                          [cTVar (idM noPosition), cTVar (idC noPosition)])]
>                (TAp (cTVar (idM noPosition))
>                     (cTCon (mkId noPosition (mkFString "Property"))))
>       intType = cTCon (mkId noPosition (mkFString "Property"))
>       f = issFile state
>       l = issLine state
>       s = issAssertSubNum state
>       n = issAssertNum state
>       mkStr = "assertion_" ++ f ++ "_" ++ (show l) ++ "__" ++ (show n)
>       nm = mkId noPosition (mkFString (mkStr ++ "_" ++ (show s)))
>       bFixed = fixReturn body
>       stmtChecker = issStmtChecker state ISCIsModule
>       convStmts = issStmtConverter state
>       r1 = run (stmtChecker (reverse bFixed)) state
>       r2 = case r1 of
>         (Right (body', sChecked)) -> run (convStmts (ISCIsModule, Just intType, Nothing) False body') sChecked
>         Left s -> Left s
>       stmts = case r2 of
>        (Right (res, s')) -> map CMStmt res
>        z -> []
>       mod = ISModule noPosition nm Nothing propType (CClause [] [] (Cmodule noPosition stmts))
>       decls = issAssertDecls state
>       decls' = case decls of
>         [] -> [[mod]]
>         (x:xs) -> (mod : x) : xs
>   put $ state { issAssertSubNum = s + 1, issAssertDecls = decls' }
>   case r2 of
>     (Right (s', res)) -> return $ cVar nm
>     Left s            -> throwError s


> fixReturn :: [ImperativeStatement] -> [ImperativeStatement]
> -- XXX This drops the pprops, but hopefully they are empty
> fixReturn ((ISBind pos _ (Right nm) exp) : xs) = (ISNakedExpr noPosition exp) : xs
> fixReturn z = internalError "CVParserImperative:fixReturn"

Creates a binding declaration

> assertBind :: CExpr -> ISConvMonad CExpr
> assertBind e = do
>   state <- get
>   let f = issFile state
>       l = issLine state
>       s = issAssertSubNum state
>       n = issAssertNum state
>       mkStr = concat ["assertion_", f, "_", show l, "__", show n, "_", show s]
>       decls = issAssertDecls state
>       newdecl = ISDecl noPosition (Right newName) Nothing []
>       newbind = ISBind noPosition [] (Right newName) e
>       decls' :: [[ImperativeStatement]]
>       decls' = case decls of
>         [] -> [[newbind, newdecl]]
>         (x:xs) -> ([newbind, newdecl] ++ x) : xs
>       newName = mkId noPosition (mkFString mkStr)
>   put $ state { issAssertSubNum = s + 1, issAssertDecls = decls' }
>   return $ cVar newName


> assertDef :: CExpr -> ISConvMonad CExpr
> assertDef e = do
>   state <- get
>   let f = issFile state
>       l = issLine state
>       s = issAssertSubNum state
>       n = issAssertNum state
>       mkStr = concat ["assertion_", f, "_", show l, "__", show n, "_", show s]
>       decls = issAssertDecls state
>       newdecl = ISDecl noPosition (Right newName) Nothing []
>       newequal = ISEqual noPosition (Right newName) e
>       decls' :: [[ImperativeStatement]]
>       decls' = case decls of
>         [] -> [[newequal, newdecl]]
>         (x:xs) -> ([newequal, newdecl] ++ x) : xs
>       newName = mkId noPosition (mkFString mkStr)
>   put $ state { issAssertSubNum = s + 1, issAssertDecls = decls' }
>   return $ CVar newName


> transAssertProp :: Bool -> SVA_CORE_PROP -> ISConvMonad CExpr
> transAssertProp isAlways p =
>  do
>    pushDecls
>    e <- transPROP p
>    ds <- popDecls
>    mod <- mkSubModule ds
>    if isAlways then
>       do
>         let n = getLongestPath p
>         let rep = CApply (cVar (mkQId noPosition (mkFString "List") (mkFString "replicateM")))
>                          [n, mod]
>         assertBind rep
>     else -- "initial assert":
>         assertBind mod

> transAssertBody :: Bool -> SVA_CORE_PROP -> ISConvMonad ([ImperativeStatement], CExpr)
> transAssertBody isAlways p = do
>   state <- get
>   case run (transAssertProp isAlways p) state of
>      (Right (res, s)) -> do
>         put s
>         return (reverse (concat (issAssertDecls s)), res)
>      Left e -> throwError e

The actual translation functions

> cnstList :: [CExpr] -> CExpr
> cnstList es = foldr f n es
>               where f e ls = CApply (cVar (mkQId noPosition (mkFString "List") (mkFString "Cons ")))
>                                     [e, ls]
>                     n = cVar (mkQId noPosition (mkFString "List") (mkFString "Nil"))

> transSEQ :: SVA_CORE_SEQ -> ISConvMonad CExpr
> transSEQ (SVA_CORE_SEQ_Expr e) | isOne e =
>    assertDef (CApply (mkAssertMod "mkSeqTrue") [])
> transSEQ (SVA_CORE_SEQ_Expr e) =
>    assertDef (CApply (mkAssertMod "mkSeqExpr") [e])
> transSEQ (SVA_CORE_SEQ_Asgn as) =
>    -- XXX Local variables are disabled
>    internalError "Local variables are not yet supported."
>    --as' <- checkImperativeStmts as
>    --action <- convImperativeStmtsToCExpr noPosition ISCAction False as
>    --assertDef (CApply (mkAssertMod "mkSeqAsgn") [action])
> transSEQ (SVA_CORE_SEQ_Concat s1 s2) =
>  do
>    e1 <- transSEQ s1
>    e2 <- transSEQ s2
>    assertDef (CApply (mkAssertMod "mkSeqConcat") [e1, e2])
> transSEQ (SVA_CORE_SEQ_Fuse s1 s2) =
>  do
>    e1 <- transSEQ s1
>    e2 <- transSEQ s2
>    assertDef (CApply (mkAssertMod "mkSeqFuse") [e1, e2])
> transSEQ (SVA_CORE_SEQ_Or s1 s2)  =
>  do
>    e1 <- transSEQ s1
>    e2 <- transSEQ s2
>    assertDef (CApply (mkAssertMod "mkSeqOr") [e1, e2])
> transSEQ (SVA_CORE_SEQ_Intersect s1 s2) =
>  do
>    e1 <- transSEQ s1
>    e2 <- transSEQ s2
>    assertDef (CApply (mkAssertMod "mkSeqIntersect") [e1, e2])
> transSEQ (SVA_CORE_SEQ_FirstMatch s) =
>  do
>    e <- transSEQ s
>    assertDef (CApply (mkAssertMod "mkSeqFirstMatch") [e])
> transSEQ (SVA_CORE_SEQ_Null s) =
>  do
>    e <- transSEQ s
>    assertDef (CApply (mkAssertMod "mkSeqNull") [e])
> transSEQ (SVA_CORE_SEQ_Unbound s) =
>  do
>    e <- transSEQ s
>    assertDef (CApply (mkAssertMod "mkSeqUnbound") [e])
> transSEQ (SVA_CORE_SEQ_Rep s (SVA_REP_Cons (SVA_Delay_Const c))) =
>  do
>    e <- transSEQ s
>    assertDef (CApply (mkAssertMod "mkSeqRepConst") [e, c])
> transSEQ (SVA_CORE_SEQ_Rep s (SVA_REP_Cons (SVA_Delay_Range low high))) =
>  do
>    e <- transSEQ s
>    assertDef (CApply (mkAssertMod "mkSeqRepRange") [e, low, high])
> transSEQ (SVA_CORE_SEQ_Rep _ d) =
>    internalError ("CVParserAssertion:transSEQ (Rep): " ++ (show d))
> transSEQ (SVA_CORE_SEQ_Delay (SVA_Delay_Unbound e) ss s1 s2) =
>  do
>    e1 <- transSEQ s1
>    e2 <- transSEQ s2
>    es <- mapM transSEQ ss
>    let les = cnstList es
>    assertDef (CApply (mkAssertMod "mkSeqDelayUnbound") [e, les, e1, e2])
> transSEQ (SVA_CORE_SEQ_Delay (SVA_Delay_Const e) ss s1 s2) =
>  do
>    e1 <- transSEQ s1
>    e2 <- transSEQ s2
>    es <- mapM transSEQ ss
>    let les = cnstList es
>    assertDef (CApply (mkAssertMod "mkSeqDelayConst") [e, les, e1, e2])
> transSEQ (SVA_CORE_SEQ_Delay (SVA_Delay_Range el eh) ss s1 s2) =
>  do
>    e1 <- transSEQ s1
>    e2 <- transSEQ s2
>    es <- mapM transSEQ ss
>    let les = cnstList es
>    assertDef (CApply (mkAssertMod "mkSeqDelayRange") [el, eh, les, e1, e2])


> transPROP :: SVA_CORE_PROP -> ISConvMonad CExpr
> transPROP (SVA_CORE_PROP_Seq s) =
>  do
>    e <- transSEQ s
>    assertBind (CApply (mkAssertMod "mkPropSeq") [e])
> transPROP (SVA_CORE_PROP_Not p) =
>  do
>    e <- transPROP p
>    assertBind (CApply (mkAssertMod "mkPropNot") [e])
> transPROP (SVA_CORE_PROP_Or p1 p2) =
>  do
>    e1 <- transPROP p1
>    e2 <- transPROP p2
>    assertBind (CApply (mkAssertMod "mkPropOr") [e1, e2])
> transPROP (SVA_CORE_PROP_And p1 p2) =
>  do
>    e1 <- transPROP p1
>    e2 <- transPROP p2
>    assertBind (CApply (mkAssertMod "mkPropAnd") [e1, e2])
> transPROP (SVA_CORE_PROP_Implies s p) =
>  do
>    e1 <- transSEQ s
>    pushDecls
>    e2 <- transPROP p
>    ds <- popDecls
>    mod <- mkSubModule ds
>    let n = getLongestPath p
>    let rep = CApply (cVar (mkQId noPosition (mkFString "List") (mkFString "replicateM")))
>                     [n, mod]
>    lst <- assertBind rep
>    assertBind (CApply (mkAssertMod "mkPropImplies") [e1, lst])

> mkAssertMod :: String -> CExpr
> mkAssertMod s = cVar s'
>   where
>     s' = mkQId noPosition (mkFString "SVA") (mkFString s)

Functions to get the longest paths of sequences. These are used to determine
how many copies of props are needed for PropImplies and AssertAlways

Note: This works because using an unbound sequence in a prop is like
calling first_match on it according to the LRM

> maxExpr :: CExpr -> CExpr -> CExpr
> maxExpr e1 e2 = CApply (cVar (mkQId noPosition (mkFString "Prelude") (mkFString "max")))
>                        [e1, e2]

> addExpr :: CExpr -> CExpr -> CExpr
> addExpr e1 e2 = CApply (cVar idPlus)
>                        [e1, e2]

> addExpr3 :: CExpr -> CExpr -> CExpr -> CExpr
> addExpr3 e1 e2 e3 = CApply (cVar idPlus)
>                        [e1, e2, e3]

> getLongestPath :: SVA_CORE_PROP -> CExpr
> getLongestPath (SVA_CORE_PROP_Seq s) = getLongestPathSeq s
> getLongestPath (SVA_CORE_PROP_Not p) = getLongestPath p
> getLongestPath (SVA_CORE_PROP_Or p1 p2) = maxExpr l1 l2
>  where
>    l1 = getLongestPath p1
>    l2 = getLongestPath p2
> getLongestPath (SVA_CORE_PROP_And p1 p2) = maxExpr l1 l2
>  where
>    l1 = getLongestPath p1
>    l2 = getLongestPath p2
> getLongestPath (SVA_CORE_PROP_Implies s p) = getLongestPathSeq s -- It handles p by itself

> getLongestPathSeq :: SVA_CORE_SEQ -> CExpr
> getLongestPathSeq (SVA_CORE_SEQ_Expr e) = one
> getLongestPathSeq (SVA_CORE_SEQ_Asgn as) = one
> getLongestPathSeq (SVA_CORE_SEQ_Concat s1 s2) = addExpr l1 l2
>  where
>    l1 = getLongestPathSeq s1
>    l2 = getLongestPathSeq s2
> getLongestPathSeq (SVA_CORE_SEQ_Fuse s1 s2) = addExpr3 l1 l2 minus1
>  where
>    l1 = getLongestPathSeq s1
>    l2 = getLongestPathSeq s2
> getLongestPathSeq (SVA_CORE_SEQ_Or s1 s2) = maxExpr l1 l2
>  where
>    l1 = getLongestPathSeq s1
>    l2 = getLongestPathSeq s2
> getLongestPathSeq (SVA_CORE_SEQ_Intersect s1 s2) = maxExpr l1 l2 -- safe to use <?
>  where
>    l1 = getLongestPathSeq s1
>    l2 = getLongestPathSeq s2
> getLongestPathSeq (SVA_CORE_SEQ_FirstMatch s) = getLongestPathSeq s
> getLongestPathSeq (SVA_CORE_SEQ_Null s) = zero
> getLongestPathSeq (SVA_CORE_SEQ_Unbound s) = getLongestPathSeq s
> getLongestPathSeq (SVA_CORE_SEQ_Delay (SVA_Delay_Const r) _ _ _)  = r
> getLongestPathSeq (SVA_CORE_SEQ_Delay (SVA_Delay_Unbound lo) _ _ _)  = lo
> getLongestPathSeq (SVA_CORE_SEQ_Delay (SVA_Delay_Range lo hi) _ _ _)  = hi
> getLongestPathSeq (SVA_CORE_SEQ_Rep _ (SVA_REP_Cons (SVA_Delay_Const r)))  = r
> getLongestPathSeq (SVA_CORE_SEQ_Rep _ (SVA_REP_Cons (SVA_Delay_Unbound lo)))  = lo
> getLongestPathSeq (SVA_CORE_SEQ_Rep _ (SVA_REP_Cons (SVA_Delay_Range lo hi)))  = hi
> getLongestPathSeq (SVA_CORE_SEQ_Rep _ r) =
>     internalError("CVParserAssertion:getLongestPathSeq (rep): " ++ (show r))


HELPER Functions

> isSequence :: Id -> ISConvMonad Bool
> isSequence var = do
>   state <- get
>   return $ isJust $ findSeq var $ issSequences state

> isProperty :: Id -> ISConvMonad Bool
> isProperty var = do
>   state <- get
>   return $ isJust $ findProp var $ issProperties state

Find a declared sequence

> findSeq :: Id -> [SequenceInfo] -> Maybe ImperativeStatement
> findSeq nm issSeqs = fd issSeqs
>  where
>   fd [] = Nothing
>   fd (s:ss) = case M.lookup nm s of
>     Just res -> Just res
>     Nothing -> fd ss

> findSeqM :: Id -> ISConvMonad (Maybe ImperativeStatement)
> findSeqM nm = do
>   state <- get
>   let fd [] = Nothing
>       fd (s:ss) = case M.lookup nm s of
>         Just res -> Just res
>         Nothing -> fd ss
>   return $ fd (issSequences state)

Add a sequence to the environment

> addSequence :: Id -> ImperativeStatement -> ISConvMonad ()
> addSequence nm body@(ISSequence pos _) = do
>  state <- get
>  let seqs = issSequences state
>      (s, ss) = unconsOrErr "CVParserAssertion.addSequence: missing frame" seqs
>  case findSeq nm seqs of
>    Nothing -> put $ state {issSequences = (M.insert nm body s):ss}
>    Just (ISSequence prevPos decl) ->
>        throwError [(pos, EMultipleDecl (pvpString nm) prevPos)]
>    _ -> internalError ("CVParserImperative:addProperty: " ++ (pvpString body))
> addSequence _ body = internalError ("CVParserImperative:addSequence:2: " ++ (pvpString body))

Find a declared property

> findProp :: Id -> [PropertyInfo] -> Maybe ImperativeStatement
> findProp nm issPrs = fd issPrs
>  where
>   fd [] = Nothing
>   fd (p:ps) = case M.lookup nm p of
>     Just res -> Just res
>     Nothing -> fd ps

> findPropM :: Id -> ISConvMonad (Maybe ImperativeStatement)
> findPropM nm = do
>   state <- get
>   let fd [] = Nothing
>       fd (s:ss) = case M.lookup nm s of
>          Just res -> Just res
>          Nothing -> fd ss
>   return $ fd $ issProperties state

Add a property to the environment

> addProperty :: Id -> ImperativeStatement -> ISConvMonad ()
> addProperty nm body@(ISProperty pos _) = do
>  state <- get
>  let props = issProperties state
>      (p, ps) = unconsOrErr "CVParserAssertion.addProperty: missing frame" props
>  case findProp nm props of
>    Nothing -> put $ state {issProperties = (M.insert nm body p):ps}
>    Just (ISProperty prevPos _) -> throwError $ [(pos, EMultipleDecl (pvpString nm) prevPos)]
>    _ -> internalError ("CVParserImperative:addProperty: " ++ (pvpString body))
> addProperty _ body = internalError ("CVParserImperative:addProperty:2: " ++ (pvpString body))
