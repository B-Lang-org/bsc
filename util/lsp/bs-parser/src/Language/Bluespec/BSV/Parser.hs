{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

-- | Parser for Bluespec SystemVerilog (BSV).
--
-- BSV uses explicit @end*@ keywords instead of layout-based grouping.
-- This parser produces the same 'Package' AST as the Classic parser.
module Language.Bluespec.BSV.Parser
  ( parseBSVPackage
  , parseBSVPackageRecovering
  ) where

import Control.Monad (guard, void, when)
import Data.List (foldl')
import Data.Maybe (catMaybes, fromMaybe, mapMaybe)
import qualified Data.Set as Set
import Data.List.NonEmpty (NonEmpty(..), toList)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Void (Void)
import Text.Megaparsec hiding (Token, token, tokens, ParseError)
import qualified Text.Megaparsec as MP

import qualified Language.Bluespec.Lexer as Lex
import Language.Bluespec.Fixity (resolveOps, bluespecFixities)
import Language.Bluespec.Position
import Language.Bluespec.Syntax

--------------------------------------------------------------------------------
-- Parser type
--------------------------------------------------------------------------------

type Parser = Parsec Void Lex.TokenStream
type ParseError = ParseErrorBundle Lex.TokenStream Void

--------------------------------------------------------------------------------
-- Entry point
--------------------------------------------------------------------------------

parseBSVPackage :: Text -> Text -> Either ParseError Package
parseBSVPackage file input = do
  ts <- first' (const bundleErr) $ Lex.tokenize file input
  MP.parse pPackage (T.unpack file) (Lex.TokenStream ts)
  where
    bundleErr = ParseErrorBundle
      { bundleErrors = pure $ FancyError 0 (Set.singleton $ ErrorFail "Lexer error")
      , bundlePosState = PosState
          { pstateInput = Lex.TokenStream []
          , pstateOffset = 0
          , pstateSourcePos = initialPos (T.unpack file)
          , pstateTabWidth = defaultTabWidth
          , pstateLinePrefix = ""
          }
      }
    first' f (Left e) = Left (f e)
    first' _ (Right a) = Right a

-- | Parse a BSV package with error recovery.
--
-- Unlike 'parseBSVPackage', this always returns a (possibly partial) 'Package'
-- even when there are parse errors. The second element is @Just bundle@ if any
-- errors occurred, @Nothing@ on clean success. Intended for the LSP.
parseBSVPackageRecovering
  :: Text
  -> Text
  -> (Package, Maybe ParseError)
parseBSVPackageRecovering file input =
  case Lex.tokenize file input of
    Left _ ->
      ( emptyPkg file
      , Just $ ParseErrorBundle
          { bundleErrors  = pure $ FancyError 0 (Set.singleton $ ErrorFail "Lexer error")
          , bundlePosState = PosState
              { pstateInput      = Lex.TokenStream []
              , pstateOffset     = 0
              , pstateSourcePos  = initialPos (T.unpack file)
              , pstateTabWidth   = defaultTabWidth
              , pstateLinePrefix = ""
              }
          }
      )
    Right ts ->
      let stream  = Lex.TokenStream ts
          initSt  = MP.State
            { MP.stateInput       = stream
            , MP.stateOffset      = 0
            , MP.statePosState    = PosState
                { pstateInput      = stream
                , pstateOffset     = 0
                , pstateSourcePos  = initialPos (T.unpack file)
                , pstateTabWidth   = defaultTabWidth
                , pstateLinePrefix = ""
                }
            , MP.stateParseErrors = []
            }
          initPosState = PosState
            { pstateInput      = stream
            , pstateOffset     = 0
            , pstateSourcePos  = initialPos (T.unpack file)
            , pstateTabWidth   = defaultTabWidth
            , pstateLinePrefix = ""
            }
          (finalSt, result) = MP.runParser' pPackageRecovering initSt
          errs = MP.stateParseErrors finalSt
      in case result of
           Left bundle ->
             -- Hard failure: return the bundle (may include recovered errors too)
             let allErrs = toList (bundleErrors bundle) ++ errs
             in case allErrs of
                  e:es -> (emptyPkg file, Just bundle { bundleErrors = e :| es })
                  []   -> (emptyPkg file, Just bundle)
           Right pkg ->
             -- Success: check for recovered errors
             case errs of
               []   -> (pkg, Nothing)
               e:es -> (pkg, Just $ ParseErrorBundle
                 { bundleErrors  = e :| es
                 , bundlePosState = initPosState
                 })

emptyPkg :: Text -> Package
emptyPkg file = Package noSpan
  (Located noSpan (ModuleId (T.takeWhile (/= '.') (T.pack (reverse (takeWhile (/= '/') (reverse (T.unpack file))))))))
  Nothing [] [] []

listToNE :: [a] -> Maybe (NonEmpty a)
listToNE []     = Nothing
listToNE (x:xs) = Just (x :| xs)

--------------------------------------------------------------------------------
-- Token primitives
--------------------------------------------------------------------------------

tok :: (Lex.TokenKind -> Maybe a) -> Parser (Located a)
tok f = MP.token match Set.empty
  where
    match (Lex.Token sp kind) = case f kind of
      Just v  -> Just (Located sp v)
      Nothing -> Nothing

keyword :: Lex.Keyword -> Parser SrcSpan
keyword kw = locSpan <$> tok (\case { Lex.TokKeyword k | k == kw -> Just (); _ -> Nothing })

punct :: Lex.Punctuation -> Parser SrcSpan
punct p = locSpan <$> tok (\case { Lex.TokPunct q | q == p -> Just (); _ -> Nothing })

semi :: Parser SrcSpan
semi = punct Lex.PunctSemi

comma :: Parser ()
comma = void $ punct Lex.PunctComma

colon :: Parser SrcSpan
colon = punct Lex.PunctColon

dcolon :: Parser SrcSpan
dcolon = punct Lex.PunctDColon

hash :: Parser ()
hash = void $ punct Lex.PunctHash

lparen :: Parser SrcSpan
lparen = punct Lex.PunctLParen

rparen :: Parser SrcSpan
rparen = punct Lex.PunctRParen

lbrace :: Parser SrcSpan
lbrace = punct Lex.PunctLBrace

rbrace :: Parser SrcSpan
rbrace = punct Lex.PunctRBrace

lbracket :: Parser SrcSpan
lbracket = punct Lex.PunctLBracket

rbracket :: Parser SrcSpan
rbracket = punct Lex.PunctRBracket

equals :: Parser ()
equals = void $ punct Lex.PunctEqual

larrow :: Parser ()
larrow = void $ punct Lex.PunctLArrow

varId :: Parser (Located Ident)
varId = tok $ \case { Lex.TokVarId t -> Just (VarId t); _ -> Nothing }

conId :: Parser (Located Ident)
conId = tok $ \case { Lex.TokConId t -> Just (ConId t); _ -> Nothing }

anyId :: Parser (Located Ident)
anyId = varId <|> conId

qualId :: Parser (Located QualIdent)
qualId = tok $ \case
  Lex.TokVarId t    -> Just $ QualIdent Nothing (VarId t)
  Lex.TokConId t    -> Just $ QualIdent Nothing (ConId t)
  Lex.TokQVarId m t -> Just $ QualIdent (Just (ModuleId m)) (VarId t)
  Lex.TokQConId m t -> Just $ QualIdent (Just (ModuleId m)) (ConId t)
  _ -> Nothing

opSym :: Parser (Located Text)
opSym = tok $ \case
  Lex.TokVarSym t -> Just t
  Lex.TokConSym t -> Just t
  _ -> Nothing

namedOp :: Text -> Parser ()
namedOp name = void $ tok $ \case
  Lex.TokVarSym t | t == name -> Just ()
  Lex.TokConSym t | t == name -> Just ()
  _ -> Nothing

intLit :: Parser (Located Literal)
intLit = tok $ \case
  Lex.TokInteger n mfmt -> Just $ LitInt n (fmap (\(w,f) -> (w, cvtFmt f)) mfmt)
  _ -> Nothing
  where
    cvtFmt Lex.IntDec' = IntDec
    cvtFmt Lex.IntHex' = IntHex
    cvtFmt Lex.IntBin' = IntBin
    cvtFmt Lex.IntOct' = IntOct

strLit :: Parser (Located Literal)
strLit = tok $ \case { Lex.TokString t -> Just (LitString t); _ -> Nothing }

anyTok :: Parser (Located ())
anyTok = tok (\_ -> Just ())

-- | A dummy span for synthesized nodes.
dummySpan :: SrcSpan
dummySpan = SrcSpan (T.pack "") (Pos 1 1) (Pos 1 1)

-- | Try to get the span of the next token without consuming it.
peekSpan :: Parser SrcSpan
peekSpan = option dummySpan $ lookAhead (locSpan <$> anyTok)

spanTo :: SrcSpan -> SrcSpan -> SrcSpan
spanTo (SrcSpan f s _) (SrcSpan _ _ e) = SrcSpan f s e

-- | Parse `(* attrName [= expr], ... *)` attribute instances, return list of names.
attrInsts :: Parser ()
attrInsts = void $ many $ do
  -- (* ... *) — lexed as TokPunct PunctLParen + TokVarSym "*" ... TokVarSym "*" + TokPunct PunctRParen
  void lparen
  namedOp "*"
  void $ manyTill anyTok (try (namedOp "*" *> void rparen))

-- | Like 'attrInsts' but requires at least one attribute (safe to use in loops).
someAttrInsts :: Parser ()
someAttrInsts = void $ some $ do
  void lparen
  namedOp "*"
  void $ manyTill anyTok (try (namedOp "*" *> void rparen))

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

pType :: Parser LType
pType = pTypePrimary

pTypePrimary :: Parser LType
pTypePrimary = choice
  [ try pTypeHashApp    -- T#(a,b)
  , try pTypeParens     -- (t) or (t1,t2)
  , pTypeAtom
  ]

-- | Parse T#(a, b) parameterized type.
pTypeHashApp :: Parser LType
pTypeHashApp = do
  name <- qualId
  hash
  lparen
  args <- pType `sepBy1` comma
  rparen
  let base = Located (locSpan name) (TCon name)
  pure $ foldl' (\a b -> Located (spanTo (locSpan a) (locSpan b)) (TApp a b)) base args

pTypeParens :: Parser LType
pTypeParens = do
  sp0 <- lparen
  t   <- pType
  ts  <- many (try $ comma *> pType)
  sp1 <- rparen
  pure $ case ts of
    [] -> Located (spanTo sp0 sp1) (TApp (Located sp0 (TCon (Located sp0 (QualIdent Nothing (ConId "Tuple1"))))) t)
    _  -> Located (spanTo sp0 sp1) (TTuple (t:ts))

pTypeAtom :: Parser LType
pTypeAtom = choice
  [ -- void -> Void
    do sp <- keyword Lex.KwVoid
       pure $ Located sp (TCon (Located sp (QualIdent Nothing (ConId "Void"))))
  , -- numeric type n
    try $ do
      sp1 <- keyword Lex.KwNumeric
      sp2 <- keyword Lex.KwType
      nm  <- anyId
      pure $ Located (spanTo sp1 (locSpan nm))
               (TVar (Located (locSpan nm) (TyVar (locVal nm) (Just KNum))))
  , -- type n (in formals)
    try $ do
      sp1 <- keyword Lex.KwType
      nm  <- anyId
      pure $ Located (spanTo sp1 (locSpan nm))
               (TVar (Located (locSpan nm) (TyVar (locVal nm) Nothing)))
  , -- Integer literal in type position
    do lit <- intLit
       case locVal lit of
         LitInt n _ -> pure $ Located (locSpan lit) (TNum n)
         _          -> fail "not a numeric type literal"
  , -- type identifier or type variable
    do qid <- qualId
       pure $ Located (locSpan qid) $ case locVal qid of
         QualIdent (Just _) _  -> TCon qid
         QualIdent Nothing  id -> case id of
           ConId _ -> TCon qid
           VarId t -> TVar (Located (locSpan qid) (TyVar (VarId t) Nothing))
  , -- BSV keywords used as type variable names (e.g. `data` in `method data read()`)
    do lk <- tok $ \case
                 Lex.TokKeyword k ->
                   let t = Lex.keywordText k
                   in case T.uncons t of
                        Just (c, _) | c >= 'a' && c <= 'z' -> Just (VarId t)
                        _                                    -> Nothing
                 _ -> Nothing
       pure $ Located (locSpan lk) (TVar (Located (locSpan lk) (TyVar (locVal lk) Nothing)))
  ]

pQualType :: Parser (Located QualType)
pQualType = do
  t <- pType
  pure $ Located (locSpan t) (QualType [] t)

pProvisos :: Parser [Located Pred]
pProvisos = do
  void $ keyword Lex.KwProvisos
  lparen
  ps <- pPred `sepBy` comma
  rparen
  pure ps

pPred :: Parser (Located Pred)
pPred = do
  cls <- qualId
  hash
  lparen
  args <- pType `sepBy1` comma
  rparen
  pure $ Located (locSpan cls) (Pred cls args)

pTypeFormals :: Parser [Located TyVar]
pTypeFormals = do
  hash
  lparen
  tvs <- pTypeFormal `sepBy` comma
  rparen
  pure tvs

pTypeFormal :: Parser (Located TyVar)
pTypeFormal = do
  isNum <- option False (True <$ keyword Lex.KwNumeric)
  void $ keyword Lex.KwType
  -- Allow BSV keywords as type formal names (e.g. `type data`, `type input`)
  nm <- anyId <|> kwAsAnyId
  pure $ Located (locSpan nm) (TyVar (locVal nm) (if isNum then Just KNum else Nothing))
  where
    kwAsAnyId = tok $ \case
      Lex.TokKeyword k -> Just (VarId (Lex.keywordText k))
      _ -> Nothing

pTypeDefType :: Parser (Located Ident, [Located TyVar])
pTypeDefType = do
  name <- conId
  tvs  <- option [] (try pTypeFormals)
  pure (name, tvs)

pDeriving :: Parser [Deriving]
pDeriving = do
  void $ keyword Lex.KwDeriving
  lparen
  ds <- pDerivCls `sepBy` comma
  rparen
  pure ds
  where
    pDerivCls = do
      qid <- qualId
      pure (Deriving qid)

--------------------------------------------------------------------------------
-- Patterns
--------------------------------------------------------------------------------

pPattern :: Parser LPattern
pPattern = choice
  [ try $ do
      sp <- keyword Lex.KwTagged
      con <- conId
      mpat <- optional (try pPatternAtom)
      pure $ Located (spanTo sp (maybe (locSpan con) locSpan mpat))
               (PCon (Located (locSpan con) (QualIdent Nothing (locVal con)))
                     (maybe [] pure mpat))
  , try pPatternTuple
  , pPatternAtom
  ]

pPatternAtom :: Parser LPattern
pPatternAtom = choice
  [ do sp <- punct Lex.PunctUnderscore
       pure $ Located sp PWild
  -- '.fieldName' pattern — binds a local variable with the same name as the field
  , do sp0 <- punct Lex.PunctDot
       nm  <- varId
       pure $ Located (spanTo sp0 (locSpan nm)) (PVar nm)
  , do con <- conId
       pure $ Located (locSpan con) (PCon (Located (locSpan con) (QualIdent Nothing (locVal con))) [])
  , do name <- varId
       pure $ Located (locSpan name) (PVar name)
  , do lit <- intLit
       pure $ Located (locSpan lit) (PLit lit)
  , do lit <- strLit
       pure $ Located (locSpan lit) (PLit lit)
  -- Parenthesised pattern: (pat)
  , do sp0 <- lparen
       p   <- pPattern
       sp1 <- rparen
       pure $ Located (spanTo sp0 sp1) (locVal p)
  ]

pPatternTuple :: Parser LPattern
pPatternTuple = do
  sp0 <- lbrace
  ps  <- pPattern `sepBy` comma
  sp1 <- rbrace
  pure $ Located (spanTo sp0 sp1) (PTuple ps)

--------------------------------------------------------------------------------
-- Expressions
--------------------------------------------------------------------------------

pExpr :: Parser LExpr
pExpr = pCondExpr

pCondExpr :: Parser LExpr
pCondExpr = do
  e <- pOperatorExpr
  -- BSV allows `expr matches pat` as a condition; consume the pattern but keep the expr.
  void $ optional $ try $ keyword Lex.KwMatches *> void pPattern
  mc <- optional $ do
    namedOp "?"
    t <- pExpr
    void colon
    f <- pExpr
    pure (t, f)
  case mc of
    Nothing    -> pure e
    Just (t,f) -> pure $ Located (spanTo (locSpan e) (locSpan f)) (EIf e t f)

pOperatorExpr :: Parser LExpr
pOperatorExpr = do
  e1 <- pUnaryExpr
  es <- many $ do
    op <- opSymNotTernary
    e2 <- pUnaryExpr
    pure (Located (locSpan op) (OpSym (locVal op)), e2)
  pure $ resolveOps bluespecFixities e1 es
  where
    -- Exclude "?" from binary operators so pCondExpr can handle it as ternary.
    opSymNotTernary = tok $ \case
      Lex.TokVarSym t | t /= "?" -> Just t
      Lex.TokConSym t -> Just t
      _ -> Nothing

pUnaryExpr :: Parser LExpr
pUnaryExpr = choice
  [ pfx "-" ENeg
  , pfx1 "!" , pfx1 "~" , pfx1 "&" , pfx1 "|" , pfx1 "^"
  , pPostfixExpr
  ]
  where
    pfx nm f = do
      sp <- peekSpan
      namedOp nm
      e <- pUnaryExpr
      pure $ Located (spanTo sp (locSpan e)) (f e)
    pfx1 nm = do
      sp <- peekSpan
      namedOp nm
      e <- pUnaryExpr
      let qid = Located sp (QualIdent Nothing (VarId nm))
      pure $ Located (spanTo sp (locSpan e)) (EApp (Located sp (EVar qid)) e)

pPostfixExpr :: Parser LExpr
pPostfixExpr = do
  base <- pAtomicExpr
  suffs <- many (try pSuffix)
  pure $ foldl' apply base suffs
  where
    apply acc suf = case suf of
      SuffixArgs [] -> acc  -- empty call, ignore
      SuffixArgs args ->
        foldl' (\f a -> Located (spanTo (locSpan f) (locSpan a)) (EApp f a)) acc args
      SuffixField fld ->
        Located (spanTo (locSpan acc) (locSpan fld)) (EFieldAccess acc fld)
      SuffixMethodArgs fld args ->
        let fa = Located (spanTo (locSpan acc) (locSpan fld)) (EFieldAccess acc fld)
        in foldl' (\f a -> Located (spanTo (locSpan f) (locSpan a)) (EApp f a)) fa args
      SuffixBitSel hi lo sp ->
        Located (spanTo (locSpan acc) sp) (EBitSelect acc hi lo)

data Suffix
  = SuffixArgs [LExpr]
  | SuffixField (Located Ident)
  | SuffixMethodArgs (Located Ident) [LExpr]
  | SuffixBitSel LExpr LExpr SrcSpan  -- hi lo sp

pSuffix :: Parser Suffix
pSuffix = choice
  [ try $ do
      void $ punct Lex.PunctDot
      fld <- varId <|> conId
      mArgs <- optional $ do
        lparen
        args <- pExpr `sepBy` comma
        rparen
        pure args
      pure $ case mArgs of
        Nothing   -> SuffixField fld
        Just args -> SuffixMethodArgs fld args
  , try $ do
      void lbracket
      hi <- pExpr
      lo <- option hi (void colon *> pExpr)
      sp <- rbracket
      pure (SuffixBitSel hi lo sp)
  , do
      void lparen
      args <- pExpr `sepBy` comma
      rparen
      pure (SuffixArgs args)
  ]

pAtomicExpr :: Parser LExpr
pAtomicExpr = choice
  [ do lit <- intLit; pure $ Located (locSpan lit) (ELit lit)
  , do lit <- strLit; pure $ Located (locSpan lit) (ELit lit)
  , do sp <- namedOp "?"; pure $ Located dummySpan EDontCare
  , try pParenExpr
  , try pBitConcat
  , try pTaggedExpr
  , try pValueOf
  , try pBeginEnd
  , try pActionBlock
  , try pActionValueBlock
  , try pInterfaceExpr
  , try pRulesExpr
  , try pSeqFsm
  , try pParFsm
  , try pTypeAssertion
  , try pStructExpr
  , do qid <- qualId
       pure $ Located (locSpan qid) $
         case locVal qid of
           QualIdent _ (ConId _) -> ECon qid
           _                     -> EVar qid
  ]

pParenExpr :: Parser LExpr
pParenExpr = do
  sp0 <- lparen
  me  <- optional pExpr
  case me of
    Nothing -> do { sp1 <- rparen; pure $ Located (spanTo sp0 sp1) (ETuple []) }
    Just e  -> do
      es  <- many (try $ comma *> pExpr)
      sp1 <- rparen
      pure $ case es of
        [] -> Located (spanTo sp0 sp1) (EParens e)
        _  -> Located (spanTo sp0 sp1) (ETuple (e:es))

-- BSV { e1, e2 } is bit-concatenation, not record update.
-- We represent it as a special EPrim to distinguish.
pBitConcat :: Parser LExpr
pBitConcat = do
  sp0 <- lbrace
  e1  <- pExpr
  _   <- comma  -- must have at least one comma to distinguish from block
  es  <- pExpr `sepBy1` comma
  sp1 <- rbrace
  pure $ Located (spanTo sp0 sp1)
    (EPrim "{}" (e1:es))

pTaggedExpr :: Parser LExpr
pTaggedExpr = do
  sp0 <- keyword Lex.KwTagged
  con <- conId
  body <- choice
    [ do void lbrace
         binds <- memberBind `sepBy` comma
         void rbrace
         pure binds
    , do me <- optional (try pAtomicExpr)
         pure $ case me of
           Nothing -> []
           Just e  -> [(Located (locSpan e) (VarId "_val"), e)]
    ]
  pure $ Located (spanTo sp0 (locSpan con)) (ETagged con body)
  where
    memberBind = do
      nm <- varId
      void colon
      e  <- pExpr
      pure (nm, e)

pValueOf :: Parser LExpr
pValueOf = do
  sp0 <- keyword Lex.KwValueOf
  void lparen
  t <- pType
  sp1 <- rparen
  pure $ Located (spanTo sp0 sp1) (EValueOf t)

pBeginEnd :: Parser LExpr
pBeginEnd = do
  sp0 <- keyword Lex.KwBegin
  void $ optional (void colon *> void anyId)
  stmts <- many (try pStmt)
  sp1   <- keyword Lex.KwEnd
  void $ optional (void colon *> void anyId)
  pure $ Located (spanTo sp0 sp1) (EBeginEnd stmts Nothing)

pActionBlock :: Parser LExpr
pActionBlock = do
  sp0   <- keyword Lex.KwAction
  void $ optional (void colon *> void anyId)
  stmts <- many (try pActionStmt)
  sp1   <- keyword Lex.KwEndAction
  void $ optional (void colon *> void anyId)
  pure $ Located (spanTo sp0 sp1) (EDo stmts)

pActionValueBlock :: Parser LExpr
pActionValueBlock = do
  sp0   <- keyword Lex.KwActionValue
  void $ optional (void colon *> void anyId)
  stmts <- many (try pActionStmt)
  sp1   <- keyword Lex.KwEndActionValue
  void $ optional (void colon *> void anyId)
  pure $ Located (spanTo sp0 sp1) (EDo stmts)

pInterfaceExpr :: Parser LExpr
pInterfaceExpr = do
  sp0  <- keyword Lex.KwInterface
  mNm  <- optional (try conId)
  void $ optional semi
  meths <- many (try pInterfaceStmt)
  sp1  <- keyword Lex.KwEndInterface
  void $ optional (void colon *> void anyId)
  let qnm = fmap (\n -> Located (locSpan n) (QualIdent Nothing (locVal n))) mNm
  pure $ Located (spanTo sp0 sp1) (EInterface qnm meths)

pRulesExpr :: Parser LExpr
pRulesExpr = do
  sp0  <- keyword Lex.KwRules
  void $ optional (void colon *> void anyId)
  rules <- many (try pRule)
  sp1  <- keyword Lex.KwEndRules
  void $ optional (void colon *> void anyId)
  pure $ Located (spanTo sp0 sp1) (ERules rules)

pSeqFsm :: Parser LExpr
pSeqFsm = do
  sp0 <- tok (\case { Lex.TokVarId "seq" -> Just (); _ -> Nothing }) >>= pure . locSpan
  stmts <- many (try pExprSemi)
  sp1   <- keyword Lex.KwEndSeq
  void $ optional (void colon *> void anyId)
  pure $ Located (spanTo sp0 sp1) (EDo stmts)
  where
    pExprSemi = do
      sp <- peekSpan
      e  <- pExpr
      void semi
      pure $ Located (spanTo sp (locSpan e)) (StmtExpr e)

pParFsm :: Parser LExpr
pParFsm = do
  sp0 <- tok (\case { Lex.TokVarId "par" -> Just (); _ -> Nothing }) >>= pure . locSpan
  stmts <- many (try pExprSemi)
  sp1   <- keyword Lex.KwEndPar
  void $ optional (void colon *> void anyId)
  pure $ Located (spanTo sp0 sp1) (EDo stmts)
  where
    pExprSemi = do
      sp <- peekSpan
      e  <- pExpr
      void semi
      pure $ Located (spanTo sp (locSpan e)) (StmtExpr e)

pTypeAssertion :: Parser LExpr
pTypeAssertion = do
  t  <- pTypePrimary
  void $ tok (\case { Lex.TokVarSym "'" -> Just (); _ -> Nothing })
  e  <- choice
    [ pBitConcat
    , do sp0 <- lparen; e <- pExpr; sp1 <- rparen
         pure $ Located (spanTo sp0 sp1) (EParens e)
    ]
  pure $ Located (spanTo (locSpan t) (locSpan e))
    (ETypeSig e (Located (locSpan t) (QualType [] t)))

pStructExpr :: Parser LExpr
pStructExpr = do
  con <- conId
  void lbrace
  binds <- memberBind `sepBy` comma
  void rbrace
  pure $ Located (locSpan con) $
    ERecord (Located (locSpan con) (QualIdent Nothing (locVal con)))
      (map (\(n,v) -> FieldBind (locSpan n) n v) binds)
  where
    memberBind = do
      nm <- varId
      void colon
      e  <- pExpr
      pure (fmap VarId (fmap identText nm), e)

--------------------------------------------------------------------------------
-- Statements
--------------------------------------------------------------------------------

pStmt :: Parser LStmt
pStmt = choice
  [ try pForStmt
  , try pWhileStmt
  , try pRepeatStmt
  , try pIfStmt
  , try pCaseStmt
  , try (Located dummySpan StmtContinue <$ (void (keyword Lex.KwContinue) <* void semi))
  , try (Located dummySpan StmtBreak    <$ (void (keyword Lex.KwBreak)    <* void semi))
  , try $ do
      sp0 <- keyword Lex.KwReturn
      e <- pExpr
      void semi
      pure $ Located (spanTo sp0 (locSpan e)) (StmtReturn e)
  , try pLetStmt
  , try pMatchStmt
  , try pVarDeclStmt
  , try pRegWriteStmt  -- must come before pExprStmt
  , try pAssignStmt   -- lhs = rhs; (variable/array reassignment)
  , try pBindStmt
  -- Skip balanced `ifdef...`endif blocks (including conditional else-if branches)
  -- and simple directives that appear inside statement blocks.
  , Located dummySpan (StmtExpr (Located dummySpan EDontCare)) <$ try skipIfdefBlock
  , Located dummySpan (StmtExpr (Located dummySpan EDontCare)) <$ try skipPreprocDirective
  -- Handle "orphan" else/else-if clauses that appear at statement level after
  -- `ifdef blocks are consumed.  Treat them as no-op statements.
  , try pOrphanElse
  , pExprStmt
  ]

pActionStmt :: Parser LStmt
pActionStmt = pStmt

pForStmt :: Parser LStmt
pForStmt = do
  sp0  <- keyword Lex.KwFor
  void lparen
  init' <- pForInit
  void semi
  cond  <- pExpr
  void semi
  incr  <- pForIncr
  void rparen
  body  <- pStmtBlock
  let sp1 = if null body then sp0 else locSpan (last body)
  pure $ Located (spanTo sp0 sp1) (StmtFor init' cond incr body)

pForInit :: Parser LStmt
pForInit = choice
  [ try $ do
      sp0 <- peekSpan
      t   <- pTypePrimary
      nm  <- varId
      void equals
      e   <- pExpr
      pure $ Located (spanTo sp0 (locSpan e))
               (StmtBind (Located (locSpan nm) (PVar nm))
                         (Just (Located (locSpan t) (QualType [] t)))
                         e)
  , do sp0 <- peekSpan
       lhs <- pPostfixExpr
       void equals
       rhs <- pExpr
       pure $ Located (spanTo sp0 (locSpan rhs)) (StmtExpr (Located (spanTo sp0 (locSpan rhs)) (EInfix lhs (Located sp0 (OpSym "=")) rhs)))
  ]

pForIncr :: Parser LStmt
pForIncr = do
  sp0 <- peekSpan
  lhs <- pPostfixExpr
  void equals
  rhs <- pExpr
  pure $ Located (spanTo sp0 (locSpan rhs))
    (StmtExpr (Located (spanTo sp0 (locSpan rhs)) (EInfix lhs (Located sp0 (OpSym "=")) rhs)))

pWhileStmt :: Parser LStmt
pWhileStmt = do
  sp0  <- keyword Lex.KwWhile
  void lparen
  cond <- pExpr
  void rparen
  body <- pStmtBlock
  let sp1 = if null body then sp0 else locSpan (last body)
  pure $ Located (spanTo sp0 sp1) (StmtWhile cond body)

pRepeatStmt :: Parser LStmt
pRepeatStmt = do
  sp0 <- keyword Lex.KwRepeat
  void lparen
  n   <- pExpr
  void rparen
  body <- pStmtBlock
  let sp1 = if null body then sp0 else locSpan (last body)
  pure $ Located (spanTo sp0 sp1) (StmtRepeat n body)

pStmtBlock :: Parser [LStmt]
pStmtBlock = choice
  [ do sp0 <- keyword Lex.KwBegin
       void $ optional (void colon *> void anyId)
       ss <- many (try pStmt)
       void $ keyword Lex.KwEnd
       void $ optional (void colon *> void anyId)
       pure ss
  , do s <- pStmt; pure [s]
  ]

pIfStmt :: Parser LStmt
pIfStmt = do
  sp0   <- keyword Lex.KwIf
  void lparen
  cond  <- pCondPredicate
  void rparen
  then_ <- pStmtBlock
  else_ <- option [] (keyword Lex.KwElse *> pStmtBlock)
  let sp1 = case else_ of { [] -> if null then_ then sp0 else locSpan (last then_); xs -> locSpan (last xs) }
      thenE = stmtsToExpr sp0 then_
      elseE = stmtsToExpr sp0 else_
  pure $ Located (spanTo sp0 sp1)
    (StmtExpr (Located (spanTo sp0 sp1) (EIf cond thenE elseE)))

pCaseStmt :: Parser LStmt
pCaseStmt = do
  sp0    <- keyword Lex.KwCase
  void lparen
  scrut  <- pExpr
  void rparen
  void $ optional (keyword Lex.KwMatches)
  alts   <- many (try pCaseItem)
  mDef   <- optional pDefaultItem
  sp1    <- keyword Lex.KwEndCase
  let allAlts = alts ++ fromMaybe [] mDef
  pure $ Located (spanTo sp0 sp1)
    (StmtExpr (Located (spanTo sp0 sp1) (ECase scrut allAlts)))
  where
    pCaseItem = do
      sp0 <- peekSpan
      pat <- pPattern
      void colon
      body <- pStmtBlock
      pure $ Alt sp0 pat Nothing (stmtsToExpr sp0 body)
    pDefaultItem = do
      sp0 <- keyword Lex.KwDefault
      void $ optional colon
      body <- pStmtBlock
      pure [Alt sp0 (Located sp0 PWild) Nothing (stmtsToExpr sp0 body)]

pLetStmt :: Parser LStmt
pLetStmt = do
  sp0  <- keyword Lex.KwLet
  nm   <- varId
  e    <- choice [void equals *> pExpr, void larrow *> pExpr]
  void semi
  let item = LetBind (Binding (locSpan nm) (Located (locSpan nm) (PVar nm)) [] Nothing e)
  pure $ Located (spanTo sp0 (locSpan e)) (StmtLet [item])

-- | Parse 'match pattern = expression;' — BSV tuple/struct destructuring.
-- 'match' is not a keyword; it lexes as TokVarId "match".
pMatchStmt :: Parser LStmt
pMatchStmt = do
  sp0 <- peekSpan
  void $ tok $ \case { Lex.TokVarId "match" -> Just (); _ -> Nothing }
  pat <- pPattern
  void equals
  e   <- pExpr
  void semi
  pure $ Located (spanTo sp0 (locSpan e)) (StmtBind pat Nothing e)

pVarDeclStmt :: Parser LStmt
pVarDeclStmt = do
  sp0 <- peekSpan
  t   <- pTypePrimary
  nm  <- varId
  rest <- choice
    [ do void larrow; e <- pExpr; void semi
         pure $ Left e
    , do mE <- optional (void equals *> pExpr)
         void semi
         pure $ Right (fromMaybe (Located sp0 EDontCare) mE)
    ]
  case rest of
    Left e ->
      pure $ Located (spanTo sp0 (locSpan e))
        (StmtBind (Located (locSpan nm) (PVar nm))
                  (Just (Located (locSpan t) (QualType [] t)))
                  e)
    Right e ->
      pure $ Located (spanTo sp0 (locSpan e))
        (StmtBind (Located (locSpan nm) (PVar nm))
                  (Just (Located (locSpan t) (QualType [] t)))
                  e)

pRegWriteStmt :: Parser LStmt
pRegWriteStmt = do
  sp0 <- peekSpan
  lhs <- pPostfixExpr
  namedOp "<="
  rhs <- pExpr
  void semi
  pure $ Located (spanTo sp0 (locSpan rhs)) (StmtAssign lhs rhs)

pAssignStmt :: Parser LStmt
pAssignStmt = do
  sp0 <- peekSpan
  lhs <- pPostfixExpr
  void equals
  rhs <- pExpr
  void semi
  pure $ Located (spanTo sp0 (locSpan rhs))
    (StmtExpr (Located (spanTo sp0 (locSpan rhs)) (EInfix lhs (Located sp0 (OpSym "=")) rhs)))

pBindStmt :: Parser LStmt
pBindStmt = do
  sp0 <- peekSpan
  pat <- pPattern
  void larrow
  e   <- pExpr
  void semi
  pure $ Located (spanTo sp0 (locSpan e)) (StmtBind pat Nothing e)

pExprStmt :: Parser LStmt
pExprStmt = do
  sp0 <- peekSpan
  e   <- pExpr
  void semi
  pure $ Located (spanTo sp0 (locSpan e)) (StmtExpr e)

-- | Handle an "orphan" @else@ or @else if@ clause that appears at statement
-- level after @`ifdef ... `endif@ blocks are consumed.  This is not standard
-- BSV but arises from preprocessor-conditional else branches.
-- Treat it as a no-op statement.
pOrphanElse :: Parser LStmt
pOrphanElse = do
  sp0 <- keyword Lex.KwElse
  void $ optional $ keyword Lex.KwIf *> lparen *> pExpr *> rparen
  void pStmtBlock
  pure $ Located sp0 (StmtExpr (Located sp0 EDontCare))

stmtsToExpr :: SrcSpan -> [LStmt] -> LExpr
stmtsToExpr sp [] = Located sp (ETuple [])
stmtsToExpr _  ss = Located (locSpan (last ss)) (EDo ss)

pCondPredicate :: Parser LExpr
pCondPredicate = do
  e  <- pExpr
  es <- many $ try $ do
    namedOp "&&&"
    e2 <- pExpr
    void $ optional $ void (keyword Lex.KwMatches) *> void pPattern
    pure e2
  pure $ foldl' (\a b -> Located (spanTo (locSpan a) (locSpan b)) (EInfix a (Located (locSpan b) (OpSym "&&&")) b)) e es

--------------------------------------------------------------------------------
-- Interface field definitions
--------------------------------------------------------------------------------

pInterfaceStmt :: Parser InterfaceField
pInterfaceStmt = choice
  [ try pMethodDef
  , try pSubifaceDef
  ]

pMethodDef :: Parser InterfaceField
pMethodDef = do
  sp0    <- keyword Lex.KwMethod
  _mTy   <- optional (try (pType <* lookAhead varId))
  nm     <- varId
  pats   <- option [] $ do
    void lparen
    fs <- methodFormal `sepBy` comma
    void rparen
    pure fs
  mGuard <- optional $ do
    void $ keyword Lex.KwIf
    void lparen; e <- pCondPredicate; void rparen
    pure e
  body <- choice
    [ do void equals; e <- pExpr; void semi; pure [Located (locSpan e) (StmtExpr e)]
    , do void semi
         ss <- many (try pActionStmt)
         void $ keyword Lex.KwEndMethod
         void $ optional (void colon *> void anyId)
         pure ss
    ]
  let whenG = fmap (\e -> [BoolGuard e]) mGuard
      sp1   = if null body then sp0 else locSpan (last body)
  pure $ InterfaceField sp0 nm pats (stmtsToExpr sp0 body) whenG
  where
    methodFormal = do
      void $ optional attrInsts
      _mTy <- optional (try (pType <* lookAhead varId))
      nm   <- varId
      pure (Located (locSpan nm) (PVar nm))

pSubifaceDef :: Parser InterfaceField
pSubifaceDef = do
  sp0 <- keyword Lex.KwInterface
  _mTy <- optional (try pType)
  nm   <- varId
  body <- choice
    [ do void equals; e <- pExpr; void semi; pure e
    , do void semi
         ss <- many (try pInterfaceStmt)
         sp1 <- keyword Lex.KwEndInterface
         void $ optional (void colon *> void anyId)
         pure $ Located (spanTo sp0 sp1) (EInterface Nothing ss)
    ]
  pure $ InterfaceField sp0 nm [] body Nothing

--------------------------------------------------------------------------------
-- Typedef
--------------------------------------------------------------------------------

pTypedef :: Parser LDefinition
pTypedef = do
  sp0 <- keyword Lex.KwTypedef
  choice
    [ try (pTypedefStruct sp0)
    , try (pTypedefTaggedUnion sp0)
    , try (pTypedefEnum sp0)
    , pTypedefSynonym sp0
    ]

pTypedefSynonym :: SrcSpan -> Parser LDefinition
pTypedefSynonym sp0 = do
  t <- pType
  (nm, tvs) <- pTypeDefType
  void semi
  pure $ Located (spanTo sp0 (locSpan nm)) (DefType nm Nothing tvs t)

pTypedefStruct :: SrcSpan -> Parser LDefinition
pTypedefStruct sp0 = do
  void $ keyword Lex.KwStruct
  void lbrace
  mems <- fmap catMaybes $ many $
    (Nothing <$ try skipIfdefBlock) <|>
    (Nothing <$ try skipPreprocDirective) <|>
    (Just <$> pStructMember)
  void rbrace
  (nm, tvs) <- pTypeDefType
  mDeriv <- optional (try pDeriving)
  void semi
  let toField (fNm, fTy) =
        Located (locSpan fNm) $ Field
          { fieldSpan    = locSpan fNm
          , fieldName    = fNm
          , fieldType    = Located (locSpan fTy) (QualType [] fTy)
          , fieldPragmas = []
          , fieldDefault = Nothing }
  pure $ Located (spanTo sp0 (locSpan nm))
           (DefInterface nm tvs (map toField mems) (fromMaybe [] mDeriv))

pTypedefTaggedUnion :: SrcSpan -> Parser LDefinition
pTypedefTaggedUnion sp0 = do
  void $ keyword Lex.KwUnion
  void $ keyword Lex.KwTagged
  void lbrace
  mems <- fmap catMaybes $ many $
    (Nothing <$ try skipIfdefBlock) <|>
    (Nothing <$ try skipPreprocDirective) <|>
    (Just <$> pUnionMember)
  void rbrace
  (nm, tvs) <- pTypeDefType
  mDeriv <- optional (try pDeriving)
  void semi
  pure $ Located (spanTo sp0 (locSpan nm))
           (DefData nm Nothing tvs mems (fromMaybe [] mDeriv))
  where
    pUnionMember = do
      sp <- peekSpan
      v  <- choice
        [ do void $ keyword Lex.KwVoid
             nm <- conId; void semi
             pure $ Constructor [nm] [] Nothing
        , do t <- pType; nm <- conId; void semi
             pure $ Constructor [nm] [t] Nothing
        ]
      pure $ Located sp v

pTypedefEnum :: SrcSpan -> Parser LDefinition
pTypedefEnum sp0 = do
  void $ keyword Lex.KwEnum
  void lbrace
  elems <- enumElem `sepBy` comma
  void rbrace
  (nm, tvs) <- pTypeDefType
  mDeriv <- optional (try pDeriving)
  void semi
  let ctors = map (\(cnm, _) -> Located (locSpan cnm) (Constructor [cnm] [] Nothing)) elems
  pure $ Located (spanTo sp0 (locSpan nm))
           (DefData nm Nothing tvs ctors (fromMaybe [] mDeriv))
  where
    enumElem = do
      cnm  <- conId
      mVal <- optional $ void equals *> intLit
      pure (cnm, mVal)

pStructMember :: Parser (Located Ident, LType)
pStructMember = do
  t <- pType
  nm <- varId <|> conId
  void semi
  pure (fmap VarId (fmap identText nm), t)

--------------------------------------------------------------------------------
-- Interface declaration
--------------------------------------------------------------------------------

pInterfaceDecl :: Parser LDefinition
pInterfaceDecl = do
  sp0 <- keyword Lex.KwInterface
  (nm, tvs) <- pTypeDefType
  void semi
  mems <- many (try pMember)
  sp1  <- keyword Lex.KwEndInterface
  void $ optional (void colon *> void anyId)
  pure $ Located (spanTo sp0 sp1) (DefInterface nm tvs (mapMaybe id mems) [])
  where
    pMember = choice
      [ try (Just <$> pMethodProto)
      , try (Just <$> pSubifaceDecl')
      , try (Nothing <$ someAttrInsts)
      , Nothing <$ try skipPreprocDirective  -- `ifdef/`endif inside interface body
      ]

    pMethodProto = do
      void $ optional attrInsts
      void $ keyword Lex.KwMethod
      mTy <- optional (try (pType <* lookAhead varId))
      nm  <- varId
      void $ optional $ do
        void lparen
        void $ methodProtoFormal `sepBy` comma
        void rparen
      void semi
      let fieldTy = case mTy of
            Just t  -> Located (locSpan t) (QualType [] t)
            Nothing -> Located (locSpan nm) (QualType [] (Located (locSpan nm)
                         (TCon (Located (locSpan nm) (QualIdent Nothing (ConId "?"))))))
      pure $ Located (locSpan nm) $ Field
        { fieldSpan    = locSpan nm
        , fieldName    = fmap VarId (fmap identText nm)
        , fieldType    = fieldTy
        , fieldPragmas = []
        , fieldDefault = Nothing }
      where
        methodProtoFormal = do
          void $ optional attrInsts
          void $ optional (try pType)
          void varId

    pSubifaceDecl' = do
      void $ optional attrInsts
      void $ keyword Lex.KwInterface
      t  <- pType
      nm <- varId
      void semi
      pure $ Located (locSpan nm) $ Field
        { fieldSpan    = locSpan nm
        , fieldName    = fmap VarId (fmap identText nm)
        , fieldType    = Located (locSpan t) (QualType [] t)
        , fieldPragmas = []
        , fieldDefault = Nothing }

--------------------------------------------------------------------------------
-- Function definition
--------------------------------------------------------------------------------

pFunctionDef :: Parser LDefinition
pFunctionDef = do
  sp0 <- keyword Lex.KwFunction
  retTy <- pType
  nm <- choice [varId, pOperIdent, kwAsVarId]
  pats <- option [] $ do
    void lparen
    fs <- funcFormal `sepBy` comma
    void rparen
    pure fs
  void $ optional (try pProvisos)
  (body, sp1) <- choice
    [ do void semi
         ss <- many (try pStmt)
         sp1 <- keyword Lex.KwEndFunction
         void $ optional (void colon *> void anyId)
         pure (ss, sp1)
    , do void equals; e <- pExpr; void semi
         pure ([Located (locSpan e) (StmtExpr e)], locSpan e)
    ]
  let qt     = Located (locSpan retTy) (QualType [] retTy)
      clause = Clause sp0 pats Nothing (stmtsToExpr sp0 body) []
  pure $ Located (spanTo sp0 sp1) (DefValue nm (Just qt) [clause])
  where
    funcFormal = do
      void $ optional attrInsts
      -- Handle `function RetType f(formals...)` function-type formals
      isFn <- option False (True <$ keyword Lex.KwFunction)
      void $ optional (try (pType <* lookAhead varId))
      nm <- varId
      -- If it's a function formal, consume the nested formals list
      when isFn $ void $ optional $ do
        void lparen
        void $ funcFormal `sepBy` comma
        void rparen
      pure $ Located (locSpan nm) (PVar nm)
    pOperIdent = do
      void $ punct Lex.PunctBackslash
      op <- opSym
      pure $ Located (locSpan op) (VarId (locVal op))
    -- Allow BSV keywords as function names (e.g. `function a when(...)`)
    kwAsVarId = tok $ \case
      Lex.TokKeyword k -> Just (VarId (Lex.keywordText k))
      _ -> Nothing

--------------------------------------------------------------------------------
-- Module definition
--------------------------------------------------------------------------------

pModuleDef :: Parser LDefinition
pModuleDef = do
  sp0  <- keyword Lex.KwModule
  void $ optional $ try $ void lbracket *> void pType *> void rbracket
  nm   <- varId
  void $ optional $ try pModuleFormalParams
  void lparen
  ifcTy <- optional $ try $ do
    t <- pType
    void $ optional varId
    -- Allow array subscript on the interface name: e.g. `Reg#(a) ifc[]`
    void $ optional $ try $ void lbracket *> void (optional pExpr) *> void rbracket
    pure t
  void rparen
  void $ optional (try pProvisos)
  void semi
  ss   <- many (try pModuleStmt)
  sp1  <- keyword Lex.KwEndModule
  void $ optional (void colon *> void anyId)
  let qt = case ifcTy of
        Nothing -> Located sp0 (QualType [] (Located sp0 (TCon (Located sp0 (QualIdent Nothing (ConId "Empty"))))))
        Just t  -> Located (locSpan t) (QualType [] t)
      modE = Located (spanTo sp0 sp1) (EModule ss)
      clause = Clause sp0 [] Nothing modE []
  pure $ Located (spanTo sp0 sp1) (DefValue nm (Just qt) [clause])

pModuleFormalParams :: Parser ()
pModuleFormalParams = do
  hash
  -- Use balanced-paren scanning so preprocessor directives inside the
  -- parameter list (e.g. `ifdef ISA_F ... `endif) are skipped gracefully.
  -- We don't extract parameter names here; see pModuleStmt for bindings.
  void $ balancedParens

-- | Consume a balanced parenthesised block, including all nested parens.
-- Handles any token stream, including preprocessor directives.
balancedParens :: Parser ()
balancedParens = do
  void lparen
  go (1 :: Int)
  where
    go 0 = pure ()
    go n = do
      mt <- optional $ tok $ \k -> Just k
      case mt of
        Nothing -> pure ()   -- EOF
        Just t  -> case locVal t of
          Lex.TokPunct Lex.PunctLParen -> go (n + 1)
          Lex.TokPunct Lex.PunctRParen -> go (n - 1)
          Lex.TokEOF                   -> pure ()
          _                            -> go n

pModuleStmt :: Parser ModuleStmt
pModuleStmt = choice
  [ try pMsRule
  , try pMsSubiface
  , try pMsMethod
  , try pMsVarDecl
  , try pMsFuncDef
  , try pMsLetBind
  , try pMsIf       -- if/else blocks in module body (conditional instantiation)
  , try pMsReturn   -- return stmt at end of module expression
  , try pMsAssign   -- lhs = rhs; (assignment to previously declared variable)
  , try pMsPreproc  -- skip `ifdef / `else / `endif / `define etc.
  , pMsExpr
  ]

-- | Skip a preprocessor directive line inside a module body.
-- These are not valid BSV tokens but pass through the lexer as
-- TokPunct PunctBacktick + TokVarId/TokConId.
--
-- We consume ONLY the directive header:
--   `ifdef COND   → backtick + "ifdef" + "COND"
--   `endif        → backtick + "endif"
--   `else         → backtick + "else"
--   `define N v   → backtick + "define" + name-ident (value left for next parse)
--
-- The body code between `ifdef and `endif is left in the stream and
-- handled by the normal pModuleStmt parsers.
pMsPreproc :: Parser ModuleStmt
pMsPreproc = do
  tok (\case { Lex.TokPunct Lex.PunctBacktick -> Just (); _ -> Nothing })
  void anyId   -- directive name: ifdef, endif, else, define, undef, …
  -- Consume one optional identifier argument (e.g. the condition for `ifdef).
  void $ optional $ tok $ \case
    Lex.TokVarId _ -> Just ()
    Lex.TokConId _ -> Just ()
    _ -> Nothing
  pure $ MStmtLet []  -- no-op

pMsRule :: Parser ModuleStmt
pMsRule = do
  void $ optional attrInsts
  r <- pRule
  pure (MStmtRules [r])

pMsSubiface :: Parser ModuleStmt
pMsSubiface = do
  sp0 <- keyword Lex.KwInterface
  -- Two cases: subinterface assignment OR interface-return
  choice
    [ try $ do
        t  <- pType
        nm <- varId
        body <- choice
          [ do void equals; e <- pExpr; void semi
               pure [InterfaceField (locSpan nm) nm [] e Nothing]
          , do void semi
               ms <- many (try pInterfaceStmt)
               void $ keyword Lex.KwEndInterface
               void $ optional (void colon *> void anyId)
               pure ms
          ]
        pure (MStmtInterface body)
    , do mNm <- optional (try conId)
         void semi
         ms <- many (try pInterfaceStmt)
         void $ keyword Lex.KwEndInterface
         void $ optional (void colon *> void anyId)
         let qnm = fmap (\n -> Located (locSpan n) (QualIdent Nothing (locVal n))) mNm
         pure (MStmtExpr (Located sp0 (EInterface qnm ms)))
    ]

pMsMethod :: Parser ModuleStmt
pMsMethod = do
  sp0  <- keyword Lex.KwMethod
  -- Only consume the optional return-type annotation if a method name
  -- (another varId) follows immediately.  Without this guard, a method
  -- with no explicit return type — e.g. "method wset(v);" — would have
  -- its name consumed as a type variable, causing the parse to fail.
  void $ optional (try (pType <* lookAhead varId))
  nm   <- varId
  pats <- option [] $ do
    void lparen
    fs <- mFormal `sepBy` comma
    void rparen
    pure fs
  mGuard <- optional $ do
    void $ keyword Lex.KwIf
    void lparen; e <- pCondPredicate; void rparen; pure e
  body <- choice
    [ do void equals; e <- pExpr; void semi
         pure [Located (locSpan e) (StmtExpr e)]
    , do void semi
         ss <- many (try pActionStmt)
         void $ keyword Lex.KwEndMethod
         void $ optional (void colon *> void anyId)
         pure ss
    ]
  let whenG = fmap (\e -> [BoolGuard e]) mGuard
  pure $ MStmtInterface
    [InterfaceField sp0 nm pats (stmtsToExpr sp0 body) whenG]
  where
    mFormal = do
      void $ optional attrInsts
      -- Only consume the type annotation if a varId (the parameter name) follows.
      void $ optional (try (pType <* lookAhead varId))
      nm <- varId
      pure (Located (locSpan nm) (PVar nm))

pMsVarDecl :: Parser ModuleStmt
pMsVarDecl = do
  sp0 <- peekSpan
  mattrs <- optional (try attrInsts)
  choice
    [ -- Attribute + bare varId <- expr  (no explicit type)
      -- e.g. `(* hide *) _ifc <- vMkCReg5(init);`
      do guard (mattrs /= Nothing)
         nm <- varId
         e  <- larrow *> pExpr
         void semi
         pure (MStmtBind (Located (locSpan nm) (PVar nm)) Nothing e)
    , -- Type name [subscript] ([ <- | = ] expr | ;)
      do t  <- pTypePrimary
         nm <- varId
         -- Allow optional array subscript: e.g. `Reg#(a) v[n];`
         void $ optional $ try $ void lbracket *> void (optional pExpr) *> void rbracket
         choice
           [ -- Initialized: Type name <- expr;  or  Type name = expr;
             do (isArrow, e) <- choice
                  [ (True,)  <$> (larrow *> pExpr)
                  , (False,) <$> (equals *> pExpr)
                  ]
                void semi
                if isArrow
                  then pure (MStmtBind (Located (locSpan nm) (PVar nm)) (Just t) e)
                  else let qt     = Located (locSpan t) (QualType [] t)
                           clause = Clause sp0 [] Nothing e []
                       in pure (MStmtDef (Located (spanTo sp0 (locSpan e))
                                            (DefValue nm (Just qt) [clause])))
           -- Forward declaration: Type name;  (variable assigned later via '=')
           , do void semi
                pure (MStmtLet [])
           ]
    ]

pMsFuncDef :: Parser ModuleStmt
pMsFuncDef = MStmtDef <$> pFunctionDef

pMsLetBind :: Parser ModuleStmt
pMsLetBind = do
  void $ keyword Lex.KwLet
  nm <- varId
  e  <- choice [void larrow *> pExpr, void equals *> pExpr]
  void semi
  let item = LetBind (Binding (locSpan nm) (Located (locSpan nm) (PVar nm)) [] Nothing e)
  pure (MStmtLet [item])

pMsExpr :: Parser ModuleStmt
pMsExpr = MStmtExpr <$> (pExpr <* void semi)

-- | Parse a variable assignment in module context: lhs = rhs;
-- Handles cases like `ifc = (interface Foo; ... endinterface);`
pMsAssign :: Parser ModuleStmt
pMsAssign = do
  lhs <- pPostfixExpr
  void equals
  rhs <- pExpr
  void semi
  pure (MStmtExpr rhs)

-- | Parse an if/else block in module context (conditional instantiation).
-- The branches may contain arbitrary module statements; we collect them all.
pMsIf :: Parser ModuleStmt
pMsIf = do
  sp0  <- keyword Lex.KwIf
  void lparen; void pExpr; void rparen
  then_ <- pMsBeginEnd
  else_ <- option [] (keyword Lex.KwElse *> pMsBeginEnd)
  -- Represent as a list of sub-statements; use MStmtLet [] as a no-op carrier
  -- and MStmtDef/MStmtBind for sub-statements that introduce bindings.
  -- For simplicity, flatten all sub-statements as an MStmtExpr(EDontCare).
  let dummy = Located sp0 EDontCare
  pure (MStmtExpr (Located sp0 (ELet (bindingsFrom (then_ ++ else_)) dummy)))
  where
    bindingsFrom :: [ModuleStmt] -> [LetItem]
    bindingsFrom = concatMap toLetItem
    toLetItem (MStmtBind (Located sp (PVar nm)) _ e) =
      [LetBind (Binding sp (Located sp (PVar nm)) [] Nothing e)]
    toLetItem (MStmtDef (Located sp (DefValue nm mty cls))) =
      [LetBind (Binding sp (Located sp (PVar nm)) [] mty
                  (case cls of { [c] -> clauseBody c; _ -> Located sp EDontCare }))]
    toLetItem _ = []

-- | Parse a `begin ... end` block as a list of module statements,
-- or a single module statement if no `begin` keyword.
pMsBeginEnd :: Parser [ModuleStmt]
pMsBeginEnd = choice
  [ do void $ keyword Lex.KwBegin
       ss <- many (try pModuleStmt)
       void $ keyword Lex.KwEnd
       pure ss
  , (:[]) <$> pModuleStmt
  ]

-- | Parse `return expr ;` in module context.
pMsReturn :: Parser ModuleStmt
pMsReturn = do
  void $ keyword Lex.KwReturn
  e <- pExpr
  void semi
  pure (MStmtExpr e)

--------------------------------------------------------------------------------
-- Rules
--------------------------------------------------------------------------------

pRule :: Parser (Located Rule)
pRule = do
  sp0  <- keyword Lex.KwRule
  nm   <- varId
  mCond <- optional $ do
    void lparen; e <- pCondPredicate; void rparen
    pure [BoolGuard e]
  void semi
  body <- many (try pActionStmt)
  sp1  <- keyword Lex.KwEndRule
  void $ optional (void colon *> void anyId)
  let nmE = Located (locSpan nm) (ELit (Located (locSpan nm) (LitString (identText (locVal nm)))))
  pure $ Located (spanTo sp0 sp1)
    (Rule sp0 (Just nmE) [] mCond (stmtsToExpr sp0 body))

--------------------------------------------------------------------------------
-- Typeclass / Instance
--------------------------------------------------------------------------------

pTypeclassDef :: Parser LDefinition
pTypeclassDef = do
  sp0  <- (keyword Lex.KwTypeclass <|> keyword Lex.KwClass)
  nm   <- conId
  tvs  <- option [] (try pTypeFormals)
  -- Optional `dependencies (...)` clause (BSV typeclasses); may have nested
  -- parens like `dependencies (r determines (a,n))`.
  void $ optional $ try $ do
    void $ tok $ \case { Lex.TokVarId "dependencies" -> Just (); _ -> Nothing }
    balancedParens
  void $ optional (try pProvisos)
  void $ optional semi
  mems <- many (try pTcMember)
  sp1  <- keyword Lex.KwEndTypeclass
  void $ optional (void colon *> void anyId)
  pure $ Located (spanTo sp0 sp1) (DefClass Nothing [] nm tvs [] mems)

pTcMember :: Parser ClassMember
pTcMember = choice
  [ try $ do
      void $ keyword Lex.KwFunction
      t <- pType
      nm <- varId
      void lparen
      void $ funcFormal `sepBy` comma
      void rparen
      void semi
      pure (ClassMethod nm (Located (locSpan t) (QualType [] t)) Nothing)
  , try $ do
      d <- pFunctionDef
      case locVal d of
        DefValue nm _ (c:_) ->
          pure (ClassDefaultImpl nm (clausePats c) (clauseBody c))
        _ -> fail "expected function"
  , do t <- pType; nm <- varId; void semi
       pure (ClassMethod (fmap VarId (fmap identText nm))
                         (Located (locSpan t) (QualType [] t))
                         Nothing)
  ]
  where
    funcFormal = do
      void $ optional (try pType)
      void varId

pInstanceDef :: Parser LDefinition
pInstanceDef = do
  sp0  <- keyword Lex.KwInstance
  cls  <- conId
  hash
  void lparen
  args <- pType `sepBy1` comma
  void rparen
  void $ optional (try pProvisos)
  void semi
  mems <- many (try pInstMember)
  sp1  <- keyword Lex.KwEndInstance
  void $ optional (void colon *> void anyId)
  let qcls = Located (locSpan cls) (QualIdent Nothing (locVal cls))
  pure $ Located (spanTo sp0 sp1) (DefInstance [] qcls args mems)

pInstMember :: Parser InstanceMember
pInstMember = choice
  [ try $ do
      d <- pFunctionDef
      case locVal d of
        DefValue nm _ clauses -> pure (InstanceMethod nm clauses)
        _ -> fail "expected function"
  , try $ do
      d <- pModuleDef
      case locVal d of
        DefValue nm _ clauses -> pure (InstanceMethod nm clauses)
        _ -> fail "expected module"
  , do nm <- varId; void equals; e <- pExpr; void semi
       pure (InstanceMethod nm [Clause (locSpan nm) [] Nothing e []])
  ]

--------------------------------------------------------------------------------
-- Export / Import declarations
--------------------------------------------------------------------------------

pExportDecl :: Parser [Located Export]
pExportDecl = do
  void $ keyword Lex.KwExport
  es <- pExportItem `sepBy1` comma
  void semi
  pure es

pExportItem :: Parser (Located Export)
pExportItem = choice
  [ try $ do
      pkg <- conId
      -- `::*` may lex as a single TokConSym "::*" (greedy scan)
      -- or as TokPunct PunctDColon + "*". Handle both.
      void $ tok $ \case
        Lex.TokConSym "::*"          -> Just ()
        Lex.TokPunct Lex.PunctDColon -> Just ()
        _ -> Nothing
      void $ optional $ tok $ \case
        Lex.TokVarSym "*" -> Just ()
        Lex.TokConSym "*" -> Just ()
        _ -> Nothing
      pure $ Located (locSpan pkg) (ExportModule (ModuleId (identText (locVal pkg))))
  , try $ do
      nm <- conId
      mSpec <- optional $ do
        void lparen
        void $ punct Lex.PunctDDot
        void rparen
      pure $ Located (locSpan nm) (ExportType (locVal nm) (mSpec >> Just []))
  , do nm <- varId
       pure $ Located (locSpan nm) (ExportVar (locVal nm))
  -- Allow lowercase keywords used as export names (e.g. 'export when;').
  -- In BSV, function/rule guards use the keyword 'when', but it can also
  -- name a prelude function exported by a library package.
  , do nm <- kwAsVarId
       pure $ Located (locSpan nm) (ExportVar (locVal nm))
  ]
  where
    -- Match a keyword token as a variable-identifier export name.
    kwAsVarId = tok $ \case
      Lex.TokKeyword k -> Just (VarId (Lex.keywordText k))
      _ -> Nothing

pImportDecl :: Parser (Located Import)
pImportDecl = do
  sp0 <- keyword Lex.KwImport
  pkg <- conId
  -- BSV import: `import Foo::*;`
  -- The `::*` may lex as a single TokConSym "::*" (greedy scan),
  -- or as TokPunct PunctDColon + TokVarSym "*" (split).  Handle both.
  void $ tok $ \case
    Lex.TokConSym "::*" -> Just ()
    Lex.TokPunct Lex.PunctDColon -> Just ()
    _ -> Nothing
  void $ optional $ tok $ \case
    Lex.TokVarSym "*"  -> Just ()
    Lex.TokConSym "*"  -> Just ()
    _ -> Nothing
  void semi
  pure $ Located (spanTo sp0 (locSpan pkg))
    (Import False (ModuleId (identText (locVal pkg))) Nothing Nothing)

--------------------------------------------------------------------------------
-- Package
--------------------------------------------------------------------------------

-- | Skip a preprocessor directive (`` `ifdef ``, `` `endif ``, `` `define ``,
-- etc.).  The lexer passes backtick + identifier through, so we consume that
-- token pair plus any trailing non-keyword tokens (directive arguments).
skipPreprocDirective :: Parser ()
skipPreprocDirective = do
  tok (\case { Lex.TokPunct Lex.PunctBacktick -> Just (); _ -> Nothing })
  void anyId   -- directive name: ifdef, endif, else, define, undef, …
  -- Skip non-keyword, non-backtick tokens (the directive arguments/condition)
  void $ manyTill anyTok $ lookAhead $ void $ tok $ \case
    Lex.TokKeyword _ -> Just ()
    Lex.TokPunct Lex.PunctBacktick -> Just ()
    Lex.TokEOF -> Just ()
    _ -> Nothing

-- | Skip a balanced `` `ifdef/`ifndef ... `endif `` block, including all
-- content and nested ifdef blocks.  Used in statement contexts where an ifdef
-- block may appear mid-statement (e.g. inside an if-else chain), making the
-- remaining `else` branches unreachable.
skipIfdefBlock :: Parser ()
skipIfdefBlock = do
  -- Consume the opening `ifdef / `ifndef
  tok (\case { Lex.TokPunct Lex.PunctBacktick -> Just (); _ -> Nothing })
  dir <- anyId
  -- Skip directive arguments
  void $ manyTill anyTok $ lookAhead $ void $ tok $ \case
    Lex.TokKeyword _ -> Just ()
    Lex.TokPunct Lex.PunctBacktick -> Just ()
    Lex.TokEOF -> Just ()
    _ -> Nothing
  -- Only proceed (and consume to matching endif) for opening directives
  let dirName = identText (locVal dir)
  if dirName `elem` ["ifdef", "ifndef"]
    then go 1
    else pure ()
  where
    backtick  = tok (\case { Lex.TokPunct Lex.PunctBacktick -> Just (); _ -> Nothing })
    stopToken = tok $ \case
      Lex.TokKeyword k | k `elem`
        [ Lex.KwEndFunction, Lex.KwEndModule, Lex.KwEndPackage
        , Lex.KwEndInterface, Lex.KwEndAction, Lex.KwEndActionValue
        , Lex.KwEndRule, Lex.KwEndMethod ] -> Just ()
      Lex.TokEOF -> Just ()
      _ -> Nothing
    isOpenDir d = let t = identText (locVal d) in t == "ifdef" || t == "ifndef"
    isEndDir  d = identText (locVal d) == "endif"
    go 0 = pure ()
    go n = do
      atStop <- option False (True <$ lookAhead stopToken)
      if atStop then pure () else do
        atBacktick <- option False (True <$ lookAhead backtick)
        if atBacktick
          then do
            void backtick
            mdir <- optional anyId
            case mdir of
              Nothing -> go n
              Just d | isOpenDir d -> go (n + 1)
                     | isEndDir  d -> go (n - 1)
                     | otherwise   -> go n
          else void anyTok >> go n

pPackage :: Parser Package
pPackage = do
  sp0   <- peekSpan
  void  $ optional $ keyword Lex.KwPackage
  pkgNm <- option (Located sp0 (ConId "Main")) conId
  void $ optional semi
  -- Exports and imports may appear in any order before definitions
  (exps, imps) <- collectExportsImports
  defns <- many (try pPkgStmt)
  void $ optional $ keyword Lex.KwEndPackage
  void $ optional (void colon *> void anyId)
  void $ optional $ tok (\case { Lex.TokEOF -> Just (); _ -> Nothing })
  sp1   <- peekSpan
  let expsMaybe = if null exps then Nothing else Just exps
  pure $ Package (spanTo sp0 sp1)
    (Located (locSpan pkgNm) (ModuleId (identText (locVal pkgNm))))
    expsMaybe imps [] defns
  where
    collectExportsImports = do
      items <- many $ choice
        [ Left  <$> try pExportDecl
        , Right <$> try pImportDecl
        , Left [] <$ try skipPreprocDirective
        ]
      let exps = concat [es | Left es  <- items]
          imps = [i        | Right i <- items]
      pure (exps, imps)

-- | Parse a package-level statement.
pPkgStmt :: Parser LDefinition
pPkgStmt = do
  void $ optional attrInsts
  choice
    [ try pInterfaceDecl
    , try pTypedef
    , try pTypeclassDef
    , try pInstanceDef
    , try pBviImport
    , try pBdpiImport
    , try pModuleDef
    , try pFunctionDef
    , pVarDecl
    ]

pBviImport :: Parser LDefinition
pBviImport = do
  sp0 <- keyword Lex.KwImport
  s   <- strLit
  -- Must be a non-BDPI string (e.g., "BVI ...")
  case locVal s of
    LitString t | t /= "BDPI" -> pure ()
    _ -> fail "not a BVI import"
  -- The BVI type name is a ConId (e.g. "RWire" in `import "BVI" RWire = module`)
  void $ optional (void anyId *> void equals)
  void $ keyword Lex.KwModule
  void $ optional $ try $ void lbracket *> void pType *> void rbracket
  nm <- varId
  skipToEndModule
  let qt = Located sp0 (QualType [] (Located sp0 (TCon (Located sp0 (QualIdent Nothing (ConId "Module"))))))
  pure $ Located (spanTo sp0 (locSpan nm)) (DefForeign nm qt Nothing)

pBdpiImport :: Parser LDefinition
pBdpiImport = do
  sp0 <- keyword Lex.KwImport
  s   <- strLit
  case locVal s of
    LitString "BDPI" -> pure ()
    _ -> fail "not a BDPI import"
  void $ optional $ try $ do void varId; void equals
  void $ keyword Lex.KwFunction
  retTy <- pType
  nm    <- varId
  void $ optional $ do
    void lparen
    void $ sepBy (void pType *> void (optional varId)) comma
    void rparen
  void semi
  pure $ Located (spanTo sp0 (locSpan nm))
    (DefForeign nm (Located (locSpan retTy) (QualType [] retTy)) Nothing)

pVarDecl :: Parser LDefinition
pVarDecl = do
  sp0 <- peekSpan
  t   <- pType
  nm  <- varId
  e   <- choice [void larrow *> pExpr, void equals *> pExpr]
  void semi
  let qt     = Located (locSpan t) (QualType [] t)
      clause = Clause sp0 [] Nothing e []
  pure $ Located (spanTo sp0 (locSpan e)) (DefValue nm (Just qt) [clause])

skipToEndModule :: Parser ()
skipToEndModule = go (0 :: Int)
  where
    go depth = do
      t <- tok (\k -> Just k)
      case locVal t of
        Lex.TokKeyword Lex.KwEndModule | depth == 0 -> do
          void $ optional (void colon *> void anyId)
        Lex.TokKeyword Lex.KwModule    -> go (depth + 1)
        Lex.TokKeyword Lex.KwEndModule -> go (depth - 1)
        Lex.TokEOF -> pure ()
        _ -> go depth

-- | Skip tokens until we reach a top-level BSV declaration boundary.
-- Used for error recovery: when a top-level item fails to parse, skip
-- forward to where the next one might begin.
-- | A parser that succeeds (without consuming input) when the current token is
-- a top-level keyword or EOF. Used as the sentinel for 'skipToTopLevel'.
topLevelBoundary :: Parser ()
topLevelBoundary = void topLevelKw <|> void eofTok
  where
    topLevelKw = tok $ \case
      Lex.TokKeyword k | isTopLevel k -> Just ()
      _ -> Nothing
    eofTok = tok $ \case { Lex.TokEOF -> Just (); _ -> Nothing }
    isTopLevel k = k `elem`
      [ Lex.KwModule, Lex.KwInterface, Lex.KwTypedef
      , Lex.KwFunction, Lex.KwClass, Lex.KwInstance
      , Lex.KwImport, Lex.KwExport, Lex.KwEndPackage
      ]

-- | Version of 'pPackage' with error recovery at the top-level statement
-- boundary. Failed top-level items are skipped and their errors registered.
pPackageRecovering :: Parser Package
pPackageRecovering = do
  sp0   <- peekSpan
  void  $ optional $ keyword Lex.KwPackage
  pkgNm <- option (Located sp0 (ConId "Main")) conId
  void $ optional semi
  (exps, imps) <- collectExportsImports
  defns <- catMaybes <$> many (withRecovery recover (Just <$> try pPkgStmt))
  void $ optional $ keyword Lex.KwEndPackage
  void $ optional (void colon *> void anyId)
  void $ optional $ tok (\case { Lex.TokEOF -> Just (); _ -> Nothing })
  sp1   <- peekSpan
  let expsMaybe = if null exps then Nothing else Just exps
  let pkg = Package (spanTo sp0 sp1)
              (Located (locSpan pkgNm) (ModuleId (identText (locVal pkgNm))))
              expsMaybe imps [] defns
  pure pkg
  where
    collect = many $ choice
      [ Left  <$> try pExportDecl
      , Right <$> try pImportDecl
      -- Skip preprocessor directives (`ifdef, `endif, `else, `define, etc.) that
      -- may appear interspersed with imports.  These are not valid BSV tokens but
      -- pass through the lexer as TokPunct PunctBacktick + TokVarId/TokConId.
      -- We consume the directive header plus any tokens up to the next keyword or
      -- backtick, so that regular imports following the directive are still collected.
      , Left [] <$ try skipPreprocDirective
      ]
    collectExportsImports = do
      items <- collect
      let exps = concat [es | Left es  <- items]
          imps = [i        | Right i <- items]
      pure (exps, imps)
    recover _ = do
      -- If we are at a top-level boundary (top-level keyword or EOF), do NOT
      -- consume it.  Failing empty here causes 'withRecovery' to propagate an
      -- empty failure, which makes 'many' stop the loop gracefully.  This also
      -- prevents us from accidentally consuming 'endpackage' or the EOF token,
      -- which would corrupt the rest of the package parse.
      --
      -- NOTE: do NOT call registerParseError here — megaparsec's withRecovery
      -- handles error registration automatically when recovery succeeds.
      -- Calling it manually causes runParser' to return Left bundle even on
      -- overall parse success.
      notFollowedBy topLevelBoundary
      Nothing <$ (anyTok *> manyTill anyTok (lookAhead topLevelBoundary))
