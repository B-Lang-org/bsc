{-# LANGUAGE TypeFamilies #-}

-- | Parser for Bluespec Classic.
module Language.Bluespec.Parser
  ( -- * Parsing functions
    parsePackage
  , parseExpr
  , parseType
  , parseFile
  , parseAuto
  , parseAutoRecovering

    -- * Parser type
  , Parser
  , ParseError
  ) where

import Control.Monad (void)
import Data.List.NonEmpty (NonEmpty(..), toList)
import System.FilePath (takeExtension)
import qualified Data.List.NonEmpty as NE
import Data.Maybe (fromMaybe, isJust)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Void (Void)
import Text.Megaparsec hiding (Token, token, tokens, ParseError)
import qualified Text.Megaparsec as MP

import qualified Language.Bluespec.Lexer as Lex
import Language.Bluespec.Layout
import qualified Language.Bluespec.BSV.Parser as BSV
import Language.Bluespec.Fixity (resolveOps, bluespecFixities)
import Language.Bluespec.Position
import Language.Bluespec.Syntax

--------------------------------------------------------------------------------
-- Parser Type
--------------------------------------------------------------------------------

type Parser = Parsec Void Lex.TokenStream
type ParseError = ParseErrorBundle Lex.TokenStream Void

--------------------------------------------------------------------------------
-- Token Matching
--------------------------------------------------------------------------------

-- | Match a specific token kind.
tok :: Lex.TokenKind -> Parser Lex.Token
tok expected = MP.token test (expected' expected)
  where
    test t = if matchKind expected (Lex.tokKind t) then Just t else Nothing
    expected' k = Set.singleton $ Tokens $ pure $ Lex.Token noSpan k

-- | Check if two token kinds match (handles virtual tokens).
matchKind :: Lex.TokenKind -> Lex.TokenKind -> Bool
matchKind Lex.TokVLBrace (Lex.TokPunct Lex.PunctLBrace) = True
matchKind (Lex.TokPunct Lex.PunctLBrace) Lex.TokVLBrace = True
matchKind Lex.TokVRBrace (Lex.TokPunct Lex.PunctRBrace) = True
matchKind (Lex.TokPunct Lex.PunctRBrace) Lex.TokVRBrace = True
matchKind Lex.TokVSemi (Lex.TokPunct Lex.PunctSemi) = True
matchKind (Lex.TokPunct Lex.PunctSemi) Lex.TokVSemi = True
matchKind a b = a == b

-- | Match a keyword.
keyword :: Lex.Keyword -> Parser Lex.Token
keyword kw = tok (Lex.TokKeyword kw)

-- | Match punctuation.
punct :: Lex.Punctuation -> Parser Lex.Token
punct p = tok (Lex.TokPunct p)

-- | Match a left brace (explicit or virtual).
lbrace :: Parser Lex.Token
lbrace = tok Lex.TokVLBrace <|> tok (Lex.TokPunct Lex.PunctLBrace)

-- | Match a right brace (explicit or virtual).
rbrace :: Parser Lex.Token
rbrace = tok Lex.TokVRBrace <|> tok (Lex.TokPunct Lex.PunctRBrace)

-- | Match a semicolon (explicit or virtual).
semi :: Parser Lex.Token
semi = tok Lex.TokVSemi <|> tok (Lex.TokPunct Lex.PunctSemi)

-- | Match one or more consecutive semicolons (handles ;; in explicit blocks).
semis :: Parser ()
semis = void (some semi)

-- | Match the pipe symbol |.
-- In Bluespec, | is a regular operator (bitwise OR), not reserved punctuation.
-- The parser handles it contextually for guards, data constructors, and fundeps.
pipe :: Parser Lex.Token
pipe = tok (Lex.TokVarSym "|")

-- | Match any variable identifier.
varId :: Parser (Located Ident)
varId = MP.token test expected
  where
    test t = case Lex.tokKind t of
      Lex.TokVarId name -> Just $ Located (Lex.tokSpan t) (VarId name)
      -- BSV-only keywords that appear as ordinary identifiers in Classic Bluespec
      Lex.TokKeyword kw | kw `elem` classicVarIdKeywords ->
        Just $ Located (Lex.tokSpan t) (VarId (Lex.keywordText kw))
      _ -> Nothing
    expected = Set.singleton $ Label $ NE.fromList "variable"

-- | BSV-only keywords that are valid ordinary identifiers in Bluespec Classic.
-- In Classic, these appear as function/value names rather than syntax keywords.
classicVarIdKeywords :: [Lex.Keyword]
classicVarIdKeywords =
  [ Lex.KwReturn, Lex.KwWhile, Lex.KwFor, Lex.KwBreak, Lex.KwContinue
  , Lex.KwRepeat, Lex.KwFunction, Lex.KwEndFunction, Lex.KwEndModule
  , Lex.KwEndInterface, Lex.KwEndRule, Lex.KwEndMethod, Lex.KwEndPackage
  , Lex.KwEndInstance, Lex.KwEndTypeclass, Lex.KwEndRules
  , Lex.KwTypedef, Lex.KwStruct, Lex.KwUnion, Lex.KwTagged, Lex.KwMatches
  , Lex.KwRule
  -- BSV keywords that can be used as method/field names in Classic interface definitions
  , Lex.KwEnd     -- 'end' is not a keyword in Classic (used as method name)
  , Lex.KwMethod  -- 'method' can appear as a class member name in Classic
  ]

-- | Match any constructor identifier.
conId :: Parser (Located Ident)
conId = MP.token test expected
  where
    test t = case Lex.tokKind t of
      Lex.TokConId name -> Just $ Located (Lex.tokSpan t) (ConId name)
      _ -> Nothing
    expected = Set.singleton $ Label $ NE.fromList "constructor"

-- | Match any identifier (var or con).
anyId :: Parser (Located Ident)
anyId = varId <|> conId

-- | Match a qualified identifier.
qualId :: Parser (Located QualIdent)
qualId = MP.token test expected
  where
    test t = case Lex.tokKind t of
      Lex.TokVarId name -> Just $ Located (Lex.tokSpan t) (QualIdent Nothing (VarId name))
      Lex.TokConId name -> Just $ Located (Lex.tokSpan t) (QualIdent Nothing (ConId name))
      Lex.TokQVarId m name -> Just $ Located (Lex.tokSpan t) (QualIdent (Just $ ModuleId m) (VarId name))
      Lex.TokQConId m name -> Just $ Located (Lex.tokSpan t) (QualIdent (Just $ ModuleId m) (ConId name))
      _ -> Nothing
    expected = Set.singleton $ Label $ NE.fromList "identifier"

-- | Match a qualified constructor.
qualConId :: Parser (Located QualIdent)
qualConId = MP.token test expected
  where
    test t = case Lex.tokKind t of
      Lex.TokConId name -> Just $ Located (Lex.tokSpan t) (QualIdent Nothing (ConId name))
      Lex.TokQConId m name -> Just $ Located (Lex.tokSpan t) (QualIdent (Just $ ModuleId m) (ConId name))
      _ -> Nothing
    expected = Set.singleton $ Label $ NE.fromList "constructor"

-- | Match a qualified variable.
qualVarId :: Parser (Located QualIdent)
qualVarId = MP.token test expected
  where
    test t = case Lex.tokKind t of
      Lex.TokVarId name -> Just $ Located (Lex.tokSpan t) (QualIdent Nothing (VarId name))
      Lex.TokQVarId m name -> Just $ Located (Lex.tokSpan t) (QualIdent (Just $ ModuleId m) (VarId name))
      -- BSV-only keywords that appear as ordinary identifiers in Classic Bluespec
      Lex.TokKeyword kw | kw `elem` classicVarIdKeywords ->
        Just $ Located (Lex.tokSpan t) (QualIdent Nothing (VarId (Lex.keywordText kw)))
      _ -> Nothing
    expected = Set.singleton $ Label $ NE.fromList "variable"

-- | Match an operator symbol.
opSym :: Parser (Located Op)
opSym = MP.token test expected
  where
    test t = case Lex.tokKind t of
      Lex.TokVarSym op -> Just $ Located (Lex.tokSpan t) (OpSym op)
      Lex.TokConSym op -> Just $ Located (Lex.tokSpan t) (OpSym op)
      Lex.TokQVarSym _ op -> Just $ Located (Lex.tokSpan t) (OpSym op)
      Lex.TokQConSym _ op -> Just $ Located (Lex.tokSpan t) (OpSym op)
      -- Handle := as an operator (register assignment)
      Lex.TokPunct Lex.PunctColonEq -> Just $ Located (Lex.tokSpan t) (OpSym ":=")
      _ -> Nothing
    expected = Set.singleton $ Label $ NE.fromList "operator"

-- | Match a backtick-quoted identifier as operator.
-- Supports both unqualified (e.g., `foo`) and qualified (e.g., `List.append`) identifiers.
backquoteOp :: Parser (Located Op)
backquoteOp = do
  void $ punct Lex.PunctBacktick
  i <- qualId
  void $ punct Lex.PunctBacktick
  pure $ Located (locSpan i) (OpIdent i)

-- | Match any operator (symbolic or backtick).
anyOp :: Parser (Located Op)
anyOp = opSym <|> backquoteOp

-- | Match a parenthesized operator as an identifier (for operator definitions).
-- E.g., (^^) in a type signature or definition.
parenOpAsId :: Parser (Located Ident)
parenOpAsId = do
  start <- getPos
  void $ punct Lex.PunctLParen
  op <- MP.token test expected
  void $ punct Lex.PunctRParen
  end <- getPos
  pure $ Located (mergeSpans start end) (VarId op)
  where
    test t = case Lex.tokKind t of
      Lex.TokVarSym op -> Just op
      Lex.TokConSym op -> Just op
      _ -> Nothing
    expected = Set.singleton $ Label $ NE.fromList "operator"

-- | Match an infix operator (not parenthesized).
-- Used for infix-style definitions like: x == y = ...
infixOp :: Parser (Located Ident)
infixOp = MP.token test expected
  where
    test t = case Lex.tokKind t of
      Lex.TokVarSym op -> Just $ Located (Lex.tokSpan t) (VarId op)
      Lex.TokConSym op -> Just $ Located (Lex.tokSpan t) (ConId op)
      _ -> Nothing
    expected = Set.singleton $ Label $ NE.fromList "operator"

-- | Match a variable or parenthesized operator (for definitions).
varIdOrOp :: Parser (Located Ident)
varIdOrOp = varId <|> parenOpAsId

-- | Match an integer literal.
intLit :: Parser (Located Literal)
intLit = MP.token test expected
  where
    test t = case Lex.tokKind t of
      Lex.TokInteger n mFmt -> Just $ Located (Lex.tokSpan t) (LitInt n (cvtFmt <$> mFmt))
      _ -> Nothing
    cvtFmt (w, Lex.IntDec') = (w, IntDec)
    cvtFmt (w, Lex.IntHex') = (w, IntHex)
    cvtFmt (w, Lex.IntBin') = (w, IntBin)
    cvtFmt (w, Lex.IntOct') = (w, IntOct)
    expected = Set.singleton $ Label $ NE.fromList "integer"

-- | Match a float literal.
floatLit :: Parser (Located Literal)
floatLit = MP.token test expected
  where
    test t = case Lex.tokKind t of
      Lex.TokFloat n -> Just $ Located (Lex.tokSpan t) (LitFloat n)
      _ -> Nothing
    expected = Set.singleton $ Label $ NE.fromList "float"

-- | Match a character literal.
charLit :: Parser (Located Literal)
charLit = MP.token test expected
  where
    test t = case Lex.tokKind t of
      Lex.TokChar c -> Just $ Located (Lex.tokSpan t) (LitChar c)
      _ -> Nothing
    expected = Set.singleton $ Label $ NE.fromList "character"

-- | Match a string literal.
stringLit :: Parser (Located Literal)
stringLit = MP.token test expected
  where
    test t = case Lex.tokKind t of
      Lex.TokString s -> Just $ Located (Lex.tokSpan t) (LitString s)
      _ -> Nothing
    expected = Set.singleton $ Label $ NE.fromList "string"

-- | Match any literal.
literal :: Parser (Located Literal)
literal = intLit <|> floatLit <|> charLit <|> stringLit

-- | Match a module identifier.
moduleId :: Parser (Located ModuleId)
moduleId = do
  c <- conId
  pure $ Located (locSpan c) (ModuleId $ identText $ locVal c)

--------------------------------------------------------------------------------
-- Position Helpers
--------------------------------------------------------------------------------

-- | Get span from token.
spanOf :: Lex.Token -> SrcSpan
spanOf = Lex.tokSpan

-- | Get current position.
getPos :: Parser SrcSpan
getPos = do
  mt <- optional $ lookAhead $ MP.token Just mempty
  pure $ maybe noSpan Lex.tokSpan mt

-- | Run parser and track span.
withSpan :: Parser a -> Parser (Located a)
withSpan p = do
  start <- getPos
  a <- p
  end <- getPos
  pure $ Located (mergeSpans start end) a

-- | Create a Located value spanning two Located values.
spanning :: Located a -> Located b -> c -> Located c
spanning a b c = Located (mergeSpans (locSpan a) (locSpan b)) c

--------------------------------------------------------------------------------
-- Block Parsing
--------------------------------------------------------------------------------

-- | Parse a braced block with layout.
block :: Parser a -> Parser [a]
block p = do
  void lbrace
  xs <- p `sepEndBy` semis
  void rbrace
  pure xs

-- | Parse a braced block with at least one element.
block1 :: Parser a -> Parser [a]
block1 p = do
  void lbrace
  xs <- p `sepEndBy1` semis
  void rbrace
  pure xs

--------------------------------------------------------------------------------
-- Package Parser
--------------------------------------------------------------------------------

-- | Parse a package.
pPackage :: Parser Package
pPackage = do
  startSpan <- getPos
  void $ keyword Lex.KwPackage
  name <- moduleId
  exports <- optional pExports
  void $ keyword Lex.KwWhere
  void lbrace
  (imports, fixities, defns) <- pPackageBody
  void rbrace
  endSpan <- getPos
  pure Package
    { pkgSpan = mergeSpans startSpan endSpan
    , pkgName = name
    , pkgExports = exports
    , pkgImports = imports
    , pkgFixity = fixities
    , pkgDefns = defns
    }

-- | Parse export list.
pExports :: Parser [Located Export]
pExports = do
  void $ punct Lex.PunctLParen
  xs <- pExport `sepBy` punct Lex.PunctComma
  void $ punct Lex.PunctRParen
  pure xs

-- | Parse a single export.
-- Supports: varId, (op), ConId, ConId(..), ConId(Con1, Con2, ...), module ModuleName, package PackageName
-- In Bluespec, 'package' is used to re-export an entire package (unlike Haskell's 'module').
pExport :: Parser (Located Export)
pExport = withSpan $ choice
  [ do
      void $ keyword Lex.KwModule
      m <- moduleId
      pure $ ExportModule (locVal m)
  , do
      -- Bluespec extension: 'package PackageName' re-exports an entire package
      void $ keyword Lex.KwPackage
      m <- moduleId
      pure $ ExportModule (locVal m)
  , do
      c <- conId
      subs <- optional $ do
        void $ punct Lex.PunctLParen
        -- Handle (..) meaning "export all constructors" or explicit list
        choice
          [ do
              void $ punct Lex.PunctDDot
              void $ punct Lex.PunctRParen
              -- Use empty list to represent (..) meaning "all constructors"
              pure []
          , do
              xs <- (locVal <$> anyId) `sepBy` punct Lex.PunctComma
              void $ punct Lex.PunctRParen
              pure xs
          ]
      -- If no parens at all, export just the type (abstract type export) - subs is Nothing
      -- If parens with (..), export all constructors - subs is Just []
      -- If parens with explicit list, export those constructors - subs is Just [...]
      pure $ ExportType (locVal c) subs
  , do
      v <- varId
      pure $ ExportVar (locVal v)
  , do
      -- Operator export: (op) or (:op)
      void $ punct Lex.PunctLParen
      export <- MP.token testOp expectedOp
      void $ punct Lex.PunctRParen
      pure export
  ]
  where
    -- Test for operator tokens and determine if they're type operators or var operators
    testOp t = case Lex.tokKind t of
      Lex.TokVarSym op -> Just (ExportVar (VarId op))
      Lex.TokConSym op -> Just (ExportType (ConId op) Nothing)
      _ -> Nothing
    expectedOp = Set.singleton $ Label $ NE.fromList "operator"

-- | Parse package body (imports, fixities, definitions).
pPackageBody :: Parser ([Located Import], [Located FixityDecl], [LDefinition])
pPackageBody = do
  items <- pPackageItem `sepEndBy` semis
  let imports = [Located s i | (s, Left i) <- items]
      fixDecls = [Located s f | (s, Right (Left f)) <- items]
      defns = [Located s d | (s, Right (Right d)) <- items]
  pure (imports, fixDecls, defns)

pPackageItem :: Parser (SrcSpan, Either Import (Either FixityDecl Definition))
pPackageItem = do
  start <- getPos
  item <- choice
    [ Left <$> pImport
    , Right . Left <$> pFixityDecl
    , Right . Right <$> pDefinition
    ]
  end <- getPos
  pure (mergeSpans start end, item)

-- | Parse an import declaration.
pImport :: Parser Import
pImport = do
  void $ keyword Lex.KwImport
  qual <- isJust <$> optional (keyword Lex.KwQualified)
  m <- moduleId
  as <- optional $ do
    -- 'as' is not a keyword in Bluespec, so we check for a specific varid
    void $ varIdNamed "as"
    moduleId
  spec <- optional pImportSpec
  pure Import
    { importQualified = qual
    , importModule = locVal m
    , importAs = locVal <$> as
    , importSpec = spec
    }

-- | Match a specific variable name.
varIdNamed :: Text -> Parser Lex.Token
varIdNamed name = MP.token test expected
  where
    test t = case Lex.tokKind t of
      Lex.TokVarId n | n == name -> Just t
      _ -> Nothing
    expected = Set.singleton $ Label $ NE.fromList $ T.unpack name

-- | Parse import specification.
pImportSpec :: Parser ImportSpec
pImportSpec = hiding <|> only
  where
    hiding = do
      void $ varIdNamed "hiding"
      void $ punct Lex.PunctLParen
      xs <- pExport `sepBy` punct Lex.PunctComma
      void $ punct Lex.PunctRParen
      pure $ ImportHiding xs
    only = do
      void $ punct Lex.PunctLParen
      xs <- pExport `sepBy` punct Lex.PunctComma
      void $ punct Lex.PunctRParen
      pure $ ImportOnly xs

-- | Parse a fixity declaration.
pFixityDecl :: Parser FixityDecl
pFixityDecl = do
  dir <- choice
    [ InfixL <$ keyword Lex.KwInfixL
    , InfixR <$ keyword Lex.KwInfixR
    , InfixN <$ keyword Lex.KwInfix
    ]
  prec <- intLit
  ops <- some anyOp
  let precVal = case locVal prec of
        LitInt n _ -> fromIntegral n
        _ -> 9
  pure FixityDecl
    { fixDeclFixity = Fixity dir precVal
    , fixDeclOps = ops
    }

--------------------------------------------------------------------------------
-- Definition Parser
--------------------------------------------------------------------------------

-- | Parse a top-level definition.
pDefinition :: Parser Definition
pDefinition = choice
  [ pDefPragma
  , pDataDef
  , pTypeDef
  , pInterfaceDef
  , pClassDef
  , pInstanceDef
  , pPrimitiveDef
  , pForeignDef
  , pValueDef
  ]

-- | Parse a pragma kind identifier.
-- Most pragma kinds are regular varIds (e.g., "properties", "noinline"),
-- but "synthesize" and "verilog" are keywords in Bluespec.
pPragmaKind :: Parser (Text, SrcSpan)
pPragmaKind = choice
  [ do
      t <- keyword Lex.KwSynthesize
      pure ("synthesize", Lex.tokSpan t)
  , do
      t <- keyword Lex.KwVerilog
      pure ("verilog", Lex.tokSpan t)
  , do
      t <- varId
      pure (identText (locVal t), locSpan t)
  , do
      t <- conId
      pure (identText (locVal t), locSpan t)
  ]

-- | Parse a top-level pragma (e.g., {-# properties mkTileImpl = { ... } #-}).
pDefPragma :: Parser Definition
pDefPragma = do
  void $ tok Lex.TokPragmaStart
  -- Parse the pragma kind (e.g., "properties", "synthesize", "verilog")
  -- Note: "synthesize" and "verilog" are keywords, not varIds
  (kind, kindSpan) <- pPragmaKind
  -- Parse the optional name being annotated
  mName <- optional anyId
  -- Consume all remaining tokens until TokPragmaEnd
  content <- pPragmaContent
  void $ tok Lex.TokPragmaEnd
  pure $ DefPragma TopLevelPragma
    { tlpKind = kind
    , tlpName = mName
    , tlpContent = content
    }

-- | Consume tokens until pragma end, collecting them as text.
-- This handles arbitrary content including nested braces.
pPragmaContent :: Parser Text
pPragmaContent = do
  toks <- many $ MP.token test mempty
  pure $ T.intercalate " " $ map tokToText toks
  where
    -- Accept any token except TokPragmaEnd
    test t = case Lex.tokKind t of
      Lex.TokPragmaEnd -> Nothing
      _ -> Just t
    tokToText t = case Lex.tokKind t of
      Lex.TokVarId s -> s
      Lex.TokConId s -> s
      Lex.TokVarSym s -> s
      Lex.TokConSym s -> s
      Lex.TokString s -> "\"" <> s <> "\""
      Lex.TokInteger n _ -> T.pack (show n)
      Lex.TokKeyword kw -> T.pack (show kw)
      Lex.TokPunct p -> punctToText p
      _ -> ""
    punctToText :: Lex.Punctuation -> Text
    punctToText p = case p of
      Lex.PunctEqual -> "="
      Lex.PunctLBrace -> "{"
      Lex.PunctRBrace -> "}"
      Lex.PunctLParen -> "("
      Lex.PunctRParen -> ")"
      Lex.PunctComma -> ","
      Lex.PunctSemi -> ";"
      Lex.PunctColon -> ":"
      Lex.PunctDColon -> "::"
      Lex.PunctArrow -> "->"
      Lex.PunctLArrow -> "<-"
      Lex.PunctFatArrow -> "=>"
      Lex.PunctDot -> "."
      Lex.PunctBacktick -> "`"
      Lex.PunctLBracket -> "["
      Lex.PunctRBracket -> "]"
      Lex.PunctAt -> "@"
      Lex.PunctBackslash -> "\\"
      Lex.PunctUnderscore -> "_"
      _ -> ""

-- | Parse a type definition.
-- Supports optional kind annotation: type (Foo :: # -> *) a = Bar a
pTypeDef :: Parser Definition
pTypeDef = do
  void $ keyword Lex.KwType
  -- Try parsing kind-annotated name: (ConId :: Kind)
  (name, mKind) <- pTypeNameWithOptionalKind
  tvars <- many pTyVar
  void $ punct Lex.PunctEqual
  ty <- pType
  pure $ DefType name mKind tvars ty

-- | Parse a type name with optional kind annotation.
-- Either just a ConId, or (ConId :: Kind)
pTypeNameWithOptionalKind :: Parser (Located Ident, Maybe (Located Kind))
pTypeNameWithOptionalKind = withKind <|> withoutKind
  where
    withKind = do
      void $ punct Lex.PunctLParen
      name <- conId
      void $ punct Lex.PunctDColon
      kind <- withSpan pKind
      void $ punct Lex.PunctRParen
      pure (name, Just kind)
    withoutKind = do
      name <- conId
      pure (name, Nothing)

-- | Parse a data definition.
-- Supports optional kind annotation: data (Foo :: * -> # -> *) a b = ...
pDataDef :: Parser Definition
pDataDef = do
  void $ keyword Lex.KwData
  -- Try parsing kind-annotated name: (ConId :: Kind) or just ConId
  (name, mKind) <- pTypeNameWithOptionalKind
  tvars <- many pTyVar
  void $ punct Lex.PunctEqual
  constrs <- pConstructor `sepBy1` pipe
  derivs <- pDerivings
  pure $ DefData name mKind tvars constrs derivs

-- | Parse a constructor.
-- Supports the Bluespec alias syntax: (Name1, Name2) Type or just Name Type
pConstructor :: Parser (Located Constructor)
pConstructor = withSpan $ do
  -- Parse constructor names: either a single name or (Name1, Name2, ...)
  names <- choice
    [ -- Alias syntax: (Name1, Name2, ...)
      do
        void $ punct Lex.PunctLParen
        ns <- conId `sepBy1` punct Lex.PunctComma
        void $ punct Lex.PunctRParen
        pure ns
    , -- Single name
      (:[]) <$> conId
    ]
  -- Check for record syntax
  mFields <- optional $ do
    void lbrace
    fs <- pField `sepEndBy` semis
    void rbrace
    pure fs
  case mFields of
    Just fields -> pure $ Constructor names [] (Just fields)
    Nothing -> do
      args <- many pAtomicType
      pure $ Constructor names args Nothing

-- | Parse an interface/struct definition.
pInterfaceDef :: Parser Definition
pInterfaceDef = do
  void $ keyword Lex.KwInterface <|> keyword Lex.KwStruct
  mKind <- optional $ try $ do
    void $ punct Lex.PunctLParen
    name <- conId
    void $ punct Lex.PunctDColon
    k <- pKind
    void $ punct Lex.PunctRParen
    pure (name, k)
  name <- case mKind of
    Just (n, _) -> pure n
    Nothing -> conId
  tvars <- many pTyVar
  void $ punct Lex.PunctEqual
  void lbrace
  fields <- pField `sepEndBy` semis
  void rbrace
  derivs <- pDerivings
  pure $ DefInterface name tvars (map (fmap id) fields) derivs

-- | Parse a field.
pField :: Parser (Located Field)
pField = withSpan $ do
  name <- varId
  void $ punct Lex.PunctDColon
  ty <- withSpan pQualType
  pragmas <- concat <$> many pMethodPragma
  def <- optional $ do
    void $ punct Lex.PunctEqual
    pExpr
  pure Field
    { fieldSpan = noSpan  -- Will be filled by withSpan
    , fieldName = name
    , fieldType = ty
    , fieldPragmas = pragmas
    , fieldDefault = def
    }

-- | Parse a single method pragma (without delimiters).
pMethodPragmaItem :: Parser MethodPragma
pMethodPragmaItem = choice
  [ MPAlwaysReady <$ varIdNamed "always_ready"
  , MPAlwaysEnabled <$ varIdNamed "always_enabled"
  -- enabled = <expr> (boolean condition)
  , do
      void $ varIdNamed "enabled"
      void $ punct Lex.PunctEqual
      MPEnabled <$> pExpr
  -- enable = "string" (port name for enable signal)
  , do
      void $ varIdNamed "enable"
      void $ punct Lex.PunctEqual
      s <- stringLit
      pure $ MPEnablePort (case locVal s of LitString t -> t; _ -> "")
  -- ready = "string" (port name for ready signal) must try before ready = <expr>
  , try $ do
      void $ varIdNamed "ready"
      void $ punct Lex.PunctEqual
      s <- stringLit
      pure $ MPReadyPort (case locVal s of LitString t -> t; _ -> "")
  -- ready = <expr> (boolean condition)
  , do
      void $ varIdNamed "ready"
      void $ punct Lex.PunctEqual
      MPReady <$> pExpr
  , do
      void $ varIdNamed "prefix"
      void $ punct Lex.PunctEqual
      s <- stringLit
      pure $ MPPrefixPort (case locVal s of LitString t -> t; _ -> "")
  , do
      void $ varIdNamed "result"
      void $ punct Lex.PunctEqual
      s <- stringLit
      pure $ MPResultPort (case locVal s of LitString t -> t; _ -> "")
  , do
      void $ varIdNamed "arg_names"
      void $ punct Lex.PunctEqual
      void $ punct Lex.PunctLBracket
      -- arg_names can be either variable identifiers or string literals
      names <- pArgName `sepBy` punct Lex.PunctComma
      void $ punct Lex.PunctRBracket
      pure $ MPArgNames names
  ]

-- | Parse an argument name (either a variable identifier or a string literal).
pArgName :: Parser Text
pArgName = choice
  [ identText . locVal <$> varId
  , do
      s <- stringLit
      pure $ case locVal s of
        LitString t -> t
        _ -> ""
  ]

-- | Parse method pragmas (returns list from one pragma block).
pMethodPragma :: Parser [MethodPragma]
pMethodPragma = do
  void $ tok Lex.TokPragmaStart
  pragmas <- pMethodPragmaItem `sepBy1` punct Lex.PunctComma
  void $ tok Lex.TokPragmaEnd
  pure pragmas

-- | Parse deriving clauses.
pDerivings :: Parser [Deriving]
pDerivings = do
  mDeriv <- optional $ do
    void $ keyword Lex.KwDeriving
    choice
      [ do
          void $ punct Lex.PunctLParen
          xs <- qualConId `sepBy` punct Lex.PunctComma
          void $ punct Lex.PunctRParen
          pure xs
      , (:[]) <$> qualConId
      ]
  pure [Deriving c | c <- fromMaybe [] mDeriv]

-- | Parse a class definition.
-- Supports: class Foo, class coherent Foo, class incoherent Foo
-- Also supports kind annotations: class (Foo :: * -> * -> *) a b where ...
pClassDef :: Parser Definition
pClassDef = do
  void $ keyword Lex.KwClass
  -- Parse optional coherent/incoherent modifier
  -- Nothing = regular, Just False = coherent, Just True = incoherent
  incoh <- choice
    [ Just False <$ keyword Lex.KwCoherent
    , Just True <$ keyword Lex.KwIncoherent
    , pure Nothing
    ]
  -- Try to parse either:
  -- 1. Kind-annotated class name: (ClassName :: Kind)
  -- 2. Context followed by =>: (Pred1, Pred2) =>
  -- 3. Just a class name
  (ctx, name) <- choice
    [ try pClassNameWithKind  -- (ClassName :: Kind) - no context
    , try pContextThenClassName  -- (Context) => ClassName
    , do  -- Just a class name, no context or kind annotation
        n <- conId
        pure ([], n)
    ]
  tvars <- many pTyVar
  fundeps <- pFunDeps
  mWhere <- optional $ do
    void $ keyword Lex.KwWhere
    block pClassMember
  pure $ DefClass incoh ctx name tvars fundeps (fromMaybe [] mWhere)

-- | Parse a kind-annotated class name: (ClassName :: Kind)
-- Returns empty context and the class name
pClassNameWithKind :: Parser ([Located Pred], Located Ident)
pClassNameWithKind = do
  void $ punct Lex.PunctLParen
  name <- conId
  void $ punct Lex.PunctDColon
  _kind <- pKind  -- Parse the kind but we don't store it (DefClass doesn't have a kind field)
  void $ punct Lex.PunctRParen
  pure ([], name)

-- | Parse context followed by => and then class name
pContextThenClassName :: Parser ([Located Pred], Located Ident)
pContextThenClassName = do
  ctx <- pContext
  void $ punct Lex.PunctFatArrow
  name <- conId
  pure (ctx, name)

-- | Parse functional dependencies.
pFunDeps :: Parser [FunDep]
pFunDeps = do
  mDeps <- optional $ do
    void pipe
    pFunDep `sepBy1` punct Lex.PunctComma
  pure $ fromMaybe [] mDeps

pFunDep :: Parser FunDep
pFunDep = do
  from <- some pTyVar
  void $ punct Lex.PunctArrow
  to <- some pTyVar
  pure $ FunDep from to

-- | Parse a class member.
-- Class members can be:
-- 1. Fixity declarations
-- 2. Type signatures: varId :: type
-- 3. Default implementations: varId [pats] = expr (without type sig)
pClassMember :: Parser ClassMember
pClassMember = choice
  [ ClassFixity <$> withSpan pFixityDecl
  , try pClassMethodWithSig  -- Type signature (possibly with inline default)
  , pClassDefaultImpl        -- Default implementation (no type sig)
  ]

-- | Parse a class method with type signature.
-- Handles: varId :: type [= expr] or (op) :: type [= expr]
pClassMethodWithSig :: Parser ClassMember
pClassMethodWithSig = do
  name <- varIdOrOp
  void $ punct Lex.PunctDColon
  ty <- withSpan pQualType
  def <- optional $ do
    void $ punct Lex.PunctEqual
    pExpr
  pure $ ClassMethod name ty def

-- | Parse a default implementation clause (without type signature).
-- Handles:
--   - Prefix style: varId [pats] = expr  or  (op) [pats] = expr
--   - Infix style: pat op pat = expr
-- These are stored as ClassDefaultImpl and should be merged with the
-- corresponding ClassMethod during later processing.
pClassDefaultImpl :: Parser ClassMember
pClassDefaultImpl = choice
  [ -- Infix style: pat op pat = expr (e.g., x == y = not (x /= y))
    try $ do
      lhs <- pAtomicPattern
      op <- infixOp
      rhs <- pAtomicPattern
      void $ punct Lex.PunctEqual
      body <- pExpr
      pure $ ClassDefaultImpl op [lhs, rhs] body
  , -- Prefix style: varId [pats] = expr or (op) [pats] = expr
    do
      name <- varIdOrOp
      pats <- many pAtomicPattern
      void $ punct Lex.PunctEqual
      body <- pExpr
      pure $ ClassDefaultImpl name pats body
  ]

-- | Parse an instance definition.
-- Supports:
--   instance ClassName args where ...
--   instance (Context) => ClassName args where ...
--   instance (ClassName args) where ...  (parenthesized head, no context)
pInstanceDef :: Parser Definition
pInstanceDef = do
  void $ keyword Lex.KwInstance
  -- Try to parse either:
  -- 1. Context followed by =>
  -- 2. Parenthesized instance head (no context)
  -- 3. Bare class name and args
  (ctx, cls, args) <- choice
    [ try pContextThenInstance  -- (Context) => Class args
    , try pParenInstanceHead    -- (Class args) - no context, just parenthesized head
    , pBareInstance             -- Class args
    ]
  mWhere <- optional $ do
    void $ keyword Lex.KwWhere
    block pInstanceMember
  pure $ DefInstance ctx cls args (fromMaybe [] mWhere)

-- | Parse context followed by => and then instance head
-- The instance head can be bare or parenthesized: (Context) => Class args OR (Context) => (Class args)
pContextThenInstance :: Parser ([Located Pred], Located QualIdent, [LType])
pContextThenInstance = do
  ctx <- pContext
  void $ punct Lex.PunctFatArrow
  -- Instance head can be parenthesized or bare
  (cls, args) <- choice
    [ do  -- Parenthesized: (Class args)
        void $ punct Lex.PunctLParen
        cls <- qualConId
        args <- many pAtomicType
        void $ punct Lex.PunctRParen
        pure (cls, args)
    , do  -- Bare: Class args
        cls <- qualConId
        args <- many pAtomicType
        pure (cls, args)
    ]
  pure (ctx, cls, args)

-- | Parse parenthesized instance head: (Class args...)
-- This is NOT a context - it's just the instance head wrapped in parens
pParenInstanceHead :: Parser ([Located Pred], Located QualIdent, [LType])
pParenInstanceHead = do
  void $ punct Lex.PunctLParen
  cls <- qualConId
  args <- many pAtomicType
  void $ punct Lex.PunctRParen
  -- Make sure this is not followed by => (which would make it a context)
  notFollowedBy (punct Lex.PunctFatArrow)
  pure ([], cls, args)

-- | Parse bare instance head (no parentheses, no context)
pBareInstance :: Parser ([Located Pred], Located QualIdent, [LType])
pBareInstance = do
  cls <- qualConId
  args <- many pAtomicType
  pure ([], cls, args)

-- | Parse an instance member.
pInstanceMember :: Parser InstanceMember
pInstanceMember = choice
  [ try pInstanceTypeSig  -- Type signature: name :: type
  , pInstanceMethodImpl   -- Method implementation: name pats = expr
  ]

-- | Parse an instance method type signature.
pInstanceTypeSig :: Parser InstanceMember
pInstanceTypeSig = do
  name <- varIdOrOp
  void $ punct Lex.PunctDColon
  ty <- withSpan pQualType
  pure $ InstanceTypeSig name ty

-- | Parse an instance method implementation.
pInstanceMethodImpl :: Parser InstanceMember
pInstanceMethodImpl = do
  name <- varIdOrOp
  clauses <- some pClause
  pure $ InstanceMethod name clauses

-- | Parse a primitive declaration.
-- Handles:
--   primitive varId :: Type         (primitive value)
--   primitive type ConId :: Kind    (primitive type)
pPrimitiveDef :: Parser Definition
pPrimitiveDef = do
  void $ keyword Lex.KwPrimitive
  choice
    [ -- primitive type Name :: Kind
      do
        void $ keyword Lex.KwType
        name <- conId
        void $ punct Lex.PunctDColon
        kind <- withSpan pKind
        pure $ DefPrimitiveType name kind
    , -- primitive name :: Type
      do
        name <- varId
        void $ punct Lex.PunctDColon
        ty <- withSpan pQualType
        pure $ DefPrimitive name ty
    ]

-- | Parse a foreign import.
-- Grammar: foreign name :: type = "external_name"
-- Also supports port mapping: foreign name :: type = "external_name",("port1","port2",...)
pForeignDef :: Parser Definition
pForeignDef = do
  void $ keyword Lex.KwForeign
  name <- varId
  void $ punct Lex.PunctDColon
  ty <- withSpan pQualType
  -- The external name is optional, with an = before the string
  mStr <- optional $ do
    void $ punct Lex.PunctEqual
    s <- locVal <$> stringLit
    -- Optional port mapping: ,("port1","port2",...)
    void $ optional $ try $ do
      void $ punct Lex.PunctComma
      void $ punct Lex.PunctLParen
      void $ stringLit `sepBy` punct Lex.PunctComma
      void $ punct Lex.PunctRParen
    pure s
  let foreignStr = case mStr of
        Just (LitString s) -> Just s
        _ -> Nothing
  pure $ DefForeign name ty foreignStr

-- | Parse a value definition (function or constant).
-- Handles three forms:
--   1. name :: type (type signature only)
--   2. name pats [guards] = expr (standard function/value definition)
--   3. lhsPat op rhsPat [guards] = expr (infix operator definition)
pValueDef :: Parser Definition
pValueDef = try pInfixValueDef <|> pPrefixValueDef

-- | Parse a standard (prefix-style) value definition.
pPrefixValueDef :: Parser Definition
pPrefixValueDef = do
  name <- varIdOrOp
  -- Check for type signature
  mTy <- optional $ try $ do
    void $ punct Lex.PunctDColon
    withSpan pQualType
  -- Check for clauses
  clauses <- case mTy of
    Just _ty -> do
      -- After type sig, may have clauses
      mClauses <- optional $ many pClause
      pure $ fromMaybe [] mClauses
    Nothing -> do
      -- Must have at least one clause
      (:[]) <$> pClause
  pure $ DefValue name mTy clauses

-- | Parse an infix operator value definition.
-- Syntax: lhsPat op rhsPat [guards] = expr
-- E.g.: _ + x = _ defines (+) in infix style.
pInfixValueDef :: Parser Definition
pInfixValueDef = do
  start <- getPos
  lhs <- pAtomicPattern
  op <- infixOp
  rhs <- pAtomicPattern
  guard <- optional pGuard
  void $ punct Lex.PunctEqual
  body <- pExpr
  whereBinds <- pWhere
  end <- getPos
  let clause = Clause
        { clauseSpan = mergeSpans start end
        , clausePats = [lhs, rhs]
        , clauseGuard = guard
        , clauseBody = body
        , clauseWhere = whereBinds
        }
  pure $ DefValue op Nothing [clause]

-- | Parse a function clause.
pClause :: Parser Clause
pClause = do
  start <- getPos
  -- Parse patterns.  For infix operator definitions like `_ + x = ...`,
  -- we parse the left-hand pattern, consume the infix operator, then the
  -- right-hand pattern, discarding the operator (the name was already
  -- captured in pValueDef).
  pats <- choice
    [ try $ do
        -- Infix operator clause: lhsPat op rhsPat = ...
        lhs <- pAtomicPattern
        void infixOp
        rhs <- pAtomicPattern
        pure [lhs, rhs]
    , many pAtomicPattern
    ]
  guard <- optional pGuard
  void $ punct Lex.PunctEqual
  body <- pExpr
  whereBinds <- pWhere
  end <- getPos
  pure Clause
    { clauseSpan = mergeSpans start end
    , clausePats = pats
    , clauseGuard = guard
    , clauseBody = body
    , clauseWhere = whereBinds
    }

-- | Parse a guard (Bluespec uses 'when' keyword).
-- Grammar: when qual {, qual}
-- qual ::= exp | pat <- exp
pGuard :: Parser Guard
pGuard = do
  void $ keyword Lex.KwWhen
  pGuardQual `sepBy1` punct Lex.PunctComma

-- | Parse a single guard qualifier.
-- A qualifier is either a boolean expression or a pattern guard (pat <- exp).
pGuardQual :: Parser GuardQual
pGuardQual = try patGuard <|> boolGuard
  where
    -- Try pattern guard: pat <- exp
    patGuard = do
      pat <- pPattern
      void $ punct Lex.PunctLArrow
      PatGuard pat <$> pExpr
    -- Boolean guard: exp
    boolGuard = BoolGuard <$> pExpr

-- | Parse where clause.
pWhere :: Parser [LDefinition]
pWhere = do
  mWhere <- optional $ do
    void $ keyword Lex.KwWhere
    block pDefinition
  pure $ fromMaybe [] $ fmap (map (Located noSpan)) mWhere

--------------------------------------------------------------------------------
-- Type Parser
--------------------------------------------------------------------------------

-- | Parse a qualified type.
pQualType :: Parser QualType
pQualType = do
  mCtx <- optional $ try $ pContext <* punct Lex.PunctFatArrow
  ty <- pType
  pure QualType
    { qtPreds = fromMaybe [] mCtx
    , qtType = ty
    }

-- | Parse a type context.
pContext :: Parser [Located Pred]
pContext = choice
  [ do
      void $ punct Lex.PunctLParen
      ps <- pPred `sepBy` punct Lex.PunctComma
      void $ punct Lex.PunctRParen
      pure ps
  , (:[]) <$> pPred
  ]

-- | Parse a predicate.
pPred :: Parser (Located Pred)
pPred = withSpan $ do
  cls <- qualConId
  args <- many pAtomicType
  pure Pred
    { predClass = cls
    , predArgs = args
    }

-- | Parse a type.
pType :: Parser LType
pType = do
  t <- pBType
  mArr <- optional $ do
    void $ punct Lex.PunctArrow
    pType
  case mArr of
    Just t2 -> pure $ spanning t t2 (TArrow t t2)
    Nothing -> pure t

-- | Parse a type application sequence.
pBType :: Parser LType
pBType = do
  ts <- some pAtomicType
  case ts of
    [] -> fail "expected type"
    [t] -> pure t
    (t:ts') -> pure $ foldl (\a b -> spanning a b (TApp a b)) t ts'

-- | Parse an atomic type.
pAtomicType :: Parser LType
pAtomicType = choice
  [ pTyVar >>= \tv -> pure $ Located (locSpan tv) (TVar tv)
  , pTyCon
  , pTupleType
  , pListType
  , pNumType
  , pStringType
  , pParenType
  , pKindAnnotation
  ]

-- | Parse a type variable.
pTyVar :: Parser (Located TyVar)
pTyVar = do
  v <- varId
  pure $ Located (locSpan v) (TyVar (locVal v) Nothing)

-- | Parse a type constructor.
pTyCon :: Parser LType
pTyCon = do
  c <- qualConId
  pure $ Located (locSpan c) (TCon c)

-- | Parse a tuple type.
pTupleType :: Parser LType
pTupleType = do
  start <- punct Lex.PunctLParen
  ts <- pType `sepBy` punct Lex.PunctComma
  end <- punct Lex.PunctRParen
  case ts of
    [] -> pure $ Located (mergeSpans (spanOf start) (spanOf end)) (TTuple [])
    [t] -> pure t  -- Parenthesized type
    _ -> pure $ Located (mergeSpans (spanOf start) (spanOf end)) (TTuple ts)

-- | Parse a list type.
pListType :: Parser LType
pListType = do
  start <- punct Lex.PunctLBracket
  t <- pType
  end <- punct Lex.PunctRBracket
  pure $ Located (mergeSpans (spanOf start) (spanOf end)) (TList t)

-- | Parse a numeric type literal.
pNumType :: Parser LType
pNumType = do
  n <- intLit
  case locVal n of
    LitInt i _ -> pure $ Located (locSpan n) (TNum i)
    _ -> fail "expected numeric type"

-- | Parse a string type literal.
pStringType :: Parser LType
pStringType = do
  s <- stringLit
  case locVal s of
    LitString t -> pure $ Located (locSpan s) (TString t)
    _ -> fail "expected string type"

-- | Parse a parenthesized type.
pParenType :: Parser LType
pParenType = do
  void $ punct Lex.PunctLParen
  t <- pType
  void $ punct Lex.PunctRParen
  pure t

-- | Parse a kind annotation.
pKindAnnotation :: Parser LType
pKindAnnotation = do
  start <- punct Lex.PunctLParen
  t <- pType
  void $ punct Lex.PunctDColon
  k <- withSpan pKind
  end <- punct Lex.PunctRParen
  pure $ Located (mergeSpans (spanOf start) (spanOf end)) (TKind t k)

-- | Parse a kind.
pKind :: Parser Kind
pKind = do
  k1 <- pAtomicKind
  mArr <- optional $ do
    void $ punct Lex.PunctArrow
    pKind
  case mArr of
    Just k2 -> pure $ KArrow k1 k2
    Nothing -> pure k1

pAtomicKind :: Parser Kind
pAtomicKind = choice
  [ KNum <$ punct Lex.PunctHash                      -- # kind (numeric)
  , KString <$ dollarKind                            -- $ kind (string)
  , KStar <$ starKind                                -- * kind
  , do
      void $ punct Lex.PunctLParen
      k <- pKind
      void $ punct Lex.PunctRParen
      pure k
  ]

-- | Match the $ kind symbol (string kind)
dollarKind :: Parser ()
dollarKind = void $ MP.token test expected
  where
    test t = case Lex.tokKind t of
      Lex.TokVarSym "$" -> Just t
      _ -> Nothing
    expected = Set.singleton $ Label $ NE.fromList "$"

-- | Match the * kind symbol (can be TokVarSym "*" or TokConSym "*")
starKind :: Parser ()
starKind = void $ MP.token test expected
  where
    test t = case Lex.tokKind t of
      Lex.TokVarSym "*" -> Just t
      Lex.TokConSym "*" -> Just t
      _ -> Nothing
    expected = Set.singleton $ Label $ NE.fromList "*"

--------------------------------------------------------------------------------
-- Expression Parser
--------------------------------------------------------------------------------

-- | Parse an expression.
pExpr :: Parser LExpr
pExpr = do
  e <- pExprOps
  -- Check for type annotation: expr :: type
  mTy <- optional $ punct Lex.PunctDColon *> withSpan pQualType
  e' <- case mTy of
    Nothing -> pure e
    Just ty -> pure $ spanning e ty (ETypeSig e ty)
  -- Check for expression-level where clause: expr where { bindings }
  -- This is sugar for let { bindings } in expr (Cletrec in the reference)
  mWhere <- optional $ try $ do
    void $ keyword Lex.KwWhere
    block pDefinition
  case mWhere of
    Nothing -> pure e'
    Just defns ->
      pure $ Located (locSpan e') (EWhere e' defns)

-- | Parse expression with operators.
pExprOps :: Parser LExpr
pExprOps = do
  e <- pLExpr
  ops <- many $ do
    op <- anyOp
    e2 <- pLExpr
    pure (op, e2)
  pure $ resolveOps bluespecFixities e ops

-- | Parse a left-hand expression (lambda, let, if, case, etc.).
pLExpr :: Parser LExpr
pLExpr = choice
  [ pLambda
  , pLet
  , pLetSeq
  , pIf
  , pCase
  , pDo
  , pModule
  , pRules
  , pInterface
  , pFExpr
  ]

-- | Parse a lambda expression.
pLambda :: Parser LExpr
pLambda = do
  start <- punct Lex.PunctBackslash
  pats <- some pAtomicPattern
  void $ punct Lex.PunctArrow
  body <- pExpr
  pure $ Located (mergeSpans (spanOf start) (locSpan body)) (ELam pats body)

-- | Parse a let expression.
pLet :: Parser LExpr
pLet = do
  start <- keyword Lex.KwLet
  items <- block pLetItem
  void $ keyword Lex.KwIn
  body <- pExpr
  pure $ Located (mergeSpans (spanOf start) (locSpan body)) (ELet items body)

-- | Parse a letseq expression.
pLetSeq :: Parser LExpr
pLetSeq = do
  start <- keyword Lex.KwLetSeq
  items <- block pLetItem
  void $ keyword Lex.KwIn
  body <- pExpr
  pure $ Located (mergeSpans (spanOf start) (locSpan body)) (ELetSeq items body)

-- | Parse an if expression.
pIf :: Parser LExpr
pIf = do
  start <- keyword Lex.KwIf
  cond <- pExpr
  void $ keyword Lex.KwThen
  thenE <- pExpr
  void $ keyword Lex.KwElse
  elseE <- pExpr
  pure $ Located (mergeSpans (spanOf start) (locSpan elseE)) (EIf cond thenE elseE)

-- | Parse a case expression.
pCase :: Parser LExpr
pCase = do
  start <- keyword Lex.KwCase
  scrut <- pExpr
  void $ keyword Lex.KwOf
  alts <- block pAlt
  end <- getPos
  pure $ Located (mergeSpans (spanOf start) end) (ECase scrut alts)

-- | Parse a case alternative.
pAlt :: Parser Alt
pAlt = do
  start <- getPos
  pat <- pPattern
  guard <- optional pGuard
  void $ punct Lex.PunctArrow
  body <- pExpr
  end <- getPos
  pure Alt
    { altSpan = mergeSpans start end
    , altPat = pat
    , altGuard = guard
    , altBody = body
    }

-- | Parse a do/action/actionvalue expression.
-- All three are monadic block syntax.
pDo :: Parser LExpr
pDo = do
  start <- keyword Lex.KwDo <|> keyword Lex.KwAction <|> keyword Lex.KwActionValue
  stmts <- block pStmt
  end <- getPos
  pure $ Located (mergeSpans (spanOf start) end) (EDo (map (Located noSpan) stmts))

-- | Skip any inline pragmas (e.g., {-# hide #-}).
-- These can appear before statements and bindings.
-- Also consumes trailing virtual semicolon if present (from layout).
skipPragma :: Parser ()
skipPragma = void $ many $ do
  void $ tok Lex.TokPragmaStart
  -- Skip all tokens until pragma end
  void $ many $ MP.token testNotPragmaEnd Set.empty
  void $ tok Lex.TokPragmaEnd
  -- Consume optional trailing virtual semicolon (layout inserts this after pragma line)
  void $ optional $ tok Lex.TokVSemi
  where
    testNotPragmaEnd t = case Lex.tokKind t of
      Lex.TokPragmaEnd -> Nothing
      _ -> Just ()

-- | Parse a statement.
pStmt :: Parser Stmt
pStmt = do
  skipPragma  -- Allow pragma before statement
  choice
    [ StmtLet <$> (keyword Lex.KwLet *> block pLetItem)
    , StmtLetSeq <$> (keyword Lex.KwLetSeq *> block pLetItem)
    , try $ do
        pat <- pPattern
        mTy <- optional $ punct Lex.PunctDColon *> withSpan pQualType
        void $ punct Lex.PunctLArrow
        e <- pExpr
        pure $ StmtBind pat mTy e
    , try $ do
        lhs <- pExpr
        void $ punct Lex.PunctColonEq
        rhs <- pExpr
        pure $ StmtAssign lhs rhs
    , StmtExpr <$> pExpr
    ]

-- | Parse a let item (type signature or binding).
pLetItem :: Parser LetItem
pLetItem = choice
  [ try pLetTypeSig  -- Try type signature first (varId :: Type without =)
  , LetBind <$> pBinding  -- Otherwise it's a binding
  ]

-- | Parse a standalone type signature in a let block.
-- This matches: varId :: Type or (op) :: Type (not followed by =)
pLetTypeSig :: Parser LetItem
pLetTypeSig = do
  name <- varIdOrOp
  void $ punct Lex.PunctDColon
  ty <- withSpan pQualType
  -- Make sure there's no = following (that would be a shortDefn/binding)
  notFollowedBy (punct Lex.PunctEqual)
  pure $ LetTypeSig name ty

-- | Parse a binding.
-- Handles both pattern bindings like @(a, b) = expr@ and function-style
-- bindings like @f x y = expr@, and guarded bindings like @f x when guard = expr@.
pBinding :: Parser Binding
pBinding = try pInfixBinding <|> pPrefixBinding

pPrefixBinding :: Parser Binding
pPrefixBinding = do
  start <- getPos
  pat <- pPattern
  -- Try to parse additional atomic patterns for function-style bindings
  args <- many pAtomicPattern
  mTy <- optional $ try $ punct Lex.PunctDColon *> withSpan pQualType
  _mGuard <- optional pGuard
  void $ punct Lex.PunctEqual
  e <- pExpr
  end <- getPos
  pure Binding
    { bindSpan = mergeSpans start end
    , bindPat = pat
    , bindArgs = args
    , bindType = mTy
    , bindExpr = e
    }

pInfixBinding :: Parser Binding
pInfixBinding = do
  start <- getPos
  lhs <- pAtomicPattern
  op <- infixOp
  rhs <- pAtomicPattern
  _mGuard <- optional pGuard
  void $ punct Lex.PunctEqual
  e <- pExpr
  end <- getPos
  pure Binding
    { bindSpan = mergeSpans start end
    , bindPat = Located (locSpan op) (PVar op)
    , bindArgs = [lhs, rhs]
    , bindType = Nothing
    , bindExpr = e
    }

-- | Parse a module expression (either regular module or verilog module).
pModule :: Parser LExpr
pModule = do
  start <- keyword Lex.KwModule
  -- Check if this is a verilog module
  mVerilog <- optional $ keyword Lex.KwVerilog
  case mVerilog of
    Just _ -> pModuleVerilogBody start
    Nothing -> do
      stmts <- block pModuleStmt
      end <- getPos
      pure $ Located (mergeSpans (spanOf start) end) (EModule stmts)

-- | Parse the body of a verilog module (after 'module verilog').
-- Grammar: module verilog vModName [vParams] clkNames rstNames [vArgs]
--          '{' {fieldId [mult] '=' portSpec {portSpec} ';'} '}'
--          [schInfo]
pModuleVerilogBody :: Lex.Token -> Parser LExpr
pModuleVerilogBody startTok = do
  -- Parse the module name (an expression, typically a string literal)
  modName <- pAExpr

  -- Parse optional parameters: (exp, exp, ...) ,
  params <- pVParams <|> pure []

  -- Parse clock names (string literals)
  clocks <- pPortNames

  -- Parse reset names (string literals)
  resets <- pPortNames

  -- Parse optional arguments: ((portName, exp), ...)
  args <- pVArgs <|> pure []

  -- Parse method definitions block: { fieldId [mult] = portSpec ... ; ... }
  void lbrace
  methods <- pVerilogMethod `sepEndBy` semis
  void rbrace

  -- Parse optional scheduling info: [ ... ]
  sched <- optional pSchedInfo

  end <- getPos
  pure $ Located (mergeSpans (spanOf startTok) end) EModuleVerilog
    { vModName = modName
    , vModParams = params
    , vModClocks = clocks
    , vModResets = resets
    , vModArgs = args
    , vModMethods = methods
    , vModSched = sched
    }

-- | Parse verilog parameters: (exp, exp, ...) followed by comma
-- Grammar: '(' {exp ','} ')' ','
pVParams :: Parser [LExpr]
pVParams = try $ do
  void $ punct Lex.PunctLParen
  exprs <- pExpr `sepBy` punct Lex.PunctComma
  void $ punct Lex.PunctRParen
  -- The trailing comma is optional in our implementation
  void $ optional $ punct Lex.PunctComma
  pure exprs

-- | Parse port names (string literals).
-- Grammar: {portName ','}
pPortNames :: Parser [Text]
pPortNames = many pPortName
  where
    pPortName = do
      s <- stringLit
      void $ optional $ punct Lex.PunctComma
      case locVal s of
        LitString t -> pure t
        _ -> fail "expected string literal for port name"

-- | Parse verilog arguments: ((portName, exp), ...)
-- Grammar: '(' {(portName ',' exp)} ')'
pVArgs :: Parser [(Text, LExpr)]
pVArgs = try $ do
  void $ punct Lex.PunctLParen
  args <- pVArg `sepBy` punct Lex.PunctComma
  void $ punct Lex.PunctRParen
  pure args
  where
    pVArg = do
      void $ punct Lex.PunctLParen
      name <- stringLit
      void $ punct Lex.PunctComma
      e <- pExpr
      void $ punct Lex.PunctRParen
      case locVal name of
        LitString t -> pure (t, e)
        _ -> fail "expected string literal for port name"

-- | Parse a verilog method definition.
-- Grammar: fieldId [mult] '=' portSpec {portSpec}
pVerilogMethod :: Parser VerilogMethod
pVerilogMethod = do
  fieldId <- varId
  -- Optional multiplicity: [n]
  mult <- optional $ do
    void $ punct Lex.PunctLBracket
    n <- intLit
    void $ punct Lex.PunctRBracket
    case locVal n of
      LitInt i _ -> pure (fromIntegral i)
      _ -> fail "expected integer for multiplicity"
  void $ punct Lex.PunctEqual
  -- Parse port specifications (at least one)
  ports <- some pPortSpec
  pure VerilogMethod
    { vmFieldId = fieldId
    , vmMult = mult
    , vmPorts = ports
    }

-- | Parse a port specification.
-- Grammar: portName [{portProp ','}]
-- A portName is a string literal, optionally followed by {prop} or {prop,prop,...}
pPortSpec :: Parser PortSpec
pPortSpec = do
  name <- stringLit
  -- Optional properties: {prop, prop, ...}
  props <- pPortProps <|> pure []
  case locVal name of
    LitString t -> pure PortSpec { psName = t, psProps = props }
    _ -> fail "expected string literal for port name"

-- | Parse port properties: {prop, prop, ...}
pPortProps :: Parser [PortProp]
pPortProps = do
  void lbrace
  props <- pPortProp `sepBy` punct Lex.PunctComma
  void rbrace
  pure props

-- | Parse a single port property.
pPortProp :: Parser PortProp
pPortProp = choice
  [ PPReg <$ varIdNamed "reg"
  , PPConst <$ varIdNamed "const"
  , PPUnused <$ varIdNamed "unused"
  , PPInHigh <$ varIdNamed "inhigh"
  ]

-- | Parse scheduling information.
-- Grammar: '[' {schMeths schOp schMeths ','} ']'
pSchedInfo :: Parser SchedInfo
pSchedInfo = do
  void $ punct Lex.PunctLBracket
  entries <- pSchedEntry `sepBy` punct Lex.PunctComma
  void $ punct Lex.PunctRBracket
  pure $ SchedInfo entries

-- | Parse a scheduling entry.
-- Grammar: schMeths schOp schMeths
pSchedEntry :: Parser SchedEntry
pSchedEntry = do
  left <- pSchedMeths
  op <- pSchedOp
  right <- pSchedMeths
  pure SchedEntry { seLeft = left, seOp = op, seRight = right }

-- | Parse scheduling methods (single or list).
-- Grammar: fieldId | '[' {fieldId ','} ']'
pSchedMeths :: Parser [Located Ident]
pSchedMeths = pSchedMethList <|> ((:[]) <$> varId)
  where
    pSchedMethList = do
      void $ punct Lex.PunctLBracket
      meths <- varId `sepBy` punct Lex.PunctComma
      void $ punct Lex.PunctRBracket
      pure meths

-- | Parse a scheduling operator (any operator symbol).
pSchedOp :: Parser SchedOp
pSchedOp = MP.token test expected
  where
    test t = case Lex.tokKind t of
      Lex.TokVarSym op -> Just op
      Lex.TokConSym op -> Just op
      _ -> Nothing
    expected = Set.singleton $ Label $ NE.fromList "operator"

-- | Parse a module statement.
pModuleStmt :: Parser ModuleStmt
pModuleStmt = do
  skipPragma  -- Allow pragma before statement (e.g., {-# hide #-})
  choice
    [ MStmtLet <$> (keyword Lex.KwLet *> block pLetItem)
    , MStmtLetSeq <$> (keyword Lex.KwLetSeq *> block pLetItem)
    , try $ do
        -- Pattern bind: pat :: T <- expr  or  pat <- expr
        pat <- pPattern
        mTy <- optional $ punct Lex.PunctDColon *> pType
        void $ punct Lex.PunctLArrow
        e <- pExpr
        pure $ MStmtBind pat mTy e
    , try $ do
        void $ keyword Lex.KwInterface
        void $ punct Lex.PunctLParen
        exprs <- sepBy pExpr (punct Lex.PunctComma)
        void $ punct Lex.PunctRParen
        pure $ MStmtTupleInterface exprs
    , try $ do
        void $ keyword Lex.KwInterface
        -- MStmtInterface is for anonymous interface blocks (interface { ... })
        -- Named interfaces (interface Foo { ... }) are parsed as pExpr
        fields <- block pInterfaceField
        pure $ MStmtInterface fields
    , MStmtExpr <$> pExpr
    ]

-- | Parse a rules expression.
pRules :: Parser LExpr
pRules = do
  start <- keyword Lex.KwRules
  rules <- block pRule
  end <- getPos
  pure $ Located (mergeSpans (spanOf start) end) (ERules rules)

-- | Parse a rule.
-- According to BH_lang.tex: rule assertions come *before* the rule they modify.
-- Grammar: ruleAssert [;] rule
--          [ruleLabel :] when guard ==> exp
pRule :: Parser (Located Rule)
pRule = withSpan $ do
  start <- getPos
  -- Parse pragmas first (they precede the rule they modify)
  pragmas <- many pRulePragma
  -- Then parse optional rule name (label): any atomic expression followed by ':'
  -- This covers static strings ("foo":), identifiers (foo:), and dynamic
  -- expressions (("prefix" +++ integerToString i):)
  mName <- optional $ try $ do
    e <- pAExpr
    void $ punct Lex.PunctColon
    pure e
  -- Parse rule body: either "when guard ==> expr" or "when guard rules { ... }"
  -- or just "==> expr" (no guard), or a nested "rules { ... }" with optional guard
  (mCond, body) <- choice
    [ -- "when guard rules { ... }" -- nested rules
      try $ do
        guard <- pGuard
        nestedStart <- keyword Lex.KwRules
        nestedRules <- block pRule
        nestedEnd <- getPos
        let nestedExpr = Located (mergeSpans (spanOf nestedStart) nestedEnd) (ERules nestedRules)
        pure (Just guard, nestedExpr)
    , -- "when guard ==> expr" -- standard rule with guard
      do
        guard <- pGuard
        void $ punct Lex.PunctRuleArrow
        expr <- pExpr
        pure (Just guard, expr)
    , -- "==> expr" -- rule without guard
      do
        void $ punct Lex.PunctRuleArrow
        expr <- pExpr
        pure (Nothing, expr)
    , -- "rules { ... }" -- nested rules without guard
      do
        nestedStart <- keyword Lex.KwRules
        nestedRules <- block pRule
        nestedEnd <- getPos
        let nestedExpr = Located (mergeSpans (spanOf nestedStart) nestedEnd) (ERules nestedRules)
        pure (Nothing, nestedExpr)
    ]
  end <- getPos
  pure Rule
    { ruleSpan = mergeSpans start end
    , ruleName = mName
    , rulePragmas = pragmas
    , ruleCond = mCond
    , ruleBody = body
    }

-- | Parse a rule pragma.
-- Supports both shorthand pragmas (e.g., {-# fire_when_enabled #-}) and
-- ASSERT-style pragmas (e.g., {-# ASSERT fire when enabled #-}).
-- Per BH_lang.tex grammar: ruleAssert [;] rule
-- The optional semicolon allows multiple pragmas to be consumed by 'many'.
pRulePragma :: Parser RulePragma
pRulePragma = do
  void $ tok Lex.TokPragmaStart
  pragma <- choice
    [ RPNoImplicitConditions <$ varIdNamed "no_implicit_conditions"
    , RPFireWhenEnabled <$ varIdNamed "fire_when_enabled"
    , RPCanScheduleFirst <$ varIdNamed "can_schedule_first"
    , RPClockCrossingRule <$ varIdNamed "clock_crossing_rule"
    , RPAggressiveImplicitConditions <$ varIdNamed "aggressive_implicit_conditions"
    , RPNoWarn <$ varIdNamed "no_warn"
    , RPHide <$ varIdNamed "hide"
    -- ASSERT-style pragmas: {-# ASSERT fire when enabled #-}
    --                       {-# ASSERT no implicit conditions #-}
    , do
        void $ conIdNamed "ASSERT"
        choice
          [ RPFireWhenEnabled <$ (varIdNamed "fire" *> keyword Lex.KwWhen *> varIdNamed "enabled")
          , RPNoImplicitConditions <$ (varIdNamed "no" *> varIdNamed "implicit" *> varIdNamed "conditions")
          ]
    ]
  void $ tok Lex.TokPragmaEnd
  -- Consume optional semicolon after pragma (per grammar: ruleAssert [;] rule)
  -- This is needed because layout rules insert virtual semicolons between
  -- pragmas on separate lines.
  void $ optional semi
  pure pragma

-- | Match a specific constructor name.
conIdNamed :: Text -> Parser Lex.Token
conIdNamed name = MP.token test expected
  where
    test t = case Lex.tokKind t of
      Lex.TokConId n | n == name -> Just t
      _ -> Nothing
    expected = Set.singleton $ Label $ NE.fromList $ T.unpack name

-- | Parse an interface expression.
pInterface :: Parser LExpr
pInterface = do
  start <- keyword Lex.KwInterface
  mName <- optional qualConId
  fields <- pInterfaceBody
  end <- getPos
  pure $ Located (mergeSpans (spanOf start) end) (EInterface mName fields)

-- | Parse interface body (list of field bindings).
pInterfaceBody :: Parser [InterfaceField]
pInterfaceBody = block pInterfaceField <|> pure []

pInterfaceField :: Parser InterfaceField
pInterfaceField = try pInterfaceFieldTypeSig <|> pInterfaceFieldDef

-- | Parse a type signature in an interface body: name :: type
-- Used in inline interface expressions like:
--   interface Waiter
--     wait :: Action
--     wait = noAction when condition
pInterfaceFieldTypeSig :: Parser InterfaceField
pInterfaceFieldTypeSig = do
  start <- getPos
  name <- varIdOrOp
  void $ punct Lex.PunctDColon
  ty <- withSpan pQualType
  end <- getPos
  -- Return as a field with no value (just a type annotation; ignored at parse level)
  pure InterfaceField
    { ifSpan = mergeSpans start end
    , ifName = name
    , ifPats = []
    , ifValue = Located (mergeSpans start end) (EVar (fmap (QualIdent Nothing) name))
    , ifWhen = Nothing
    }

-- | Parse a field definition in an interface body: name pats = expr [when ...]
pInterfaceFieldDef :: Parser InterfaceField
pInterfaceFieldDef = do
  start <- getPos
  name <- varIdOrOp
  pats <- many pAtomicPattern
  void $ punct Lex.PunctEqual
  e <- pExpr
  -- The when-guard can be a simple expression or a pattern guard (pat <- expr)
  mWhen <- optional pGuard
  end <- getPos
  pure InterfaceField
    { ifSpan = mergeSpans start end
    , ifName = name
    , ifPats = pats
    , ifValue = e
    , ifWhen = mWhen
    }

-- | Parse function application.
pFExpr :: Parser LExpr
pFExpr = do
  f <- pAExpr
  args <- many pAExpr
  case args of
    [] -> pure f
    _ -> pure $ foldl (\a b -> spanning a b (EApp a b)) f args

-- | Parse an atomic expression.
pAExpr :: Parser LExpr
pAExpr = do
  e <- pAExpr'
  -- Handle field access, record update, and bit selection
  suffixes <- many pSuffix
  pure $ foldl applySuffix e suffixes
  where
    applySuffix e (SuffixField fld) = spanning e fld (EFieldAccess e fld)
    applySuffix e (SuffixRecordUpd binds) = Located (locSpan e) (ERecordUpd e binds)
    applySuffix e (SuffixBitSelect hi lo) = spanning e lo (EBitSelect e hi lo)

-- | Suffix types for postfix operators.
data Suffix
  = SuffixField (Located Ident)
  | SuffixRecordUpd [FieldBind]
  | SuffixBitSelect LExpr LExpr

pSuffix :: Parser Suffix
pSuffix = choice
  [ SuffixField <$> (punct Lex.PunctDot *> (varId <|> ((\v -> Located (locSpan v) (VarId (identText (locVal v)))) <$> conId)))
  , SuffixRecordUpd <$> (lbrace *> pFieldBind `sepEndBy` semis <* rbrace)
  , try pBitSelect  -- Bit selection: e[hi:lo]
  ]

-- | Parse bit selection suffix: [hi:lo]
pBitSelect :: Parser Suffix
pBitSelect = do
  void $ punct Lex.PunctLBracket
  hi <- pExpr
  void $ punct Lex.PunctColon
  lo <- pExpr
  void $ punct Lex.PunctRBracket
  pure $ SuffixBitSelect hi lo

-- | Parse atomic expression without suffixes.
-- Includes do/if/case/let/lambda so they can be function arguments.
pAExpr' :: Parser LExpr
pAExpr' = choice
  [ pVar
  , pCon
  , pLitExpr
  , pValueOf
  , pStringOf
  , pPrimOp
  , pParenExpr
  , pList
  , pRecord
  , pDo
  , pIf
  , pCase
  , pLet
  , pLetSeq
  , pLambda
  ]

-- | Parse a variable.
pVar :: Parser LExpr
pVar = do
  v <- qualVarId
  pure $ Located (locSpan v) (EVar v)

-- | Parse a constructor.
pCon :: Parser LExpr
pCon = do
  c <- qualConId
  pure $ Located (locSpan c) (ECon c)

-- | Parse a literal.
pLitExpr :: Parser LExpr
pLitExpr = do
  l <- literal
  pure $ Located (locSpan l) (ELit l)

-- | Parse valueOf.
pValueOf :: Parser LExpr
pValueOf = do
  start <- keyword Lex.KwValueOf
  ty <- pAtomicType
  pure $ Located (mergeSpans (spanOf start) (locSpan ty)) (EValueOf ty)

-- | Parse stringOf.
pStringOf :: Parser LExpr
pStringOf = do
  start <- keyword Lex.KwStringOf
  ty <- pAtomicType
  pure $ Located (mergeSpans (spanOf start) (locSpan ty)) (EStringOf ty)

-- | Parse primitive operation ($display, etc.).
pPrimOp :: Parser LExpr
pPrimOp = do
  v <- MP.token test expected
  args <- many pAExpr
  pure $ Located (locSpan v) (EPrim (identText $ locVal v) args)
  where
    test t = case Lex.tokKind t of
      Lex.TokVarId name | "$" `T.isPrefixOf` name -> Just $ Located (Lex.tokSpan t) (VarId name)
      _ -> Nothing
    expected = Set.singleton $ Label $ NE.fromList "primitive"

-- | Parse a list expression.
pList :: Parser LExpr
pList = do
  start <- punct Lex.PunctLBracket
  es <- pExpr `sepBy` punct Lex.PunctComma
  end <- punct Lex.PunctRBracket
  pure $ Located (mergeSpans (spanOf start) (spanOf end)) (EList es)

-- | Parse a record construction.
pRecord :: Parser LExpr
pRecord = do
  con <- qualConId
  void lbrace
  binds <- pFieldBind `sepEndBy` semis
  void rbrace
  pure $ Located (locSpan con) (ERecord con binds)

-- | Parse a field binding.
pFieldBind :: Parser FieldBind
pFieldBind = do
  start <- getPos
  -- Accept qualified field names (e.g. Module.field = value), discard qualifier
  name <- fmap (fmap qualIdent) qualVarId
  void $ punct Lex.PunctEqual
  e <- pExpr
  end <- getPos
  pure FieldBind
    { fbSpan = mergeSpans start end
    , fbName = name
    , fbValue = e
    }

-- | Parse a parenthesized expression, tuple, field section, or operator section.
-- (.field) is syntactic sugar for (\x -> x.field)
-- (op) is an operator used as a value, e.g., (++) for zipWith (++) xs ys
-- This handles all (-starting expressions: (), (e), (e1, e2, ...), (.field), (op)
pParenExpr :: Parser LExpr
pParenExpr = do
  start <- punct Lex.PunctLParen
  -- Check for field section: (.field)
  mFieldSection <- optional $ try $ do
    void $ punct Lex.PunctDot
    field <- varId
    pure field
  case mFieldSection of
    Just field -> do
      end <- punct Lex.PunctRParen
      pure $ Located (mergeSpans (spanOf start) (spanOf end)) (EFieldSection field)
    Nothing -> do
      -- Check for operator section: (op) where op is a symbolic operator
      mOpSection <- optional $ try $ do
        op <- opSym
        end <- punct Lex.PunctRParen
        pure (op, end)
      case mOpSection of
        Just (op, end) -> do
          -- Convert operator to a variable reference
          let qIdent = case locVal op of
                OpSym t -> QualIdent Nothing (VarId t)
                OpIdent i -> locVal i
          pure $ Located (mergeSpans (spanOf start) (spanOf end)) (EVar (Located (locSpan op) qIdent))
        Nothing -> do
          -- Parse comma-separated expressions (handles (), (e), and (e1, e2, ...))
          es <- pExpr `sepBy` punct Lex.PunctComma
          end <- punct Lex.PunctRParen
          let sp = mergeSpans (spanOf start) (spanOf end)
          pure $ case es of
            []  -> Located sp (ETuple [])
            [e] -> Located sp (EParens e)
            _   -> Located sp (ETuple es)

--------------------------------------------------------------------------------
-- Pattern Parser
--------------------------------------------------------------------------------

-- | Parse a pattern.
pPattern :: Parser LPattern
pPattern = do
  p <- pLPattern
  mOp <- optional $ do
    op <- opSym
    p2 <- pPattern
    pure (op, p2)
  case mOp of
    Just (op, p2) -> pure $ spanning p p2 (PInfix p op p2)
    Nothing -> pure p

-- | Parse a left pattern (constructor application or record pattern).
-- Handles both: Con p1 p2 ... (positional) and Con { field = pat, ... } (labeled)
pLPattern :: Parser LPattern
pLPattern = do
  mp <- optional $ try $ do
    c <- qualConId
    -- Check if this is a record pattern (followed by {)
    mRec <- optional $ do
      void lbrace
      fields <- pFieldPat `sepEndBy` pFieldPatSep
      void rbrace
      pure fields
    case mRec of
      Just fields -> pure $ Left (c, fields)  -- Record pattern
      Nothing -> do
        -- Positional constructor pattern
        ps <- many pAtomicPattern
        pure $ Right (c, ps)
  case mp of
    Just (Left (c, fields)) -> pure $ Located (locSpan c) (PRecord c fields)
    Just (Right (c, ps)) -> pure $ Located (locSpan c) (PCon c ps)
    Nothing -> pAtomicPattern

-- | Parse separator between field patterns (comma or semicolon).
-- In record patterns, both commas and semicolons are accepted as separators.
-- Multiple consecutive semicolons are allowed (e.g., ;;).
pFieldPatSep :: Parser ()
pFieldPatSep = void (punct Lex.PunctComma) <|> semis

-- | Parse an atomic pattern.
pAtomicPattern :: Parser LPattern
pAtomicPattern = choice
  [ pVarPat
  , pWildPat
  , pLitPat
  , pConPat
  , try pOpVarPat   -- (op) as var pattern - before pTuplePat!
  , pTuplePat
  , pListPat
  , pParenPat
  ]

-- | Parse a parenthesized operator as a variable pattern: (<=), (+), etc.
pOpVarPat :: Parser LPattern
pOpVarPat = do
  v <- parenOpAsId
  pure $ Located (locSpan v) (PVar v)

-- | Parse a variable pattern (possibly with as-pattern).
pVarPat :: Parser LPattern
pVarPat = do
  v <- varId
  mAs <- optional $ do
    void $ punct Lex.PunctAt
    pAtomicPattern
  case mAs of
    Just p -> pure $ spanning v p (PAs v p)
    Nothing -> pure $ Located (locSpan v) (PVar v)

-- | Parse wildcard pattern.
pWildPat :: Parser LPattern
pWildPat = do
  t <- punct Lex.PunctUnderscore
  pure $ Located (spanOf t) PWild

-- | Parse literal pattern.
pLitPat :: Parser LPattern
pLitPat = do
  l <- literal
  pure $ Located (locSpan l) (PLit l)

-- | Parse constructor pattern (nullary).
pConPat :: Parser LPattern
pConPat = do
  c <- qualConId
  mRec <- optional $ do
    void lbrace
    fields <- pFieldPat `sepEndBy` pFieldPatSep
    void rbrace
    pure fields
  case mRec of
    Just fields -> pure $ Located (locSpan c) (PRecord c fields)
    Nothing -> pure $ Located (locSpan c) (PCon c [])

-- | Parse a field pattern.
-- Grammar: fieldId = pat | fieldId (shorthand for fieldId = fieldId)
-- Also accepts qualified field names (Module.field = pat), discarding the qualifier.
pFieldPat :: Parser (Located Ident, LPattern)
pFieldPat = do
  -- Accept qualified field names (e.g. Module.field = pat), discard qualifier
  name <- fmap (fmap qualIdent) qualVarId
  -- Check if there's an explicit pattern (fieldId = pat) or shorthand (fieldId)
  mPat <- optional $ do
    void $ punct Lex.PunctEqual
    pPattern
  case mPat of
    Just p -> pure (name, p)
    -- Shorthand: fieldId means fieldId = fieldId (bind to a variable with same name)
    Nothing -> pure (name, Located (locSpan name) (PVar name))

-- | Parse tuple pattern.
pTuplePat :: Parser LPattern
pTuplePat = do
  start <- punct Lex.PunctLParen
  ps <- pPattern `sepBy` punct Lex.PunctComma
  end <- punct Lex.PunctRParen
  let sp = mergeSpans (spanOf start) (spanOf end)
  case ps of
    [] -> pure $ Located sp (PTuple [])
    [p] -> pure $ Located sp (PParens p)
    _ -> pure $ Located sp (PTuple ps)

-- | Parse list pattern.
pListPat :: Parser LPattern
pListPat = do
  start <- punct Lex.PunctLBracket
  ps <- pPattern `sepBy` punct Lex.PunctComma
  end <- punct Lex.PunctRBracket
  pure $ Located (mergeSpans (spanOf start) (spanOf end)) (PList ps)

-- | Parse parenthesized pattern.
pParenPat :: Parser LPattern
pParenPat = do
  start <- punct Lex.PunctLParen
  p <- pPattern
  end <- punct Lex.PunctRParen
  pure $ Located (mergeSpans (spanOf start) (spanOf end)) (PParens p)

--------------------------------------------------------------------------------
-- Top-level Parsing Functions
--------------------------------------------------------------------------------

-- | Parse a complete package.
parsePackage :: Text -> Text -> Either ParseError Package
parsePackage file input = do
  ts <- first (const $ bundleError "Lexer error") $ Lex.tokenize file input
  let ts' = processLayout ts
  parse pPackage (T.unpack file) (Lex.TokenStream ts')
  where
    bundleError msg = ParseErrorBundle
      { bundleErrors = pure $ FancyError 0 (Set.singleton $ ErrorFail msg)
      , bundlePosState = PosState
          { pstateInput = Lex.TokenStream []
          , pstateOffset = 0
          , pstateSourcePos = initialPos (T.unpack file)
          , pstateTabWidth = defaultTabWidth
          , pstateLinePrefix = ""
          }
      }
    first f (Left e) = Left (f e)
    first _ (Right a) = Right a

-- | Parse a single expression.
parseExpr :: Text -> Text -> Either ParseError LExpr
parseExpr file input = do
  ts <- first (const $ bundleError "Lexer error") $ Lex.tokenize file input
  let ts' = processLayout ts
  parse pExpr (T.unpack file) (Lex.TokenStream ts')
  where
    bundleError msg = ParseErrorBundle
      { bundleErrors = pure $ FancyError 0 (Set.singleton $ ErrorFail msg)
      , bundlePosState = PosState
          { pstateInput = Lex.TokenStream []
          , pstateOffset = 0
          , pstateSourcePos = initialPos (T.unpack file)
          , pstateTabWidth = defaultTabWidth
          , pstateLinePrefix = ""
          }
      }
    first f (Left e) = Left (f e)
    first _ (Right a) = Right a

-- | Parse a single type.
parseType :: Text -> Text -> Either ParseError LType
parseType file input = do
  ts <- first (const $ bundleError "Lexer error") $ Lex.tokenize file input
  let ts' = processLayout ts
  parse pType (T.unpack file) (Lex.TokenStream ts')
  where
    bundleError msg = ParseErrorBundle
      { bundleErrors = pure $ FancyError 0 (Set.singleton $ ErrorFail msg)
      , bundlePosState = PosState
          { pstateInput = Lex.TokenStream []
          , pstateOffset = 0
          , pstateSourcePos = initialPos (T.unpack file)
          , pstateTabWidth = defaultTabWidth
          , pstateLinePrefix = ""
          }
      }
    first f (Left e) = Left (f e)
    first _ (Right a) = Right a

-- | Parse a file from disk.
parseFile :: FilePath -> IO (Either ParseError Package)
parseFile path = do
  content <- TIO.readFile path
  pure $ parsePackage (T.pack path) content

-- | Parse a file, auto-dispatching on extension (.bs -> Classic, .bsv -> BSV).
parseAuto :: FilePath -> Text -> Either ParseError Package
parseAuto fp src
  | takeExtension fp == ".bsv" = BSV.parseBSVPackage (T.pack fp) src
  | otherwise                  = parsePackage (T.pack fp) src

-- | Like 'parseAuto', but uses error recovery to always return a (possibly
-- partial) 'Package' along with any parse errors. Intended for the LSP.
--
-- Returns @(pkg, Nothing)@ on clean success, @(pkg, Just bundle)@ on error.
-- The package is always non-empty (may be a partial AST for BSV files).
parseAutoRecovering
  :: FilePath
  -> Text
  -> (Package, Maybe ParseError)
parseAutoRecovering fp src
  | takeExtension fp == ".bsv" = BSV.parseBSVPackageRecovering (T.pack fp) src
  | otherwise                  =
      -- For Classic, fall back to strict parse for now.
      case parsePackage (T.pack fp) src of
        Right pkg  -> (pkg, Nothing)
        Left bundle ->
          ( Package noSpan (Located noSpan (ModuleId "Main")) Nothing [] [] []
          , Just bundle
          )
