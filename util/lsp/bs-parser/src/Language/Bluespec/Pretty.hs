-- | Pretty printer for Bluespec Classic AST.
module Language.Bluespec.Pretty
  ( -- * Pretty printing
    prettyPackage
  , prettyExpr
  , prettyType
  , prettyPattern
  , prettyDefinition

    -- * Rendering
  , renderPretty
  , renderCompact
  ) where

import Data.Maybe (catMaybes, maybeToList)
import Data.Text (Text)
import qualified Data.Text as T
import Prettyprinter
import Prettyprinter.Render.Text (renderStrict)

import Language.Bluespec.Position
import Language.Bluespec.Syntax

--------------------------------------------------------------------------------
-- Rendering
--------------------------------------------------------------------------------

-- | Render a document to text with a given width.
renderPretty :: Int -> Doc ann -> Text
renderPretty width doc = renderStrict (layoutPretty opts doc)
  where
    opts = LayoutOptions (AvailablePerLine width 1.0)

-- | Render a document compactly.
renderCompact :: Doc ann -> Text
renderCompact doc = renderStrict (layoutCompact doc)

--------------------------------------------------------------------------------
-- Package Printing
--------------------------------------------------------------------------------

-- | Pretty print a package.
prettyPackage :: Package -> Doc ann
prettyPackage pkg = vsep
  [ "package" <+> prettyModuleId (locVal $ pkgName pkg) <+> exports <+> "where"
  , mempty
  , vsep (map prettyImport (pkgImports pkg))
  , mempty
  , vsep (map prettyFixityDecl (pkgFixity pkg))
  , mempty
  , vsep (punctuate line (map prettyLDefinition (pkgDefns pkg)))
  ]
  where
    exports = case pkgExports pkg of
      Nothing -> mempty
      Just es -> parens (hsep $ punctuate comma $ map (prettyExport . locVal) es)

prettyModuleId :: ModuleId -> Doc ann
prettyModuleId (ModuleId t) = pretty t

prettyExport :: Export -> Doc ann
prettyExport = \case
  ExportVar i -> prettyIdent i
  ExportType i msubs -> prettyIdent i <> case msubs of
    Nothing -> mempty
    Just [] -> "(..)"
    Just subs -> parens (hsep $ punctuate comma $ map prettyIdent subs)
  ExportModule m -> "module" <+> prettyModuleId m

prettyImport :: Located Import -> Doc ann
prettyImport (Located _ imp) = hsep $ catMaybes
  [ Just "import"
  , if importQualified imp then Just "qualified" else Nothing
  , Just $ prettyModuleId (importModule imp)
  , ("as" <+>) . prettyModuleId <$> importAs imp
  , prettyImportSpec <$> importSpec imp
  ]

prettyImportSpec :: ImportSpec -> Doc ann
prettyImportSpec = \case
  ImportOnly es -> parens (hsep $ punctuate comma $ map (prettyExport . locVal) es)
  ImportHiding es -> "hiding" <+> parens (hsep $ punctuate comma $ map (prettyExport . locVal) es)

prettyFixityDecl :: Located FixityDecl -> Doc ann
prettyFixityDecl (Located _ fd) = hsep
  [ prettyFixityDir (fixDir $ fixDeclFixity fd)
  , pretty (fixPrec $ fixDeclFixity fd)
  , hsep $ punctuate comma $ map (prettyOp . locVal) (fixDeclOps fd)
  ]

prettyFixityDir :: FixityDir -> Doc ann
prettyFixityDir = \case
  InfixL -> "infixl"
  InfixR -> "infixr"
  InfixN -> "infix"

--------------------------------------------------------------------------------
-- Definition Printing
--------------------------------------------------------------------------------

prettyLDefinition :: LDefinition -> Doc ann
prettyLDefinition = prettyDefinition . locVal

-- | Pretty print a definition.
prettyDefinition :: Definition -> Doc ann
prettyDefinition = \case
  DefValue name mTy clauses -> vsep $ catMaybes
    [ (\ty -> prettyLIdent name <+> "::" <+> prettyQualType (locVal ty)) <$> mTy
    , if null clauses then Nothing else Just $ vsep (map (prettyClause (locVal name)) clauses)
    ]

  DefTypeSig name ty ->
    prettyLIdent name <+> "::" <+> prettyQualType (locVal ty)

  DefType name mKind tvars ty ->
    "type" <+> prettyTypeName name mKind <+> hsep (map prettyLTyVar tvars) <+> "=" <+> prettyLType ty

  DefData name mKind tvars constrs derivs -> vsep
    [ "data" <+> prettyTypeName name mKind <+> hsep (map prettyLTyVar tvars) <+> "="
    , indent 2 $ vsep $ punctuate " |" $ map (prettyConstructor . locVal) constrs
    , prettyDerivings derivs
    ]

  DefInterface name tvars fields derivs -> vsep
    [ "interface" <+> prettyLIdent name <+> hsep (map prettyLTyVar tvars) <+> "="
    , indent 2 $ vsep $ map (prettyField . locVal) fields
    , prettyDerivings derivs
    ]

  DefClass incoh ctx name tvars fundeps members -> vsep
    [ classKw <+> prettyContext ctx <+> prettyLIdent name <+>
      hsep (map prettyLTyVar tvars) <+> prettyFunDeps fundeps <+> "where"
    , indent 2 $ vsep $ map prettyClassMember members
    ]
    where
      classKw = case incoh of
        Nothing    -> "class"
        Just False -> "class coherent"
        Just True  -> "class incoherent"

  DefInstance ctx cls args members -> vsep
    [ "instance" <+> prettyContext ctx <+> prettyQualIdent (locVal cls) <+>
      hsep (map prettyLType args) <+> "where"
    , indent 2 $ vsep $ map prettyInstanceMember members
    ]

  DefPrimitive name ty ->
    "primitive" <+> prettyLIdent name <+> "::" <+> prettyQualType (locVal ty)

  DefPrimitiveType name kind ->
    "primitive type" <+> prettyLIdent name <+> "::" <+> prettyKind (locVal kind)

  DefForeign name ty mStr -> hsep $ catMaybes
    [ Just "foreign"
    , Just $ prettyLIdent name
    , Just "::"
    , Just $ prettyQualType (locVal ty)
    , (dquotes . pretty) <$> mStr
    ]

  DefPragma pragma ->
    "{-#" <+> pretty (tlpKind pragma) <+>
    maybe emptyDoc prettyLIdent (tlpName pragma) <+>
    pretty (tlpContent pragma) <+> "#-}"

prettyClause :: Ident -> Clause -> Doc ann
prettyClause name cl =
  prettyIdent name <+>
  hsep (map prettyLPattern (clausePats cl)) <>
  maybe mempty prettyGuard (clauseGuard cl) <+>
  "=" <+>
  prettyLExpr (clauseBody cl) <>
  prettyWhere (clauseWhere cl)

prettyGuard :: Guard -> Doc ann
prettyGuard quals = " when" <+> hsep (punctuate comma (map prettyGuardQual quals))

prettyGuardQual :: GuardQual -> Doc ann
prettyGuardQual = \case
  BoolGuard e -> prettyLExpr e
  PatGuard p e -> prettyLPattern p <+> "<-" <+> prettyLExpr e

prettyWhere :: [LDefinition] -> Doc ann
prettyWhere [] = mempty
prettyWhere defs = line <> indent 2 (vsep
  [ "where"
  , indent 2 $ vsep $ map prettyLDefinition defs
  ])

prettyConstructor :: Constructor -> Doc ann
prettyConstructor con = case conRecord con of
  Just fields ->
    prettyConNames (conNames con) <+> braces (vsep $ punctuate semi $ map (prettyField . locVal) fields)
  Nothing ->
    prettyConNames (conNames con) <+> hsep (map prettyLType (conFields con))
  where
    prettyConNames [n] = prettyLIdent n
    prettyConNames ns = parens $ hsep $ punctuate comma $ map prettyLIdent ns

prettyField :: Field -> Doc ann
prettyField f =
  prettyLIdent (fieldName f) <+> "::" <+> prettyQualType (locVal (fieldType f)) <>
  hsep (map prettyMethodPragma (fieldPragmas f)) <>
  maybe mempty (\e -> " =" <+> prettyLExpr e) (fieldDefault f)

prettyMethodPragma :: MethodPragma -> Doc ann
prettyMethodPragma = \case
  MPAlwaysReady -> " {-# always_ready #-}"
  MPAlwaysEnabled -> " {-# always_enabled #-}"
  MPEnabled e -> " {-# enabled =" <+> prettyLExpr e <+> "#-}"
  MPReady e -> " {-# ready =" <+> prettyLExpr e <+> "#-}"
  MPPrefixPort t -> " {-# prefix =" <+> dquotes (pretty t) <+> "#-}"
  MPResultPort t -> " {-# result =" <+> dquotes (pretty t) <+> "#-}"
  MPEnablePort t -> " {-# enable =" <+> dquotes (pretty t) <+> "#-}"
  MPReadyPort t -> " {-# ready =" <+> dquotes (pretty t) <+> "#-}"
  MPArgNames ns -> " {-# arg_names = [" <> hsep (punctuate comma (map pretty ns)) <> "] #-}"
  MPDoc t -> " {-#" <+> pretty t <+> "#-}"

prettyDerivings :: [Deriving] -> Doc ann
prettyDerivings [] = mempty
prettyDerivings [d] = " deriving" <+> prettyQualIdent (locVal $ derivingClass d)
prettyDerivings ds = " deriving" <+> parens (hsep $ punctuate comma $ map (prettyQualIdent . locVal . derivingClass) ds)

prettyFunDeps :: [FunDep] -> Doc ann
prettyFunDeps [] = mempty
prettyFunDeps fds = "|" <+> hsep (punctuate comma $ map prettyFunDep fds)

prettyFunDep :: FunDep -> Doc ann
prettyFunDep fd =
  hsep (map prettyLTyVar (fdFrom fd)) <+> "->" <+> hsep (map prettyLTyVar (fdTo fd))

prettyClassMember :: ClassMember -> Doc ann
prettyClassMember = \case
  ClassMethod name ty def ->
    prettyLIdent name <+> "::" <+> prettyQualType (locVal ty) <>
    maybe mempty (\e -> line <> prettyLIdent name <+> "=" <+> prettyLExpr e) def
  ClassDefaultImpl name pats body ->
    prettyLIdent name <+> hsep (map prettyLPattern pats) <+> "=" <+> prettyLExpr body
  ClassFixity fd -> prettyFixityDecl fd

prettyInstanceMember :: InstanceMember -> Doc ann
prettyInstanceMember (InstanceMethod name clauses) =
  vsep $ map (prettyClause (locVal name)) clauses
prettyInstanceMember (InstanceTypeSig name ty) =
  prettyLIdent name <+> "::" <+> prettyQualType (locVal ty)

--------------------------------------------------------------------------------
-- Type Printing
--------------------------------------------------------------------------------

prettyLType :: LType -> Doc ann
prettyLType = prettyType . locVal

-- | Pretty print a type.
prettyType :: Type -> Doc ann
prettyType = \case
  TVar tv -> prettyTyVar (locVal tv)
  TCon qid -> prettyQualIdent (locVal qid)
  TApp t1 t2 -> prettyLType t1 <+> prettyAtomicType (locVal t2)
  TArrow t1 t2 -> prettyBType (locVal t1) <+> "->" <+> prettyLType t2
  TTuple [] -> "()"
  TTuple ts -> parens (hsep $ punctuate comma $ map prettyLType ts)
  TList t -> brackets (prettyLType t)
  TNum n -> pretty n
  TString s -> dquotes (pretty s)
  TKind t k -> parens (prettyLType t <+> "::" <+> prettyKind (locVal k))

prettyBType :: Type -> Doc ann
prettyBType t@TArrow{} = parens (prettyType t)
prettyBType t = prettyType t

prettyAtomicType :: Type -> Doc ann
prettyAtomicType t@TApp{} = parens (prettyType t)
prettyAtomicType t@TArrow{} = parens (prettyType t)
prettyAtomicType t = prettyType t

prettyQualType :: QualType -> Doc ann
prettyQualType qt = case qtPreds qt of
  [] -> prettyLType (qtType qt)
  preds -> prettyContext preds <+> "=>" <+> prettyLType (qtType qt)

prettyContext :: [Located Pred] -> Doc ann
prettyContext [] = mempty
prettyContext [p] = prettyPred (locVal p)
prettyContext ps = parens (hsep $ punctuate comma $ map (prettyPred . locVal) ps)

prettyPred :: Pred -> Doc ann
prettyPred p = prettyQualIdent (locVal $ predClass p) <+> hsep (map prettyLType (predArgs p))

prettyTyVar :: TyVar -> Doc ann
prettyTyVar tv = prettyIdent (tvName tv)

prettyLTyVar :: Located TyVar -> Doc ann
prettyLTyVar = prettyTyVar . locVal

prettyKind :: Kind -> Doc ann
prettyKind = \case
  KStar -> "*"
  KNum -> "#"
  KString -> "$"
  KArrow k1 k2 -> prettyAtomicKind k1 <+> "->" <+> prettyKind k2

prettyAtomicKind :: Kind -> Doc ann
prettyAtomicKind k@KArrow{} = parens (prettyKind k)
prettyAtomicKind k = prettyKind k

--------------------------------------------------------------------------------
-- Expression Printing
--------------------------------------------------------------------------------

prettyLExpr :: LExpr -> Doc ann
prettyLExpr = prettyExpr . locVal

-- | Pretty print an expression.
prettyExpr :: Expr -> Doc ann
prettyExpr = \case
  EVar qid -> prettyQualIdentAsExpr (locVal qid)
  ECon qid -> prettyQualIdent (locVal qid)
  ELit lit -> prettyLiteral (locVal lit)
  EApp e1 e2 -> prettyLExpr e1 <+> prettyAtomicExpr (locVal e2)
  EInfix e1 op e2 -> prettyLExpr e1 <+> prettyOp (locVal op) <+> prettyLExpr e2
  ENeg e -> "-" <> prettyAtomicExpr (locVal e)
  ELam pats body ->
    "\\" <> hsep (map prettyLPattern pats) <+> "->" <+> prettyLExpr body
  ELet items body -> vsep
    [ "let"
    , indent 2 $ vsep $ map prettyLetItem items
    , "in" <+> prettyLExpr body
    ]
  ELetSeq items body -> vsep
    [ "letseq"
    , indent 2 $ vsep $ map prettyLetItem items
    , "in" <+> prettyLExpr body
    ]
  EWhere e defns -> vsep
    [ prettyLExpr e
    , "where"
    , indent 2 $ vsep $ map prettyDefinition defns
    ]
  EIf cond thenE elseE ->
    "if" <+> prettyLExpr cond <+> "then" <+> prettyLExpr thenE <+> "else" <+> prettyLExpr elseE
  ECase scrut alts -> vsep
    [ "case" <+> prettyLExpr scrut <+> "of"
    , indent 2 $ vsep $ map prettyAlt alts
    ]
  EDo stmts -> vsep
    [ "do"
    , indent 2 $ vsep $ map (prettyStmt . locVal) stmts
    ]
  ETuple [] -> "()"
  ETuple es -> parens (hsep $ punctuate comma $ map prettyLExpr es)
  EList es -> brackets (hsep $ punctuate comma $ map prettyLExpr es)
  ERecord con binds ->
    prettyQualIdent (locVal con) <+> braces (hsep $ punctuate semi $ map prettyFieldBind binds)
  ERecordUpd e binds ->
    prettyAtomicExpr (locVal e) <> braces (hsep $ punctuate semi $ map prettyFieldBind binds)
  EFieldAccess e fld -> prettyAtomicExpr (locVal e) <> "." <> prettyIdent (locVal fld)
  EFieldSection fld -> "(." <> prettyIdent (locVal fld) <> ")"
  EBitSelect e hi lo -> prettyAtomicExpr (locVal e) <> "[" <> prettyLExpr hi <> ":" <> prettyLExpr lo <> "]"
  ETypeSig e ty -> prettyLExpr e <+> "::" <+> prettyQualType (locVal ty)
  EModule stmts -> vsep
    [ "module"
    , indent 2 $ vsep $ map prettyModuleStmt stmts
    ]
  ERules rules -> vsep
    [ "rules"
    , indent 2 $ vsep $ map (prettyRule . locVal) rules
    ]
  EInterface mName fields -> vsep
    [ "interface" <+> maybe mempty (prettyQualIdent . locVal) mName
    , indent 2 $ vsep $ map prettyInterfaceField fields
    ]
  EValueOf ty -> "valueOf" <+> prettyAtomicType (locVal ty)
  EStringOf ty -> "stringOf" <+> prettyAtomicType (locVal ty)
  EPrim name args -> pretty name <+> hsep (map (prettyAtomicExpr . locVal) args)
  EParens e -> parens (prettyLExpr e)
  EModuleVerilog name params clocks resets args methods sched -> vsep
    [ "module verilog" <+> prettyLExpr name
        <> (if null params then mempty else space <> parens (hsep $ punctuate comma $ map prettyLExpr params))
        <> (if null clocks then mempty else space <> hsep (map (dquotes . pretty) clocks))
        <> (if null resets then mempty else space <> hsep (map (dquotes . pretty) resets))
        <> (if null args then mempty else space <> parens (hsep $ punctuate comma $ map prettyVArg args))
        <+> "{"
    , indent 2 $ vsep $ map prettyVerilogMethod methods
    , "}" <> maybe mempty prettySchedInfo sched
    ]
    where
      prettyVArg (name', e) = parens (dquotes (pretty name') <> comma <+> prettyLExpr e)
      prettyVerilogMethod (VerilogMethod fid mult ports) =
        prettyLIdent fid
          <> maybe mempty (\n -> brackets (pretty n)) mult
          <+> "="
          <+> hsep (map prettyPortSpec ports)
          <> semi
      prettyPortSpec (PortSpec pname props) =
        dquotes (pretty pname)
          <> (if null props then mempty else braces (hsep $ punctuate comma $ map prettyPortProp props))
      prettyPortProp PPReg = "reg"
      prettyPortProp PPConst = "const"
      prettyPortProp PPUnused = "unused"
      prettyPortProp PPInHigh = "inhigh"
      prettySchedInfo (SchedInfo entries) =
        space <> brackets (hsep $ punctuate comma $ map prettySchedEntry entries)
      prettySchedEntry (SchedEntry left op right) =
        prettySchedMeths left <+> prettySchedOp op <+> prettySchedMeths right
      prettySchedMeths [x] = prettyLIdent x
      prettySchedMeths xs = brackets (hsep $ punctuate comma $ map prettyLIdent xs)
      prettySchedOp op = pretty op

prettyAtomicExpr :: Expr -> Doc ann
prettyAtomicExpr e@EApp{} = parens (prettyExpr e)
prettyAtomicExpr e@EInfix{} = parens (prettyExpr e)
prettyAtomicExpr e@ELam{} = parens (prettyExpr e)
prettyAtomicExpr e@ELet{} = parens (prettyExpr e)
prettyAtomicExpr e@ELetSeq{} = parens (prettyExpr e)
prettyAtomicExpr e@EWhere{} = parens (prettyExpr e)
prettyAtomicExpr e@EIf{} = parens (prettyExpr e)
prettyAtomicExpr e@ECase{} = parens (prettyExpr e)
prettyAtomicExpr e@ETypeSig{} = parens (prettyExpr e)
prettyAtomicExpr e = prettyExpr e

prettyLetItem :: LetItem -> Doc ann
prettyLetItem = \case
  LetTypeSig name ty ->
    prettyLIdent name <+> "::" <+> prettyQualType (locVal ty)
  LetBind b -> prettyBinding b

prettyBinding :: Binding -> Doc ann
prettyBinding b =
  prettyLPattern (bindPat b) <>
  (if null (bindArgs b) then mempty else " " <> hsep (map prettyLPattern (bindArgs b))) <>
  maybe mempty (\ty -> " ::" <+> prettyQualType (locVal ty)) (bindType b) <+>
  "=" <+> prettyLExpr (bindExpr b)

prettyAlt :: Alt -> Doc ann
prettyAlt alt =
  prettyLPattern (altPat alt) <>
  maybe mempty prettyGuard (altGuard alt) <+>
  "->" <+> prettyLExpr (altBody alt)

prettyStmt :: Stmt -> Doc ann
prettyStmt = \case
  StmtBind pat mTy e ->
    prettyLPattern pat <>
    maybe mempty (\ty -> " ::" <+> prettyQualType (locVal ty)) mTy <+>
    "<-" <+> prettyLExpr e
  StmtLet items -> "let" <+> align (vsep $ map prettyLetItem items)
  StmtLetSeq items -> "letseq" <+> align (vsep $ map prettyLetItem items)
  StmtAssign lhs rhs -> prettyLExpr lhs <+> ":=" <+> prettyLExpr rhs
  StmtExpr e -> prettyLExpr e

prettyFieldBind :: FieldBind -> Doc ann
prettyFieldBind fb = prettyIdent (locVal $ fbName fb) <+> "=" <+> prettyLExpr (fbValue fb)

prettyModuleStmt :: ModuleStmt -> Doc ann
prettyModuleStmt = \case
  MStmtBind pat mTy e ->
    prettyLPattern pat <>
    maybe mempty (\ty -> " ::" <+> prettyLType ty) mTy <+>
    "<-" <+> prettyLExpr e
  MStmtLet items -> "let" <+> align (vsep $ map prettyLetItem items)
  MStmtLetSeq items -> "letseq" <+> align (vsep $ map prettyLetItem items)
  MStmtExpr e -> prettyLExpr e
  MStmtRules rules -> "rules" <+> align (vsep $ map (prettyRule . locVal) rules)
  MStmtInterface fields -> "interface" <+> align (vsep $ map prettyInterfaceField fields)
  MStmtTupleInterface exprs -> "interface" <+> tupled (map prettyLExpr exprs)

prettyRule :: Rule -> Doc ann
prettyRule r = hsep $ catMaybes
  [ ((<> ":") . prettyLExpr) <$> ruleName r
  , if null (rulePragmas r) then Nothing else Just $ hsep $ map prettyRulePragma (rulePragmas r)
  , (\g -> prettyGuard g <+> "==>") <$> ruleCond r
  , Just $ prettyLExpr (ruleBody r)
  ]

prettyRulePragma :: RulePragma -> Doc ann
prettyRulePragma = \case
  RPNoImplicitConditions -> "{-# ASSERT no implicit conditions #-}"
  RPFireWhenEnabled -> "{-# ASSERT fire when enabled #-}"
  RPCanScheduleFirst -> "{-# can_schedule_first #-}"
  RPClockCrossingRule -> "{-# clock_crossing_rule #-}"
  RPDoc t -> "{-#" <+> pretty t <+> "#-}"

prettyInterfaceField :: InterfaceField -> Doc ann
prettyInterfaceField f =
  prettyIdent (locVal $ ifName f) <+>
  hsep (map prettyLPattern (ifPats f)) <+>
  "=" <+> prettyLExpr (ifValue f) <>
  maybe mempty prettyGuard (ifWhen f)

prettyLiteral :: Literal -> Doc ann
prettyLiteral = \case
  LitInt n Nothing -> pretty n
  LitInt n (Just (0, IntHex)) -> "0x" <> pretty (showHex n)
  LitInt n (Just (0, IntBin)) -> "0b" <> pretty (showBin n)
  LitInt n (Just (0, IntOct)) -> "0o" <> pretty (showOct n)
  LitInt n (Just (w, IntHex)) -> pretty w <> "'h" <> pretty (showHex n)
  LitInt n (Just (w, IntDec)) -> pretty w <> "'d" <> pretty n
  LitInt n (Just (w, IntBin)) -> pretty w <> "'b" <> pretty (showBin n)
  LitInt n (Just (w, IntOct)) -> pretty w <> "'o" <> pretty (showOct n)
  LitFloat d -> pretty d
  LitChar c -> squotes (pretty (escapeChar c))
  LitString s -> dquotes (pretty (T.concatMap escapeString s))
  where
    showHex n = showIntAtBase 16 hexDigit n ""
    showBin n = showIntAtBase 2 binDigit n ""
    showOct n = showIntAtBase 8 octDigit n ""

    hexDigit i = "0123456789abcdef" !! i
    binDigit i = "01" !! i
    octDigit i = "01234567" !! i

    showIntAtBase base toDigit n rest
      | n < 0 = '-' : showIntAtBase base toDigit (-n) rest
      | n < base = toDigit (fromIntegral n) : rest
      | otherwise = showIntAtBase base toDigit q (toDigit (fromIntegral r) : rest)
      where (q, r) = n `divMod` base

    escapeChar '\n' = "\\n"
    escapeChar '\t' = "\\t"
    escapeChar '\r' = "\\r"
    escapeChar '\\' = "\\\\"
    escapeChar '\'' = "\\'"
    escapeChar c = T.singleton c

    escapeString '\n' = "\\n"
    escapeString '\t' = "\\t"
    escapeString '\r' = "\\r"
    escapeString '\\' = "\\\\"
    escapeString '"' = "\\\""
    escapeString c = T.singleton c

--------------------------------------------------------------------------------
-- Pattern Printing
--------------------------------------------------------------------------------

prettyLPattern :: LPattern -> Doc ann
prettyLPattern = prettyPattern . locVal

-- | Pretty print a pattern.
prettyPattern :: Pattern -> Doc ann
prettyPattern = \case
  PVar v -> prettyIdent (locVal v)
  PCon qid [] -> prettyQualIdent (locVal qid)
  PCon qid pats -> prettyQualIdent (locVal qid) <+> hsep (map prettyAtomicPattern pats)
  PInfix p1 op p2 -> prettyLPattern p1 <+> prettyOp (locVal op) <+> prettyLPattern p2
  PLit lit -> prettyLiteral (locVal lit)
  PWild -> "_"
  PTuple [] -> "()"
  PTuple ps -> parens (hsep $ punctuate comma $ map prettyLPattern ps)
  PList ps -> brackets (hsep $ punctuate comma $ map prettyLPattern ps)
  PRecord qid fields ->
    prettyQualIdent (locVal qid) <+> braces (hsep $ punctuate comma $ map prettyFieldPat fields)
  PAs v p -> prettyIdent (locVal v) <> "@" <> prettyAtomicPattern p
  PTypeSig p ty -> prettyLPattern p <+> "::" <+> prettyQualType (locVal ty)
  PParens p -> parens (prettyLPattern p)

prettyAtomicPattern :: LPattern -> Doc ann
prettyAtomicPattern p = case locVal p of
  PCon _ (_:_) -> parens (prettyPattern $ locVal p)
  PInfix{} -> parens (prettyPattern $ locVal p)
  PAs{} -> parens (prettyPattern $ locVal p)
  PTypeSig{} -> parens (prettyPattern $ locVal p)
  _ -> prettyPattern $ locVal p

prettyFieldPat :: (Located Ident, LPattern) -> Doc ann
prettyFieldPat (name, pat) = prettyIdent (locVal name) <+> "=" <+> prettyLPattern pat

--------------------------------------------------------------------------------
-- Identifier Printing
--------------------------------------------------------------------------------

prettyIdent :: Ident -> Doc ann
prettyIdent (VarId t) = pretty t
prettyIdent (ConId t) = pretty t

prettyLIdent :: Located Ident -> Doc ann
prettyLIdent = prettyIdent . locVal

-- | Pretty print a type name with optional kind annotation.
-- If kind is present, outputs (Name :: Kind), otherwise just Name.
prettyTypeName :: Located Ident -> Maybe (Located Kind) -> Doc ann
prettyTypeName name Nothing = prettyLIdent name
prettyTypeName name (Just k) = parens (prettyLIdent name <+> "::" <+> prettyKind (locVal k))

prettyQualIdent :: QualIdent -> Doc ann
prettyQualIdent qid = case qualModule qid of
  Nothing -> prettyIdent (qualIdent qid)
  Just m -> prettyModuleId m <> "." <> prettyIdent (qualIdent qid)

-- | Pretty print a qualified identifier as an expression.
-- If the identifier is an operator (starts with operator character),
-- wrap it in parentheses to make it a valid expression.
prettyQualIdentAsExpr :: QualIdent -> Doc ann
prettyQualIdentAsExpr qid
  | isOperatorIdent (qualIdent qid) = parens (prettyQualIdent qid)
  | otherwise = prettyQualIdent qid

-- | Check if an identifier is an operator (starts with an operator character).
isOperatorIdent :: Ident -> Bool
isOperatorIdent (VarId t) = case T.uncons t of
  Just (c, _) -> isOpChar c
  Nothing -> False
isOperatorIdent (ConId t) = case T.uncons t of
  Just (c, _) -> isOpChar c
  Nothing -> False

-- | Check if a character is an operator character.
isOpChar :: Char -> Bool
isOpChar c = c `elem` ("!#$%&*+./<=>?@\\^|-~:" :: String) || c == '\x2218'

prettyOp :: Op -> Doc ann
prettyOp = \case
  OpSym t -> pretty t
  OpIdent i -> "`" <> prettyQualIdent (locVal i) <> "`"
