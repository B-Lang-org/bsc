-- | Type environment for Bluespec: basic type resolution and inference.
--
-- This module provides enough type information to improve hover output:
-- - Collect declared types from signatures and definitions
-- - Strip Module#/ActionValue# wrappers from \<- bindings
-- - Resolve typedef aliases (via SymbolTable.AliasMap)
-- - Basic expression inference for literals and variable references
module Language.Bluespec.LSP.TypeEnv
  ( TypeEnv (..)
  , emptyTypeEnv
  , buildTypeEnv
  , mergeTypeEnv
  , lookupVarType
  , inferExprType
  , stripWrapper
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (listToMaybe, mapMaybe)
import Data.Text (Text)

import Language.Bluespec.LSP.SymbolTable (AliasMap, collectAliases, expandType, qualIdentSimpleName)
import Language.Bluespec.Position (Located (..), noSpan)
import Language.Bluespec.Syntax

-- | Type environment: maps names to their declared types.
data TypeEnv = TypeEnv
  { -- | Variable/function name → declared QualType
    teVars    :: !(Map Text QualType)
    -- | Type alias map (name → params, body); shared with SymbolTable
  , teAliases :: !AliasMap
    -- | Struct/interface name → fields
  , teStructs :: !(Map Text [Field])
  }
  deriving stock (Show)

-- | Empty type environment.
emptyTypeEnv :: TypeEnv
emptyTypeEnv = TypeEnv Map.empty Map.empty Map.empty

-- | Build a TypeEnv from a parsed Package.
buildTypeEnv :: Package -> TypeEnv
buildTypeEnv pkg =
  let aliases = collectAliases (pkgDefns pkg)
      env0    = emptyTypeEnv { teAliases = aliases }
  in foldr collectDef env0 (pkgDefns pkg)

-- | Merge two TypeEnvs (right-biased for conflicts).
mergeTypeEnv :: TypeEnv -> TypeEnv -> TypeEnv
mergeTypeEnv a b = TypeEnv
  { teVars    = teVars a    `Map.union` teVars b
  , teAliases = teAliases a `Map.union` teAliases b
  , teStructs = teStructs a `Map.union` teStructs b
  }

-- | Collect type information from a single definition.
collectDef :: LDefinition -> TypeEnv -> TypeEnv
collectDef (Located _ def) env = case def of
  DefTypeSig name qt ->
    env { teVars = Map.insert (identText (locVal name)) (locVal qt) (teVars env) }

  DefValue name (Just qt) clauses ->
    -- Prefer DefTypeSig if already present; DefValue type sig is a fallback
    let k = identText (locVal name)
        env' = env { teVars = Map.insertWith (\_ old -> old) k (locVal qt) (teVars env) }
    in foldr collectClauseTypes env' clauses

  DefValue _ Nothing clauses ->
    foldr collectClauseTypes env clauses

  -- Struct definition: DefData with one constructor that has record fields.
  DefData name _ _ [Located _ Constructor { conRecord = Just rfields }] _ ->
    env { teStructs = Map.insert (identText (locVal name)) (map locVal rfields) (teStructs env) }

  DefInterface name _ fields _ ->
    env { teStructs = Map.insert (identText (locVal name)) (map locVal fields) (teStructs env) }

  DefClass _ _ _ _ _ members ->
    -- Collect type signatures from class members
    let sigs = [ (identText (locVal n), locVal qt)
               | ClassMethod n qt _ <- members ]
    in env { teVars = Map.fromList sigs `Map.union` teVars env }

  _ -> env

-- | Collect types from a clause body (walk into module expressions).
collectClauseTypes :: Clause -> TypeEnv -> TypeEnv
collectClauseTypes Clause { clauseBody } env =
  collectExprTypes (locVal clauseBody) env

-- | Walk an expression looking for module bodies to collect local binding types.
collectExprTypes :: Expr -> TypeEnv -> TypeEnv
collectExprTypes expr env = case expr of
  EModule stmts  -> foldr collectModuleStmtType env stmts
  EParens e      -> collectExprTypes (locVal e) env
  _              -> env

-- | Collect types declared in a module statement.
-- For MStmtBind with an explicit type annotation, records pat-name → stripped type.
-- For MStmtLet/MStmtLetSeq, records let-bound type signatures.
collectModuleStmtType :: ModuleStmt -> TypeEnv -> TypeEnv
collectModuleStmtType stmt env = case stmt of
  MStmtBind pat (Just lty) _ ->
    collectPatternType pat (locVal lty) env
  MStmtBind pat Nothing expr ->
    -- Infer from the RHS and strip Module#/ActionValue# wrapper
    case fmap (stripWrapper . expandAlias env) (inferExprType env expr) of
      Nothing -> env
      Just t  -> collectPatternType pat t env
  MStmtLet items  -> extendEnvWithLetItems env items
  MStmtLetSeq items -> extendEnvWithLetItems env items
  MStmtDef def    -> collectDef def env
  _               -> env

-- | Record type for a single-variable pattern.
collectPatternType :: LPattern -> Type -> TypeEnv -> TypeEnv
collectPatternType lpat ty env = case locVal lpat of
  PVar name ->
    let k  = identText (locVal name)
        qt = plainQualType ty
    in env { teVars = Map.insertWith (\_ old -> old) k qt (teVars env) }
  PTypeSig p _ -> collectPatternType p ty env
  PParens   p  -> collectPatternType p ty env
  _            -> env

-- | Wrap a bare Type in a QualType with no predicates.
plainQualType :: Type -> QualType
plainQualType t = QualType [] (Located noSpan t)

-- | Look up the declared type of a variable name.
lookupVarType :: TypeEnv -> Text -> Maybe QualType
lookupVarType env name = Map.lookup name (teVars env)

-- | Very basic expression type inference.
-- Returns Nothing for expressions that are too complex to infer without
-- full type checking. Never crashes.
inferExprType :: TypeEnv -> LExpr -> Maybe Type
inferExprType env (Located _ expr) = case expr of
  EVar qi        -> fmap (locVal . qtType) $ lookupVarType env (qualIdentText qi)
  ELit lit       -> Just $ inferLitType (locVal lit)
  ETypeSig _ qt  -> Just $ expandAlias env $ locVal $ qtType $ locVal qt
  EParens e      -> inferExprType env e
  ENeg e         -> inferExprType env e
  EIf _ t _      -> inferExprType env t
  EApp f _       -> inferExprType env f >>= returnType
  ELet items body ->
    let env' = extendEnvWithLetItems env items
    in  inferExprType env' body
  ELetSeq items body ->
    let env' = extendEnvWithLetItems env items
    in  inferExprType env' body
  EDo stmts      -> inferDoType env stmts
  _              -> Nothing

-- | Infer the type of a literal.
inferLitType :: Literal -> Type
inferLitType (LitInt _ (Just (width, _))) =
  TApp (Located noSpan (TCon (Located noSpan (QualIdent Nothing (ConId "Bit")))))
       (Located noSpan (TNum (fromIntegral width)))
inferLitType (LitInt _ Nothing) = TCon (Located noSpan (QualIdent Nothing (ConId "Integer")))
inferLitType (LitFloat _)       = TCon (Located noSpan (QualIdent Nothing (ConId "Real")))
inferLitType (LitChar _)        = TCon (Located noSpan (QualIdent Nothing (ConId "Char")))
inferLitType (LitString _)      = TCon (Located noSpan (QualIdent Nothing (ConId "String")))

-- | Strip one arrow from a function type (return type after one application).
returnType :: Type -> Maybe Type
returnType (TArrow _ b) = Just (locVal b)
returnType _            = Nothing

-- | Infer the type of a do-block from its last statement.
inferDoType :: TypeEnv -> [LStmt] -> Maybe Type
inferDoType env stmts = listToMaybe $ mapMaybe inferStmt (reverse stmts)
  where
    inferStmt (Located _ stmt) = case stmt of
      StmtExpr e  -> inferExprType env e
      StmtBind _ (Just qt) _ ->
        Just $ expandAlias env $ locVal $ qtType $ locVal qt
      StmtBind _ Nothing e ->
        fmap (stripWrapper . expandAlias env) (inferExprType env e)
      _           -> Nothing

-- | Strip Module#(t) / ActionValue#(t) / Action wrappers.
-- Used when processing <- bindings: the bound variable has the inner type.
stripWrapper :: Type -> Type
stripWrapper t = case collectTApp t of
  (Located _ (TCon qi), [arg])
    | n `elem` ["Module", "ActionValue", "ActionValue_"] ->
        locVal arg
    where n = qualIdentSimpleName (locVal qi)
  _ -> t

-- | Extend the type environment with let-binding items.
extendEnvWithLetItems :: TypeEnv -> [LetItem] -> TypeEnv
extendEnvWithLetItems env items =
  foldr addItem env items
  where
    addItem (LetTypeSig name qt) e =
      e { teVars = Map.insert (identText (locVal name)) (locVal qt) (teVars e) }
    addItem (LetBind Binding { bindPat, bindType }) e =
      case (locVal bindPat, bindType) of
        (PVar name, Just qt) ->
          e { teVars = Map.insert (identText (locVal name)) (locVal qt) (teVars e) }
        _ -> e

-- | Expand a type using the alias map in the environment.
expandAlias :: TypeEnv -> Type -> Type
expandAlias env = expandType (teAliases env)

-- | Extract unqualified text from a QualIdent in an expression.
qualIdentText :: Located QualIdent -> Text
qualIdentText lqi = case locVal lqi of
  QualIdent (Just (ModuleId m)) ident -> m <> "." <> identText ident
  QualIdent Nothing ident             -> identText ident

-- | Decompose a left-spine TApp into head + args.
collectTApp :: Type -> (LType, [LType])
collectTApp (TApp f arg) =
  let (hd, args) = collectTApp (locVal f)
  in (hd, args ++ [arg])
collectTApp t = (Located noSpan t, [])
