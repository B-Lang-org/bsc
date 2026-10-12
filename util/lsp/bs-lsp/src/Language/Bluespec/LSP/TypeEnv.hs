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
  , expandAlias
  , stripWrapper
  , Subst
  , applySubst
  , unifyTypes
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, listToMaybe, mapMaybe)
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
  let aliases  = collectAliases (pkgDefns pkg)
      env0     = emptyTypeEnv { teAliases = aliases }
      -- First pass: collect declared types, structs, and class method signatures
      envSigs  = foldr collectDef env0 (pkgDefns pkg)
      -- Second pass: distribute parameter types into teVars using the
      -- gathered function type signatures
  in foldr (collectDefParams envSigs) envSigs (pkgDefns pkg)

-- | Merge two TypeEnvs (right-biased for conflicts).
mergeTypeEnv :: TypeEnv -> TypeEnv -> TypeEnv
mergeTypeEnv a b = TypeEnv
  { teVars    = teVars a    `Map.union` teVars b
  , teAliases = teAliases a `Map.union` teAliases b
  , teStructs = teStructs a `Map.union` teStructs b
  }

-- | Extract ordered argument types from a QualType (splits on TArrow).
extractArgTypes :: QualType -> [Type]
extractArgTypes qt = go (locVal (qtType qt))
  where
    go (TArrow a b) = locVal a : go (locVal b)
    go _            = []

-- | Distribute function parameter types into teVars using gathered signatures.
-- For each DefValue, looks up the function's declared type in sigEnv and
-- assigns the corresponding argument types to the named parameters in each clause.
collectDefParams :: TypeEnv -> LDefinition -> TypeEnv -> TypeEnv
collectDefParams sigEnv (Located _ def) env = case def of
  DefValue name _ clauses ->
    let k = identText (locVal name)
    in case Map.lookup k (teVars sigEnv) of
         Nothing -> env
         Just qt ->
           let argTypes = extractArgTypes qt
           in foldr (collectClauseParams argTypes) env clauses
  _ -> env

-- | Associate clause pattern names with the expected argument types from
-- the function's type signature.
collectClauseParams :: [Type] -> Clause -> TypeEnv -> TypeEnv
collectClauseParams argTypes Clause { clausePats, clauseBody } env =
  let env' = zipPatTypes clausePats argTypes env
  in collectExprTypes (locVal clauseBody) env'

-- | Walk a list of patterns and a list of argument types together,
-- adding PVar bindings to the env.
zipPatTypes :: [LPattern] -> [Type] -> TypeEnv -> TypeEnv
zipPatTypes [] _ env = env
zipPatTypes _ [] env = env
zipPatTypes (p:ps) (t:ts) env =
  collectPatternType p t (zipPatTypes ps ts env)

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
  EIf _ t _        -> inferExprType env t
  EApp f arg       -> inferAppType env f arg
  EFieldAccess e f -> inferFieldAccessType env e f
  EInfix l op r    -> inferInfixType env (locVal op) l r
  ELet items body ->
    let env' = extendEnvWithLetItems env items
    in  inferExprType env' body
  ELetSeq items body ->
    let env' = extendEnvWithLetItems env items
    in  inferExprType env' body
  EDo stmts      -> inferDoType env stmts
  _              -> Nothing

-- | Infer the type of a function application using argument-type specialization.
-- If the argument type can be inferred, unifies it with the function's parameter
-- type to specialize type variables in the return type.
-- E.g. mkReg :: a -> Module#(Reg#(a)), arg = 0 :: Integer → Module#(Reg#(Integer))
inferAppType :: TypeEnv -> LExpr -> LExpr -> Maybe Type
inferAppType env f arg = do
  fty <- inferExprType env f
  case fty of
    TArrow paramTy retTy ->
      let subst = case inferExprType env arg of
                    Nothing    -> Map.empty
                    Just argTy -> fromMaybe Map.empty
                                    (unifyTypes (locVal paramTy) argTy)
      in  Just (applySubst subst (locVal retTy))
    _ -> Nothing

-- | Infer the type of a field access expression (receiver.field).
-- Looks up the receiver type in teStructs, then finds the matching field.
inferFieldAccessType :: TypeEnv -> LExpr -> Located Ident -> Maybe Type
inferFieldAccessType env recv field = do
  recvTy  <- inferExprType env recv
  tyName  <- outerTypeName recvTy
  fields  <- Map.lookup tyName (teStructs env)
  let name = identText (locVal field)
  matched <- listToMaybe (filter (\fi -> identText (locVal (fieldName fi)) == name) fields)
  pure (locVal (qtType (locVal (fieldType matched))))

-- | Infer the result type of an infix operator application.
-- For comparison operators, always returns Bool.
-- For arithmetic/bitwise operators, returns the type of the left operand
-- (correct in well-typed Bluespec code where both sides have the same type).
inferInfixType :: TypeEnv -> Op -> LExpr -> LExpr -> Maybe Type
inferInfixType env op l _r =
  let sym = opSym op
  in if sym `elem` cmpOps
       then Just boolType
       else if sym `elem` logicOps
         then Just boolType
         else inferExprType env l  -- arithmetic/bitwise: same type as left
  where
    cmpOps   = ["==", "/=", "<", ">", "<=", ">="]
    logicOps = ["&&", "||"]
    boolType = TCon (Located noSpan (QualIdent Nothing (ConId "Bool")))
    opSym (OpSym s)      = s
    opSym (OpIdent lqi)  = qualIdentText lqi

-- | Extract the outermost type constructor name from a type.
outerTypeName :: Type -> Maybe Text
outerTypeName (TCon qi)  = Just (qualIdentSimpleName (locVal qi))
outerTypeName (TApp f _) = outerTypeName (locVal f)
outerTypeName _          = Nothing

-- | Infer the type of a literal.
inferLitType :: Literal -> Type
inferLitType (LitInt _ (Just (width, _))) =
  TApp (Located noSpan (TCon (Located noSpan (QualIdent Nothing (ConId "Bit")))))
       (Located noSpan (TNum (fromIntegral width)))
inferLitType (LitInt _ Nothing) = TCon (Located noSpan (QualIdent Nothing (ConId "Integer")))
inferLitType (LitFloat _)       = TCon (Located noSpan (QualIdent Nothing (ConId "Real")))
inferLitType (LitChar _)        = TCon (Located noSpan (QualIdent Nothing (ConId "Char")))
inferLitType (LitString _)      = TCon (Located noSpan (QualIdent Nothing (ConId "String")))

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

-- ---------------------------------------------------------------------------
-- Type substitution and unification
-- ---------------------------------------------------------------------------

-- | A substitution maps type-variable names to types.
type Subst = Map Text Type

-- | Apply a substitution to a type.
-- Replaces type variables; leaves all other constructors intact.
applySubst :: Subst -> Type -> Type
applySubst s (TVar lv) =
  Map.findWithDefault (TVar lv) (identText (tvName (locVal lv))) s
applySubst s (TApp f a)   = TApp (fmap (applySubst s) f) (fmap (applySubst s) a)
applySubst s (TArrow a b) = TArrow (fmap (applySubst s) a) (fmap (applySubst s) b)
applySubst s (TTuple ts)  = TTuple (map (fmap (applySubst s)) ts)
applySubst s (TList t)    = TList (fmap (applySubst s) t)
applySubst s (TKind t k)  = TKind (fmap (applySubst s) t) k
applySubst _ t            = t  -- TCon, TNum, TString: no variables to substitute

-- | Unify two types and return a substitution on success.
-- Does not perform an occurs check — safe because applySubst is not
-- applied recursively here, so there is no risk of looping.
-- Returns Nothing when the types cannot be unified.
unifyTypes :: Type -> Type -> Maybe Subst
unifyTypes (TVar lv) t =
  Just (Map.singleton (identText (tvName (locVal lv))) t)
unifyTypes t (TVar lv) =
  Just (Map.singleton (identText (tvName (locVal lv))) t)
unifyTypes (TCon a) (TCon b)
  | qualIdentSimpleName (locVal a) == qualIdentSimpleName (locVal b) = Just Map.empty
unifyTypes (TNum n) (TNum m)
  | n == m    = Just Map.empty
unifyTypes (TApp f1 a1) (TApp f2 a2) = do
  s1 <- unifyTypes (locVal f1) (locVal f2)
  s2 <- unifyTypes (applySubst s1 (locVal a1)) (applySubst s1 (locVal a2))
  pure (s1 `Map.union` s2)
unifyTypes (TArrow a1 b1) (TArrow a2 b2) = do
  s1 <- unifyTypes (locVal a1) (locVal a2)
  s2 <- unifyTypes (applySubst s1 (locVal b1)) (applySubst s1 (locVal b2))
  pure (s1 `Map.union` s2)
unifyTypes _ _ = Nothing
