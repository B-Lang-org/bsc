{-# LANGUAGE DuplicateRecordFields #-}

-- | Symbol table construction and name resolution for Bluespec.
module Language.Bluespec.LSP.SymbolTable
  ( -- * Symbol Table
    SymbolTable (..),
    emptySymbolTable,
    buildSymbolTable,

    -- * Prelude
    discoverPreludeFilePath,
    loadPreludeSymbolTable,

    -- * Library Discovery
    LibrarySearchResult (..),
    discoverLibrariesDirWithDebug,
    discoverLibrariesDir,
    formatLibrarySearchError,

    -- * Symbols
    Symbol (..),
    SymbolKind (..),

    -- * Queries
    lookupAtPosition,
    lookupByName,
    getAllSymbols,

    -- * Import Info
    ImportInfo (..),

    -- * Type alias utilities (used by TypeEnv)
    AliasMap,
    collectAliases,
    expandType,
    qualIdentSimpleName,
  )
where

import Control.Exception (SomeException, try)
import Control.Monad (forM_)
import Control.Monad.State.Strict
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Language.Bluespec.Parser (parsePackage)
import Language.Bluespec.Position
import Language.Bluespec.Pretty (prettyType, renderPretty)
import Language.Bluespec.Syntax
import System.Directory (doesDirectoryExist, doesFileExist)
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..))
import System.FilePath (takeDirectory, (</>))
import System.Process (readProcessWithExitCode)

-- | Type alias map: type name → (type parameters, expansion type).
type AliasMap = Map Text ([TyVar], Type)

-- | Collect type aliases from a list of definitions.
collectAliases :: [LDefinition] -> AliasMap
collectAliases defs = Map.fromList
  [ (identText (locVal name), (map locVal tvars, locVal ty))
  | Located _ (DefType name _kind tvars ty) <- defs
  ]

-- | Expand type aliases in a 'Type' (single step, applied recursively).
expandType :: AliasMap -> Type -> Type
expandType aliases = go
  where
    go (TCon qi) =
      let name = qualIdentSimpleName (locVal qi)
      in case Map.lookup name aliases of
           Just ([], body) -> go body
           _               -> TCon qi
    go t@(TApp _ _) =
      let (hd, args) = collectTApp t
      in case hd of
           Located _ (TCon qi) ->
             let name = qualIdentSimpleName (locVal qi)
                 args' = map (fmap go) args
             in case Map.lookup name aliases of
                  Just (tvars, body)
                    | length tvars == length args ->
                        let subst = Map.fromList
                              $ zip (map (identText . tvName) tvars) (map locVal args')
                        in go (applyTySubst subst body)
                  _ -> rebuildTApp hd args'
           _ -> rebuildTApp (fmap go hd) (map (fmap go) args)
    go (TArrow a b) = TArrow (fmap go a) (fmap go b)
    go (TTuple ts)  = TTuple (map (fmap go) ts)
    go (TList t)    = TList (fmap go t)
    go (TKind t k)  = TKind (fmap go t) k
    go t            = t  -- TVar, TNum, TString

    -- Collect a left-spine TApp into head + arg list
    collectTApp :: Type -> (LType, [LType])
    collectTApp (TApp f arg) =
      let (hd, args) = collectTApp (locVal f)
      in (hd, args ++ [arg])
    collectTApp t = (noLocate t, [])

    -- Rebuild a TApp from head + arg list
    rebuildTApp :: LType -> [LType] -> Type
    rebuildTApp hd [] = locVal hd
    rebuildTApp hd (a:as) =
      locVal $ foldl (\acc x -> Located (locSpan acc) (TApp acc x)) (Located (locSpan hd) (TApp hd a)) as

    noLocate :: Type -> LType
    noLocate t = Located noSpan t

-- | Apply a type variable substitution.
applyTySubst :: Map Text Type -> Type -> Type
applyTySubst subst = go
  where
    go (TVar (Located sp tv)) =
      Map.findWithDefault (TVar (Located sp tv)) (identText (tvName tv)) subst
    go (TCon qi)      = TCon qi
    go (TApp f arg)   = TApp (fmap go f) (fmap go arg)
    go (TArrow a b)   = TArrow (fmap go a) (fmap go b)
    go (TTuple ts)    = TTuple (map (fmap go) ts)
    go (TList t)      = TList (fmap go t)
    go (TKind t k)    = TKind (fmap go t) k
    go t              = t

-- | Extract the unqualified name from a QualIdent.
qualIdentSimpleName :: QualIdent -> Text
qualIdentSimpleName (QualIdent _ ident) = identText ident

-- | Format a qualified type for display.
-- This is a simple implementation since prettyQualType isn't exported.
formatQualType :: QualType -> Text
formatQualType qt = case qtPreds qt of
  [] -> renderPretty 80 $ prettyType $ locVal $ qtType qt
  preds -> T.intercalate ", " (map formatPred preds) <> " => " <> renderPretty 80 (prettyType $ locVal $ qtType qt)
  where
    formatPred (Located _ (Pred cls args)) =
      formatQualIdent (locVal cls) <> " " <> T.intercalate " " (map (renderPretty 80 . prettyType . locVal) args)
    formatQualIdent (QualIdent mMod ident) = case mMod of
      Just (ModuleId m) -> m <> "." <> identText ident
      Nothing -> identText ident

-- | Like 'formatQualType' but expands typedef aliases in the type.
formatQualTypeExpanded :: AliasMap -> QualType -> Text
formatQualTypeExpanded aliases qt =
  let qt' = qt { qtType = fmap (expandType aliases) (qtType qt) }
  in formatQualType qt'

-- | Symbol kinds matching Bluespec constructs.
data SymbolKind
  = -- | Module/package name
    SKModule
  | -- | Type synonym
    SKType
  | -- | Data type
    SKData
  | -- | Interface definition
    SKInterface
  | -- | Type class
    SKClass
  | -- | Function/value
    SKFunction
  | -- | Data constructor
    SKConstructor
  | -- | Interface/record field
    SKField
  | -- | Type variable
    SKTypeVar
  | -- | Local variable
    SKVariable
  | -- | Function parameter
    SKParameter
  deriving stock (Eq, Show)

-- | A symbol with its definition location and type info.
data Symbol = Symbol
  { -- | Symbol name
    symName :: !Text,
    -- | Kind of symbol
    symKind :: !SymbolKind,
    -- | Where it's defined
    symSpan :: !SrcSpan,
    -- | Type (if known, pretty-printed)
    symType :: !(Maybe Text),
    -- | Doc comment if present
    symDoc :: !(Maybe Text),
    -- | Parent symbol (for nested symbols)
    symParent :: !(Maybe Text)
  }
  deriving stock (Show)

-- | Import information.
data ImportInfo = ImportInfo
  { -- | Module being imported
    iiModule :: !ModuleId,
    -- | Is it qualified?
    iiQualified :: !Bool,
    -- | Import alias
    iiAlias :: !(Maybe ModuleId),
    -- | Source span of the import statement
    iiSpan :: !SrcSpan
  }
  deriving stock (Show)

-- | Symbol table for a single document.
data SymbolTable = SymbolTable
  { -- | Name -> definitions (may have multiple)
    stDefinitions :: !(Map Text [Symbol]),
    -- | Position-indexed for hover/goto
    stByPosition :: ![(SrcSpan, Symbol)],
    -- | Imported modules
    stImports :: ![ImportInfo],
    -- | Package name
    stPackageName :: !(Maybe Text)
  }
  deriving stock (Show)

-- | Create empty symbol table.
emptySymbolTable :: SymbolTable
emptySymbolTable =
  SymbolTable
    { stDefinitions = Map.empty,
      stByPosition = [],
      stImports = [],
      stPackageName = Nothing
    }

-- | Discover the actual Prelude.bs file path.
-- Tries in order:
-- 1. BLUESPEC_LIB_DIR environment variable
-- 2. BLUESPEC_SRC environment variable
-- 3. BLUESPECDIR environment variable
-- 4. Querying Bazel for @bsc-source location
-- Returns the path to the real Prelude.bs if found, otherwise Nothing.
discoverPreludeFilePath :: IO (Maybe FilePath)
discoverPreludeFilePath = do
  mLibDir <- lookupEnv "BLUESPEC_LIB_DIR"
  case mLibDir of
    Just libDir -> do
      mPrelude <- resolvePreludeFromLibDir libDir
      case mPrelude of
        Just _ -> pure mPrelude
        Nothing -> tryBluespecSrc
    Nothing -> tryBluespecSrc
  where
    tryBluespecSrc = do
      -- Try BLUESPEC_SRC (source repository)
      mBluespecSrc <- lookupEnv "BLUESPEC_SRC"
      case mBluespecSrc of
        Just srcDir -> do
          let preludePath = srcDir </> "src" </> "Libraries" </> "Base1" </> "Prelude.bs"
          exists <- doesFileExist preludePath
          if exists then pure (Just preludePath) else tryBluespecDir
        Nothing -> tryBluespecDir

    tryBluespecDir = do
      mBluespecDir <- lookupEnv "BLUESPECDIR"
      case mBluespecDir of
        Nothing -> tryBazel
        Just bluespecDir -> do
          let preludePath = bluespecDir </> "lib" </> "Libraries" </> "Prelude.bs"
          exists <- doesFileExist preludePath
          if exists then pure (Just preludePath) else tryBazel

    tryBazel = do
      mLibDir <- discoverFromBazel
      case mLibDir of
        Nothing -> pure Nothing
        Just libDir -> do
          let preludePath = libDir </> "Base1" </> "Prelude.bs"
          exists <- doesFileExist preludePath
          pure $ if exists then Just preludePath else Nothing

-- | Load the prelude symbol table by parsing the actual Prelude.bs file.
-- Returns Nothing if the file cannot be found or parsed.
loadPreludeSymbolTable :: IO (Maybe SymbolTable)
loadPreludeSymbolTable = do
  mPath <- discoverPreludeFilePath
  case mPath of
    Nothing -> pure Nothing
    Just path -> do
      contents <- TIO.readFile path
      case parsePackage (T.pack path) contents of
        Left _ -> pure Nothing
        Right pkg -> pure $ Just $ buildSymbolTable pkg

-- | Result of searching for the standard library.
data LibrarySearchResult
  = LibraryFound FilePath
  | LibraryNotFound [String] -- List of places searched
  deriving stock (Show)

-- | Discover the Bluespec standard library directory.
-- Tries in order:
-- 1. BLUESPEC_LIB_DIR environment variable
-- 2. BLUESPEC_SRC environment variable
-- 3. BLUESPECDIR environment variable
-- 4. Querying Bazel for @bsc-source location
-- Returns either the path found or a list of places searched.
discoverLibrariesDirWithDebug :: IO LibrarySearchResult
discoverLibrariesDirWithDebug = do
  mLibDir <- lookupEnv "BLUESPEC_LIB_DIR"
  mBluespecSrc <- lookupEnv "BLUESPEC_SRC"
  mBluespecDir <- lookupEnv "BLUESPECDIR"

  case mLibDir of
    Just libDir -> do
      mResolved <- resolveLibraryDir libDir
      case mResolved of
        Just resolved -> pure (LibraryFound resolved)
        Nothing -> tryBluespecSrc mBluespecSrc mBluespecDir
    Nothing -> tryBluespecSrc mBluespecSrc mBluespecDir
  where
    tryBluespecSrc mBluespecSrc mBluespecDir =
      case mBluespecSrc of
        Just srcDir -> do
          let libDir = srcDir </> "src" </> "Libraries"
          exists <- doesDirectoryExist libDir
          if exists
            then pure (LibraryFound libDir)
            else tryBluespecDir mBluespecDir
        Nothing -> tryBluespecDir mBluespecDir

    tryBluespecDir mBluespecDir =
      case mBluespecDir of
        Just bluespecDir -> do
          let libDir = bluespecDir </> "lib" </> "Libraries"
          exists <- doesDirectoryExist libDir
          if exists
            then pure (LibraryFound libDir)
            else tryBazel
        Nothing -> tryBazel

    tryBazel = do
      result <- discoverFromBazel
      case result of
        Just libDir -> pure (LibraryFound libDir)
        Nothing ->
          pure
            ( LibraryNotFound
                [ "BLUESPEC_LIB_DIR: (not set)",
                  "BLUESPEC_SRC: (not set)",
                  "BLUESPECDIR: (not set)",
                  "Bazel query: failed or @bsc-source not available"
                ]
            )

-- | Try to discover the Bluespec source from Bazel.
-- Queries Bazel for the @bsc-source external repository location.
-- Returns Nothing if bazel is not installed or the query fails.
discoverFromBazel :: IO (Maybe FilePath)
discoverFromBazel = do
  -- Get bazel output base (bazel may not be installed)
  r1 <- try (readProcessWithExitCode "bazel" ["info", "output_base"] "") :: IO (Either SomeException (ExitCode, String, String))
  (exitCode1, outputBase) <- case r1 of
    Left _  -> pure (ExitFailure 1, "")
    Right (ec, out, _) -> pure (ec, out)
  case exitCode1 of
    ExitFailure _ -> pure Nothing
    ExitSuccess -> do
      let outputBasePath = filter (/= '\n') outputBase
      -- Query for the prelude file location
      (exitCode2, preludePath, _) <-
        readProcessWithExitCode
          "bazel"
          ["cquery", "--output=files", "@bsc-source//:prelude"]
          ""
      case exitCode2 of
        ExitFailure _ -> pure Nothing
        ExitSuccess -> do
          let relPath = filter (/= '\n') (head (lines preludePath))
              -- The path is relative, prepend output base
              fullPath = outputBasePath </> relPath
              -- Go up from src/Libraries/Base1/Prelude.bs to get the source root
              srcRoot = takeDirectory (takeDirectory (takeDirectory (takeDirectory fullPath)))
              libDir = srcRoot </> "src" </> "Libraries"
          exists <- doesDirectoryExist libDir
          pure $ if exists then Just libDir else Nothing

-- | Simple version that just returns Maybe FilePath.
discoverLibrariesDir :: IO (Maybe FilePath)
discoverLibrariesDir = do
  result <- discoverLibrariesDirWithDebug
  pure $ case result of
    LibraryFound path -> Just path
    LibraryNotFound _ -> Nothing

-- | Format the library search result for error messages.
formatLibrarySearchError :: LibrarySearchResult -> String
formatLibrarySearchError (LibraryFound _) = "Library found (this shouldn't be an error)"
formatLibrarySearchError (LibraryNotFound searched) =
  "Standard library not found. Searched locations:\n"
    ++ unlines (map ("  - " ++) searched)
    ++ "\nEither set BLUESPEC_LIB_DIR/BLUESPECDIR/BLUESPEC_SRC or run from within a Bazel workspace."

-- | Resolve a standard library directory from a provided path.
resolveLibraryDir :: FilePath -> IO (Maybe FilePath)
resolveLibraryDir baseDir = do
  let directBase1 = baseDir </> "Base1"
      nestedBase1 = baseDir </> "Libraries" </> "Base1"
  directExists <- doesDirectoryExist directBase1
  if directExists
    then pure (Just baseDir)
    else do
      nestedExists <- doesDirectoryExist nestedBase1
      pure $ if nestedExists then Just (baseDir </> "Libraries") else Nothing

-- | Resolve Prelude.bs from an explicit library directory.
resolvePreludeFromLibDir :: FilePath -> IO (Maybe FilePath)
resolvePreludeFromLibDir baseDir = do
  mLibDir <- resolveLibraryDir baseDir
  case mLibDir of
    Nothing -> pure Nothing
    Just libDir -> do
      let preludePath = libDir </> "Base1" </> "Prelude.bs"
      exists <- doesFileExist preludePath
      pure $ if exists then Just preludePath else Nothing

-- | State for building symbol tables.
data BuildState = BuildState
  { bsSymbols :: ![Symbol],
    bsImports :: ![ImportInfo],
    bsParent  :: !(Maybe Text),
    bsAliases :: !AliasMap
  }

type Builder a = State BuildState a

-- | Build symbol table from a parsed package.
buildSymbolTable :: Package -> SymbolTable
buildSymbolTable pkg =
  SymbolTable
    { stDefinitions = buildDefMap symbols,
      stByPosition = [(symSpan s, s) | s <- symbols],
      stImports = bsImports finalState,
      stPackageName = Just $ unModuleId $ locVal $ pkgName pkg
    }
  where
    -- Pre-collect type aliases so symbol types can be expanded
    aliases      = collectAliases (pkgDefns pkg)
    initialState = BuildState [] [] Nothing aliases
    finalState   = execState (collectPackage pkg) initialState
    symbols      = bsSymbols finalState

-- | Build map from names to symbols.
buildDefMap :: [Symbol] -> Map Text [Symbol]
buildDefMap = foldr insertSym Map.empty
  where
    insertSym sym = Map.insertWith (++) (symName sym) [sym]

-- | Format a QualType using the current alias map from build state.
fmtQT :: QualType -> Builder Text
fmtQT qt = do
  aliases <- gets bsAliases
  pure $ formatQualTypeExpanded aliases qt

-- | Add a symbol to the builder state.
addSymbol :: Symbol -> Builder ()
addSymbol sym = modify $ \s -> s {bsSymbols = sym : bsSymbols s}

-- | Add an import to the builder state.
addImport :: ImportInfo -> Builder ()
addImport imp = modify $ \s -> s {bsImports = imp : bsImports s}

-- | Run builder with a parent context.
withParent :: Text -> Builder a -> Builder a
withParent name action = do
  oldParent <- gets bsParent
  modify $ \s -> s {bsParent = Just name}
  result <- action
  modify $ \s -> s {bsParent = oldParent}
  pure result

-- | Collect all symbols from a package.
collectPackage :: Package -> Builder ()
collectPackage Package {..} = do
  -- Add package as a symbol
  let pkgNameText = unModuleId $ locVal pkgName
  addSymbol
    Symbol
      { symName = pkgNameText,
        symKind = SKModule,
        symSpan = locSpan pkgName,
        symType = Nothing,
        symDoc = Nothing,
        symParent = Nothing
      }

  -- Collect imports
  mapM_ collectImport pkgImports

  -- Collect definitions
  mapM_ collectDefinition pkgDefns

-- | Collect import information.
collectImport :: Located Import -> Builder ()
collectImport (Located spn Import {..}) =
  addImport
    ImportInfo
      { iiModule = importModule,
        iiQualified = importQualified,
        iiAlias = importAs,
        iiSpan = spn
      }

-- | Collect symbols from a definition.
collectDefinition :: LDefinition -> Builder ()
collectDefinition (Located _span def) = case def of
  DefValue name mTy clauses -> do
    let nameText = identText $ locVal name
    typeText <- traverse (fmtQT . locVal) mTy
    addSymbol
      Symbol
        { symName = nameText,
          symKind = SKFunction,
          symSpan = locSpan name,
          symType = typeText,
          symDoc = Nothing,
          symParent = Nothing
        }
    -- Collect parameters from clauses
    withParent nameText $ mapM_ collectClause clauses
  DefTypeSig name ty -> do
    typeText <- fmtQT (locVal ty)
    addSymbol
      Symbol
        { symName = identText $ locVal name,
          symKind = SKFunction,
          symSpan = locSpan name,
          symType = Just typeText,
          symDoc = Nothing,
          symParent = Nothing
        }
  DefType name _kind tvars ty -> do
    let nameText = identText $ locVal name
    addSymbol
      Symbol
        { symName = nameText,
          symKind = SKType,
          symSpan = locSpan name,
          symType = Just $ renderPretty 80 $ prettyType $ locVal ty,
          symDoc = Nothing,
          symParent = Nothing
        }
    withParent nameText $ mapM_ collectTyVar tvars
  DefData name _kind tvars constrs _derivs -> do
    let nameText = identText $ locVal name
    addSymbol
      Symbol
        { symName = nameText,
          symKind = SKData,
          symSpan = locSpan name,
          symType = Nothing,
          symDoc = Nothing,
          symParent = Nothing
        }
    withParent nameText $ do
      mapM_ collectTyVar tvars
      mapM_ collectConstructor constrs
  DefInterface name tvars fields _derivs -> do
    let nameText = identText $ locVal name
    addSymbol
      Symbol
        { symName = nameText,
          symKind = SKInterface,
          symSpan = locSpan name,
          symType = Nothing,
          symDoc = Nothing,
          symParent = Nothing
        }
    withParent nameText $ do
      mapM_ collectTyVar tvars
      mapM_ collectField fields
  DefClass _coherence _preds name tvars _fundeps members -> do
    let nameText = identText $ locVal name
    addSymbol
      Symbol
        { symName = nameText,
          symKind = SKClass,
          symSpan = locSpan name,
          symType = Nothing,
          symDoc = Nothing,
          symParent = Nothing
        }
    withParent nameText $ do
      mapM_ collectTyVar tvars
      mapM_ collectClassMember members
  DefInstance _preds clsName _types members -> do
    -- Instance methods are collected under the class name
    let clsNameText = identText $ qualIdent $ locVal clsName
    withParent clsNameText $ mapM_ collectInstanceMember members
  DefPrimitive name ty -> do
    typeText <- fmtQT (locVal ty)
    addSymbol
      Symbol
        { symName = identText $ locVal name,
          symKind = SKFunction,
          symSpan = locSpan name,
          symType = Just typeText,
          symDoc = Nothing,
          symParent = Nothing
        }
  DefForeign name ty _ext -> do
    typeText <- fmtQT (locVal ty)
    addSymbol
      Symbol
        { symName = identText $ locVal name,
          symKind = SKFunction,
          symSpan = locSpan name,
          symType = Just typeText,
          symDoc = Nothing,
          symParent = Nothing
        }
  DefPrimitiveType name _kind -> do
    addSymbol
      Symbol
        { symName = identText $ locVal name,
          symKind = SKType,
          symSpan = locSpan name,
          symType = Nothing,
          symDoc = Nothing,
          symParent = Nothing
        }
  DefPragma _ -> pure ()

-- | Collect symbols from a function clause.
collectClause :: Clause -> Builder ()
collectClause Clause {..} = do
  mapM_ collectPattern clausePats
  collectExpr clauseBody -- Traverse expression body to collect let bindings
  mapM_ collectLetItem (concat [clauseWhere >>= defnsToLetItems])
  where
    defnsToLetItems :: LDefinition -> [LetItem]
    defnsToLetItems (Located _ (DefValue name mTy _)) =
      [LetTypeSig name (fromMaybe (error "no type") mTy) | isJust mTy]
      where
        isJust Nothing = False
        isJust (Just _) = True
        fromMaybe _ (Just x) = x
        fromMaybe d Nothing = d
    defnsToLetItems _ = []

-- | Traverse an expression to collect symbols from let bindings and lambdas.
collectExpr :: LExpr -> Builder ()
collectExpr (Located _ expr) = case expr of
  ELet items body -> do
    mapM_ collectLetItem items
    collectExpr body
  ELetSeq items body -> do
    mapM_ collectLetItem items
    collectExpr body
  ELam pats body -> do
    mapM_ collectPattern pats
    collectExpr body
  EApp e1 e2 -> collectExpr e1 >> collectExpr e2
  EInfix e1 _ e2 -> collectExpr e1 >> collectExpr e2
  ENeg e -> collectExpr e
  EIf c t e -> collectExpr c >> collectExpr t >> collectExpr e
  ECase scrut alts -> do
    collectExpr scrut
    forM_ alts $ \Alt {..} -> do
      collectPattern altPat
      collectExpr altBody
  EDo stmts -> mapM_ collectStmt stmts
  EModule stmts -> mapM_ collectModuleStmt stmts
  ETuple es -> mapM_ collectExpr es
  EList es -> mapM_ collectExpr es
  ERecordUpd e _ -> collectExpr e
  EFieldAccess e _ -> collectExpr e
  ETypeSig e _ -> collectExpr e
  EParens e -> collectExpr e
  EBitSelect e1 e2 e3 -> collectExpr e1 >> collectExpr e2 >> collectExpr e3
  -- For other expression types, we don't need to recurse
  _ -> pure ()

-- | Collect symbols from do-notation statements.
collectStmt :: LStmt -> Builder ()
collectStmt (Located _ stmt) = case stmt of
  StmtBind pat _ expr -> collectPattern pat >> collectExpr expr
  StmtLet items -> mapM_ collectLetItem items
  StmtLetSeq items -> mapM_ collectLetItem items
  StmtAssign _ e -> collectExpr e
  StmtExpr expr -> collectExpr expr
  StmtFor init_ cond incr body -> collectStmt init_ >> collectExpr cond >> collectStmt incr >> mapM_ collectStmt body
  StmtWhile cond body -> collectExpr cond >> mapM_ collectStmt body
  StmtRepeat n body -> collectExpr n >> mapM_ collectStmt body
  StmtContinue -> pure ()
  StmtBreak -> pure ()
  StmtReturn e -> collectExpr e

-- | Collect symbols from module statements.
collectModuleStmt :: ModuleStmt -> Builder ()
collectModuleStmt stmt = case stmt of
  MStmtBind pat _mTy expr -> do
    collectPattern pat
    collectExpr expr
  MStmtLet items -> mapM_ collectLetItem items
  MStmtLetSeq items -> mapM_ collectLetItem items
  MStmtExpr expr -> collectExpr expr
  MStmtRules _rules -> pure ()
  MStmtInterface fields -> mapM_ collectInterfaceFieldFromExpr fields
  MStmtTupleInterface exprs -> mapM_ collectExpr exprs
  MStmtDef def -> collectDefinition def

-- | Collect symbols from interface fields in module expressions.
collectInterfaceFieldFromExpr :: InterfaceField -> Builder ()
collectInterfaceFieldFromExpr InterfaceField {..} = do
  parent <- gets bsParent
  -- Add the field name as a symbol
  addSymbol
    Symbol
      { symName = identText $ locVal ifName,
        symKind = SKField,
        symSpan = locSpan ifName,
        symType = Nothing,
        symDoc = Nothing,
        symParent = parent
      }
  -- Collect patterns from method parameters
  mapM_ collectPattern ifPats
  -- Traverse the field value expression
  collectExpr ifValue

-- | Collect symbols from a pattern (variables become parameters).
collectPattern :: LPattern -> Builder ()
collectPattern (Located _ pat) = case pat of
  PVar name -> do
    parent <- gets bsParent
    addSymbol
      Symbol
        { symName = identText $ locVal name,
          symKind = SKParameter,
          symSpan = locSpan name,
          symType = Nothing,
          symDoc = Nothing,
          symParent = parent
        }
  PCon _ pats -> mapM_ collectPattern pats
  PInfix p1 _ p2 -> collectPattern p1 >> collectPattern p2
  PLit _ -> pure ()
  PWild -> pure ()
  PTuple pats -> mapM_ collectPattern pats
  PList pats -> mapM_ collectPattern pats
  PRecord _ binds -> mapM_ (collectPattern . snd) binds
  PAs name p -> do
    parent <- gets bsParent
    addSymbol
      Symbol
        { symName = identText $ locVal name,
          symKind = SKParameter,
          symSpan = locSpan name,
          symType = Nothing,
          symDoc = Nothing,
          symParent = parent
        }
    collectPattern p
  PTypeSig p _ -> collectPattern p
  PParens p -> collectPattern p

-- | Collect type variable.
collectTyVar :: Located TyVar -> Builder ()
collectTyVar (Located tvSpan TyVar {..}) = do
  parent <- gets bsParent
  addSymbol
    Symbol
      { symName = identText tvName,
        symKind = SKTypeVar,
        symSpan = tvSpan,
        symType = Nothing,
        symDoc = Nothing,
        symParent = parent
      }

-- | Collect data constructor.
collectConstructor :: Located Constructor -> Builder ()
collectConstructor (Located _ Constructor {..}) = do
  parent <- gets bsParent
  -- Constructor can have multiple names (aliases), collect all of them
  forM_ conNames $ \name ->
    addSymbol
      Symbol
        { symName = identText $ locVal name,
          symKind = SKConstructor,
          symSpan = locSpan name,
          symType = Nothing,
          symDoc = Nothing,
          symParent = parent
        }
  -- Collect record fields if present
  case conRecord of
    Just fields -> mapM_ collectField fields
    Nothing -> pure ()

-- | Collect interface/record field.
collectField :: Located Field -> Builder ()
collectField (Located _ Field {..}) = do
  parent   <- gets bsParent
  typeText <- fmtQT (locVal fieldType)
  addSymbol
    Symbol
      { symName = identText $ locVal fieldName,
        symKind = SKField,
        symSpan = locSpan fieldName,
        symType = Just typeText,
        symDoc = Nothing,
        symParent = parent
      }

-- | Collect class member.
collectClassMember :: ClassMember -> Builder ()
collectClassMember member = case member of
  ClassMethod name ty _ -> do
    parent   <- gets bsParent
    typeText <- fmtQT (locVal ty)
    addSymbol
      Symbol
        { symName = identText $ locVal name,
          symKind = SKFunction,
          symSpan = locSpan name,
          symType = Just typeText,
          symDoc = Nothing,
          symParent = parent
        }
  ClassDefaultImpl name pats _ -> do
    parent <- gets bsParent
    addSymbol
      Symbol
        { symName = identText $ locVal name,
          symKind = SKFunction,
          symSpan = locSpan name,
          symType = Nothing,
          symDoc = Nothing,
          symParent = parent
        }
    withParent (identText $ locVal name) $ mapM_ collectPattern pats
  ClassFixity _ -> pure ()

-- | Collect instance member.
collectInstanceMember :: InstanceMember -> Builder ()
collectInstanceMember (InstanceMethod name clauses) = do
  parent <- gets bsParent
  addSymbol
    Symbol
      { symName = identText $ locVal name,
        symKind = SKFunction,
        symSpan = locSpan name,
        symType = Nothing,
        symDoc = Nothing,
        symParent = parent
      }
  withParent (identText $ locVal name) $ mapM_ collectClause clauses
collectInstanceMember (InstanceTypeSig name ty) = do
  parent   <- gets bsParent
  typeText <- fmtQT (locVal ty)
  addSymbol
    Symbol
      { symName = identText $ locVal name,
        symKind = SKFunction,
        symSpan = locSpan name,
        symType = Just typeText,
        symDoc = Nothing,
        symParent = parent
      }

-- | Collect symbols from let items.
collectLetItem :: LetItem -> Builder ()
collectLetItem item = case item of
  LetTypeSig name ty -> do
    parent   <- gets bsParent
    typeText <- fmtQT (locVal ty)
    addSymbol
      Symbol
        { symName = identText $ locVal name,
          symKind = SKVariable,
          symSpan = locSpan name,
          symType = Just typeText,
          symDoc = Nothing,
          symParent = parent
        }
  LetBind Binding {..} -> do
    parent   <- gets bsParent
    typeText <- traverse (fmtQT . locVal) bindType
    -- Get name and span from pattern (if it's a simple variable)
    case getPatternNameAndSpan bindPat of
      Just (name, nameSpan) -> do
        addSymbol
          Symbol
            { symName = name,
              symKind = SKVariable,
              symSpan = nameSpan, -- Use the name's span, not the whole binding span
              symType = typeText,
              symDoc = Nothing,
              symParent = parent
            }
        withParent name $ do
          mapM_ collectPattern bindArgs
          -- Traverse the binding body to collect nested let bindings
          collectExpr bindExpr
      Nothing -> collectPattern bindPat
    where
      getPatternNameAndSpan (Located _ (PVar n)) = Just (identText $ locVal n, locSpan n)
      getPatternNameAndSpan _ = Nothing

--------------------------------------------------------------------------------
-- Queries
--------------------------------------------------------------------------------

-- | Look up symbol at a position.
lookupAtPosition :: SymbolTable -> Pos -> Maybe Symbol
lookupAtPosition st pos = case filter (containsPos pos . fst) (stByPosition st) of
  [] -> Nothing
  xs -> Just $ snd $ minimumBySpanSize xs
  where
    containsPos p ss =
      spanBegin ss <= p && p <= spanFinal ss

    minimumBySpanSize = foldr1 (\a b -> if spanSize (fst a) < spanSize (fst b) then a else b)

    spanSize ss =
      let start = spanBegin ss
          end   = spanFinal ss
       in (posLine end - posLine start) * 1000 + (posColumn end - posColumn start)

-- | Look up symbols by name.
lookupByName :: SymbolTable -> Text -> [Symbol]
lookupByName st name = Map.findWithDefault [] name (stDefinitions st)

-- | Get all symbols.
getAllSymbols :: SymbolTable -> [Symbol]
getAllSymbols = concat . Map.elems . stDefinitions
