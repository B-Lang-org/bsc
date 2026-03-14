-- | Code completion for Bluespec LSP.
--
-- Provides three kinds of completions:
--  * Scope completions: identifier prefix → matching names in scope
--  * Dot completions: receiver._ → fields/methods of the receiver's interface
--  * Import completions: `import ` → known module names
module Language.Bluespec.LSP.Completion
  ( getCompletions
  ) where

import Data.List (isPrefixOf, nubBy)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T

import Language.LSP.Protocol.Types hiding (SymbolKind)

import Language.Bluespec.LSP.State (ServerState (..), DocumentState (..), ModuleInfo (..), getPreludeSymbols)
import Language.Bluespec.LSP.SymbolTable (Symbol (..), SymbolKind (..), getAllSymbols, formatQualType, formatQualTypeExpanded)
import Language.Bluespec.LSP.TypeEnv (TypeEnv (..), lookupVarType)
import Language.Bluespec.LSP.Util (getIdentifierAtPosition)
import Language.Bluespec.Position (Located (..), locVal)
import Language.Bluespec.Syntax

-- | Bluespec Classic keywords.
bluespecKeywords :: [Text]
bluespecKeywords =
  [ "module", "endmodule", "interface", "endinterface"
  , "function", "endfunction", "rule", "endrule"
  , "method", "endmethod", "action", "endaction", "actionvalue"
  , "typedef", "struct", "enum", "union", "tagged"
  , "import", "export", "package", "endpackage"
  , "let", "letseq", "return", "if", "else", "case", "matches"
  , "begin", "end", "for", "while", "repeat"
  , "provisos", "deriving", "instance", "class"
  , "rules", "endrules", "when"
  , "type", "numeric", "string"
  ]

-- | Get completions for a given position.
-- Dispatches to dot completions, import completions, or scope completions.
getCompletions :: ServerState -> DocumentState -> Text -> Position -> [CompletionItem]
getCompletions serverState doc sourceText pos@(Position line col) =
  let textLines = T.lines sourceText
      lineText  = if fromIntegral line < length textLines
                     then textLines !! fromIntegral line
                     else ""
      -- Text to the left of the cursor on this line
      prefix    = T.take (fromIntegral col) lineText
   in if "." `T.isSuffixOf` prefix
        -- Dot completions: receiver.
        then dotCompletions serverState doc prefix
        else if isImportLine prefix
          -- Import completions
          then importCompletions serverState prefix
          -- Scope completions: all names matching partial identifier
          else scopeCompletions serverState doc sourceText pos

-- | Check if a line looks like an import statement.
isImportLine :: Text -> Bool
isImportLine t = "import " `T.isPrefixOf` T.stripStart t

-- ---------------------------------------------------------------------------
-- Dot completions
-- ---------------------------------------------------------------------------

-- | Get completions after a dot: receiver.
-- Looks up the receiver's type in the TypeEnv, then returns the
-- fields/methods of its interface.  Falls back to imported module TypeEnvs
-- when the struct is not defined locally.
dotCompletions :: ServerState -> DocumentState -> Text -> [CompletionItem]
dotCompletions serverState doc prefix =
  let receiverPart = T.dropEnd 1 prefix  -- drop the trailing '.'
      -- Extract the identifier immediately before the dot
      mReceiver = extractLastIdent receiverPart
  in case mReceiver of
       Nothing  -> []
       Just recv ->
         let tenv = dsTypeEnv doc
             -- Build a merged TypeEnv including all indexed modules (for struct defs)
             mergedStructs = Map.unions $
               teStructs tenv
               : map (teStructs . miTypeEnv) (Map.elems (ssModuleIndex serverState))
             tenvMerged = tenv { teStructs = mergedStructs }
         in case lookupVarType tenv recv of
              Nothing  -> []
              Just qty ->
                let ty = locVal (qtType qty)
                in fieldsForType tenvMerged ty

-- | Extract the last identifier in a piece of text (before a dot).
extractLastIdent :: Text -> Maybe Text
extractLastIdent t =
  let cs = T.unpack t
      end = length cs - 1
  in if end < 0 then Nothing
     else
       let e = findEnd cs end
           s = findStart cs e
           ident = T.pack $ take (e - s + 1) (drop s cs)
       in if T.null ident then Nothing else Just ident
  where
    isIdentChar c = c `elem` (['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ "_'")
    findEnd cs i
      | i < 0     = 0
      | isIdentChar (cs !! i) = i
      | otherwise = findEnd cs (i - 1)
    findStart cs i
      | i <= 0    = 0
      | isIdentChar (cs !! (i - 1)) = findStart cs (i - 1)
      | otherwise = i

-- | Get the fields/methods for a type from the TypeEnv.
fieldsForType :: TypeEnv -> Type -> [CompletionItem]
fieldsForType tenv ty =
  case resolveTypeName ty of
    Nothing   -> []
    Just name -> case Map.lookup name (teStructs tenv) of
      Nothing     -> []
      Just fields -> map fieldToCompletion fields

-- | Extract the outermost type constructor name from a type.
resolveTypeName :: Type -> Maybe Text
resolveTypeName (TCon qi) =
  case locVal qi of
    QualIdent _ ident -> Just (identText ident)
resolveTypeName (TApp f _) =
  resolveTypeName (locVal f)
resolveTypeName _ = Nothing

-- | Convert a Field to a CompletionItem.
fieldToCompletion :: Field -> CompletionItem
fieldToCompletion Field { fieldName, fieldType } =
  CompletionItem
    { _label               = identText (locVal fieldName)
    , _labelDetails        = Nothing
    , _kind                = Just CompletionItemKind_Field
    , _tags                = Nothing
    , _detail              = Just (formatQualType (locVal fieldType))
    , _documentation       = Nothing
    , _deprecated          = Nothing
    , _preselect           = Nothing
    , _sortText            = Nothing
    , _filterText          = Nothing
    , _insertText          = Nothing
    , _insertTextFormat    = Nothing
    , _insertTextMode      = Nothing
    , _textEdit            = Nothing
    , _textEditText        = Nothing
    , _additionalTextEdits = Nothing
    , _commitCharacters    = Nothing
    , _command             = Nothing
    , _data_                = Nothing
    }

-- ---------------------------------------------------------------------------
-- Import completions
-- ---------------------------------------------------------------------------

-- | Complete module names on import lines.
importCompletions :: ServerState -> Text -> [CompletionItem]
importCompletions serverState prefix =
  let modPrefix = extractModulePrefix prefix
      allModules = Map.keys (ssModuleIndex serverState)
      matching   = filter (T.isPrefixOf modPrefix) allModules
  in map moduleToCompletion matching

-- | Extract the partial module name from an import line prefix.
extractModulePrefix :: Text -> Text
extractModulePrefix t =
  case T.stripPrefix "import " (T.stripStart t) of
    Nothing  -> ""
    Just rest -> T.takeWhile (\c -> c /= ' ' && c /= ';' && c /= ':') (T.stripStart rest)

-- | Convert a module name to a CompletionItem.
moduleToCompletion :: Text -> CompletionItem
moduleToCompletion name =
  CompletionItem
    { _label               = name
    , _labelDetails        = Nothing
    , _kind                = Just CompletionItemKind_Module
    , _tags                = Nothing
    , _detail              = Just "module"
    , _documentation       = Nothing
    , _deprecated          = Nothing
    , _preselect           = Nothing
    , _sortText            = Nothing
    , _filterText          = Nothing
    , _insertText          = Nothing
    , _insertTextFormat    = Nothing
    , _insertTextMode      = Nothing
    , _textEdit            = Nothing
    , _textEditText        = Nothing
    , _additionalTextEdits = Nothing
    , _commitCharacters    = Nothing
    , _command             = Nothing
    , _data_                = Nothing
    }

-- ---------------------------------------------------------------------------
-- Scope completions
-- ---------------------------------------------------------------------------

-- | Get scope completions: all names that start with the partial identifier at cursor.
scopeCompletions :: ServerState -> DocumentState -> Text -> Position -> [CompletionItem]
scopeCompletions serverState doc sourceText pos =
  let partial = case getIdentifierAtPosition sourceText pos of
                   Nothing    -> ""
                   Just ident -> ident
      -- Collect symbols from: local doc, imports, prelude, keywords
      localSyms   = getAllSymbols (dsSymbols doc)
      preludeSyms = maybe [] getAllSymbols (getPreludeSymbols serverState)
      indexedSyms = concatMap (getAllSymbols . miSymbols)
                              (Map.elems (ssModuleIndex serverState))
      allSyms     = localSyms ++ preludeSyms ++ indexedSyms
      -- Deduplicate by name
      uniqueSyms  = nubBy (\a b -> symName a == symName b) allSyms
      -- Filter by prefix
      matching    = filter (\s -> T.unpack partial `isPrefixOf` T.unpack (symName s)) uniqueSyms
      tenv        = dsTypeEnv doc
      symItems    = map (symbolToCompletionWithEnv tenv) matching
      -- Add keyword completions
      kwItems     = if T.null partial
                       then []
                       else [ keywordToCompletion kw
                            | kw <- bluespecKeywords
                            , T.unpack partial `isPrefixOf` T.unpack kw ]
  in symItems ++ kwItems

-- | Convert a Symbol to a CompletionItem, enriching missing type from TypeEnv.
symbolToCompletionWithEnv :: TypeEnv -> Symbol -> CompletionItem
symbolToCompletionWithEnv tenv sym =
  case symType sym of
    Just _  -> symbolToCompletion sym
    Nothing ->
      case lookupVarType tenv (symName sym) of
        Nothing -> symbolToCompletion sym
        Just qt ->
          symbolToCompletion sym
            { symType = Just (formatQualTypeExpanded (teAliases tenv) qt) }

-- | Convert a Symbol to a CompletionItem.
symbolToCompletion :: Symbol -> CompletionItem
symbolToCompletion sym =
  CompletionItem
    { _label               = symName sym
    , _labelDetails        = Nothing
    , _kind                = Just (symKindToCompletionKind (symKind sym))
    , _tags                = Nothing
    , _detail              = symType sym
    , _documentation       = Nothing
    , _deprecated          = Nothing
    , _preselect           = Nothing
    , _sortText            = Nothing
    , _filterText          = Nothing
    , _insertText          = Nothing
    , _insertTextFormat    = Nothing
    , _insertTextMode      = Nothing
    , _textEdit            = Nothing
    , _textEditText        = Nothing
    , _additionalTextEdits = Nothing
    , _commitCharacters    = Nothing
    , _command             = Nothing
    , _data_               = Nothing
    }

-- | Convert a keyword to a CompletionItem.
keywordToCompletion :: Text -> CompletionItem
keywordToCompletion kw =
  CompletionItem
    { _label               = kw
    , _labelDetails        = Nothing
    , _kind                = Just CompletionItemKind_Keyword
    , _tags                = Nothing
    , _detail              = Nothing
    , _documentation       = Nothing
    , _deprecated          = Nothing
    , _preselect           = Nothing
    , _sortText            = Nothing
    , _filterText          = Nothing
    , _insertText          = Nothing
    , _insertTextFormat    = Nothing
    , _insertTextMode      = Nothing
    , _textEdit            = Nothing
    , _textEditText        = Nothing
    , _additionalTextEdits = Nothing
    , _commitCharacters    = Nothing
    , _command             = Nothing
    , _data_               = Nothing
    }

-- | Map SymbolKind to CompletionItemKind.
symKindToCompletionKind :: SymbolKind -> CompletionItemKind
symKindToCompletionKind SKModule      = CompletionItemKind_Module
symKindToCompletionKind SKType        = CompletionItemKind_TypeParameter
symKindToCompletionKind SKData        = CompletionItemKind_Enum
symKindToCompletionKind SKInterface   = CompletionItemKind_Interface
symKindToCompletionKind SKClass       = CompletionItemKind_Class
symKindToCompletionKind SKFunction    = CompletionItemKind_Function
symKindToCompletionKind SKConstructor = CompletionItemKind_Constructor
symKindToCompletionKind SKField       = CompletionItemKind_Field
symKindToCompletionKind SKTypeVar     = CompletionItemKind_TypeParameter
symKindToCompletionKind SKVariable    = CompletionItemKind_Variable
symKindToCompletionKind SKParameter   = CompletionItemKind_Variable
