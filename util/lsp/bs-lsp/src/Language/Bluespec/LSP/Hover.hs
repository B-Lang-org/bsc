-- | Hover information provider for Bluespec LSP.
module Language.Bluespec.LSP.Hover
  ( getHoverInfo
  , getHoverInfoCrossFile
  , symbolToHover
  ) where

import Data.List (sortOn)
import Data.Map.Strict qualified as Map
import Data.Maybe (listToMaybe, mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T

import Language.LSP.Protocol.Types hiding (SymbolKind)

import Language.Bluespec.Position (Pos (..), SrcSpan (..))
import Language.Bluespec.LSP.State (ServerState (..), ModuleInfo (..), getPreludeSymbols)
import Language.Bluespec.LSP.SymbolTable
import Language.Bluespec.LSP.TypeEnv (TypeEnv (..), lookupVarType)
import Language.Bluespec.LSP.Util (spanToRange, positionToPos, getIdentifierAtPosition, parseQualifiedName)
import Language.Bluespec.Syntax (ModuleId (..))

-- | Get hover information for a symbol at a position.
-- First tries position-based lookup (cursor on definition), then falls back to
-- name-based lookup (cursor on usage/reference).
-- Uses the TypeEnv to fill in types for symbols that lack them (e.g. module-local bindings).
getHoverInfo :: TypeEnv -> SymbolTable -> Text -> Position -> Maybe Hover
getHoverInfo tenv st sourceText pos =
  case lookupAtPosition st (positionToPos pos) of
    Just sym -> Just $ symbolToHoverWithEnv tenv (enrichFromSiblings st sym)
    Nothing  ->
      -- Try name-based lookup: extract identifier at position, search by name
      case getIdentifierAtPosition sourceText pos of
        Nothing    -> Nothing
        Just ident -> case lookupByName st ident of
          []   -> Nothing
          syms ->
            let best = selectBestForHover (positionToPos pos) syms
            in Just $ symbolToHoverWithEnv tenv (enrichFromSiblings st best)

-- | Get hover information with cross-file fallback.
-- Searches imports and prelude when the symbol is not found locally.
getHoverInfoCrossFile :: ServerState -> TypeEnv -> SymbolTable -> Text -> Position -> Maybe Hover
getHoverInfoCrossFile serverState tenv st sourceText pos =
  case getHoverInfo tenv st sourceText pos of
    Just h  -> Just h
    Nothing ->
      case getIdentifierAtPosition sourceText pos of
        Nothing    -> Nothing
        Just ident ->
          let (mModQual, symName) = parseQualifiedName ident
          in case mModQual of
               Just modName -> fmap symbolToHover $ lookupSymInModule serverState modName symName
               Nothing      ->
                 case lookupSymInImports serverState (stImports st) ident of
                   Just sym -> Just (symbolToHover sym)
                   Nothing  ->
                     case lookupSymInModuleIndex serverState ident of
                       Just sym -> Just (symbolToHover sym)
                       Nothing  -> fmap symbolToHover $ lookupSymInPrelude serverState ident

-- | Select best symbol for hover given cursor position.
-- Prefers the symbol whose definition is closest to (but before) the cursor.
selectBestForHover :: Pos -> [Symbol] -> Symbol
selectBestForHover curPos syms =
  let beforeCursor = filter (\s -> spanBegin (symSpan s) `posLe` curPos) syms
  in case beforeCursor of
       []  -> head syms
       bcs -> head $ sortOn (negate . defPos) bcs
  where
    posLe p1 p2 = posLine p1 < posLine p2
                  || (posLine p1 == posLine p2 && posColumn p1 <= posColumn p2)
    defPos s = let p = spanBegin (symSpan s)
               in posLine p * 10000 + posColumn p

-- | Look up a symbol in a specific module.
lookupSymInModule :: ServerState -> Text -> Text -> Maybe Symbol
lookupSymInModule serverState modName symName =
  case Map.lookup modName (ssModuleIndex serverState) of
    Nothing   -> Nothing
    Just info -> case lookupByName (miSymbols info) symName of
      []      -> Nothing
      (s : _) -> Just s

-- | Look up a symbol in imported modules.
lookupSymInImports :: ServerState -> [ImportInfo] -> Text -> Maybe Symbol
lookupSymInImports serverState imports symName =
  listToMaybe $ mapMaybe tryImport imports
  where
    tryImport imp = lookupSymInModule serverState (unModuleId (iiModule imp)) symName

-- | Look up a symbol across all indexed modules (only when unambiguous).
lookupSymInModuleIndex :: ServerState -> Text -> Maybe Symbol
lookupSymInModuleIndex serverState symName =
  case allMatches of
    [s] -> Just s
    _   -> Nothing
  where
    allMatches = concatMap (\info -> lookupByName (miSymbols info) symName)
                           (Map.elems (ssModuleIndex serverState))

-- | Look up a symbol in the prelude.
lookupSymInPrelude :: ServerState -> Text -> Maybe Symbol
lookupSymInPrelude serverState symName =
  case getPreludeSymbols serverState of
    Nothing      -> Nothing
    Just prelude -> case lookupByName prelude symName of
      []      -> Nothing
      (s : _) -> Just s

-- | If a symbol has no type, fill it from a sibling declaration with the same
-- name that does have one (e.g. a LetTypeSig / DefTypeSig alongside the
-- corresponding LetBind / DefValue).
enrichFromSiblings :: SymbolTable -> Symbol -> Symbol
enrichFromSiblings st sym = case symType sym of
  Just _  -> sym
  Nothing ->
    let siblings  = lookupByName st (symName sym)
        sibType   = listToMaybe (mapMaybe symType siblings)
    in sym { symType = sibType }

-- | Convert a symbol to hover, enriching missing type info from TypeEnv.
symbolToHoverWithEnv :: TypeEnv -> Symbol -> Hover
symbolToHoverWithEnv tenv sym =
  case symType sym of
    Just _  -> symbolToHover sym
    Nothing ->
      case lookupVarType tenv (symName sym) of
        Nothing -> symbolToHover sym
        Just qt ->
          let typeText = formatQualTypeExpanded (teAliases tenv) qt
          in symbolToHover sym { symType = Just typeText }

-- | Convert a symbol to hover information.
symbolToHover :: Symbol -> Hover
symbolToHover sym = Hover
  { _contents = InL $ MarkupContent MarkupKind_Markdown content
  , _range    = Just $ spanToRange (symSpan sym)
  }
  where
    content = T.unlines $ filter (not . T.null)
      [ "**" <> kindLabel (symKind sym) <> "** `" <> symName sym <> "`"
      , ""
      , maybe "" (\t -> "```bluespec\n" <> t <> "\n```") (symType sym)
      , maybe "" (\d -> "\n---\n" <> d) (symDoc sym)
      , maybe "" (\p -> "\n*Defined in: " <> p <> "*") (symParent sym)
      ]

-- | Get human-readable label for symbol kind.
kindLabel :: SymbolKind -> Text
kindLabel SKModule      = "module"
kindLabel SKType        = "type"
kindLabel SKData        = "data"
kindLabel SKInterface   = "interface"
kindLabel SKClass       = "class"
kindLabel SKFunction    = "function"
kindLabel SKConstructor = "constructor"
kindLabel SKField       = "field"
kindLabel SKTypeVar     = "type variable"
kindLabel SKVariable    = "variable"
kindLabel SKParameter   = "parameter"
