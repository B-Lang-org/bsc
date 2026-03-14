-- | Go-to-definition implementation for Bluespec LSP.
module Language.Bluespec.LSP.Definition
  ( getDefinition,
    getDefinitionCrossFile,
  )
where

import Data.List (sortOn)
import Data.Map.Strict qualified as Map
import Data.Maybe (listToMaybe, mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Language.Bluespec.LSP.State (ModuleInfo (..), ServerState (..), getModuleSymbols, getPreludeSymbols)
import Language.Bluespec.LSP.SymbolTable
import Language.Bluespec.LSP.Util (spanToRange, positionToPos, getIdentifierAtPosition)
import Language.Bluespec.Position (Pos (..), SrcSpan (..))
import Language.Bluespec.Syntax (ModuleId (..))
import Language.LSP.Protocol.Types

-- | Get definition location for symbol at a position.
-- First tries to find a definition at the exact position (for when cursor is on a definition).
-- If that fails, extracts the identifier at the position and looks it up by name.
getDefinition :: SymbolTable -> Text -> Position -> Maybe Location
getDefinition st sourceText pos =
  -- First try: exact position match (cursor is on a definition site)
  case lookupAtPosition st (positionToPos pos) of
    Just sym -> Just $ symbolToLocation sym
    Nothing ->
      -- Second try: extract identifier at position and look up by name
      case getIdentifierAtPosition sourceText pos of
        Nothing -> Nothing
        Just ident -> case lookupByName st ident of
          [] -> Nothing
          syms ->
            -- Select the closest definition before the cursor position
            let best = selectBestSymbol (positionToPos pos) syms
             in Just $ symbolToLocation best

-- | Select the best matching symbol for a given cursor position.
-- Prefers symbols based on:
-- 1. Only consider symbols defined before the cursor
-- 2. For symbols on the SAME line as cursor, prefer the closest one before cursor
-- 3. For symbols on DIFFERENT lines, prefer function-scoped parameters over
--    let-bound variables (which have limited scope)
selectBestSymbol :: Pos -> [Symbol] -> Symbol
selectBestSymbol cursorPos syms =
  -- Filter to symbols defined at or before cursor position
  let beforeCursor = filter (isBeforeOrAt cursorPos) syms
   in case beforeCursor of
        [] -> head syms -- Fall back to first if none before cursor
        candidates ->
          -- First, check if any candidates are on the same line as cursor
          let sameLine = filter (isSameLine cursorPos) candidates
              diffLine = filter (not . isSameLine cursorPos) candidates
           in case sameLine of
                -- If there are same-line candidates, pick the closest one
                (_ : _) -> head $ sortOn (negate . defPosition) sameLine
                -- Otherwise, for different-line candidates, prefer function parameters
                -- over let-bound variables (let bindings have limited scope)
                [] -> selectFromDiffLine cursorPos diffLine
  where
    isBeforeOrAt pos s =
      let symPos = spanBegin (symSpan s)
       in posLine symPos < posLine pos
            || (posLine symPos == posLine pos && posColumn symPos <= posColumn pos)

    isSameLine pos s = posLine (spanBegin (symSpan s)) == posLine pos

    defPosition s =
      let p = spanBegin (symSpan s)
       in posLine p * 10000 + posColumn p

    -- For symbols on different lines, we need to distinguish:
    -- 1. Same symbol (same parent) - e.g., type sig vs definition → pick closest
    -- 2. Different scopes (different parents) - e.g., outer x vs inner x → pick outer (earliest)
    selectFromDiffLine _pos candidates =
      -- Group by parent
      let byParent = groupByParent candidates
       in if length byParent == 1
            -- All have same parent → pick closest (highest position)
            then head $ sortOn (negate . defPosition) candidates
            -- Different parents (shadowing) → pick from earliest parent (outer scope)
            else
              let earliestParentGroup = head $ sortOn (minimum . map defPosition) byParent
               in head $ sortOn (negate . defPosition) earliestParentGroup

    groupByParent :: [Symbol] -> [[Symbol]]
    groupByParent [] = []
    groupByParent (s : ss) =
      let (same, diff) = partition (\x -> symParent x == symParent s) ss
       in (s : same) : groupByParent diff

    partition :: (a -> Bool) -> [a] -> ([a], [a])
    partition _ [] = ([], [])
    partition p (x : xs) =
      let (yes, no) = partition p xs
       in if p x then (x : yes, no) else (yes, x : no)

-- | Get definition location with cross-file resolution.
-- If the symbol is not found in the current file, searches imported modules,
-- then falls back to the Prelude for builtin types.
getDefinitionCrossFile :: ServerState -> SymbolTable -> Text -> Position -> Maybe Location
getDefinitionCrossFile serverState st sourceText pos =
  -- First try: local lookup
  case getDefinition st sourceText pos of
    Just loc -> Just loc
    Nothing ->
      -- Extract identifier and search in imported modules
      case getIdentifierAtPosition sourceText pos of
        Nothing -> Nothing
        Just ident ->
          -- Handle qualified names (e.g., "Module.symbol")
          let (mModQual, symName) = parseQualifiedName ident
           in case mModQual of
                -- Qualified: look in specific module
                Just modName -> lookupInModule serverState modName symName
                -- Unqualified: search all imports, then fall back to Prelude
                Nothing -> case lookupInImports serverState (stImports st) ident of
                  Just loc -> Just loc
                  Nothing -> case lookupInModuleIndexByName serverState ident of
                    Just loc -> Just loc
                    Nothing -> lookupInPrelude serverState ident

-- | Parse a potentially qualified name into (Maybe module, symbol).
parseQualifiedName :: Text -> (Maybe Text, Text)
parseQualifiedName name =
  case T.breakOnEnd "." name of
    ("", n) -> (Nothing, n) -- No dot, unqualified
    (modPart, n) ->
      let modName = T.dropEnd 1 modPart -- Remove trailing dot
       in if T.null modName || T.null n
            then (Nothing, name) -- Invalid, treat as unqualified
            else (Just modName, n)

-- | Look up a symbol in a specific module's symbol table.
lookupInModule :: ServerState -> Text -> Text -> Maybe Location
lookupInModule serverState modName symName =
  case getModuleSymbols modName serverState of
    Nothing -> Nothing
    Just modSt -> case lookupByName modSt symName of
      [] -> Nothing
      (sym : _) -> Just $ symbolToLocation sym

-- | Look up a symbol in imported modules.
lookupInImports :: ServerState -> [ImportInfo] -> Text -> Maybe Location
lookupInImports serverState imports symName =
  listToMaybe $ mapMaybe tryImport imports
  where
    tryImport imp =
      let modName = unModuleId (iiModule imp)
       in lookupInModule serverState modName symName

-- | Look up a symbol by name across all indexed modules.
-- Returns a location only when the symbol name is unambiguous.
lookupInModuleIndexByName :: ServerState -> Text -> Maybe Location
lookupInModuleIndexByName serverState symName =
  case allMatches of
    [loc] -> Just loc
    _ -> Nothing
  where
    moduleInfos = Map.elems (ssModuleIndex serverState)
    allMatches =
      concatMap
        (\info -> map symbolToLocation (lookupByName (miSymbols info) symName))
        moduleInfos

-- | Look up a symbol in the Prelude (builtin types and type classes).
lookupInPrelude :: ServerState -> Text -> Maybe Location
lookupInPrelude serverState symName =
  case getPreludeSymbols serverState of
    Nothing -> Nothing
    Just preludeSt -> case lookupByName preludeSt symName of
      [] -> Nothing
      (sym : _) -> Just $ symbolToLocation sym

-- | Convert a symbol to a location.
symbolToLocation :: Symbol -> Location
symbolToLocation sym =
  Location
    { _uri = spanToUri (symSpan sym),
      _range = spanToRange (symSpan sym)
    }

-- | Convert file path from SrcSpan to URI.
-- For now, we use the file path from the span.
-- In practice, we'd need to resolve this to a proper file URI.
spanToUri :: SrcSpan -> Uri
spanToUri SrcSpan {..} = Uri $ "file://" <> spanFile

