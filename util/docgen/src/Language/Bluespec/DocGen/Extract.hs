-- | Extract documentation entries from parsed Bluespec packages.
--
-- Walks the 'Package' AST, collects consecutive @--\@@ or @-- |@ comment
-- lines immediately before each definition, and attaches them to a 'DocEntry'.
module Language.Bluespec.DocGen.Extract
  ( extractDocsFromFile
  , extractDocsFromSource
  ) where

import Data.Maybe (mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO

import Language.Bluespec.DocGen.DocAST
import Language.Bluespec.DocGen.TexParser (parseDocComment)
import Language.Bluespec.DocGen.PlainParser (parsePlainComment)

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

-- | Extract documentation entries from a @.bs@ or @.bsv@ file.
extractDocsFromFile :: FilePath -> IO [DocEntry]
extractDocsFromFile path = do
  src <- TIO.readFile path
  pure $ extractDocsFromSource (T.pack path) src

-- | Extract documentation entries from source text.
extractDocsFromSource :: Text -> Text -> [DocEntry]
extractDocsFromSource filePath src =
  -- First try to parse to get the package name; if parse fails, fall back to
  -- scanning the raw source lines.
  let pkgName  = extractPackageName src
      lines_   = T.lines src
      groups   = collectCommentGroups lines_
  in mapMaybe (groupToEntry filePath pkgName) groups

-- ---------------------------------------------------------------------------
-- Package name extraction
-- ---------------------------------------------------------------------------

extractPackageName :: Text -> Text
extractPackageName src =
  case mapMaybe parseLine (T.lines src) of
    (name : _) -> name
    []         -> "Unknown"
  where
    parseLine line =
      let t = T.strip line
      in if "package " `T.isPrefixOf` t
           then let rest = T.strip $ T.drop 8 t
                    name = T.takeWhile isIdentChar rest
                in if T.null name then Nothing else Just name
           else Nothing
    isIdentChar c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
                 || (c >= '0' && c <= '9') || c == '_'

-- ---------------------------------------------------------------------------
-- Comment group collection
-- ---------------------------------------------------------------------------

-- | A comment group: consecutive doc-comment lines immediately preceding a
-- definition line, plus the definition line itself.
data CommentGroup = CommentGroup
  { cgStyle   :: !CommentStyle
  , cgLines   :: ![Text]       -- ^ doc comment lines (raw, with prefix)
  , cgDefLine :: !(Maybe Text) -- ^ the definition line following the comments
  , cgLineNo  :: !Int          -- ^ 1-indexed line number of first comment line
  } deriving stock (Show)

data CommentStyle = StyleAt | StylePipe | StyleMixed
  deriving stock (Show, Eq)

collectCommentGroups :: [Text] -> [CommentGroup]
collectCommentGroups lines_ = go (zip [1..] lines_) []
  where
    go [] _ = []
    go ((n, l) : rest) acc
      | isAtLine l    = go rest ((n, l) : acc)
      | isPipeLine l  = go rest ((n, l) : acc)
      | null acc      = go rest []
      | otherwise     =
          -- `l` is the definition line following the accumulated comments
          let revAcc = reverse acc
              style  = inferStyle (map snd revAcc)
              grp    = CommentGroup
                { cgStyle   = style
                , cgLines   = map snd revAcc
                , cgDefLine = Just l
                , cgLineNo  = fst (head revAcc)
                }
          in grp : go rest []

    isAtLine t   = "--@ " `T.isPrefixOf` T.strip t || "--@" == T.strip t
    isPipeLine t = "-- | " `T.isPrefixOf` T.strip t || "-- |" == T.strip t

    inferStyle ls
      | all isAtLine ls   = StyleAt
      | all isPipeLine ls = StylePipe
      | otherwise         = StyleMixed

-- ---------------------------------------------------------------------------
-- Convert comment group to DocEntry
-- ---------------------------------------------------------------------------

groupToEntry :: Text -> Text -> CommentGroup -> Maybe DocEntry
groupToEntry filePath pkgName grp = do
  defLine <- cgDefLine grp
  name    <- extractDefName defLine
  let docBlocks = case cgStyle grp of
        StyleAt   -> parseDocComment (cgLines grp)
        StylePipe -> parsePlainComment (cgLines grp)
        StyleMixed -> parseDocComment (cgLines grp)   -- best effort
      kind      = inferKind defLine
      typeSig   = extractTypeSig defLine
      lineNo    = cgLineNo grp
  pure DocEntry
    { dePackage  = pkgName
    , deName     = name
    , deSection  = "stdlib"
    , deKind     = kind
    , deTypeSig  = typeSig
    , deDoc      = docBlocks
    , deSpan     = SrcSpan filePath lineNo lineNo
    }

-- ---------------------------------------------------------------------------
-- Definition line parsing (heuristic, good-enough for doc extraction)
-- ---------------------------------------------------------------------------

-- | Extract the defined name from a definition line.
extractDefName :: Text -> Maybe Text
extractDefName line =
  let t = T.strip line
  in firstOf
    [ extractAfterKeyword "interface " t
    , extractAfterKeyword "typedef "   t
    , extractAfterKeyword "typeclass " t
    , extractAfterKeyword "instance "  t
    , extractAfterKeyword "struct "    t
    , extractValueName t
    ]
  where
    firstOf []     = Nothing
    firstOf (x:xs) = case x of { Nothing -> firstOf xs; Just _ -> x }

    extractAfterKeyword kw s
      | kw `T.isPrefixOf` s = Just $ T.takeWhile isIdentChar (T.drop (T.length kw) s)
      | otherwise            = Nothing

    -- Value/function definition: "foo :: ..." or "foo ..." (Classic)
    -- or "function ... foo(" (BSV)
    extractValueName s
      | "function " `T.isPrefixOf` s =
          -- BSV: function <type> <name>(...
          let afterFunc = T.strip $ T.drop 9 s
              -- skip past the return type to the function name
              skipType t = T.strip $ T.dropWhile (/= ' ') t
              name = T.takeWhile isIdentChar (skipType afterFunc)
          in if T.null name then Nothing else Just name
      | otherwise =
          -- Classic: name :: ... or name x = ...
          let name = T.takeWhile isIdentChar s
          in if T.null name || isKeyword name then Nothing else Just name

    isIdentChar c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
                 || (c >= '0' && c <= '9') || c == '_' || c == '\''

    isKeyword w = w `elem`
      ["import", "export", "package", "where", "let", "in", "do",
       "if", "then", "else", "case", "of", "module", "endmodule",
       "begin", "end", "rule", "endrule", "rules", "endrules"]

-- | Infer the kind of definition from the first line.
inferKind :: Text -> DocKind
inferKind line =
  let t = T.strip line
  in if any (`T.isPrefixOf` t) ["interface ", "struct "]   then DKType
     else if "typedef " `T.isPrefixOf` t                   then DKType
     else if "typeclass " `T.isPrefixOf` t                 then DKClass
     else if "instance " `T.isPrefixOf` t                  then DKInstance
     else                                                        DKValue

-- | Extract a type signature from a Classic definition line.
-- Returns the portion after @::@, or @Nothing@ for non-annotated defs.
extractTypeSig :: Text -> Maybe Text
extractTypeSig line =
  case T.breakOn "::" line of
    (_, rest) | not (T.null rest) -> Just (T.strip (T.drop 2 rest))
    _                             -> Nothing

