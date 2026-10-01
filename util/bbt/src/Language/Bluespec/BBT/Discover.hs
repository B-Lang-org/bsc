-- | Source file discovery and package-name conflict detection.
--
-- Bluespec has no namespace system: every @.bs@/@.bsv@ file declares
-- @package Foo where@, and @bsc@ resolves @import Foo@ by searching
-- the @-p@ path for the first matching file.  Two files in different
-- directories can declare the same package name — sometimes intentionally
-- (variant selection), sometimes accidentally.
--
-- This module detects conflicts and reports them so the user can add
-- explicit resolution to @bsc.toml@.
module Language.Bluespec.BBT.Discover
  ( SourceFile (..)
  , Conflict (..)
  , discoverSources
  , resolveConflicts
  , searchPath
  , readPackageName
  ) where

import Control.Exception (SomeException, catch, evaluate, try)
import Data.List (isSuffixOf, nub)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.Directory (doesDirectoryExist, listDirectory, makeAbsolute)
import System.FilePath ((</>), isRelative, takeExtension)

import Language.Bluespec.BBT.Config

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

-- | A discovered source file with its package name.
data SourceFile = SourceFile
  { sfPath        :: !FilePath
  , sfPackageName :: !Text
  } deriving stock (Show, Eq)

-- | A package-name conflict: the same name declared in multiple files.
data Conflict = Conflict
  { cPackageName :: !Text
  , cFiles       :: ![FilePath]
  } deriving stock (Show)

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

-- | Collect all source files, detect conflicts, and apply resolutions.
-- Returns @Left conflicts@ if unresolved conflicts remain after applying
-- all @[[conflict]]@ entries and profile exclusions.
-- Returns @Right files@ with the unique resolved list otherwise.
discoverSources :: Config -> Maybe Text -> IO (Either [Conflict] [SourceFile])
discoverSources cfg mProfile = do
  let dirs = effectiveSourceDirs cfg mProfile
  root <- makeAbsolute (cfgRoot cfg)
  absDirs <- mapM (toAbs root) (expandGlobs dirs)
  existingDirs <- filterM doesDirectoryExist absDirs
  let scanExclude = map (root </>) (buildScanExclude (cfgBuild cfg))
  files <- fmap concat $ mapM (collectDir scanExclude) existingDirs
  let conflictMap = buildConflictMap files
  case resolveConflicts conflictMap (cfgConflicts cfg) of
    Left cs    -> pure (Left cs)
    Right resolved -> pure (Right resolved)
  where
    toAbs root dir
      | isRelative dir = pure (root </> dir)
      | otherwise      = pure dir
    filterM p = foldr go (pure [])
      where
        go x acc = do
          ok <- p x
          if ok then (x :) <$> acc else acc

-- | Given a resolved source list, compute the ordered @-p@ search path.
-- Each unique directory appears once, in discovery order.
searchPath :: [SourceFile] -> [FilePath]
searchPath = nub . map (dirOf . sfPath)
  where
    dirOf p = reverse $ dropWhile (/= '/') (reverse p)

-- | Resolve conflicts using @[[conflict]]@ winner declarations.
-- Returns @Left@ with remaining unresolved conflicts, or @Right@ with
-- the deduplicated winner list.
resolveConflicts
  :: Map Text [SourceFile]
  -> [ConflictResolution]
  -> Either [Conflict] [SourceFile]
resolveConflicts conflictMap resolutions =
  let winnerMap = Map.fromList [(crPackage r, crWinner r) | r <- resolutions]
      resolved  = Map.mapWithKey (applyResolution winnerMap) conflictMap
      remaining = [ Conflict k (map sfPath vs)
                  | (k, Left vs) <- Map.toList resolved ]
      successes = [ v | (_, Right v) <- Map.toList resolved ]
  in if null remaining
       then Right successes
       else Left remaining
  where
    applyResolution wm pkg files =
      case Map.lookup pkg wm of
        Nothing     ->
          if length files == 1
            then Right (head files)
            else Left files
        Just winner ->
          case filter (\sf -> sfPath sf `endsWithPath` winner) files of
            (f : _) -> Right f
            []      -> Left files  -- winner path didn't match any file
    -- | True if @haystack@ ends with the path component @needle@.
    -- Handles the common case where @needle@ is a relative path
    -- (e.g. "src_Core/CPU/Foo.bsv") and @haystack@ is absolute
    -- (e.g. "/work/Flute/src_Core/CPU/Foo.bsv").
    endsWithPath haystack needle =
      haystack == needle
      || ("/" ++ needle) `isSuffixOf` haystack

-- ---------------------------------------------------------------------------
-- Internal helpers
-- ---------------------------------------------------------------------------

-- | Expand trailing @/**@ in a path to mean "this dir and all subdirs"
-- (handled at collection time — we just strip the @/**@ here and recurse).
expandGlobs :: [FilePath] -> [FilePath]
expandGlobs = map stripGlob
  where
    stripGlob p
      | "/**" `T.isSuffixOf` T.pack p = T.unpack $ T.dropEnd 3 $ T.pack p
      | otherwise = p

-- | Recursively collect all @.bs@ and @.bsv@ files in a directory.
-- The @scanExclude@ list contains absolute directory paths to skip entirely
-- during the recursive walk (e.g. test or example subdirs).
collectDir :: [FilePath] -> FilePath -> IO [SourceFile]
collectDir scanExclude dir = do
  entries <- listDirectory dir `catchAll` \_ -> pure []
  fmap concat $ mapM (processEntry dir) entries
  where
    processEntry parent entry = do
      let fullPath = parent </> entry
      isDir <- doesDirectoryExist fullPath
      if isDir
        then if fullPath `elem` scanExclude
               then pure []
               else collectDir scanExclude fullPath
        else case takeExtension entry of
               ".bs"  -> toSourceFile fullPath
               ".bsv" -> toSourceFile fullPath
               _      -> pure []

    toSourceFile path = do
      mName <- readPackageName path
      case mName of
        Nothing   -> pure []
        Just name -> pure [SourceFile { sfPath = path, sfPackageName = name }]

    catchAll :: IO a -> (SomeException -> IO a) -> IO a
    catchAll = catch

-- | Group source files by package name to find conflicts.
buildConflictMap :: [SourceFile] -> Map Text [SourceFile]
buildConflictMap = foldr insert Map.empty
  where
    insert sf m = Map.insertWith (++) (sfPackageName sf) [sf] m

-- | Read just the package name from a @.bs@ or @.bsv@ file.
-- Looks for the first line matching @package <Name> where@.
-- Uses a simple text scan — no need to run the full parser.
readPackageName :: FilePath -> IO (Maybe Text)
readPackageName path = do
  result <- try (TIO.readFile path >>= evaluate) :: IO (Either SomeException Text)
  case result of
    Left _    -> pure Nothing
    Right txt -> pure $ extractPackageName txt

-- | Extract the package name from file contents.
-- Handles both @package Foo where@ and @package Foo(...)@ forms.
extractPackageName :: Text -> Maybe Text
extractPackageName txt =
  listToMaybe $ mapMaybe parseLine (T.lines txt)
  where
    parseLine line =
      let stripped = T.strip line
      in if "package " `T.isPrefixOf` stripped
           then let rest = T.strip $ T.drop 8 stripped  -- drop "package "
                    name = T.takeWhile isIdentChar rest
                in if T.null name then Nothing else Just name
           else Nothing

    isIdentChar c = (c >= 'a' && c <= 'z')
                 || (c >= 'A' && c <= 'Z')
                 || (c >= '0' && c <= '9')
                 || c == '_' || c == '\''

listToMaybe :: [a] -> Maybe a
listToMaybe []    = Nothing
listToMaybe (x:_) = Just x
