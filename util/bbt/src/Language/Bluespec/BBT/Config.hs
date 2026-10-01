-- | Parse and represent a @bsc.toml@ project manifest.
module Language.Bluespec.BBT.Config
  ( Config (..)
  , PackageMeta (..)
  , BuildConfig (..)
  , FlagsConfig (..)
  , TargetConfig (..)
  , ProfileConfig (..)
  , DependencyConfig (..)
  , ConflictResolution (..)
  , defaultFlagsConfig
  , loadConfig
  , loadConfigFrom
  , effectiveSourceDirs
  , bscFlags
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.FilePath (takeDirectory)
import Toml (Table' (..), Value' (..))
import Toml qualified

-- ---------------------------------------------------------------------------
-- Data types
-- ---------------------------------------------------------------------------

-- | The full contents of a @bsc.toml@ file.
data Config = Config
  { cfgPackage      :: !PackageMeta
  , cfgBuild        :: !BuildConfig
  , cfgFlags        :: !FlagsConfig
  , cfgDefines      :: !(Map Text Text)
  , cfgDependencies :: ![DependencyConfig]
  , cfgConflicts    :: ![ConflictResolution]
  , cfgTargets      :: !(Map Text TargetConfig)
  , cfgProfiles     :: !(Map Text ProfileConfig)
  , cfgRoot         :: !FilePath               -- ^ directory containing bsc.toml
  } deriving stock (Show)

data PackageMeta = PackageMeta
  { pkgName        :: !Text
  , pkgVersion     :: !(Maybe Text)
  , pkgDescription :: !(Maybe Text)
  } deriving stock (Show)

data BuildConfig = BuildConfig
  { buildTopFile           :: !(Maybe FilePath)
  , buildTopModule         :: !(Maybe Text)
  , buildSrc               :: !(Maybe FilePath)
  , buildSourceDirs        :: ![FilePath]
  , buildSourceDirsExclude :: ![FilePath]
  , buildSourceDirsAdd     :: ![FilePath]
  -- | Directories to skip entirely during recursive source scanning.
  -- Unlike 'buildSourceDirsExclude', this applies during the recursive
  -- walk — useful for excluding test/example subdirs nested inside a
  -- source directory (e.g. @Near_Mem_IO/Near_Mem_IO_AXI4_Unit_Test@).
  , buildScanExclude       :: ![FilePath]
  } deriving stock (Show)

data FlagsConfig = FlagsConfig
  { flagAggressiveConditions  :: !Bool
  , flagNoWarnActionShadowing :: !Bool
  , flagNoShowTimestamps      :: !Bool
  , flagKeepFires             :: !Bool
  , flagCheckAssert           :: !Bool
  , flagRtsHeap               :: !(Maybe Text)  -- ^ Nothing = disabled
  , flagSuppressWarnings      :: ![Text]
  , flagExtra                 :: ![Text]
  } deriving stock (Show)

-- | Sensible defaults matching the survey of real Bluespec projects.
defaultFlagsConfig :: FlagsConfig
defaultFlagsConfig = FlagsConfig
  { flagAggressiveConditions  = True
  , flagNoWarnActionShadowing = True
  , flagNoShowTimestamps      = True
  , flagKeepFires             = False
  , flagCheckAssert           = False
  , flagRtsHeap               = Just "128M"
  , flagSuppressWarnings      = []
  , flagExtra                 = []
  }

data TargetConfig = TargetConfig
  { targetVerilogDir :: !(Maybe FilePath)
  , targetBuildDir   :: !(Maybe FilePath)
  , targetInfoDir    :: !(Maybe FilePath)
  , targetSimDir     :: !(Maybe FilePath)
  , targetSimulator  :: !(Maybe Text)
  , targetTopModule  :: !(Maybe Text)   -- ^ per-target top module override (e.g. mkSim for sim targets)
  , targetCSources   :: ![FilePath]
  , targetCLib       :: !(Maybe FilePath)
  , targetDefines    :: !(Map Text Text)
  , targetFlags      :: ![Text]
  , targetPostBuild  :: ![Text]
  } deriving stock (Show)

data ProfileConfig = ProfileConfig
  { profileDefines           :: !(Map Text Text)
  , profileFlags             :: ![Text]
  , profileSourceDirsAdd     :: ![FilePath]
  , profileSourceDirsExclude :: ![FilePath]
  } deriving stock (Show)

data DependencyConfig = DependencyConfig
  { depName :: !Text
  , depPath :: !Text
  } deriving stock (Show)

data ConflictResolution = ConflictResolution
  { crPackage :: !Text
  , crWinner  :: !FilePath
  } deriving stock (Show)

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

-- | Load @bsc.toml@ from the given file path.
loadConfigFrom :: FilePath -> IO (Either String Config)
loadConfigFrom path = do
  txt <- TIO.readFile path
  pure $ case Toml.parse txt of
    Left err  -> Left err
    Right tbl -> parseConfig (takeDirectory path) tbl

loadConfig :: FilePath -> IO (Either String Config)
loadConfig = loadConfigFrom

-- | Compute the effective source directory list for a build,
-- given an optional profile name.
effectiveSourceDirs :: Config -> Maybe Text -> [FilePath]
effectiveSourceDirs cfg mProfile =
  let build   = cfgBuild cfg
      baseAdd = buildSourceDirsAdd build
      baseExclude = buildSourceDirsExclude build
      (profAdd, profExclude) = case mProfile >>= \p -> Map.lookup p (cfgProfiles cfg) of
        Nothing -> ([], [])
        Just pc -> (profileSourceDirsAdd pc, profileSourceDirsExclude pc)
      allExclude = baseExclude ++ profExclude
      base = buildSourceDirs build
             ++ maybe [] (\s -> [s]) (buildSrc build)
             ++ baseAdd ++ profAdd
  in filter (`notElem` allExclude) base

-- | Render the flags config as bsc command-line arguments.
bscFlags :: FlagsConfig -> [String]
bscFlags fc = concat
  [ ["-aggressive-conditions"    | flagAggressiveConditions  fc]
  , ["-no-warn-action-shadowing" | flagNoWarnActionShadowing fc]
  , ["-no-show-timestamps"       | flagNoShowTimestamps      fc]
  , ["-keep-fires"               | flagKeepFires             fc]
  , ["-check-assert"             | flagCheckAssert           fc]
  , case flagRtsHeap fc of
      Nothing -> []
      Just h  -> ["+RTS", "-K" ++ T.unpack h, "-RTS"]
  , concatMap (\w -> ["-suppress-warnings", T.unpack w]) (flagSuppressWarnings fc)
  , map T.unpack (flagExtra fc)
  ]

-- ---------------------------------------------------------------------------
-- Internal: walk the toml-parser value tree
-- ---------------------------------------------------------------------------

-- | Unlocated TOML table: annotation type is ().
type TomlTable = Table' ()

parseConfig :: FilePath -> Table' Toml.Position -> Either String Config
parseConfig root rawTbl =
  let tbl = Toml.forgetTableAnns rawTbl
  in do
    pkg     <- parsePkg     (subTable "package"  tbl)
    build   <- parseBuild   (subTable "build"    tbl)
    flags   <- parseFlags   (subTable "flags"    tbl)
    defs    <- parseDefines (subTable "defines"  tbl)
    deps    <- mapM parseDep (arrayOfTables "dependency" tbl)
    confs   <- mapM parseCR  (arrayOfTables "conflict"   tbl)
    targets <- traverse parseTarget  (namedSubTables "target"  tbl)
    profs   <- traverse parseProfile (namedSubTables "profile" tbl)
    pure Config
      { cfgPackage      = pkg
      , cfgBuild        = build
      , cfgFlags        = flags
      , cfgDefines      = defs
      , cfgDependencies = deps
      , cfgConflicts    = confs
      , cfgTargets      = targets
      , cfgProfiles     = profs
      , cfgRoot         = root
      }

-- ---------------------------------------------------------------------------
-- Table navigation helpers
-- ---------------------------------------------------------------------------

-- | Extract a sub-table by key, returning empty table if missing/wrong type.
subTable :: Text -> TomlTable -> TomlTable
subTable key (MkTable m) =
  case fmap snd (Map.lookup key m) of
    Just (Table' _ t) -> t
    _                 -> MkTable Map.empty

-- | Extract an array of tables for [[key]] sections.
arrayOfTables :: Text -> TomlTable -> [TomlTable]
arrayOfTables key (MkTable m) =
  case fmap snd (Map.lookup key m) of
    Just (List' _ vs) -> mapMaybe extractTable vs
    _                 -> []
  where
    extractTable (Table' _ t) = Just t
    extractTable _            = Nothing

-- | Extract named sub-tables for [prefix.name] sections.
namedSubTables :: Text -> TomlTable -> Map Text TomlTable
namedSubTables prefix (MkTable m) =
  case fmap snd (Map.lookup prefix m) of
    Just (Table' _ (MkTable inner)) ->
      Map.fromList
        [ (k, case snd v of { Table' _ t -> t; _ -> MkTable Map.empty })
        | (k, v) <- Map.toList inner
        ]
    _ -> Map.empty

-- ---------------------------------------------------------------------------
-- Scalar helpers
-- ---------------------------------------------------------------------------

-- | Look up a value in a TOML table by key (strips annotation).
lookupVal :: Text -> TomlTable -> Maybe (Value' ())
lookupVal key (MkTable m) = fmap snd (Map.lookup key m)

getStr :: Text -> TomlTable -> Maybe Text
getStr key tbl = case lookupVal key tbl of
  Just (Text' _ s) -> Just s
  _                -> Nothing

getBool :: Text -> TomlTable -> Maybe Bool
getBool key tbl = case lookupVal key tbl of
  Just (Bool' _ b) -> Just b
  _                -> Nothing

getBoolD :: Text -> Bool -> TomlTable -> Bool
getBoolD key def_ tbl = fromMaybe def_ (getBool key tbl)

getStrList :: Text -> TomlTable -> [Text]
getStrList key tbl = case lookupVal key tbl of
  Just (List' _ vs) -> [s | Text' _ s <- vs]
  _                 -> []

-- ---------------------------------------------------------------------------
-- Section parsers
-- ---------------------------------------------------------------------------

parsePkg :: TomlTable -> Either String PackageMeta
parsePkg tbl =
  case getStr "name" tbl of
    Nothing -> Left "bsc.toml: [package] is missing required field 'name'"
    Just n  -> Right PackageMeta
      { pkgName        = n
      , pkgVersion     = getStr "version" tbl
      , pkgDescription = getStr "description" tbl
      }

parseBuild :: TomlTable -> Either String BuildConfig
parseBuild tbl = Right BuildConfig
  { buildTopFile           = fmap T.unpack (getStr "top_file" tbl)
  , buildTopModule         = getStr "top_module" tbl
  , buildSrc               = fmap T.unpack (getStr "src" tbl)
  , buildSourceDirs        = map T.unpack (getStrList "source_dirs" tbl)
  , buildSourceDirsExclude = map T.unpack (getStrList "source_dirs_exclude" tbl)
  , buildSourceDirsAdd     = map T.unpack (getStrList "source_dirs_add" tbl)
  , buildScanExclude       = map T.unpack (getStrList "scan_exclude" tbl)
  }

parseFlags :: TomlTable -> Either String FlagsConfig
parseFlags tbl = Right FlagsConfig
  { flagAggressiveConditions  = getBoolD "aggressive_conditions"    True  tbl
  , flagNoWarnActionShadowing = getBoolD "no_warn_action_shadowing" True  tbl
  , flagNoShowTimestamps      = getBoolD "no_show_timestamps"       True  tbl
  , flagKeepFires             = getBoolD "keep_fires"               False tbl
  , flagCheckAssert           = getBoolD "check_assert"             False tbl
  , flagRtsHeap               = case getStr "rts_heap" tbl of
                                   Just "" -> Nothing
                                   Just h  -> Just h
                                   Nothing -> Just "128M"
  , flagSuppressWarnings      = getStrList "suppress_warnings" tbl
  , flagExtra                 = getStrList "extra" tbl
  }

-- | Parse a [defines] table: bool True → "", string value → value, bool False → skip.
parseDefines :: TomlTable -> Either String (Map Text Text)
parseDefines (MkTable m) = Right $ Map.fromList
  [ (k, toVal v)
  | (k, (_, v)) <- Map.toList m
  , include v
  ]
  where
    include (Bool' _ False) = False
    include _               = True
    toVal (Bool' _ True) = ""
    toVal (Text' _ s)    = s
    toVal _              = ""

parseDep :: TomlTable -> Either String DependencyConfig
parseDep tbl =
  case (getStr "name" tbl, getStr "path" tbl) of
    (Just n, Just p) -> Right DependencyConfig { depName = n, depPath = p }
    _ -> Left "bsc.toml: [[dependency]] missing 'name' or 'path'"

parseCR :: TomlTable -> Either String ConflictResolution
parseCR tbl =
  case (getStr "package" tbl, getStr "winner" tbl) of
    (Just pkg, Just win) -> Right ConflictResolution
      { crPackage = pkg, crWinner = T.unpack win }
    _ -> Left "bsc.toml: [[conflict]] missing 'package' or 'winner'"

parseTarget :: TomlTable -> Either String TargetConfig
parseTarget tbl = do
  defs <- parseDefines (subTable "defines" tbl)
  Right TargetConfig
    { targetVerilogDir = fmap T.unpack (getStr "verilog_dir" tbl)
    , targetBuildDir   = fmap T.unpack (getStr "build_dir"   tbl)
    , targetInfoDir    = fmap T.unpack (getStr "info_dir"    tbl)
    , targetSimDir     = fmap T.unpack (getStr "sim_dir"     tbl)
    , targetSimulator  = getStr "simulator" tbl
    , targetTopModule  = getStr "top_module" tbl
    , targetCSources   = map T.unpack (getStrList "c_sources" tbl)
    , targetCLib       = fmap T.unpack (getStr "c_lib" tbl)
    , targetDefines    = defs
    , targetFlags      = getStrList "flags" tbl
    , targetPostBuild  = getStrList "post_build" tbl
    }

parseProfile :: TomlTable -> Either String ProfileConfig
parseProfile tbl = do
  defs <- parseDefines (subTable "defines" tbl)
  Right ProfileConfig
    { profileDefines           = defs
    , profileFlags             = getStrList "flags" tbl
    , profileSourceDirsAdd     = map T.unpack (getStrList "source_dirs_add" tbl)
    , profileSourceDirsExclude = map T.unpack (getStrList "source_dirs_exclude" tbl)
    }

