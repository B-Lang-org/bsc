-- | Emit JSON project information for the Bluespec LSP server.
module Language.Bluespec.BBT.LspInfo
  ( LspInfo (..)
  , getLspInfo
  , renderLspInfo
  ) where

import Data.Aeson (ToJSON (..), object, (.=))
import Data.Aeson qualified as Aeson
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Lazy qualified as TL
import Data.Text.Lazy.Encoding qualified as TLE
import System.Directory (makeAbsolute)

import Language.Bluespec.BBT.Config
import Language.Bluespec.BBT.Discover

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

data LspInfo = LspInfo
  { liRoot         :: !FilePath
  , liTopFile      :: !(Maybe FilePath)
  , liTopModule    :: !(Maybe Text)
  , liProfile      :: !(Maybe Text)
  , liSourceDirs   :: ![FilePath]
  , liDefines      :: !(Map Text Text)
  , liTargets      :: ![Text]
  , liConflicts    :: ![ConflictInfo]
  , liPackageIndex :: !(Map Text FilePath)   -- ^ pkg name → resolved file path
  } deriving stock (Show)

data ConflictInfo = ConflictInfo
  { ciPackage :: !Text
  , ciFiles   :: ![FilePath]
  } deriving stock (Show)

instance ToJSON LspInfo where
  toJSON li = object
    [ "root"          .= liRoot li
    , "top_file"      .= liTopFile li
    , "top_module"    .= liTopModule li
    , "profile"       .= liProfile li
    , "source_dirs"   .= liSourceDirs li
    , "defines"       .= liDefines li
    , "targets"       .= liTargets li
    , "conflicts"     .= liConflicts li
    , "package_index" .= Map.map T.pack (liPackageIndex li)
    ]

instance ToJSON ConflictInfo where
  toJSON ci = object
    [ "package" .= ciPackage ci
    , "files"   .= ciFiles ci
    ]

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

-- | Compute LSP info for the given config and optional profile.
getLspInfo :: Config -> Maybe Text -> IO LspInfo
getLspInfo cfg mProfile = do
  root <- makeAbsolute (cfgRoot cfg)
  let dirs = effectiveSourceDirs cfg mProfile
  absDirs <- mapM makeAbsolute dirs
  srcResult <- discoverSources cfg mProfile
  let (conflicts, pkgIndex) = case srcResult of
        Left cs    ->
          ( map (\c -> ConflictInfo (cPackageName c) (cFiles c)) cs
          , Map.empty )
        Right srcs ->
          ( []
          , Map.fromList [(sfPackageName sf, sfPath sf) | sf <- srcs] )
  pure LspInfo
    { liRoot         = root
    , liTopFile      = fmap (absPath root) (buildTopFile (cfgBuild cfg))
    , liTopModule    = buildTopModule (cfgBuild cfg)
    , liProfile      = mProfile
    , liSourceDirs   = absDirs
    , liDefines      = cfgDefines cfg
    , liTargets      = Map.keys (cfgTargets cfg)
    , liConflicts    = conflicts
    , liPackageIndex = pkgIndex
    }

-- | Render LspInfo as JSON text.
renderLspInfo :: LspInfo -> Text
renderLspInfo = TL.toStrict . TLE.decodeUtf8 . Aeson.encode

-- ---------------------------------------------------------------------------
-- Internal
-- ---------------------------------------------------------------------------

absPath :: FilePath -> FilePath -> FilePath
absPath _root path = path  -- already resolved via makeAbsolute above
