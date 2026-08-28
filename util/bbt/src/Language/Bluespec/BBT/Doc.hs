-- | @bbt doc@ — thin wrapper that invokes @bs-docgen@ for the current project.
module Language.Bluespec.BBT.Doc
  ( DocOpts (..)
  , runDoc
  ) where

import Data.Text qualified as T
import System.FilePath ((</>))

import Language.Bluespec.BBT.Config (Config (..), BuildConfig (..), PackageMeta (..))
import Language.Bluespec.DocGen.Generate (DocGenConfig (..), runDocGen)

-- | Options for @bbt doc@.
data DocOpts = DocOpts
  { doOutDir    :: !FilePath       -- ^ output directory (default: @docs/@)
  , doVerbose   :: !Bool
  , doProfile   :: !(Maybe T.Text)
  } deriving stock (Show)

-- | Run @bbt doc@: discover sources from @bsc.toml@ and generate documentation.
runDoc :: Config -> DocOpts -> IO ()
runDoc cfg opts = do
  let root     = cfgRoot cfg
      pkg      = cfgPackage cfg
      -- Use the description as the project title when present (it is usually a
      -- full human-readable name like "SOC: Bluespec SoC with BDPI UART").
      -- Fall back to the package name when no description is provided.
      projTitle = Just $ case pkgDescription pkg of
        Just d  -> d
        Nothing -> pkgName pkg
      srcDirs  = map (root </>) (buildSourceDirs (cfgBuild cfg))
      dgcfg    = DocGenConfig
        { dgcLibDirs      = srcDirs
        , dgcOutDir       = doOutDir opts
        , dgcRefManual    = Nothing   -- user projects have no LaTeX manual
        , dgcBscDocDir    = Nothing   -- user projects have no BSC doc/ tree
        , dgcStdlibUrl    = Nothing   -- TODO: expose via bbt.toml or --stdlib-url flag
        , dgcVerbose      = doVerbose opts
        , dgcBscSha       = Nothing   -- user projects: no BSC SHA in footer
        , dgcProjectName  = projTitle
        , dgcProjectDesc  = pkgDescription pkg
        }
  runDocGen dgcfg
