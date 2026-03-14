-- | @bbt doc@ — thin wrapper that invokes @bs-docgen@ for the current project.
module Language.Bluespec.BBT.Doc
  ( DocOpts (..)
  , runDoc
  ) where

import Data.Text qualified as T
import System.FilePath ((</>))

import Language.Bluespec.BBT.Config (Config (..), BuildConfig (..))
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
      srcDirs  = map (root </>) (buildSourceDirs (cfgBuild cfg))
      dgcfg    = DocGenConfig
        { dgcLibDirs   = srcDirs
        , dgcOutDir    = doOutDir opts
        , dgcRefManual = Nothing   -- user projects have no LaTeX manual
        , dgcStdlibUrl = Nothing   -- TODO: expose via bbt.toml or --stdlib-url flag
        , dgcVerbose   = doVerbose opts
        , dgcBscSha    = Nothing   -- user projects: no BSC SHA in footer
        }
  runDocGen dgcfg
