-- | Project discovery: locate @bsc.toml@ by searching up the directory tree.
module Language.Bluespec.BBT.Project
  ( findProjectRoot
  , findBscToml
  ) where

import System.Directory (doesFileExist, getCurrentDirectory)
import System.FilePath ((</>), takeDirectory, isDrive)

-- | Search upwards from the given directory for @bsc.toml@.
-- Returns the path to the @bsc.toml@ file if found.
findProjectRoot :: FilePath -> IO (Maybe FilePath)
findProjectRoot startDir = go startDir
  where
    go dir = do
      let candidate = dir </> "bsc.toml"
      exists <- doesFileExist candidate
      if exists
        then pure (Just candidate)
        else if isDrive dir
               then pure Nothing
               else go (takeDirectory dir)

-- | Find @bsc.toml@ starting from the current directory.
findBscToml :: IO (Maybe FilePath)
findBscToml = getCurrentDirectory >>= findProjectRoot
