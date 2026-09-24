module StaleUtils ( getModTime, allFreshVs ) where

import System.Posix.Files
import System.Posix.Types(EpochTime)

-- Shared primitives for the generated-file staleness checks: the -u
-- recompilation check (Depend), Bluesim object reuse (SimFileUtils) and
-- Verilog reuse at link (VFileUtils) all decide "regenerate or reuse"
-- by comparing a source artifact's time against its products'.  The
-- conventions live here so the checks agree: a missing product is never
-- fresh, and equal timestamps are fresh.

-- modification time of a file, or Nothing if it does not exist
getModTime :: FilePath -> IO (Maybe EpochTime)
getModTime f =
    do ok <- fileExist f
       if ok
        then do s <- getFileStatus f
                return $ Just (modificationTime s)
        else return Nothing

-- are all the products at least as new as the source?
-- (a missing product, or a missing source, is not fresh)
allFreshVs :: FilePath -> [FilePath] -> IO Bool
allFreshVs source products = do
    msrc <- getModTime source
    mprods <- mapM getModTime products
    let fresh (Just st) (Just pt) = pt >= st
        fresh _         _         = False
    return $ all (fresh msrc) mprods
