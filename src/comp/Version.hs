module Version(bluespec, bscVersionStr, versionStr, versionname,
               copyright, buildnum
              ) where

import BuildVersion(buildVersion, buildVersionNum, buildVersionName)

{-# NOINLINE bluespec #-}
{-# NOINLINE versionname #-}
{-# NOINLINE copyright #-}

bluespec :: String
bluespec = "Bluespec"

versionname :: String
versionname = buildVersionName

buildname :: String
buildname = buildVersionName

buildnum :: Integer
buildnum = read buildVersionNum

buildstr :: String
buildstr = buildVersion

-- Generate the version string (for a given tool)
versionStr :: Bool -> String -> String
versionStr showVersion toolname
  | not showVersion = toolname
  | otherwise =
    let emptyOr a b = if null a then a else b
        versionstr  = versionname `emptyOr` (", version " ++ versionname)
        buildstr    = buildVersion `emptyOr` (" (build " ++ buildVersion ++ ")")
  in  concat [toolname, versionstr, buildstr]

-- The version string for BSC
bscVersionStr :: Bool -> String
bscVersionStr showVersion = versionStr showVersion (bluespec ++ " Compiler")

copyright :: String
copyright = unlines copyrights

copyrights :: [String]
copyrights = ["This is free software; for source code and copying conditions, see",
              "https://github.com/B-Lang-org/bsc"]
