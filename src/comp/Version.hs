module Version(bluespec, bscVersionStr, versionStr, versionname,
               copyright, buildnum
              ) where

import BuildVersion(buildVersion, buildVersionNum)

{-# NOINLINE bluespec #-}
{-# NOINLINE versionname #-}
{-# NOINLINE copyright #-}

bluespec :: String
bluespec = "Bluespec"

-- This can be used to give a name to a release
--
-- Note: Bluesim models have a get_version() method that can
--       return the parts of a version when specified in the
--       format YEAR.MONTH or YEAR.MONTH.ANNOTATION
--       (eg. 2019.05.beta2 or 2017.07.A)
--
versionname :: String
versionname = ""

buildnum :: Integer
buildnum = buildVersionNum

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
copyrights = ["Copyright 2000-2020 Bluespec, Inc.",
              "Parts copyright 2002, The University Court of the University of Glasgow.",
              "Parts copyright 1982-1999 Lennart Augustsson, Thomas Johnsson,",
              "    Chalmers University of Technology.",
              "Parts copyright 1999-2000, Daan Leijen.",
              "Parts copyright 1991, 1999 Free Software Foundation, Inc.",
              "Parts copyright 2010, Don Stewart.",
              "All rights reserved.",
              "See documentation for license details."]
