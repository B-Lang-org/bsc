module Version(bluespec, version, versionStr, versionname, versiondate, copyright,
               buildnum
              ) where

import BuildVersion(buildVersion, buildVersionNum)

{-# NOINLINE bluespec #-}
{-# NOINLINE versionname #-}
{-# NOINLINE versiondate #-}
{-# NOINLINE copyright #-}

bluespec = "Bluespec"

-- These fields can be used to give a name and date to a release
--
-- Note: Bluesim models have a get_version() method that can
--       return the parts of a version when specified in the
--       format YEAR.MONTH or YEAR.MONTH.ANNOTATION
--       (eg. 2019.05.beta2 or 2017.07.A)
--
versionname = ""
versiondate = ""

buildnum = buildVersionNum

-- Generate the version string (for a given tool)
versionStr toolname =
  let versionstr = if null versionname then "" else ", version " ++ versionname
      buildstr = if null buildVersion then "" else "build " ++ buildVersion
  in  toolname ++
      versionstr ++
      (if (null buildstr && null versiondate) then "" else " (") ++
      buildstr ++
      (if (null buildstr || null versiondate) then "" else ", ") ++
      versiondate ++
      (if (null buildstr && null versiondate) then "" else ")")

-- The version string for the Bluespec Compiler
version = versionStr (bluespec ++ " Compiler")

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
