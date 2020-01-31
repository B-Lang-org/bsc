module FileNameUtil where


-- ==================================================
-- FileNameUtil
--
-- This module contains functions for file name processing
-- and standard file name conventions.
--
-- ==================================================

import System.Directory
import Numeric(showInt)

import Util(rTake)


-- =====
-- Names

-- various suffixes
bscSrcSuffix = "bs"
bsvSrcSuffix = "bsv"
bseSrcSuffix = "bse"
binSuffix = "bo"
abinSuffix = "ba"
cSuffix   = "c"
cxxSuffix = "cxx"
cppSuffix = "cpp"
ccSuffix  = "cc"
hSuffix   = "h"
comodSuffix = "cdf"
objSuffix = "o"
arSuffix  = "a"
soSuffix  = "so"
verSuffix = "v"
verSuffix2 = "V"
verSuffix3 = "vqm"
verSuffix4 = "vo"
verSuffix5 = "sv"
verSuffix6 = "vp"
vhdlSuffix = "vhd"
vhdlSuffix2 = "vhdl"
useSuffix = "use"
scheduleSuffix = "sched"
dotSuffix = "dot"
vcdSuffix = "vcd"
makeSuffix = "mk"

-- XX Assumes that the prefix string contains a trailing / if needed
mkPre :: Maybe String -> String -> String
mkPre Nothing "./"  = ""
mkPre Nothing pre  = pre
mkPre (Just ".")  _ = ""
mkPre (Just d)  _ = d ++ "/"

-- Given
--   m   = maybe a path for output files of this type
--   pre = otherwise a default prefix (for the current dir?)
--   s   = a base filename string
-- append a dot suffix for the type of file
mkVName :: Maybe String -> String -> String -> String
mkVName     m pre s = mkPre m pre ++ s ++ "." ++ verSuffix
mkAName     m pre s = mkPre m pre ++ s ++ "." ++ abinSuffix
mkSchedName m pre s = mkPre m pre ++ s ++ "." ++ scheduleSuffix
mkCxxName   m pre s = mkPre m pre ++ s ++ "." ++ cxxSuffix
mkCName     m pre s = mkPre m pre ++ s ++ "." ++ cSuffix
mkHName     m pre s = mkPre m pre ++ s ++ "." ++ hSuffix
mkObjName   m pre s = mkPre m pre ++ s ++ "." ++ objSuffix
mkSoName    m pre s = mkPre m pre ++ s ++ "." ++ soSuffix
mkDOTName   m pre s = mkPre m pre ++ s ++ "." ++ dotSuffix
mkMakeName  m pre s = mkPre m pre ++ s ++ "." ++ makeSuffix

-- add prefix (and possible suffix) based on the type of file
mkVPICName m pre s = mkPre m pre ++ "vpi_wrapper_" ++ s ++ "." ++ cSuffix
mkVPIHName m pre s = mkPre m pre ++ "vpi_wrapper_" ++ s ++ "." ++ hSuffix
mkVPIArrayCName m pre = mkPre m pre ++ "vpi_startup_array" ++ "." ++ cSuffix

-- add prefix but no suffix
mkNameWithoutSuffix m pre s = mkPre m pre ++ s

-- =====
-- File name utilities

dirName :: String -> String
dirName s =
    case dropWhile (/= '/') (reverse s) of
    '/':cs -> reverse cs
    _ -> "."  -- we know this case only matches "", but compiler doesn't

baseName ::  String -> String
baseName = reverse . takeWhile (/= '/') . reverse

hasSuf :: String -> String -> Bool
hasSuf suf name = length name > length suf && rTake (length suf) name == suf

hasPre :: String -> String -> Bool
hasPre pre name = length name > length pre && take (length pre) name == pre

hasPrefix :: String -> String -> Bool
hasPrefix pre name = length name > length pre && take (length pre) name == pre

hasDotSuf :: String -> String -> Bool
hasDotSuf suf name = hasSuf ('.':suf) name

dropSuf :: String -> String
dropSuf s = dropSufChar '.' s

dropSufChar :: Char -> String -> String
dropSufChar c s =
    if c `elem` s
    then (reverse . tail . dropWhile (/= c) . reverse) s
    else s

takeSuf :: String -> String
takeSuf s = takeSufChar '.' s

takeSufChar :: Char -> String -> String
takeSufChar c s =
    if c `elem` s
    then (reverse . takeWhile (/= c) . reverse) s
    else ""

hasNoSuffix :: String -> Bool
hasNoSuffix = all (/= '.')

--
mangleFileName :: String -> String
mangleFileName s =
    let d = dirName s
        b = baseName s
        ns = dropSuf b
        suf = takeSuf b
        addDir "." f = f
        addDir d f = d ++ "/" ++ f
        addSuf f "" = f
        addSuf f s = f ++ "." ++ s
        hashstr s =
            showInt (foldr
                        (\ c r -> toInteger (fromEnum c) + 17 * r)
                        0
                        ns `mod` 1000000000000)
                ""
        maxFileName = 100
    in  if length ns > maxFileName then
            addSuf (addDir d (take maxFileName ns ++ "-" ++ hashstr ns)) suf
        else
            s


-- =====

-- This creates a full file path from the relative path and the pwd.
-- The pwd is encoded in the full path using /// (instead of /).
-- This allows either the full or relative path to be extracted for
-- output (in error messages, cross reference info, etc).
-- Paths which were provided absolutely have /// at the beginning.

createEncodedFullFilePath :: FilePath -> FilePath -> FilePath
createEncodedFullFilePath filePath pwd =
        if head (filePath ++ " ") == '/'
        then "//" ++ filePath
        else
          if (take 2 (filePath ++ "  ")) == "./"
          then pwd ++ "///" ++ (drop 2 filePath)
          else pwd ++ "///" ++ filePath

-- /// is replaced with /
getFullFilePath :: FilePath -> FilePath
getFullFilePath "" = ""
getFullFilePath path = -- trace("JJJ" ++ path) $
    let start = takeWhile (/= '/') path
        rest = dropWhile (/= '/') path
        prefix = take 3 rest
    in if (prefix == "///")
       then start ++ (drop 2 rest)
       else start ++ "/" ++ (getFullFilePath (drop 1 rest))

-- If the path starts with ///, it is replaced with /,
-- else everything up through /// is dropped.  If there
-- is no ///, the path is returned unchanged.
getRelativeFilePath :: FilePath -> FilePath
getRelativeFilePath path =
    let prefix = take 3 path
        relative = (getRelativeFilePathInternal path)
    in if (prefix == "///")
       then drop 2 path
       else if (relative == "") then path else relative

getRelativeFilePathInternal :: FilePath -> FilePath
getRelativeFilePathInternal "" = ""
getRelativeFilePathInternal path =
    let rest = dropWhile (/= '/') path
        prefix = take 3 rest
    in if (prefix == "///")
       then drop 3 rest
       else getRelativeFilePathInternal (drop 1 rest)

-- =====

-- When we create a name with mkVName (as an example), we pass it vdir
-- (which is Maybe a path) and prefix.  If vdir is Nothing, we use prefix,
-- else we use vdir.  Thus, both need to be in the same form.
-- The prefix is encoded, so vdir needs to be encoded too.
-- Use this function as a wrapper around "mk...Name" to encode the
-- vdir (bdir, infodir, etc).
genFileName :: (Maybe String -> String -> String -> String) ->
               Maybe String -> String -> String -> IO (String)
genFileName mkFn mdir prefix basename = do
    pwd <- getCurrentDirectory
    let dir_encoded =
            case mdir of
              Nothing -> Nothing
              Just dir -> Just (createEncodedFullFilePath dir pwd)
    -- XXX why mangleFileName???
    return (mkFn dir_encoded prefix (mangleFileName basename))

-- =====

removeQuotes :: FilePath -> FilePath
removeQuotes "" = ""
removeQuotes path = (takeWhile (/= '\"') (dropWhile (== '\"') path))
