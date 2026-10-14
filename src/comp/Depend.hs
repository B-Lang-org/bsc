{-# LANGUAGE CPP #-}
module Depend(chkDeps, parseFile, chkParse, doCPP, genDepend, genFileDepend,
              outlaw_sv_kws_as_classic_ids) where

import Data.Maybe(isJust)
import Data.List(nub)
import Control.Monad(when)
import System.Process(system)
import System.Exit(ExitCode(..))
import System.Directory(getModificationTime, getCurrentDirectory)
import System.Time -- XXX: in old-time package
import System.IO.Error(ioeGetErrorType)
import GHC.IO.Exception(IOErrorType(..))
import Data.Time.Clock.POSIX(utcTimeToPOSIXSeconds)
import qualified Control.Exception as CE
import qualified Data.Map as DM

import TmpNam(tmpNam, localTmpNam)
import SCC(tsort)
import Flags
import Backend
import Pragma(Pragma(..),PProp(..))
import Position(noPosition, filePosition)
import Error(internalError, EMsg, ErrMsg(..), ErrorHandle, bsError,
             exitFailWith, bsWarning, WMsg)
import PFPrint
import FStringCompat
import Lex
import Parse
import FileNameUtil(hasDotSuf, dropSuf, baseName, dirName,
                    bscSrcSuffix, bsvSrcSuffix, binSuffix,
                    mkAName, mkVName, mkVPIHName, mkVPICName,
                    createEncodedFullFilePath)
import FileIOUtil(readFilesPath, readBinFilePath, readFileCatch, writeFileCatch,
                  removeFileCatch)
import Id
import PreIds(idPrelude, idPreludeBSV)
import Parser.Classic(pPackage, errSyntax, classicWarnings)
import Parser.BSV(bsvParseString)
import CSyntax
import GenFuncWrap(makeGenFuncId)
import IOUtil(getEnvDef, progArgs)
import TopUtils
--import Debug.Trace

outlaw_sv_kws_as_classic_ids :: Bool
outlaw_sv_kws_as_classic_ids = "-outlaw-sv-kws-as-classic-ids" `elem` progArgs

type PkgName = Id
type ModName = Id
type ForeignName = Id

type MClockTime = Maybe ClockTime

-- Compilation status for a package
data CompileStatus = Binary                      -- .bo file, no recompilation needed
                   | UpToDate CPackage [WMsg]    -- parsed source, dependencies up to date
                   | Recompile CPackage [WMsg]   -- parsed source, needs recompilation
                   deriving (Show)

data PkgInfo = PkgInfo {
        pkgName :: PkgName,
        fileName :: FilePath,
        srcMod :: MClockTime,
        lastMod :: MClockTime,
        imports :: [PkgName],
        includes :: [FilePath],
        gens :: [ModName],
        foreigns :: [ForeignName],
        compileStatus :: CompileStatus
        }
    deriving (Show)

getModificationTime' :: FilePath -> IO ClockTime
getModificationTime' file =
  do utcTime <- getModificationTime file
     let s = (floor . utcTimeToPOSIXSeconds) utcTime
     return (TOD s 0)

-- returns a list of Bluespec source files which need recompiling.
-- (This used to also return a list of all generated files which would
-- result from codegen, so that a later stage could link them.  But this
-- feature is no longer supported.)
chkDeps :: ErrorHandle -> Flags -> String -> IO [(FilePath, CPackage, [WMsg])]
chkDeps errh flags name = do
        let gflags = [ mkId noPosition (mkFString s) | s <- genName flags ]
        (pkg, _, warns) <- parseFile errh flags False name
        pi <- getInfo errh flags gflags name pkg warns
        let initMap = DM.singleton (pkgName pi) pi
        (errs, piMap) <- transClose errh flags ([], initMap) (imports pi)
        when (not $ null errs) $ bsError errh errs

        let pis = DM.elems piMap
        case tsort [ (n, is) | PkgInfo { pkgName = n, imports = is } <- pis ] of
            Left cycle@(firstImport:_) ->
                bsError errh [(getPosition firstImport,
                               ECircularImports (map ppReadable cycle))]
            Right ns -> do
                let lookupPkg n = case DM.lookup n piMap of
                                    Just pi -> pi
                                    Nothing -> internalError "Depend.chkDeps: lookupPkg"
                    -- the pkginfo of all depended modules, in dependency order
                    pis' = map lookupPkg ns
                    -- names of files resulting from codegen, if we want
                    -- to return them, for a linking stage to use
                    --genfs = concatMap (getGenFs flags) pis'
                -- the pkginfos with "recompile" marked for any files whose
                -- source is newer than any of its related files
                pis'' <- chkUpd flags DM.empty [] pis'
                -- extract the files to recompile with their parsed packages and warnings, in dependency order
                return (reverse [ (fileName pi, pkg, warns) | pi@(PkgInfo { compileStatus = Recompile pkg warns }) <- pis'' ])
            Left [] -> internalError "Depend.chkDeps: tsort empty cycle"

-- Get PkgInfo for a package name.  Try to open the corresponding file.
-- Also try the .bo file (for installed libraries).
getPkgInfo :: ErrorHandle -> Flags -> PkgName -> IO (Either EMsg PkgInfo)
getPkgInfo errh flags pname =
    let name = getIdString pname ++ "." ++ bscSrcSuffix
        bsvname = getIdString pname ++ "." ++ bsvSrcSuffix
        bname = getIdString pname ++ "." ++ binSuffix
        path = ifcPath flags
        errPackageMissing = (getIdPosition pname,
                             EMissingPackage (pfpString pname))
        trybsv :: IO (Maybe PkgInfo)
        trybsv = do
          mfile <- readFilesPath errh noPosition False [bsvname, name] path
          case mfile of
            Nothing -> return Nothing
            Just (_, fname) -> do
                (pkg, _, warns) <- parseFile errh flags True fname
                pi <- getInfo errh flags [] fname pkg warns
                -- parseFile checks package name matches filename (fatal error)
                return (Just pi)
        trybo :: IO (Maybe PkgInfo)
        trybo = do
          mfile <- readBinFilePath errh noPosition False bname path
          case mfile of
            Nothing -> return Nothing
            Just (file, fname) ->
                -- this comparison forces evaluation to force close on the file
                if file /= file then internalError "getPkgInfo" else do
                  t <- getModTime fname
                  return $ Just $
                      PkgInfo { pkgName = pname, fileName = fname,
                                srcMod = Nothing, lastMod = t, imports = [], includes = [],
                                gens = [], foreigns = [],
                                compileStatus = Binary }

        -- if a stage returns Nothing, then try the next stage;
        -- once a stage returns something, return it
        contIfNothing :: IO (Maybe a) -> Maybe a -> IO (Maybe a)
        contIfNothing fn Nothing = fn
        contIfNothing fn res     = return res
    in
       -- any IO failure along the way aborts the process
       trybsv >>=
       contIfNothing trybo >>=
       \res -> case res of
                 Nothing -> return (Left errPackageMissing)
                 Just r -> return (Right r)

-- Extract PkgInfo from a parsed CPackage
getInfo :: ErrorHandle -> Flags -> [ModName] -> FilePath -> CPackage -> [WMsg] -> IO PkgInfo
getInfo errh flags gflags fname pkg@(CPackage i _ imps _ _ defs incs) warns = do
    -- the mod time of the source file
    tbs <- getModTime fname

    -- function to change fname's path to a new directory
    -- (like TopUtils::putInDir)
    let mkdname dir suf = dir ++ "/" ++ baseName (dropSuf fname) ++ "." ++ suf

    -- find the mod time of the bo file (either in same dir or in the bdir)
    tbo_samedir <- getModTime (dropSuf fname ++ "." ++ binSuffix)
    tbo_bdir <- case (bdir flags) of
                    Nothing -> return Nothing
                    Just dir -> getModTime (mkdname dir binSuffix)
    let tbo = if (isJust tbo_bdir) then tbo_bdir else tbo_samedir

    -- include the prelude to avoid failures when predule was updated.
    let prelude
           | not (usePrelude flags) = []
           | i == idPrelude = []
           | i == idPreludeBSV = [idPrelude]
           | otherwise = [idPrelude, idPreludeBSV]
    let status = if tbo < tbs then Recompile pkg warns else UpToDate pkg warns
    return $ PkgInfo {
                      pkgName = i,
                      fileName = fname,
                      srcMod = tbs,
                      lastMod = tbs `max` tbo,
                      imports = [ i | CImpId _ i <- imps] ++ prelude,
                      includes = [i |  CInclude i <- incs],
                      gens = [ i | CPragma (Pproperties i pps) <- defs,
                                   PPverilog `elem` pps ] ++
                             [ i | CValueSign (CDef i _ _) <- defs,
                                   i `elem` gflags ] ++
                             [ makeGenFuncId i
                                 | CPragma (Pnoinline is) <- defs,
                                   i <- is ],
                      foreigns = [ i | CPragma (Pproperties _ pps) <- defs,
                                       (PPforeignImport i) <- pps ],
                      compileStatus = status }

-- Compute the transitive closure of all imports.
-- The `done' arg are the already visited packages,
-- and the `ns' arg are the names of the remaining ones.
transClose :: ErrorHandle -> Flags -> ([EMsg], DM.Map PkgName PkgInfo) -> [PkgName] ->
              IO ([EMsg], DM.Map PkgName PkgInfo)
transClose errh flags done [] = return done
transClose errh flags (errs,done) (n:ns) = do
        --putStr (ppReadable n)
        case DM.lookup n done of
             Just _ -> transClose errh flags (errs,done) ns
             Nothing -> do
                epi <- getPkgInfo errh flags n
                case epi of
                  Left  em -> transClose errh flags (em:errs,done) (ns)
                  Right pi -> transClose errh flags (errs, DM.insert n pi done) (ns ++ imports pi)

-- This tries to return a list of all files that will be generated from
-- this file after codegen.
-- XXX This needs to be kept in sync with what the backend actually does!
getGenFs :: Flags -> PkgInfo -> [String]
getGenFs flags pi =
    let prefix = dirName (fileName pi) ++ "/"
        getName = getIdString . unQualId
        mkABinFileName i = mkAName (bdir flags) prefix (getName i)
        mkVerFileName i = mkVName (vdir flags) prefix (getName i)
        mkVPIFileNames i = [ mkVPIHName (vdir flags) prefix (getName i),
                             mkVPICName (vdir flags) prefix (getName i) ]
        -- files common to all backends
        foreign_abin_files = map mkABinFileName (foreigns pi)
    in case backend flags of
         Just Bluesim ->
            let mod_abin_files = map mkABinFileName (gens pi)
            in  foreign_abin_files ++ mod_abin_files
         Just Verilog ->
            let mod_ver_files = map mkVerFileName (gens pi)
                foreign_vpi_files = if (useDPI flags)
                                    then []
                                    else concatMap mkVPIFileNames (foreigns pi)
                mod_abin_files =
                    if (genABin flags)
                    then map mkABinFileName (gens pi)
                    else []
            in  foreign_abin_files ++ foreign_vpi_files ++
                mod_ver_files ++ mod_abin_files
         Nothing ->
            foreign_abin_files

-- Update the compile status in all the PkgInfo.
-- Transforms UpToDate -> Recompile when dependencies require it.
-- Uses both a Map (for efficient import lookups) and a List (to preserve dependency order).
chkUpd :: Flags -> DM.Map PkgName PkgInfo -> [PkgInfo] -> [PkgInfo] -> IO [PkgInfo]
chkUpd flags doneMap resultList [] = return resultList
chkUpd flags doneMap resultList (pi:pis) = do
    --putStrLn ("chkUpd " ++ show pi)
    case compileStatus pi of
      UpToDate pkg warns | not (isPreludePkg flags (fileName pi)) -> do
        -- Check if recompilation is needed
        let genfs = getGenFs flags pi
            incfs = includes pi
        --putStrLn (show genfs)
        genfsClks <- mapM getModTime genfs
        incfsClks <- mapM getModTime incfs
        let needGenUpd = any (srcMod pi >) genfsClks
            needIncUpd = any (lastMod pi <) incfsClks
        --putStrLn (show (fileName pi, genfs, map (srcMod pi >) genfsClks))
        --putStr (ppReadable (pkgName pi, imports pi, DM.keys doneMap))
            lastCompTime = minimum ((lastMod pi) : genfsClks)
        if any (needsUpd lastCompTime doneMap) (imports pi) || needGenUpd || needIncUpd then
          let pi' = pi { compileStatus = Recompile pkg warns }
          in chkUpd flags (DM.insert (pkgName pi') pi' doneMap) (pi' : resultList) pis
        else
          chkUpd flags (DM.insert (pkgName pi) pi doneMap) (pi : resultList) pis
      _ ->
        -- Binary, Recompile, or Prelude packages: no change needed
        chkUpd flags (DM.insert (pkgName pi) pi doneMap) (pi : resultList) pis

-- Is this an installed library?
isPreludePkg :: Flags -> FilePath -> Bool
isPreludePkg flags n =
    let sl = bluespecDir flags ++ "/Libraries/"
    in  take (length sl) n == sl

-- Check if out-of-date with respect to an imported module.
-- Recompilation is needed if the imported file will be
-- recompiled or if it has a later date stamp.
needsUpd :: MClockTime -> DM.Map PkgName PkgInfo -> PkgName -> Bool
needsUpd myMod piMap n =
    case DM.lookup n piMap of
    Nothing -> internalError ("needsUpd " ++ pfpString n)
    Just pi -> case compileStatus pi of
                 Recompile _ _ -> True
                 _ -> lastMod pi > myMod

getModTime :: String -> IO MClockTime
getModTime f = CE.catch (getModificationTime' f >>= return . Just) handler
  where handler :: CE.SomeException -> IO MClockTime
        handler _ = return Nothing

-----

doCPP :: ErrorHandle -> Flags -> String -> IO String
doCPP errh flags name =
    if cpp flags
    then do
        tempName <- tmpNam
        topNameRoot <- localTmpNam
        let topName = topNameRoot ++ ".c"
            tmpNameOut = tempName ++ ".out"
        writeFileCatch errh topName ("#include \""++name++"\"\n")
        comp <- getEnvDef "CC" dfltCCompile

{- If the compiler specified in the CC environment variable has a
spaces in its name, for example CC="/usr/local/my c compiler/bin/cc",
then this will fail.  You need to properly quote the spaces.  As a
side effect, (and in fact, this was the reason why), if you include
flags in the CC variable, for example CC="cc -g", then it will work.
-}

        let backend_def = case backend flags of
                            Just Bluesim -> ["-D__GENC__"]
                            Just Verilog -> ["-D__GENVERILOG__"]
                            Nothing -> []
            cmd = unwords ([comp] ++ backend_def ++
                           ["-D__BSC__", "-E", "-nostdinc", "-traditional"] ++
                           -- the show function quotes things
                           (map show (cppFlags flags))
                           ++ [ topName, ">", tmpNameOut])
        when (verbose flags) $ putStrLn ("exec: " ++ cmd)
        rc <- system cmd
        case rc of
         ExitSuccess -> do
                file <- readFileCatch errh noPosition tmpNameOut
                removeFileCatch errh topName
                removeFileCatch errh tmpNameOut
                return file
         ExitFailure n -> do
                removeFileCatch errh topName
                removeFileCatch errh tmpNameOut
                exitFailWith errh n
    else readFileCatch errh noPosition name

-- Parse a file: run CPP, dump CPP output, parse, check name, dump CSyntax, stats
-- Returns CPackage, TimeInfo, and warnings for passing to compilation
-- If fatal_name_mismatch is True, package name mismatch causes bsError (aborts)
-- If False, it's just a bsWarning
parseFile :: ErrorHandle -> Flags -> Bool -> FilePath -> IO (CPackage, TimeInfo, [WMsg])
parseFile errh flags fatal_name_mismatch fname = do
    let isClassic = hasDotSuf bscSrcSuffix fname

    t <- getNow
    let dumpnames = (Just (baseName (dropSuf fname)), Nothing, Nothing)

    -- parseSrc needs encoded path for position tracking
    pwd <- getCurrentDirectory
    let fname_encoded = createEncodedFullFilePath fname pwd

    start flags DFcpp
    file <- doCPP errh flags fname_encoded
    _ <- dumpStr errh flags t DFcpp dumpnames file

    -- parseSrc handles its own dump stages (DFparsed, DFvpp, etc.)
    (pkg@(CPackage i _ _ _ _ _ _), t', warns) <- parseSrc isClassic errh flags fname_encoded file

    -- Check for package name mismatch
    let reportMismatch = if fatal_name_mismatch then bsError else bsWarning
    -- Use getIdString rather than pfpString here: pfpString calls isClassic(),
    -- which reads a global IORef.  If it fires before compilePackage calls
    -- setSyntax, GHC can memoize the result as CLASSIC and corrupt the print
    -- mode for the entire subsequent compilation.  Package names are always
    -- simple unqualified identifiers, so getIdString is equivalent.
    when (getIdString i /= baseName (dropSuf fname)) $
         reportMismatch errh
             [(getPosition i, WFilePackageNameMismatch fname (getIdString i))]

    -- dump CSyntax
    when (showCSyntax flags) (putStrLnF (show pkg))
    -- dump stats
    stats flags DFparsed pkg

    return (pkg, t', warns)

-- wrapper to detect file encoding errors (which are detected lazily)
parseSrc :: Bool -> ErrorHandle -> Flags -> String -> String ->
            IO (CPackage, TimeInfo, [WMsg])
parseSrc classic errh flags filename inp = CE.handleJust isEncErr handleErr $ parseSrc' classic errh flags filename inp
    where isEncErr :: CE.IOException -> Maybe CE.IOException
          isEncErr e | InvalidArgument <- ioeGetErrorType e = Just e
                     | otherwise = Nothing
          handleErr _ = bsError errh [(filePosition $ mkFString filename, ENotUTF8)]

parseSrc' :: Bool -> ErrorHandle -> Flags -> String -> String ->
            IO (CPackage, TimeInfo, [WMsg])
parseSrc' True errh flags filename inp = do
  -- Classic parser
  t <- getNow
  let dumpnames = (Just (baseName (dropSuf filename)), Nothing, Nothing)
  start flags DFparsed
  let lflags = LFlags { lf_is_stdlib = stdlibNames flags,
                        lf_allow_sv_kws = not outlaw_sv_kws_as_classic_ids }
  case chkParse pPackage (lexStart lflags (mkFString filename) inp) of
      Right pkg -> do t <- dump errh flags t DFparsed dumpnames pkg
                      let ws = classicWarnings pkg
                      return (pkg, t, ws)
      Left errs -> bsError errh errs
parseSrc' False errh flags filename inp =
  -- BSV parser
  bsvParseString errh flags filename (baseName $ dropSuf filename) inp

chkParse :: Parser [Token] a -> [Token] -> Either [EMsg] a
chkParse p ts =
    case parse p ts of
        Right ((m,_):_) -> Right m
        Left  (ss,ts)   -> Left [errSyntax (filter (not . null ) ss) ts]
        Right []        -> internalError "Depend.chkParse: Right []"

----
findPackages :: ErrorHandle -> Flags -> FilePath -> IO ([EMsg],[PkgInfo])
findPackages errh flags name = do
  let gflags = [ mkId noPosition (mkFString s) | s <- genName flags ]
  (pkg, _, warns) <- parseFile errh flags True name
  pi <- getInfo errh flags gflags name pkg warns
  (errs, piMap) <- transClose errh flags ([], DM.singleton (pkgName pi) pi) (imports pi)
  return (errs, DM.elems piMap)

-- generate the file name dependencies for filename
-- A package depends on its own source file name
-- plus the imported packages (.bo)
-- plus the included files
genDepend :: ErrorHandle -> Flags -> FilePath ->
             IO ([EMsg],[(FilePath, [FilePath])])
genDepend errh flags name = do
  (errs,pis) <- findPackages errh flags name
  let pmap :: DM.Map PkgName PkgInfo
      pmap = DM.fromList [(pkgName pki, pki) | pki <- pis]
      lookupP p =
            case (DM.lookup p pmap) of
              Just pinfo -> [pinfo]
              Nothing    -> [] -- internalError $ "Depend:genDepend " ++ show p
      --
      -- bo name and location
      boName p  = putInDir (bdir flags) (fileName p) binSuffix
      -- bsv source file (if it exists)
      getSelf p | Binary <- compileStatus p = []
                | otherwise = [fileName p]
      --
      getImports p = -- package name .bo
          let fnp p | Binary <- compileStatus p = fileName p
                    | otherwise = boName p
          in map fnp (concatMap lookupP (imports p))
      --
      extr :: PkgInfo -> [(FilePath, [FilePath])]
      extr pki | Binary <- compileStatus pki = []
      extr pki = [(boName pki, getSelf pki ++ getImports pki ++ includes pki)]
  return (errs,concatMap extr pis)

genFileDepend :: ErrorHandle -> Flags -> FilePath -> IO ([EMsg],[FilePath])
genFileDepend errh flags name = do
    (errs,pis) <- findPackages errh flags name
    let extrFiles :: PkgInfo -> [FilePath]
        extrFiles p | Binary <- compileStatus p = []
                    | otherwise = fileName p : includes p
    return (errs, nub $ concatMap extrFiles pis)
