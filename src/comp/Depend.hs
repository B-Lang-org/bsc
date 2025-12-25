{-# LANGUAGE CPP #-}
module Depend(chkDeps, parseSrc, chkParse, doCPP, genDepend, genFileDepend,
              outlaw_sv_kws_as_classic_ids) where

import Data.Maybe(isJust)
import Data.List(nub)
import Control.Monad(when)
import System.Process(system)
import System.Exit(ExitCode(..))
import System.Directory(getModificationTime)
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
             exitFailWith, bsWarning)
import PFPrint
import FStringCompat
import Lex
import Parse
import FileNameUtil(hasDotSuf, dropSuf, baseName, dirName,
                    bscSrcSuffix, bsvSrcSuffix, binSuffix,
                    mkAName, mkVName, mkVPIHName, mkVPICName)
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

type FileName = String
type PkgName = Id
type ModName = Id
type ForeignName = Id

type MClockTime = Maybe ClockTime

data PkgInfo = PkgInfo {
        pkgName :: PkgName,
        fileName :: FileName,
        srcMod :: MClockTime,
        lastMod :: MClockTime,
        imports :: [PkgName],
        includes :: [FileName],
        gens :: [ModName],
        foreigns :: [ForeignName],
        recompile :: Bool,
        isbin :: Bool
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
chkDeps :: ErrorHandle -> Flags -> String -> IO [FileName]
chkDeps errh flags name = do
        let gflags = [ mkId noPosition (mkFString s) | s <- genName flags ]
        pi <- getInfo errh flags gflags name
        (errs,pis) <- transClose errh flags ([],[pi]) (imports pi)
        when (not $ null errs) $ bsError errh errs

        case tsort [ (n, is) | PkgInfo { pkgName = n, imports = is } <- pis ] of
            Left cycle@(firstImport:_) ->
                bsError errh [(getPosition firstImport,
                               ECircularImports (map ppReadable cycle))]
            Right ns -> do
                let -- the pkginfo of all depended modules
                    pis' = let getInfo n = case findInfo n pis of
                                             Just pi -> pi
                                             _ -> internalError "Depend.chkDeps: pis'"
                           in  map getInfo ns
                    -- names of files resulting from codegen, if we want
                    -- to return them, for a linking stage to use
                    --genfs = concatMap (getGenFs flags) pis'
                -- the pkginfos with "recompile" marked for any files whose
                -- source is newer than any of its related files
                pis'' <- chkUpd flags [] pis'
                -- just the names of the pkgs to be recompiled,
                -- in dependency order
                let fs = reverse [ f | PkgInfo { fileName = f, recompile = True } <- pis'' ]
                return fs
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
        die_nameMismatch fname pname =
            bsError errh [(getIdPosition pname,
                           WFilePackageNameMismatch
                                 (pfpString fname) (pfpString pname))]
        trybsv :: IO (Maybe PkgInfo)
        trybsv = do
          mfile <- readFilesPath errh noPosition False [bsvname, name] path
          case mfile of
            Nothing -> return Nothing
            Just (_, fname) -> do
                pi <- getInfo errh flags [] fname
                -- XXX return the EMsg instead of dying?
                when (pkgName pi /= pname)
                    (die_nameMismatch pname (pkgName pi))
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
                                gens = [], foreigns = [], recompile = False,
                                isbin = True }

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
                 Just pi -> return (Right pi)

-- Get PkgInfo for a string (from a given file name), fail if not parsable.
getInfo :: ErrorHandle -> Flags -> [ModName] -> FileName -> IO PkgInfo
getInfo errh flags gflags fname = do
    file' <- doCPP errh flags fname
    let isClassic = not $ hasDotSuf bsvSrcSuffix fname
    -- setClassic isClassic
    (CPackage i _ imps _ _ defs incs, _)
        <- parseSrc isClassic errh flags False fname file'

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
    return $ PkgInfo {
                      pkgName = i,
                      fileName = fname,
                      srcMod = tbs,
                      lastMod = tbs `max` tbo,
                      imports = [ i | CImpId _ i <- imps] ++ prelude,
                      includes = [i |  CInclude i <- incs],
                      recompile = tbo < tbs,
                      gens = [ i | CPragma (Pproperties i pps) <- defs,
                                   PPverilog `elem` pps ] ++
                             [ i | CValueSign (CDef i _ _) <- defs,
                                   i `elem` gflags ] ++
                             [ makeGenFuncId i
                                 | CPragma (Pnoinline is) <- defs,
                                   i <- is ],
                      foreigns = [ i | CPragma (Pproperties _ pps) <- defs,
                                       (PPforeignImport i) <- pps ],
                      isbin = False }

-- Compute the transitive closure of all imports.
-- The `done' arg are the already visited packages,
-- and the `ns' arg are the names of the remaining ones.
transClose :: ErrorHandle -> Flags -> ([EMsg],[PkgInfo]) -> [PkgName] ->
              IO ([EMsg],[PkgInfo])
transClose errh flags done [] = return done
transClose errh flags (errs,done) (n:ns) = do
        --putStr (ppReadable n)
        case findInfo n done of
             Just _ -> transClose errh flags (errs,done) ns
             Nothing -> do
                epi <- getPkgInfo errh flags n
                case epi of
                  Left  em -> transClose errh flags (em:errs,done) (ns)
                  Right pi -> transClose errh flags (errs,pi:done) (ns ++ imports pi)

findInfo :: PkgName -> [PkgInfo] -> Maybe PkgInfo
findInfo _ [] = Nothing
findInfo n (pi@(PkgInfo { pkgName = n' }):_) | n == n' = Just pi
findInfo n (_:pis) = findInfo n pis

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

-- Update the `recompile' flag in all the PkgInfo.
chkUpd :: Flags -> [PkgInfo] -> [PkgInfo] -> IO [PkgInfo]
chkUpd flags done [] = return done
chkUpd flags done (pi:pis) = do
    --putStrLn ("chkUpd " ++ show pi)
    let genfs = getGenFs flags pi
    let incfs = includes pi
    --putStrLn (show genfs)
    genfsClks <- mapM getModTime genfs
    incfsClks <- mapM getModTime incfs
    let needGenUpd = any (srcMod pi >) genfsClks
    let needIncUpd = any (lastMod pi <) incfsClks
    --putStrLn (show (fileName pi, genfs, map (srcMod pi >) genfsClks))
    --putStr (ppReadable (pkgName pi, imports pi, map pkgName done))
    let pi' = pi { recompile = True }
    if isPreludePkg flags (fileName pi) || isbin pi then
       -- Never update Prelude files
       chkUpd flags (pi : done) pis
     else do
       -- Update if the package (i.e. .bo) or any generated files (i.e. .ba/.v)
       -- are out-of-date with respect to any import
       -- or the generated files are out-of-date with respect to the source.
       let lastCompTime = minimum ((lastMod pi) : genfsClks)
       if any (needsUpd lastCompTime done) (imports pi) || needGenUpd || needIncUpd then
           chkUpd flags (pi' : done) pis
        else
           chkUpd flags (pi : done) pis

-- Is this an installed library?
isPreludePkg :: Flags -> FileName -> Bool
isPreludePkg flags n =
    let sl = bluespecDir flags ++ "/Libraries/"
    in  take (length sl) n == sl

-- Check if out-of-date with respect to an imported module.
-- Recompilation is needed if the imported file will be
-- recompiled or if it has a later date stamp.
needsUpd :: MClockTime -> [PkgInfo] -> PkgName -> Bool
needsUpd myMod pis n =
    case findInfo n pis of
    Nothing -> internalError ("needsUpd " ++ pfpString n)
    Just pi -> recompile pi || lastMod pi > myMod

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

-- wrapper to detect file encoding errors (which are detected lazily)
parseSrc :: Bool -> ErrorHandle -> Flags -> Bool -> String -> String ->
            IO (CPackage, TimeInfo)
parseSrc classic errh flags show_warns filename inp = CE.handleJust isEncErr handleErr $ parseSrc' classic errh flags show_warns filename inp
    where isEncErr :: CE.IOException -> Maybe CE.IOException
          isEncErr e | InvalidArgument <- ioeGetErrorType e = Just e
                     | otherwise = Nothing
          handleErr _ = bsError errh [(filePosition $ mkFString filename, ENotUTF8)]

parseSrc' :: Bool -> ErrorHandle -> Flags -> Bool -> String -> String ->
            IO (CPackage, TimeInfo)
parseSrc' True errh flags show_warns filename inp = do
  -- Classic parser
  t <- getNow
  let dumpnames = (baseName (dropSuf filename), "", "")
  start flags DFparsed
  let lflags = LFlags { lf_is_stdlib = stdlibNames flags,
                        lf_allow_sv_kws = not outlaw_sv_kws_as_classic_ids }
  case chkParse pPackage (lexStart lflags (mkFString filename) inp) of
      Right pkg -> do t <- dump errh flags t DFparsed dumpnames pkg
                      let ws = classicWarnings pkg
                      when (show_warns && (not $ null ws)) $ bsWarning errh ws
                      return (pkg, t)
      Left errs -> bsError errh errs
parseSrc' False errh flags show_warns filename inp =
  -- BSV parser
  bsvParseString errh flags show_warns filename (baseName $ dropSuf filename) inp

chkParse :: Parser [Token] a -> [Token] -> Either [EMsg] a
chkParse p ts =
    case parse p ts of
        Right ((m,_):_) -> Right m
        Left  (ss,ts)   -> Left [errSyntax (filter (not . null ) ss) ts]
        Right []        -> internalError "Depend.chkParse: Right []"

----
findPackages :: ErrorHandle -> Flags -> FileName -> IO ([EMsg],[PkgInfo])
findPackages errh flags name = do
  let gflags = [ mkId noPosition (mkFString s) | s <- genName flags ]
  pi <- getInfo errh flags gflags name
  transClose errh flags ([],[pi]) (imports pi)

-- generate the file name dependencies for filename
-- A package depends on its own source file name
-- plus the imported packages (.bo)
-- plus the included files
genDepend :: ErrorHandle -> Flags -> FileName ->
             IO ([EMsg],[(FileName, [FileName])])
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
      getSelf p | isbin p = []
                | otherwise = [fileName p]
      --
      getImports p = -- package name .bo
          let fnp p | isbin p = fileName p
                    | otherwise = boName p
          in map fnp (concatMap lookupP (imports p))
      --
      extr :: PkgInfo -> [(FileName, [FileName])]
      extr pki | isbin pki = []
      extr pki = [(boName pki, getSelf pki ++ getImports pki ++ includes pki)]
  return (errs,concatMap extr pis)

genFileDepend :: ErrorHandle -> Flags -> FileName -> IO ([EMsg],[FileName])
genFileDepend errh flags name = do
    (errs,pis) <- findPackages errh flags name
    let extrFiles :: PkgInfo -> [FileName]
        extrFiles p | isbin p   = []
                    | otherwise = fileName p : includes p
    return (errs, nub $ concatMap extrFiles pis)
