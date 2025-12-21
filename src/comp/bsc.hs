{-# LANGUAGE BangPatterns, CPP #-}
module Main_bsc(main, hmain) where

-- Haskell libs
import Prelude
import System.Environment(getArgs, getProgName)
import System.Process(runInteractiveProcess, waitForProcess)
import System.Process(system)
import System.Exit(ExitCode(ExitFailure, ExitSuccess))
import System.FilePath(takeDirectory)
import System.IO(hFlush, stdout, hPutStr, stderr, hGetContents, hClose, hSetBuffering, BufferMode(LineBuffering))
import System.IO(hSetEncoding, utf8)
import System.Posix.Files(fileMode,  unionFileModes, ownerExecuteMode, groupExecuteMode, setFileMode, getFileStatus, fileAccess)
import System.Directory(getDirectoryContents, doesFileExist, getCurrentDirectory)
import System.Time(getClockTime, ClockTime(TOD)) -- XXX: from old-time package
import Data.Char(isSpace, toLower, ord)
import Data.List(intersect, nub, partition, intersperse, sort,
            isPrefixOf, isSuffixOf, unzip5, intercalate)
import Data.Time.Clock.POSIX(getPOSIXTime)
import Data.Maybe(isJust, isNothing)
import Numeric(showOct)

import Control.Monad(when, unless, filterM, liftM, foldM)
import Control.Monad.Except(runExceptT)
import Control.Concurrent(forkIO)
import Control.Concurrent.MVar(newEmptyMVar, putMVar, takeMVar)
import qualified Control.Exception as CE
import qualified Data.Map as M
import qualified Data.Set as S

import ListMap(lookupWithDefault)
import SCC(scc)

-- utility libs
import ParseOp
import PFPrint
import Util(headOrErr, fromJustOrErr, joinByFst, quote)
import FileNameUtil(baseName, hasDotSuf, dropSuf, dirName, mangleFileName,
                    mkAName, mkVName, mkVPICName,
                    mkNameWithoutSuffix,
                    mkSoName, mkObjName, mkMakeName,
                    bscSrcSuffix, binSuffix,
                    hSuffix, cSuffix, cxxSuffix, cppSuffix, ccSuffix,
                    objSuffix, useSuffix,
                    genFileName, createEncodedFullFilePath,
                    getFullFilePath, getRelativeFilePath)
import FileIOUtil(writeFileCatch, readFileMaybe, removeFileCatch,
                  readFilePath)
import TopUtils
import SystemCheck(doSystemCheck)
import BuildSystem
import IOUtil(getEnvDef)

-- compiler libs
--import FStringCompat
import Exceptions(bsCatch)
import Flags(
        Flags(..),
        DumpFlag(..),
        hasDump,
        verbose, extraVerbose, quiet)
import FlagsDecode(
        Decoded(..),
        decodeArgs,
        updateFlags,
        showFlags,
        showFlagsRaw,
        exitWithUsage,
        exitWithHelp,
        exitWithHelpHidden)
import Error(internalError, ErrMsg(..),
             ErrorHandle, initErrorHandle, setErrorHandleFlags,
             bsError, bsWarning, bsMessage,
             exitFail, exitOK, exitFailWith)
import Position(noPosition, cmdPosition)
import CVPrint
import Id
import Backend
import Pragma
import VModInfo(VPathInfo, VPort)
import Deriving(derive)
import SymTab
import MakeSymTab(mkSymTab, cConvInst)
import TypeCheck(cCtxReduceIO, cTypeCheck)
import PoisonUtils(mkPoisonedCDefn)
import GenSign(genUserSign, genEverythingSign)
import Simplify(simplify)
import ISyntax(IPackage(..), IModule(..),
               IEFace(..), IDef(..), IExpr(..), fdVars)
import ISyntaxUtil(iMkRealBool, iMkLitSize, iMkString{-, itSplit -}, isTrue)
import InstNodes(getIStateLocs, flattenInstTree)
import IConv(iConvPackage, iConvDef)
import FixupDefs(fixupDefs, updDef)
import ISyntaxCheck(tCheckIPackage, tCheckIModule)
import ISimplify(iSimplify)
import BinUtil(BinMap, HashMap, readImports, replaceImports)
import GenBin(genBinFile)
import GenWrap(genWrap, WrapInfo(..))
import GenFuncWrap(genFuncWrap, addFuncWrap)
import GenForeign(genForeign)
import IExpand(iExpand)
import IExpandUtils(HeapData)
import ITransform(iTransform)
import IInline(iInline)
import IInlineFmt(iInlineFmt)
import Params(iParams)
import ASyntax(APackage(..), ASPackage(..),
               ppeAPackage,
               getAPackageFieldInfos)
import ASyntaxUtil(getForeignCallNames)
import ACheck(aMCheck, aSMCheck, aSignalCheck, aSMethCheck)
import AConv(aConv)
import IDropRules(iDropRules)
import ARankMethCalls(aRankMethCalls)
import AState(aState)
import ARenameIO(aRenameIO)
import ASchedule(AScheduleInfo(..), AScheduleErrInfo(..), aSchedule)
import AAddScheduleDefs(aAddScheduleDefs)
import APaths(aPathsPreSched, aPathsPostSched)
import AProofs(aCheckProofs)
import ADropDefs(aDropDefs)
import AOpt(aOpt)
import AVerilog(aVerilog)
import AVeriQuirks(aVeriQuirks)
import VIOProps(VIOProps, getIOProps)
import VFinalCleanup(finalCleanup)
import Synthesize(aSynthesize)
import ABin(ABin(..), ABinModInfo(..), ABinForeignFuncInfo(..),
           ABinModSchedErrInfo(..))
import ABinUtil(readAndCheckABin, readAndCheckABinPathCatch, getABIHierarchy,
                assertNoSchedErr)
import GenABin(genABinFile)
import ForeignFunctions(ForeignFunction(..), ForeignFuncMap,
                        mkImportDeclarations)
import VPIWrappers(genVPIWrappers, genVPIRegistrationArray)
import DPIWrappers(genDPIWrappers)
import SimCCBlock
import SimExpand(simExpand, simCheckPackage)
import SimPackage(SimSystem(..))
import SimPackageOpt(simPackageOpt)
import SimMakeCBlocks(simMakeCBlocks)
import SimCOpt(simCOpt)
import SimBlocksToC(simBlocksToC)
import SystemCWrapper(checkSystemCIfc, wrapSystemC)
import SimFileUtils(analyzeBluesimDependencies)
import Verilog(VProgram(..), vGetMainModName, getVeriInsts)
import Depend
import Version(bscVersionStr, copyright, buildnum)
import Classic
import ILift(iLift)
import ACleanup(aCleanup)
import ATaskSplice(aTaskSplice)
import ADumpSchedule (MethodDumpInfo, aDumpSchedule, aDumpScheduleErr,
                      dumpMethodInfo, dumpMethodBVIInfo)
import ANoInline (aNoInline)
import AAddSchedAssumps(aAddSchedAssumps,aAddCFConditionWires)
import ARemoveAssumps(aRemoveAssumps)
import ADropUndet(aDropUndet)
import SAT(checkSATFlags)
import InlineWires(aInlineWires)
import InlineCReg(aInlineCReg)
import LambdaCalc(convAPackageToLambdaCalc)
import SAL(convAPackageToSAL)

import VVerilogDollar
import ISplitIf(iSplitIf)
import VFileName

--import Debug.Trace

main :: IO ()
main = do
    hSetBuffering stdout LineBuffering
    hSetBuffering stderr LineBuffering
    hSetEncoding stdout utf8
    hSetEncoding stderr utf8
    args <- getArgs
    -- bsc can raise exception,  catch them here  print the message and exit out.
    bsCatch (hmain args)

-- Use with hugs top level
hmain :: [String] -> IO ()
hmain args = do
    pprog <- getProgName
    cdir <- getEnvDef "BLUESPECDIR" dfltBluespecDir
    bscopts <- getEnvDef "BSC_OPTIONS" ""
    let args' = words bscopts ++ args
    -- reconstruct original command line (modulo whitespace)
    -- add a newline at the end so it is offset
    let cmdLine = concat ("Invoking command line:\n" : (intersperse " " (pprog:args'))) ++ "\n"
    let showPreamble flags = do
          when (verbose flags) $ putStrLnF (bscVersionStr True)
          when (verbose flags) $ putStrLnF copyright
          when ((verbose flags) || (printFlags flags)) $ putStrLnF cmdLine
          when ((printFlags flags) || (printFlagsHidden flags)) $
                putStrLnF (showFlags flags)
          when (printFlagsRaw flags) $ putStrLnF (showFlagsRaw flags)
    let (warnings, decoded) = decodeArgs (baseName pprog) args' cdir
    errh <- initErrorHandle
    let doWarnings = when ((not . null) warnings) $ bsWarning errh warnings
        setFlags = setErrorHandleFlags errh
    case decoded of
        DHelp flags ->
            do { setFlags flags; doWarnings;
                 exitWithHelp errh pprog args' cdir }
        DHelpHidden flags ->
            do { setFlags flags; doWarnings;
                 exitWithHelpHidden errh pprog args' cdir }
        DUsage -> exitWithUsage errh pprog
        DError msgs -> bsError errh msgs
        DNoSrc flags ->
            -- XXX we want to allow "bsc -v" and similar calls
            -- XXX to print version, etc, but if there are other flags
            -- XXX on the command-line we probably should report an error
            do { setFlags flags; doWarnings; showPreamble flags;
                 exitOK errh }
        DBlueSrc flags src ->
            do { setFlags flags; doWarnings; showPreamble flags;
                 main' errh flags src;
                 exitOK errh }
        DVerLink flags top verSrcFiles abinFiles cSrcFiles ->
            do { setFlags flags; doWarnings; showPreamble flags;
                 vLink errh flags top verSrcFiles abinFiles cSrcFiles;
                 exitOK errh }
        DSimLink flags top abinFiles cSrcFiles ->
            do { setFlags flags; doWarnings; showPreamble flags;
                 simLink errh flags top abinFiles cSrcFiles;
                 exitOK errh }


main' :: ErrorHandle -> Flags -> String -> IO ()
main' errh flags name =  do
    tStart <- getNow

    flags' <- checkSATFlags errh flags

    -- check system requirements
    doSystemCheck errh

    let comp = if updCheck flags'
               then compile_with_deps
               else compile_no_deps

    success <- comp errh flags' name

    -- final verbose message
    _ <- timestampStr flags' "total" tStart

    if success then
      return ()
     else
       exitFail errh

compile_with_deps :: ErrorHandle -> Flags -> String -> IO (Bool)
compile_with_deps errh flags name = do
    let
        verb = showUpds flags && not (quiet flags)
        -- the flags to "compileFile" when re-compiling depended modules
        flags_depend = flags { updCheck = False,
                               genName = [],
                               showCodeGen = verb }
        -- the flags to "compileFile" when re-compiling this module
        flags_this = flags_depend { genName = genName flags }
        comp (success, binmap0, hashmap0) fn = do
            when (verb) $ putStrLnF ("compiling " ++ fn)
            let fl = if (fn == name)
                     then flags_this
                     else flags_depend
            (cur_success, binmap, hashmap)
                <- compileFile errh fl binmap0 hashmap0 fn
            return (cur_success && success, binmap, hashmap)
    when (verb) $ putStrLnF "checking package dependencies"

    t <- getNow
    let dumpnames = (baseName (dropSuf name), "", "")

    -- get the list of depended files which need recompiling
    start flags DFdepend
    fs <- chkDeps errh flags name
    _ <- dump errh flags t DFdepend dumpnames fs

    -- compile them
    (ok, _, _) <- foldM comp (True, M.empty, M.empty) fs

    when (verb) $
      if ok then
          putStrLnF "All packages are up to date."
      else putStrLnF "All packages compiled (some with errors)."

    return ok

compile_no_deps :: ErrorHandle -> Flags -> String -> IO (Bool)
compile_no_deps errh flags name = do
  (ok, _, _) <- compileFile errh flags M.empty M.empty name
  return ok

-- returns whether the compile errored or not
compileFile :: ErrorHandle -> Flags -> BinMap HeapData -> HashMap -> String ->
               IO (Bool, BinMap HeapData, HashMap)
compileFile errh flags binmap hashmap name_orig = do
    pwd <- getCurrentDirectory
    let name = (createEncodedFullFilePath name_orig pwd)
        name_rel = (getRelativeFilePath name)

    let syntax = if hasDotSuf bscSrcSuffix name then CLASSIC else BSV
    setSyntax syntax

    t <- getNow
    let dumpnames = (baseName (dropSuf name), "", "")

    start flags DFcpp
    file <- doCPP errh flags name
    _ <- dumpStr errh flags t DFcpp dumpnames file

    -- ===== the break point between file manipulation and compilation

    -- We don't start and dump this stage because that is handled inside
    -- the "parseSrc" function (since BSV parsing has multiple stages)
    (pkg@(CPackage i _ _ _ _ _), t)
        <- parseSrc (syntax == CLASSIC) errh flags True name file
    when (getIdString i /= baseName (dropSuf name)) $
         bsWarning errh
             [(noPosition, WFilePackageNameMismatch name_rel (pfpString i))]

    -- dump CSyntax
    when (showCSyntax flags) (putStrLnF (show pkg))
    -- dump stats
    stats flags DFparsed pkg

    let dumpnames = (baseName (dropSuf name), getIdString (unQualId i), "")
    compilePackage errh flags dumpnames t binmap hashmap name pkg

-------------------------------------------------------------------------

compilePackage ::
    ErrorHandle ->
    Flags ->
    DumpNames ->
    TimeInfo ->
    BinMap HeapData ->
    HashMap ->
    String ->
    CPackage ->
    IO (Bool, BinMap HeapData, HashMap)
compilePackage
    errh
    flags                -- user switches
    dumpnames
    tStart
    binmap0
    hashmap0
    name -- String --
    min@(CPackage pkgId _ _ _ _ _) = do

    clkTime <- getClockTime
    epochTime <- getPOSIXTime

    -- Values needed for the Environment module
    let env =
            [("compilerVersion",iMkString $ bscVersionStr True),
             ("date",                iMkString $ show clkTime),
             ("epochTime",      iMkLitSize 32 $ floor epochTime),
             ("buildVersion",   iMkLitSize 32 $ buildnum),
             ("genPackageName", iMkString $ getIdBaseString pkgId),
             ("testAssert",        iMkRealBool $ testAssert flags)
            ]

    start flags DFimports
    -- Read imported signatures
    (mimp@(CPackage _ _ imps _ _ _), binmap, hashmap)
        <- readImports errh flags binmap0 hashmap0 min
    when (hasDump flags DFimports) $
      let imps' = [ppReadable s |  (CImpSign _ _ s) <- imps]
      in mapM_ (putStr) imps'
         --mapM_ (\ (CImpSign _ _ s) -> putStr (ppReadable s)) imps
    t <- dump errh flags tStart DFimports dumpnames mimp

    start flags DFopparse
    mop <- parseOps errh mimp
    t <- dump errh flags t DFopparse dumpnames mop

    -- Generate a global symbol table
    --
    -- Later stages will introduce new symbols that will need to be added
    -- to the symbol table.  Rather than worry about properly inserting
    -- the new symbols, we just build the symbol table fresh each time.
    -- So this is the first of several times that the table is built.
    -- We can't delay the building of the table until after all symbols
    -- are known, because these next stages need a table of the current
    -- symbols.
    --
    start flags DFsyminitial
    symt00 <- mkSymTab errh mop
    t <- dump errh flags t DFsyminitial dumpnames symt00

    -- whether we are doing code generation for modules
    let generating = backend flags /= Nothing

    -- Turn `noinline' into module definitions
    start flags DFgenfuncwrap
    (mfwrp, symt0, funcs) <- genFuncWrap errh flags generating mop symt00
    t <- dump errh flags t DFgenfuncwrap dumpnames mfwrp

    -- Generate wrapper for Verilog interface.
    start flags DFgenwrap
    (mwrp, gens) <- genWrap errh flags (genName flags) generating mfwrp symt0
    t <- dump errh flags t DFgenwrap dumpnames mwrp

    -- Rebuild the symbol table because GenWrap added new types
    -- and typeclass instances for those types
    start flags DFsympostgenwrap
    symt1 <- mkSymTab errh mwrp
    t <- dump errh flags t DFsympostgenwrap dumpnames symt1

    -- Re-add function definitions for `noinline'
    mfawrp <- addFuncWrap errh symt1 funcs mwrp

    -- Turn deriving into instance declarations
    start flags DFderiving
    mder <- derive errh flags symt1 mfawrp
    t <- dump errh flags t DFderiving dumpnames mder

    -- Rebuild the symbol table because Deriving added new instances
    start flags DFsympostderiving
    symt11 <- mkSymTab errh mder
    t <- dump errh flags t DFsympostderiving dumpnames symt11

    -- Reduce the contexts as far as possible
    start flags DFctxreduce
    mctx <- cCtxReduceIO errh flags symt11 mder
    t <- dump errh flags t DFctxreduce dumpnames mctx

    -- Rebuild the symbol table because CtxReduce has possibly changed
    -- the types of top-level definitions
    start flags DFsympostctxreduce
    symt <- mkSymTab errh mctx
    t <- dump errh flags t DFsympostctxreduce dumpnames symt

    -- Turn instance declarations into ordinary definitions
    start flags DFconvinst
    let minst = cConvInst errh symt mctx
    t <- dump errh flags t DFconvinst dumpnames minst

    -- Type check and insert dictionaries
    start flags DFtypecheck
    (mod, tcErrors) <- cTypeCheck errh flags symt minst
    --putStr (ppReadable mod)
    t <- dump errh flags t DFtypecheck dumpnames mod

    --when (early flags) $ return ()
    let prefix = dirName name ++ "/"

    -- Generate wrapper info for foreign function imports
    -- (this always happens, even when not generating for modules)
    start flags DFgenforeign
    foreign_func_info <- genForeign errh flags prefix mod
    t <- dump errh flags t DFgenforeign dumpnames foreign_func_info

    -- Generate VPI wrappers for foreign function imports
    start flags DFgenVPI
    blurb <- mkGenFileHeader flags
    let ffuncs = map snd foreign_func_info
    vpi_wrappers <- if (backend flags /= Just Verilog)
                    then return []
                    else if (useDPI flags)
                         then genDPIWrappers errh flags prefix blurb ffuncs
                         else genVPIWrappers errh flags prefix blurb ffuncs
    t <- dump errh flags t DFgenVPI dumpnames vpi_wrappers

    -- Simplify a little
    start flags DFsimplified
    let mod' = simplify flags mod
    t <- dump errh flags t DFsimplified dumpnames mod'
    stats flags DFsimplified mod'

    --------------------------------------------
    -- Convert to internal abstract syntax
    --------------------------------------------
    start flags DFinternal
    imod <- iConvPackage errh flags symt mod'
    t <- dump errh flags t DFinternal dumpnames imod
    when (showISyntax flags) (putStrLnF (show imod))
    iPCheck flags symt imod "internal"
    stats flags DFinternal imod

    -- Read binary interface files
    start flags DFbinary
    let (_, _, impsigs, binmods0, pkgsigs) =
            let findFn i = fromJustOrErr "bsc: binmap" $ M.lookup i binmap
                sorted_ps = [ getIdString i
                               | CImpSign _ _ (CSignature i _ _ _) <- imps ]
            in  unzip5 $ map findFn sorted_ps

    -- injects the "magic" variables genC and genVerilog
    -- should probably be done via primitives
    -- XXX does this interact with signature matching
    -- or will it be caught by flag-matching?
    let adjEnv ::
            [(String, IExpr a)] ->
            (IPackage a) ->
            (IPackage a)
        adjEnv env (IPackage i lps ps ds)
                            | getIdString i == "Prelude" =
                    IPackage i lps ps (map adjDef ds)
            where
                adjDef (IDef i t x p) =
                    case lookup (getIdString (unQualId i)) env of
                        Just e ->  IDef i t e p
                        Nothing -> IDef i t x p
        adjEnv _ p = p

    let
        -- adjust the "raw" packages and then add back their signatures
        -- so they can be put into the current IPackage for linking info
        binmods = zip (map (adjEnv env) binmods0) pkgsigs

    t <- dump errh flags t DFbinary dumpnames binmods

    -- For "genModule" we construct a symbol table that includes all defs,
    -- not just those that are user visible.
    -- XXX This is needed for inserting RWire primitives in AAddSchedAssumps
    -- XXX but is it needed anywhere else?
    start flags DFsympostbinary
    -- XXX The way we construct the symtab is to replace the user-visible
    -- XXX imports with the full imports.
    let mint = replaceImports mctx impsigs
    internalSymt <- mkSymTab errh mint
    t <- dump errh flags t DFsympostbinary dumpnames mint

    start flags DFfixup
    let (imodf, alldefsList) = fixupDefs imod binmods
    let alldefs = M.fromList [(i, e) | IDef i _ e _ <- alldefsList]
    iPCheck flags symt imodf "fixup"
    t <- dump errh flags t DFfixup dumpnames imodf

    start flags DFisimplify
    let imods :: IPackage HeapData
        imods = iSimplify imodf
    iPCheck flags symt imods "isimplify"
    t <- dump errh flags t DFisimplify dumpnames imods
    stats flags DFisimplify imods

    let orderGens :: IPackage HeapData -> [WrapInfo] -> [WrapInfo]
        orderGens (IPackage pid _ _ ds) gs =
                --trace (ppReadable (gis, g, os)) $
                                              map get os
          where gis = [ qualId pid i
                                | (WrapInfo i _ _ _ _ _) <- gs ]
                tr = [ (qualId pid i_, qualId pid i)
                                | (WrapInfo i _ _ i_ _ _) <- gs ]
                ds' = [ IDef (lookupWithDefault tr i i) t e p
                                | IDef i t e p <- ds, i `notElem` gis ]
                is = [ i | IDef i _ _ _ <- ds' ]
                g  = [ (i, fdVars e `intersect` is) | IDef i _ e _ <- ds' ]
                iis = scc g
                os = concat iis `intersect` gis
                get i = headOrErr "bsc.orderGens: no WrapInfo"
                                  [ x | x@(WrapInfo i' _ _ _ _ _) <- gs,
                                                unQualId i == i' ]
        ordgens :: [WrapInfo]
        ordgens = orderGens imods gens

    when (verbose flags) $
        putStr ("modules: " ++
                    ppReadable [ i | (WrapInfo { mod_nm = i }) <- ordgens ] ++
                    "\n")

    let getDef :: IPackage a -> Id -> IDef a
        getDef (IPackage _ _ _ ds) i =
           case [ d | d@(IDef i' _ _ _) <- ds, unQualId i == unQualId i' ] of
                [ d ] -> d
                _ -> internalError ("No definition for " ++ pfpString i)

    -- Generate code for all requested modules
    -- TODO this function gen should be defined outside the compilePackage body
    -- Note: This accumulates the new IPackage on each iteration, but it
    --   doesn't update "alldefs"; this is likely OK because it is only used
    --   to build undefined values (in IExpand) and to insert RWires
    --   (in AAddSchedAssumps)
    let gen :: (IPackage HeapData, Bool) -> [WrapInfo] -> IO (IPackage HeapData, Bool)
        gen (im, !success) []  = return (im, success)
        gen (im, !success) (wi@(WrapInfo { mod_nm = i, wrapped_mod = i' }) : xs) = do
            let (filename, pkgname, _) = dumpnames
                dumpnames' = (filename, pkgname, getIdString (unQualId i))
                fwrapper = i `elem` map (\ (i, _, _, _, _) -> i) funcs

            let
                -- in the Maybe monad
                ex_filt ex = do (CE.ErrorCall s) <- (CE.fromException ex)::(Maybe CE.ErrorCall)
                                return s
                def_comp = do
                  def <- genModule errh wi fwrapper flags dumpnames'
                             prefix (getIdBaseString pkgId)
                             internalSymt alldefs (getDef im i')
                  return (def, True)
                ex_comp s = do
                  hFlush stdout >> hPutStr stderr s
                  -- XXX exitFail will do the pre-exit actions again
                  when (not (enablePoisonPills flags)) $ exitFail errh
                  return (mkPoisonedCDefn i (orig_cqt wi), False)

            (def, ok) <- CE.catchJust ex_filt def_comp ex_comp

            -- wrappercomp has substages, so record the overall start time
            tStartWrapper <- getNow

            start flags DFwrappercomp
            when (extraVerbose flags) $
                putStr ("definition of " ++
                        getIdString i ++
                        ":\n" ++
                        ppReadable def ++
                        "\n\n")

            -- "ok2" indicates whether there was a type-checking error
            -- but multiple-error-reporting chose to keep going;
            -- since it will already appear as a user error, no need for
            -- an internal error
            (idef, ok2) <- compileCDefToIDef errh flags dumpnames' symt imods def

            t <- getNow
            start flags DFfixup
            -- Replace the pre-synthesis definition for a module with its
            -- post-synthesis definition, and update the package's cyclic
            -- references
            -- XXX Note that alldefs is not updated here.  This works
            -- XXX because the defs we use from it will not have changed.
            let im' = updDef idef im binmods
            t <- dump errh flags t DFfixup dumpnames' im'

            t <- dump errh flags tStartWrapper DFwrappercomp dumpnames' idef
            -- recurse for each module in [WrapInfo]
            gen (im', success && ok && ok2) xs


    (imodr, success) <- gen (imods, True) ordgens

    t <- getNow
    -- Finally, generate interface files
    start flags DFwriteBin

    -- Generate the user-visible type signature
    bi_sig <- genUserSign errh symt mctx
    -- Generate a type signature where everything is visible
    bo_sig <- genEverythingSign errh symt mctx

    -- Generate binary version of the internal tree .bo file
    let bin_filename = putInDir (bdir flags) name binSuffix
    genBinFile errh bin_filename bi_sig bo_sig imodr

    -- Print one message for the two files
    let rel_binname = getRelativeFilePath bin_filename
    when (verbose flags) $
         putStrLnF ("Compiled package file created: " ++ rel_binname)
    t <- dumpStr errh flags t DFwriteBin dumpnames bin_filename

    -- XXX We could add the generated .bo directly to the maps,
    -- XXX but we lack the hash (which is generated when reading in a file)
    -- let binfile = (rel_binname, bi_sig, bo_sig, modr, ...)
    --     binmap' = ...
    --     hashmap' = ...

    return (success && not tcErrors, binmap, hashmap)


genModule ::
    ErrorHandle ->
    WrapInfo ->
    Bool ->
    Flags ->
    DumpNames ->
    String -> -- prefix
    String -> -- source package name
    SymTab ->
    M.Map Id (IExpr HeapData) ->
    IDef HeapData ->
    IO (CDefn)

-- [IDef HeapData], VSchedInfo, VPathInfo, VWireInfo, [VFieldInfo], [VPort])
genModule
    errh
    wi
    fwrapper
    flags0
    dumpnames
    prefix
    srcName
    symt
    alldefs
    def  =

  do
    let pps = wi_prags wi
        def_pos = let (IDef i _ _ _) = def
                  in  getPosition i
    flags <- updateFlags errh def_pos [ s | PPoptions ss <- pps, s <- ss ] flags0

    let modstr = getIdString (unQualId (mod_nm wi))

    when (verbose flags) $ putStrLnF ("*****")
    when (showCodeGen flags || verbose flags) $ putStrLnF ("code generation for " ++ modstr ++ " starts")
    t <- getNow

    -- "run" it
    start flags DFexpanded
    imod0 <- iExpand errh flags symt alldefs fwrapper pps def
    iMCheck flags symt imod0 "expanded"
    t <- dump errh flags t DFexpanded dumpnames imod0
    when (showIESyntax flags) (putStrLnF (show imod0))
    stats flags DFexpanded imod0

    progArgs <- getArgs
    when ("-trace-state-loc" `elem` progArgs) $ do
      let (inst_locs, rule_locs) = getIStateLocs imod0
      putStrLn "Instance state locs"
      putStr (ppReadable inst_locs)
      putStrLn "Rule state locs"
      putStr (ppReadable rule_locs)

    start flags DFinlineFmt
    imod_fmt <- iInlineFmt errh imod0
    iMCheck flags symt imod_fmt "Fmt inline"
    t <- dump errh flags t DFinlineFmt dumpnames imod_fmt
    stats flags DFinlineFmt imod_fmt

    -- Inline defs
    start flags DFinline
    let imod_inline@(IModule { imod_interface = ifc }) =
            if inlineISyntax flags
            then (iInline (inlineSimple flags) imod_fmt)
            else imod_fmt
    iMCheck flags symt imod_inline "inline"
    t <- dump errh flags t DFinline dumpnames imod_inline
    stats flags DFinline imod_inline

    start flags DFtransform
    let imod_trans = iTransform errh flags "__i" imod_inline
    iMCheck flags symt imod_trans "transform"
    t <- dump errh flags t DFtransform dumpnames imod_trans
    stats flags DFtransform imod_trans

    -- Split rules containing if statements
    start flags DFsplitIf
    let imod_splitif = iSplitIf flags imod_trans
    iMCheck flags symt imod_splitif "splitIf"
    t <- dump errh flags t DFsplitIf dumpnames imod_splitif
    stats flags DFsplitIf imod_splitif

    -- Lift where possible
    start flags DFlift
    let imod_lift = iLift errh flags imod_splitif
    iMCheck flags symt imod_lift "lift"
    t <- dump errh flags t DFlift dumpnames imod_lift
    stats flags DFlift imod_lift

    -- Transform to simpler form (take 2)
    start flags DFtransform
    let imod_trans2 = iTransform errh flags "__j" imod_lift
    iMCheck flags symt imod_trans2 "transform"
    t <- dump errh flags t DFtransform dumpnames imod_trans2
    stats flags DFtransform imod_trans2

    -- Inline expressions for submodule instantiation parameters
    -- Or separate them into localparam defs instead of wire defs
    start flags DFiparams
    imod_param <- iParams errh imod_trans2
    t <- dump errh flags t DFiparams dumpnames imod_param

    start flags DFidroprules
    imod_drop <- iDropRules errh flags imod_param
    stats flags DFidroprules imod_drop
    t <- dump errh flags t DFidroprules dumpnames imod_drop

    -- Generate ATS
    -- ATS stands for "Abstract Transition System" from James C. Hoe's Ph.D. thesis
    start flags DFATS
    amod <- aConv errh pps flags imod_drop
    aCheck flags amod "ATS"
    t <- dump errh flags t DFATS dumpnames amod
    amod == amod `seq` return ()
    t <- if (isJust $ lookup DFATSexpand $ dumps flags)
         then dumpStr errh flags t DFATSexpand dumpnames $
              pretty 120 100 $ ppeAPackage (expandATSlimit flags) PDReadable amod
         else return t
    stats flags DFATS amod

    let flat_inst_tree = flattenInstTree (apkg_inst_tree amod)
    when ("-hack-strict-inst-tree" `elem` progArgs) $ do
      when (any isNothing (map snd (concatMap snd flat_inst_tree))) $
        internalError ("Bad inst tree:\n " ++ ppReadable flat_inst_tree)

    when ("-trace-inst-tree" `elem` progArgs) $ do
      putStrLn "Instantiation tree"
      putStr (ppReadable (apkg_inst_tree amod))
--      putStrLn "Instantiation tree"
--      putStr (ppReadable flat_inst_tree)

-- append ranks to method names and calls for "performance guarantees"
    start flags DFATSperfspec
    amod_ranked <- aRankMethCalls errh pps amod
    aCheck flags amod_ranked "ATSperfspec"
    t <- dump errh flags t DFATSperfspec dumpnames amod_ranked

-- splice in the identifiers set by ActionValue tasks into the ATaskAction calls
    start flags DFATSsplice
    let amod_splice = aTaskSplice amod_ranked
    aCheck flags amod_splice "ATSsplice"
    t <- dump errh flags t DFATSsplice dumpnames amod_splice
    stats flags DFATSsplice amod_splice

-- clean up ATS (merge any ME calls to the same action in the same rule)
    start flags DFATSclean
    amod_clean <- aCleanup errh flags amod_splice
    aCheck flags amod_clean "ATSclean"
    t <- dump errh flags t DFATSclean dumpnames amod_clean

    start flags DFdumpLambdaCalculus
    lc_pkg <- convAPackageToLambdaCalc errh flags amod_clean
    t <- dump errh flags t DFdumpLambdaCalculus dumpnames lc_pkg

    start flags DFdumpSAL
    sal_ctx <- convAPackageToSAL errh flags amod_clean
    t <- dump errh flags t DFdumpSAL dumpnames sal_ctx

    -- Build path graph for everything except rules
    start flags DFpathsPreSched
    (pathGraphInfo, urgency_pairs) <- aPathsPreSched errh flags amod_clean
    t <- dump errh flags t DFpathsPreSched dumpnames pathGraphInfo

    -- Schedule
    start flags DFschedule
    (schedule_info, amod_sched)
        <- do res <- aSchedule errh flags prefix urgency_pairs pps amod_clean
              case res of
                Right r -> return r
                Left schedule_info -> do
                    t <- dump errh flags t DFschedule dumpnames
                             (asei_schedule schedule_info)
                    -- dump the schedule, if requested
                    t <- if (showSchedule flags)
                         then do start flags DFdumpschedule
                                 aDumpScheduleErr errh flags prefix
                                                  amod_clean schedule_info
                                 dump errh flags t DFdumpschedule dumpnames ()
                         else return t
                    -- generate a .ba file, if requested
                    t <- if (genABin flags)
                         then writeABinSchedErr errh pps flags dumpnames t
                                  prefix modstr srcName (orig_cqt wi)
                                  schedule_info amod_clean
                         else return t
                    exitFail errh
    t <- dump errh flags t DFschedule dumpnames (asi_schedule schedule_info)
    stats flags DFschedule amod_sched
    start flags DFresources
    t <- dump errh flags t DFresources dumpnames
         (asi_resource_alloc_table schedule_info)
    start flags DFvschedinfo
    t <- dump errh flags t DFvschedinfo dumpnames (asi_v_sched_info schedule_info)

    -- Add CAN_FIRE and WILL_FIRE defs based on the schedule
    start flags DFscheduledefs
    amod_scheduled <- aAddScheduleDefs flags
                                       pps
                                       amod_sched
                                       schedule_info
    t <- dump errh flags t DFscheduledefs dumpnames amod_scheduled

    start flags DFdumpschedule
    -- only difference from amod_scheduled to amod_dump is some rules removed
    (amod_dump, schedule_info_updated, methodConflict)
        <- aDumpSchedule errh flags pps prefix amod_scheduled schedule_info
    let schedule_final = asi_schedule schedule_info_updated
    let ms = (amod_dump, schedule_final)
    t <- dump errh flags t DFdumpschedule dumpnames ms

    -- prove any proof obligations accumulated at this point
    start flags DFcheckproofs
    -- the obligations are removed from the module
    (amod_check, ok) <- aCheckProofs errh flags amod_dump
    t <- dump errh flags t DFcheckproofs dumpnames ok

    -- Add scheduler edges to the path graph
    -- (we assume that pathGraphInfo is consistent with amod_checked, because
    -- at most only a few rules have been removed since amod_clean)
    start flags DFpathsPostSched
    vPathInfo <- aPathsPostSched flags pps amod_check pathGraphInfo schedule_final
    t <- dump errh flags t DFpathsPostSched dumpnames vPathInfo

    -- lift all no-inline func calls and assign instance names to them
    start flags DFnoinline
    let amod_noinline = aNoInline flags amod_check
    t <- dump errh flags t DFnoinline dumpnames amod_noinline

    -- add scheduling assumptions (ME, CF, etc.) to APackage (in two steps)
    start flags DFaddSchedAssumps
    (amod_wires, sched_info')
        <- aAddCFConditionWires errh symt alldefs flags
                                amod_noinline schedule_info_updated
    let (amod_assumps, sched_info'') =
            aAddSchedAssumps amod_wires schedule_final sched_info'
    aCheck flags amod_assumps "addSchedAssumps"
    t <- dump errh flags t DFaddSchedAssumps dumpnames
             (amod_assumps,
              asi_method_uses_map sched_info'',
              asi_resource_alloc_table sched_info'')

    -- move assumption actions into rule bodies
    start flags DFremoveAssumps
    let amod_no_assumps = aRemoveAssumps amod_assumps
    aCheck flags amod_no_assumps "aRemoveAssumps"
    t <- dump errh flags t DFremoveAssumps dumpnames amod_no_assumps

    -- drop ASAny with "chosen" values
    -- just before the split because other paths add new expressions
    -- and because we might choose more undets in pathsPostSched
    start flags DFdropundet
    let amod_no_undet = aDropUndet errh flags amod_no_assumps
    t <- dump errh flags t DFdropundet dumpnames amod_no_undet

    -- the amod doesn't change beyond this point
    let amod_final = amod_no_undet

    -- save wireinfo
    let wireinfo = apkg_external_wires amod_final
    let fieldinfo = getAPackageFieldInfos amod_final

    blurb <- mkGenFileHeader flags
    let methodConflictBlurb :: [String] -- string printed in top of Verilog file
        methodConflictBlurb
            | methodConf flags =
                ["Method conflict info:"]
                ++ lines (pretty 78 78 (vcat (dumpMethodInfo flags methodConflict)) )
            | otherwise = []

    let methodConflictBVI :: [String] -- string printed in top of Verilog file
        methodConflictBVI
            | methodBVI flags =
                ["BVI format method schedule info:"]
                ++ lines (pretty 78 78 (vcat (dumpMethodBVIInfo methodConflict)) )
            | otherwise = []
    -- Additional info from the Verilog backend
    -- * veriPortProps =
    --           IO properties which can be included as attributes in the
    --           Cmoduleverilog (import-BVI)
    --           XXX it would be nice if the Bluesim backend had the same info
    -- * vprog = the Verilog data structure, for recording in the .ba file,
    --           so that it's available to bluetcl
    (t, veriPortProps, vprog)
        <- if (backend flags == Just Verilog)
           then do (t', ips, v)
                       <- genModuleVerilog
                             errh pps flags dumpnames t prefix modstr
                             blurb methodConflictBlurb methodConflictBVI
                             vPathInfo sched_info'' amod_final
                   return (t', ips, Just v)
           else return (t, [], Nothing)

    t <- if (genABin flags)
         then writeABin errh pps flags dumpnames t prefix
                  modstr srcName (orig_cqt wi)
                  sched_info'' methodConflict vPathInfo
                  amod_final vprog
         else return t

    -- Wrapper generation
    start flags DFwrappergen

    -- ids of value methods with constant True output
    -- (any rdy signals in this list don't need to be wired up
    -- in the wrapper; it can assume a value of 1)
    let true_ifc_ids  = [ i | IEFace i _ (Just (e, t)) _ _ _ <- ifc, isTrue e || isAlwaysRdy pps i ]
    def <- (deffun wi)
                 fwrapper
                 wireinfo
                 (asi_v_sched_info schedule_info)
                 vPathInfo
                 veriPortProps
                 symt
                 fieldinfo
                 true_ifc_ids

    -- mainly because hypering the def will force any embedded exceptions
    t <- dump errh flags t DFwrappergen dumpnames def
    return (def)


writeABin :: ErrorHandle -> [PProp] -> Flags -> DumpNames -> TimeInfo ->
             String -> String -> String -> CQType ->
             AScheduleInfo -> MethodDumpInfo -> VPathInfo ->
             APackage -> Maybe VProgram -> IO (TimeInfo)
writeABin errh pps flags dumpnames t prefix modstr srcName oqt
          sched_info methodConflict vPathInfo amod vprog =
    do
       start flags DFwriteABin

       -- Don't generate .ba file if the backend is Bluesim and the
       -- module has features not supported by Bluesim.
       -- XXX For Verilog, this currently does nothing, but it could be
       -- XXX made to taint the .ba and issue a warning.
       amod_for_abin
           <- simCheckPackage errh (backend flags == Just Bluesim) amod

       -- generate the abin file
       let afilename = mkAName (bdir flags) prefix modstr
           afilename_rel = getRelativeFilePath afilename
           backend = apkg_backend amod_for_abin
           abinPrintPrefix =
              case (backend) of
                  Nothing -> "Elaborated module file created: "
                  Just be ->
                      "Elaborated " ++ ppString be ++ " module file created: "
           modinfo = ABinModInfo {
                          abmi_path = prefix,
                          abmi_src_name = srcName,
                          --abmi_time = now,
                          abmi_apkg        = amod_for_abin,
                          abmi_aschedinfo  = sched_info,
                          abmi_pps         = pps,
                          abmi_oqt         = oqt,
                          abmi_method_dump = methodConflict,
                          abmi_pathinfo = vPathInfo,
                          abmi_flags       = flags,
                          abmi_vprogram    = if (genABinVerilog flags)
                                             then vprog else Nothing
                     }
           abin = ABinMod modinfo (bscVersionStr True)
       genABinFile errh afilename abin
       unless (quiet flags) $ putStrLnF $ abinPrintPrefix ++ afilename_rel
       dump errh flags t DFwriteABin dumpnames afilename


writeABinSchedErr :: ErrorHandle -> [PProp] -> Flags -> DumpNames -> TimeInfo ->
                     String -> String -> String -> CQType ->
                     AScheduleErrInfo -> APackage -> IO (TimeInfo)
writeABinSchedErr errh pps flags dumpnames t prefix modstr srcName oqt
                  sched_info amod =
    do
       start flags DFwriteABin

       -- generate the abin file
       let afilename = mkAName (bdir flags) prefix modstr
           afilename_rel = getRelativeFilePath afilename
           abinPrintPrefix = "Elaborated error module file created: "
           modinfo = ABinModSchedErrInfo {
                          abmsei_path          = prefix,
                          abmsei_src_name      = srcName,
                          abmsei_apkg          = amod,
                          abmsei_aschederrinfo = sched_info,
                          abmsei_pps           = pps,
                          abmsei_oqt           = oqt,
                          abmsei_flags         = flags
                     }
           abin = ABinModSchedErr modinfo (bscVersionStr True)
       genABinFile errh afilename abin
       unless (quiet flags) $ putStrLnF $ abinPrintPrefix ++ afilename_rel
       dump errh flags t DFwriteABin dumpnames afilename


-- ===============
-- genModuleVerilog

genModuleVerilog :: ErrorHandle
                 -> [PProp]
                 -> Flags
                 -> DumpNames
                 -> TimeInfo
                 -> String -- prefix
                 -> String -- top module name
                 -> [String] -- header blurb lines
                 -> [String] -- method conflict blurb lines
                 -> [String] -- method bvi format blurb lines
                 -> VPathInfo -- used to create path info blurb lines
                 -> AScheduleInfo
                 -> APackage
                 -> IO (TimeInfo,
                        [VPort],   -- port properties for the import-BVI
                        VProgram)  -- generated Verilog
genModuleVerilog errh pprops flags dumpnames time0 prefix moduleName
                 blurb methodConflictBlurb methodConflictBVI vPathInfo scheduleInfo
                 atsPackage =
    do
       -- Read in foreign function info from .ba files for
       -- all foreign functions used in the design, and build a
       -- map to be used when generating verilog
       start flags DFforeignMap
       let foreign_func_names = getForeignCallNames atsPackage
           readABin ffname =
               let err = (noPosition,
                          EMissingABinForeignFuncFile ffname moduleName)
               in  readAndCheckABinPathCatch errh
                       (verbose flags) (ifcPath flags) (Just Verilog)
                       ffname err
       abis <- mapM readABin foreign_func_names
       ff_map <- buildForeignFunctionMap errh abis
       t <- dump errh flags time0 DFforeignMap dumpnames ff_map

       -- Generate muxes etc.
       start flags DFastate
       asmod <- aState errh flags pprops scheduleInfo atsPackage
       -- after aState, method calls should no longer exist
       asMethCheck flags asmod "astate"
       t <- dump errh flags t DFastate dumpnames asmod
       stats flags DFastate asmod

       -- Get rid of wires (and warn about BypassWire where necessary)
       start flags DFrwire
       let (asmodNoWires, wireWarnings, wireErrors)
               | removeRWire flags = aInlineWires flags asmod
               | otherwise = (asmod, [], [])
       when (not (null wireWarnings)) $ bsWarning errh wireWarnings
       when (not (null wireErrors))   $ bsError errh wireErrors
       asCheck flags asmodNoWires "ainlinewires"
       t <- dump errh flags t DFrwire dumpnames asmodNoWires
       stats flags DFrwire asmodNoWires

       -- Inline CReg modules (replacing with Reg modules)
       start flags DFcreg
       let asmodNoCReg
               | removeCReg flags = aInlineCReg asmodNoWires
               | otherwise = asmodNoWires
       asCheck flags asmodNoCReg "ainlinecreg"
       t <- dump errh flags t DFcreg dumpnames asmodNoCReg
       stats flags DFrwire asmodNoCReg

       -- Rename submodule ports from the method-notation to the actual
       -- Verilog port names
       start flags DFrenameio
       let armod = aRenameIO flags asmodNoCReg
       asCheck flags armod "renameio"
       t <- dump errh flags t DFrenameio dumpnames armod
       stats flags DFrenameio armod

       -- drop unused defs
       start flags DFadropdefs
       let adropmod = aDropDefs armod
       asCheck flags adropmod "adropdefs"
       t <- dump errh flags t DFadropdefs dumpnames adropmod
       stats flags DFadropdefs adropmod

       -- Improve
       start flags DFaopt
       aomod <- aOpt errh flags adropmod
       asCheck flags aomod "aopt"
       t <- dump errh flags t DFaopt dumpnames aomod
       stats flags DFaopt aomod

       -- Expand some primitives
       start flags DFsynthesize
       let asynmod = (aSynthesize flags aomod)
       asCheck flags asynmod "asynthesize"
       -- Check that referenced signal names exist
       asSignalCheck flags asynmod "synthesize"
       t <- dump errh flags t DFsynthesize dumpnames asynmod
       stats flags DFsynthesize asynmod

       -- Transform to adapt to Verilog quirks
       start flags DFveriquirks
       let aqmod = aVeriQuirks flags asynmod
       -- this check is too strict on plus operator output size
       -- XXX fix the check, don't disable it
       when (not (keepAddSize flags))
            (asCheck flags aqmod "veriquirks")
       t <- dump errh flags t DFveriquirks dumpnames aqmod
       stats flags DFveriquirks aqmod

       -- Transform to adapt to Verilog quirks
       start flags DFfinalcleanup
       let aumod =  finalCleanup flags aqmod
       -- this check is too strict on plus operator output size
       -- XXX fix the check, don't disable it
       when (not (keepAddSize flags))
            (asCheck flags aumod "finalcleanup")
       t <- dump errh flags t DFfinalcleanup dumpnames aumod
       stats flags DFfinalcleanup aumod

       start flags DFIOproperties
       let (ioprops, ips) = getIOProps flags aumod
       t <- dump errh flags t DFIOproperties dumpnames ioprops

       -- Generate Verilog
       start flags DFverilog
       -- This is monadic because it can report an error
       vprog0 <- aVerilog errh flags pprops aumod ff_map
       t <- dump errh flags t DFverilog dumpnames vprog0

       -- Remove dollar signs from Verilog identifiers
       start flags DFverilogDollar
       let vprog = if (removeVerilogDollar flags)
                   then (removeDollarsFromVerilog vprog0)
                   else vprog0
       t <- dump errh flags t DFverilogDollar dumpnames vprog

       -- Write the Verilog files
       start flags DFwriteVerilog
       vfilenames <- writeVerilog errh flags prefix
                         blurb methodConflictBlurb methodConflictBVI ioprops vPathInfo
                         vprog
       t <- dump errh flags t DFwriteVerilog dumpnames vfilenames

       -- Return
       -- * the port properties (to be included in the import-BVI)
       -- * the Verilog structure (for accessing in bluetcl)
       return (t, ips, vprog)


-- Write a Verilog program to file (along with its use file)
writeVerilog :: ErrorHandle -> Flags -> String ->
                [String] -> [String] -> [String] -> VIOProps -> VPathInfo ->
                VProgram -> IO ([VFileName])
writeVerilog errh flags prefix
             blurb methodConflictBlurb methodConflictBVI ioprops vPathInfo
             vprog =
    do
       let modName :: String
           modName = (vGetMainModName vprog)

       -- Make the filename (full path, but with the relative prefix encoded)
       vName_init <- genFileName mkVName (vdir flags) prefix modName
       -- The relative filename, for reporting to the user
       let vNameRel = (getRelativeFilePath vName_init)
       -- The final name used to write the file (full path)
       let vName = VFileName (getFullFilePath vName_init)

       -- Names for the use file
       let useNameRel = dropSuf vNameRel ++ "." ++ useSuffix
           useName = dropSuf (vfnString vName) ++ "." ++ useSuffix

       -- Comments at the top of the Verilog file
       let pathInfoBlurb = lines (pp80 vPathInfo)
           ioblurb = "" : "Ports:" : lines (pp80 ioprops)
           comment = commentV (blurb ++ methodConflictBlurb ++ methodConflictBVI ++
                               ioblurb ++
                               pathInfoBlurb ++ [""])

       -- The contents of the Verilog file
       let vstring = comment ++ pp80 vprog

       writeVFileCatch errh flags vName vstring
       unless (quiet flags) $ putStrLnF ("Verilog file created: " ++ vNameRel)

       -- if generating a use file
       when (showModuleUse flags) $ do
           writeFileCatch errh useName (unlines (getVeriInsts vprog))
           unless (quiet flags) $ putStrLnF ("Use file created: " ++ useNameRel)

       return [vName]


writeVFileCatch :: ErrorHandle -> Flags -> VFileName -> String -> IO ()
writeVFileCatch errh flags (VFileName fn) s = do
    let dropTrailingBlanks :: String -> String
        dropTrailingBlanks s | null s           = s
                             | isSpace $ last s = dropTrailingBlanks $ init s
                             | otherwise        = s
        --
        s' = unlines $  map dropTrailingBlanks $ lines s
    writeFileCatch errh fn s'
    let applyFilter :: String -> IO ()
        applyFilter command = do
          let cmdstr = command ++ " " ++ fn
          when (verbose flags) $
            unless (quiet flags) $ putStrLnF ("Executing Verilog filter " ++ quote cmdstr)
          code <- system cmdstr
          case code of
            ExitSuccess     -> return ()
            (ExitFailure n) -> bsError errh [(cmdPosition, EVerilogFilterError command fn n)]
    mapM_ applyFilter $ reverse $ verilogFilter flags

-- ===============
-- genModuleC

-- might as well inline this into simLink (no need to be separate)
genModuleC :: ErrorHandle
           -> Flags
           -> DumpNames
           -> TimeInfo
           -> String
           -> [(String, ABin)]
           -> IO (TimeInfo, [String], [String], TimeInfo)
genModuleC errh flags dumpnames time0 toplevel abis =
    do
       pwd <- getCurrentDirectory
       let name = createEncodedFullFilePath "placeholder" pwd
           prefix = (dirName name) ++ "/"

       -- create SimSystem which contains SimPackages and SimSchedules
       start flags DFsimExpand
       sim_system <- simExpand errh flags toplevel abis
       time <- dump errh flags time0 DFsimExpand dumpnames sim_system

       -- extract file dependency structure and determine if any
       -- existing bluesim packages can reuse existing object files
       start flags DFsimDepend
       reused <- analyzeBluesimDependencies flags sim_system prefix
       time <- dump errh flags time DFsimDepend dumpnames reused

       -- optimize the SimPackages and SimSchedules
       start flags DFsimPackageOpt
       sim_system_opt <- simPackageOpt errh flags sim_system
       time <- dump errh flags time DFsimPackageOpt dumpnames sim_system_opt

       -- convert SimPackages and SimSchedules to SimCCBlocks and SimCCScheds
       start flags DFsimMakeCBlocks
       let (simblocks, simCCscheds, clk_groups, gate_info, top_id) =
                simMakeCBlocks flags sim_system_opt
       let simBlockInfo = (simblocks, simCCscheds, clk_groups, gate_info)
       time <- dump errh flags time DFsimMakeCBlocks dumpnames simBlockInfo

       -- optimize the SimCCBlocks and SimCCScheds
       start flags DFsimCOpt
       let (simblocks_opt, simCCscheds_opt, clk_groups_opt, gate_info_opt) =
               simCOpt flags
                       (ssys_instmap sim_system_opt)
                       (simblocks, simCCscheds, clk_groups, gate_info)
       let simBlockInfo = (simblocks_opt, simCCscheds_opt, clk_groups_opt, gate_info_opt)
       time <- dump errh flags time DFsimCOpt dumpnames simBlockInfo

       -- get the map of ForeignFunctions
       let ff_map = ssys_ffuncmap sim_system_opt

       blurb <- mkGenFileHeader flags
       let mkEncodedName s = genFileName mkNameWithoutSuffix (cdir flags) prefix s
           -- write CCSyntax to file and return the relative file name
           writeFileC :: String -> String -> IO String
           writeFileC name file = do
             t_start <- getNow
             start flags DFwriteC
             encoded_name <- mkEncodedName name
             let full_name = getFullFilePath encoded_name
                 rel_name = getRelativeFilePath encoded_name
             writeFileCatch errh full_name ((commentC blurb) ++ file)
             _<- dumpStr errh flags t_start DFwriteC dumpnames name
             return rel_name

       -- convert SimCCBlocks and SimCCScheds to CCSyntax
       start flags DFsimBlocksToC
       let sb_map = M.fromList $ map (\sb -> (sb_id sb,sb))
                                     (simblocks_opt ++ primBlocks)
           creation_time = time

       block_names <- simBlocksToC flags
                                   creation_time
                                   top_id
                                   (ssys_default_clk sim_system_opt)
                                   (ssys_default_rst sim_system_opt)
                                   sb_map
                                   ff_map
                                   reused
                                   simblocks_opt
                                   simCCscheds_opt
                                   clk_groups_opt
                                   gate_info_opt
                                   writeFileC

       -- generate a header with imported function declarations
       let import_header =
             if M.null ff_map
             then []
             else [("imported_BDPI_functions.h",
                    ppReadable (mkImportDeclarations ff_map))]

       imp_names <- mapM (uncurry writeFileC) import_header

       let core_names = imp_names ++ block_names

       time <- dumpStr errh flags time DFsimBlocksToC dumpnames (unlines core_names)

       -- if generation target is SystemC, generate the wrapper file too
       start flags DFgenSystemC
       when (genSysC flags) $
            do bsMessage errh [(cmdPosition, MRestrictions "creating SystemC models" "the -systemc option")]
               checkSystemCIfc errh flags sim_system_opt
       sysc_files <- if (genSysC flags)
                     then wrapSystemC flags sim_system_opt
                     else return []
       time <- dump errh flags time DFgenSystemC dumpnames sysc_files

       sysc_names <- mapM (uncurry writeFileC) sysc_files

       let names = core_names ++ sysc_names

       reused_names <- mapM (\s -> do let cxx = mkObjName Nothing "" s
                                      n <- mkEncodedName cxx
                                      return $ getRelativeFilePath n)
                            reused

       -- XXX return the headers separate from the files which need to be
       -- XXX compiled
       return (time, names, reused_names, creation_time)

-- ===============
-- SimLink

simLink :: ErrorHandle -> Flags -> String -> [String] -> [String] -> IO ()
simLink errh flags toplevel afilenames cfilenames = do
    tStart <- getNow
    let t = tStart

    -- XXX (file, package, module) names for %-substitution in dump filenames
    let dumpnames = ("","","")

    -- in case the user listed the same file twice
    -- (they could still have given two .ba for the same module,
    -- and simExpand will check for that)
    let afilenames_unique = nub afilenames
    let cfilenames_unique = nub cfilenames

    -- check that .c and .o files listed on the command-line exist
    missing <- missingUserFiles flags cfilenames_unique
    when (not (null missing)) $
        bsError errh
            [(cmdPosition, EMissingUserFile f ["."]) | f <- missing]
    t <- timestampStr flags "confirm C files exist" t

    -- read in the abin files (check hash and that they are C files)
    start flags DFreadelab
    let read_abin_fn = readAndCheckABin errh (Just Bluesim)
    abis <- mapM read_abin_fn afilenames_unique
    t <- dump errh flags t DFreadelab dumpnames (map fst abis)

    -- generate the files, get back a list of files to be compiled
    -- and a list of files which have already been compiled
    (t, to_compile, to_reuse, creation_time)
        <- genModuleC errh flags dumpnames t toplevel abis
    let t_before_compilations = t

    -- print a message to the user that we are reusing the files
    ofiles_reused <- mapM (reuseBluesimCFile flags) to_reuse

    -- XXX in the absence of genModuleC returning separate lists of header
    -- XXX files and actual C files to be compiled, partition them here
    let ({-hfiles-}_, gen_cfiles) = partition (hasDotSuf hSuffix) to_compile
    let (user_cfiles, user_ofiles) =
            partition (\f -> hasDotSuf cSuffix f   ||
                             hasDotSuf cxxSuffix f ||
                             hasDotSuf cppSuffix f ||
                             hasDotSuf ccSuffix f
                      )
                      cfilenames_unique

    start flags DFbluesimcompile
    let jobs = parallelSimLink flags
    (gen_ofiles, compiled_user_ofiles) <-
        if (jobs > 1)
        then do
          compileParallelCFiles errh flags False
              toplevel gen_cfiles user_cfiles
        else do
          ofiles0 <- mapM (compileBluesimCFile errh flags) gen_cfiles
          t <- timestampStr flags "compile generated C++ files" t

          ofiles1 <- mapM (compileUserCFile errh flags False) user_cfiles
          t <- timestampStr flags "compile user-provided C/C++ files" t

          return (ofiles0, ofiles1)
    let ofiles = gen_ofiles ++
                 user_ofiles ++ compiled_user_ofiles ++
                 ofiles_reused
    t <- dump errh flags t_before_compilations DFbluesimcompile dumpnames
              ofiles

    -- if not generating a SystemC model, link to a Bluesim executable
    start flags DFbluesimlink
    when (not (genSysC flags)) $
      cxxLink errh flags toplevel ofiles creation_time
    t <- dump errh flags t DFbluesimlink dumpnames toplevel

    -- final verbose message
    _ <- timestampStr flags "total" tStart

    return ()

-- Reuse a Bluesim generated object file
-- returns the name of the object file being reused
reuseBluesimCFile :: Flags -> String -> IO String
reuseBluesimCFile flags oName = do
    -- show is used for quoting
    systemc <- liftM show $ getEnvDef "SYSTEMC" ""
    let engine = if (genSysC flags) && ("_systemc" `isSuffixOf` (dropSuf oName))
                 then "SystemC"
                 else "Bluesim"
        oNameRel = getRelativeFilePath oName
    -- we lie here and mention both header and object (un-mangled name)
    let msg = engine ++ " object reused: " ++ (dropSuf oNameRel) ++
              ".{" ++ hSuffix ++ "," ++ objSuffix ++ "}"
    unless (quiet flags) $ putStrLnF msg
    return oName

-- compile a Bluesim generated CXX file
-- returns the name of the object file created
compileBluesimCFile :: ErrorHandle -> Flags -> String -> IO String
compileBluesimCFile errh flags cName = do
    (cmd, oName, msg) <- cmdCompileBluesimCFile flags cName
    execCmd errh flags cmd
    unless (quiet flags) $ putStrLnF msg
    return oName

-- construct the command for compiling a Bluesim CXX file
-- and return the name of the object file
-- and the message to display to the user
-- (this is shared by the serial and parallel compilation paths)
cmdCompileBluesimCFile :: Flags -> String -> IO (String, String, String)
cmdCompileBluesimCFile flags cName = do
    systemc <- getEnvDef "SYSTEMC" ""
    let engine = if (genSysC flags) && ("_systemc" `isSuffixOf` (dropSuf cName))
                 then "SystemC"
                 else "Bluesim"
    let oName = mkObjName Nothing "" (dropSuf cName)
    -- show is used for quoting
    let incflags = ["-I" ++ show (bluespecDir flags) ++ "/Bluesim"] ++
                   (if ((engine == "SystemC") && (systemc /= ""))
                    then ["-I" ++ show systemc ++ "/include"]
                    else [])
        -- Generated C++ code may reference uninitialized variables when it
        -- is known to be safe.
        switches = incflags ++
                   [ "-Wno-uninitialized"
                   , "-fPIC"
                   , "-c"
                   , "-o"
                   , show (mangleFileName oName)
                   ]
        -- show is used for quoting
        opts = map show (cxxFlags flags)
        files = [show (mangleFileName cName)]
    cmd <- cmdCXXCompile flags (opts ++ switches) files
    let cNameRel = getRelativeFilePath cName
    -- we lie here and mention both header and object (un-mangled name)
    let msg = engine ++ " object created: " ++ (dropSuf cNameRel) ++
              ".{" ++ hSuffix ++ "," ++ objSuffix ++ "}"
    return (cmd, oName, msg)

-- returns the name of the object file created
compileVPICFile :: ErrorHandle -> Flags -> [String] -> String -> IO String
compileVPICFile errh flags incdirs cName = do
    let oName = mkObjName Nothing "" (dropSuf cName)
    -- show is used for quoting
    let incflags = map (("-I"++) . show) (cIncPath flags) ++
                   ["-I" ++ show (bluespecDir flags) ++ "/VPI"] ++
                   map (\d -> "-I" ++ d) incdirs
        switches = incflags ++
                   [ "-fPIC"
                   , "-c"
                   , "-o"
                   , show (mangleFileName oName)
                   ]
        files = [show (mangleFileName cName)]
    let compileFn = if hasDotSuf cSuffix cName
                    then cCompile
                    else cxxCompile
    -- show is used for quoting
    let opts = map show $ if hasDotSuf cSuffix cName
                          then cFlags flags
                          else cxxFlags flags
    compileFn errh flags (opts ++ switches) files
    let cNameRel = getRelativeFilePath cName
    let msg = "VPI object created: " ++
              (mkObjName Nothing "" (dropSuf cNameRel))
    unless (quiet flags) $ putStrLnF msg
    return oName

-- returns the name of the object file created
compileUserCFile :: ErrorHandle -> Flags -> Bool -> String -> IO String
compileUserCFile errh flags forVerilog cName = do
    (cmd, oName, msg) <- cmdCompileUserCFile flags forVerilog cName
    execCmd errh flags cmd
    unless (quiet flags) $ putStrLnF msg
    return oName

-- construct the command for compiling a user C or CXX file
-- and return the name of the object file
-- and the message to display to the user
-- (this is shared by the serial and parallel compilation paths)
cmdCompileUserCFile :: Flags -> Bool -> String -> IO (String, String, String)
cmdCompileUserCFile flags forVerilog cName = do
    let oName = mkObjName Nothing "" (dropSuf cName)
    -- show is used for quoting
    let incflags = map (("-I"++) . show) (cIncPath flags)
        switches = incflags ++
                   [ "-fPIC"
                   , "-c"
                   , "-o"
                   , show (mangleFileName oName)
                   ]
        files = [show (mangleFileName cName)]
    let cmdCompileFn = if hasDotSuf cSuffix cName
                       then cmdCCompile
                       else cmdCXXCompile
    -- show is used for quoting
    let opts = map show $ if hasDotSuf cSuffix cName
                          then cFlags flags
                          else cxxFlags flags
    cmd <- cmdCompileFn flags (opts ++ switches) files
    let cNameRel = getRelativeFilePath cName
    let msg = "User object created: " ++
              (mkObjName Nothing "" (dropSuf cNameRel))
    return (cmd, oName, msg)

-- Compile Bluesim and user C/C++ files in parallel, using "make"
compileParallelCFiles :: ErrorHandle -> Flags -> Bool ->
                         String -> [String] -> [String] ->
                         IO ([String], [String])
-- avoid having "make" report "nothing to be done"
compileParallelCFiles errh flags forVerilog toplevel [] [] = return ([], [])
compileParallelCFiles errh flags forVerilog toplevel gen_cNames user_cNames = do
    let mkBluesimRule cName = do
          (cmd, oName, msg) <- cmdCompileBluesimCFile flags cName
          let esc_oName = escMakeTarget oName
              esc_cmd = escMakeRecipe cmd
              esc_msg = escMakeRecipe msg
          -- we use "PHONY" to force recompilation
          -- we use singlequotes on the echos, to avoid interpreting strings
          let rule = ".PHONY: " ++ esc_oName ++ "\n" ++
                     esc_oName ++ ":\n" ++
                     (if (quiet flags) then ""
                      else "\t@echo exec: '" ++ esc_cmd ++ "'\n") ++
                     "\t@" ++ esc_cmd ++ "\n" ++
                     (if (quiet flags) then ""
                      else "\t@echo '" ++ esc_msg ++ "'\n")
          return (oName, rule, esc_oName)
    let mkUserRule cName = do
          (cmd, oName, msg) <- cmdCompileUserCFile flags forVerilog cName
          let esc_oName = escMakeTarget oName
              esc_cmd = escMakeRecipe cmd
              esc_msg = escMakeRecipe msg
          -- we use "PHONY" to force recompilation
          -- we use singlequotes on the echos, to avoid interpreting strings
          let rule = ".PHONY: " ++ esc_oName ++ "\n" ++
                     esc_oName ++ ":\n" ++
                     (if (quiet flags) then ""
                      else "\t@echo exec: '" ++ esc_cmd ++ "'\n") ++
                     "\t@" ++ esc_cmd ++ "\n" ++
                     (if (quiet flags) then ""
                      else "\t@echo '" ++ esc_msg ++ "'\n")
          return (oName, rule, esc_oName)
    (gen_oNames, gen_rules, gen_esc_oNames)
        <- mapM mkBluesimRule gen_cNames >>= return . unzip3
    (user_oNames, user_rules, user_esc_oNames)
        <- mapM mkUserRule user_cNames >>= return . unzip3
    let all_target = "all: " ++
                     intercalate " " (gen_esc_oNames ++ user_esc_oNames)

    -- write the makefile
    pwd <- getCurrentDirectory
    let pwdpath = createEncodedFullFilePath "placeholder" pwd
        prefix = (dirName pwdpath) ++ "/"
        basename = "compile_" ++ toplevel
    fname_init <- genFileName mkMakeName (cdir flags) prefix basename
    let fname = getFullFilePath fname_init
        fcontents = intercalate "\n" $
                        [all_target] ++ [""] ++
                        gen_rules ++ [""] ++
                        user_rules
    writeFileCatch errh fname fcontents

    -- execute make
    let jobs = parallelSimLink flags
        -- show is used for quoting
        switches = ["-f", show fname, "-j", show jobs]
        targets = ["all"]
    cmd <- cmdMake flags switches targets
    execCmd errh flags cmd

    -- delete the makefile unless in debug mode
    when (not (cDebug flags)) $
         removeFileCatch errh fname

    -- return the generated object file names
    return (gen_oNames, user_oNames)

-- Escape file names for use in a Makefile
escMakeTarget :: String -> String
escMakeTarget tname =
    let doEscape '#' = True
        doEscape ',' = True
        doEscape ':' = True
        doEscape ';' = True
        doEscape '=' = True
        doEscape '%' = True
        doEscape '$' = True
        doEscape c = isSpace c
        escChar c accum_str =
            if (doEscape c)
            then "\\0" ++ showOct (ord c) accum_str
            else (c:accum_str)
    in  foldr escChar "" tname

-- Escape commands for use in a Makefile
escMakeRecipe :: String -> String
escMakeRecipe cmd =
    let -- hash in a command is OK
        escChar '$' accum_str = "\044" ++ accum_str
        escChar c accum_str = (c:accum_str)
    in  foldr escChar "" cmd

-- Construct the Make command
cmdMake :: Flags -> [String] -> [String] -> IO String
cmdMake flags sws targets = do
    make <- getEnvDef "MAKE" dfltMake
    -- MAKEFLAGS is a reserved variable that 'make' uses for recursive calls;
    -- it should not be explicitly added to calls to 'make'
    --makeflags <- getEnvDef "MAKEFLAGS" dfltMAKEFLAGS
    let debug_flags = ""
    bsc_makeflags <- getEnvDef "BSC_MAKEFLAGS" dfltBSC_MAKEFLAGS
    let cmd = unwords $ [ make, debug_flags, bsc_makeflags ] ++
                        sws ++ targets
    return cmd

-- Call the C compiler (typically to generate .o from .c)
--   sws = switches (like -c, -o)
--   fs  = filenames
cCompile :: ErrorHandle -> Flags -> [String] -> [String] -> IO ()
cCompile errh flags sws fs = do
    cmd <- cmdCCompile flags sws fs
    execCmd errh flags cmd

-- Construct the C compiler command (typically to generate .o from .c)
--   sws = switches (like -c, -o)
--   fs  = filenames
cmdCCompile :: Flags -> [String] -> [String] -> IO String
cmdCCompile flags sws fs = do
    comp <- getEnvDef "CC" dfltCCompile
    cflags <- getEnvDef "CFLAGS" dfltCFLAGS
    let debug_flags = if (cDebug flags) then "-g" else ""
    bsc_cflags <- getEnvDef "BSC_CFLAGS" dfltBSC_CFLAGS
    let cmd = unwords $ [ comp, cflags, debug_flags, bsc_cflags ] ++ sws ++ fs
    return cmd

-- Call the C++ compiler (typically to generate .o from .cxx)
--   sws = switches (like -c, -o)
--   fs  = filenames
cxxCompile :: ErrorHandle -> Flags -> [String] -> [String] -> IO ()
cxxCompile errh flags sws fs = do
    cmd <- cmdCXXCompile flags sws fs
    execCmd errh flags cmd

-- Construct the C++ compiler command (typically to generate .o from .cxx)
--   sws = switches (like -c, -o)
--   fs  = filenames
cmdCXXCompile :: Flags -> [String] -> [String] -> IO String
cmdCXXCompile flags sws fs = do
    comp <- getEnvDef "CXX" dfltCxxCompile
    cflags <- getEnvDef "CXXFLAGS" dfltCXXFLAGS
    let debug_flags = if (cDebug flags) then "-g" else ""
    bsc_cflags <- getEnvDef "BSC_CXXFLAGS" dfltBSC_CXXFLAGS
    let cmd = unwords $ [ comp, cflags, debug_flags, bsc_cflags ] ++ sws ++ fs
    return cmd

-- Execute the command constructed by one of the above functions
execCmd :: ErrorHandle -> Flags -> String -> IO ()
execCmd errh flags cmd = do
    when (verbose flags) $ putStrLnF ("exec: " ++ cmd)
    rc <- system cmd
    case rc of
        ExitSuccess   -> return ()
        ExitFailure n -> exitFailWith errh n


-- link object files into a shared library
cxxLink :: ErrorHandle -> Flags -> String -> [String] -> TimeInfo -> IO ()
cxxLink errh flags toplevel names creation_time = do
    -- Construct the Bluesim object names
    let bsimLibDir = (bluespecDir flags) ++ "/Bluesim/"
        bsim_names = [ bsimLibDir ++ "lib" ++ name ++ ".a"
                     | name <- ["bskernel", "bsprim"] ]

    -- The schedule.o object should come after libkernel.a
    -- in the link order.  We remove it from names and let
    -- cFiles put it in the correct place.
    let isSchedule n = (baseName n == ("model_" ++ toplevel ++ ".o"))
        (schedule_name, other_names) = partition isSchedule names
        compile_names =
            other_names ++
            schedule_name ++
            bsim_names
    -- link the objects into a .so file
    when (verbose flags) $ putStrLnF "linking"
    let outFile = oFile flags
        soFile = if (dirName outFile) == "."
                 then mkSoName Nothing "" (baseName outFile)
                 else mkSoName (Just (dirName outFile)) "" (baseName outFile)
        -- show is used for quoting
        libdirflags = (map (("-L"++) . show) (cLibPath flags))
        userlibs = map (("-l"++) . show) (cLibs flags)
        exportmap = let binfmt = map toLower (binFmtToString getBinFmtType)
                    in  show $ (bluespecDir flags) ++ "/Bluesim/" ++
                               "bs_" ++ binfmt ++ "_export_map.txt"
        -- this flag doesn't seem to work, so we use a separate call to "strip"
        stripflags = [] -- if (cDebug flags) then [] else ["-Wl,-x"]
        switches =
          case getBinFmtType of
            ELF   -> ["-shared", "-fPIC", "-Wl,-Bsymbolic"] ++ libdirflags ++
                     ["-Wl,--version-script=" ++ exportmap] ++ stripflags ++
                     ["-o", soFile]
            MachO -> ["-dynamiclib", "-fPIC"] ++ libdirflags ++
                     ["-exported_symbols_list", exportmap] ++ stripflags ++
                     ["-o", soFile]
        -- show is used for quoting
        opts = map show $ linkFlags flags
        files = map show compile_names ++ ["-lm"] ++ userlibs
    cxxCompile errh flags (opts ++ switches) files
    when (not (cDebug flags)) $ cleanseSharedLib errh flags soFile
    unless (quiet flags) $ putStrLnF ("Simulation shared library created: " ++ soFile)
    -- Write a script to execute bluesim.tcl with the .so file argument
    let bluesim_cmd = "$BLUESPECDIR/tcllib/bluespec/bluesim.tcl"
        (TimeInfo _ (TOD t _)) = creation_time
        time_flags = if (timeStamps flags)
                     then [ "--creation_time", show t]
                     else []
    writeFileCatch errh outFile $
                   unlines [ "#!/bin/sh"
                           , ""
                           , "BLUESPECDIR=`echo 'puts $env(BLUESPECDIR)' | bluetcl`"
                           , ""
                           , "for arg in $@"
                           , "do"
                           , "  if (test \"$arg\" = \"-h\")"
                           , "  then"
                           , "    " ++ (unwords ["exec", bluesim_cmd, "$0.so", toplevel, "--script_name", "`basename $0`", "-h"])
                           , "  fi"
                           , "done"
                           , unwords $ ["exec", bluesim_cmd, "$0.so", toplevel, "--script_name", "`basename $0`"] ++ time_flags ++ ["\"$@\""]
                           ]
    stat <- getFileStatus outFile
    let mode = fileMode stat
        mode' = foldl1 unionFileModes [mode, ownerExecuteMode, groupExecuteMode]
    setFileMode outFile mode'
    unless (quiet flags) $ putStrLnF ("Simulation executable created: " ++ outFile)

-- strip unwanted symbols from a .so file
cleanseSharedLib :: ErrorHandle -> Flags -> String -> IO ()
cleanseSharedLib errh flags soFile = do
    let switches = case getBinFmtType of
                      ELF    -> ["-x"]
                      MachO  -> ["-u", "-x"]
        cmd = unwords $ ["strip"] ++ switches ++ [soFile]
    when (verbose flags) $ putStrLnF ("exec: " ++ cmd)
    rc <- system cmd
    case rc of
        ExitSuccess   -> return ()
        ExitFailure n -> exitFailWith errh n

-- ===============
-- vLink

vLink :: ErrorHandle -> Flags ->
         String -> [VFileName] -> [String] -> [String] -> IO ()
vLink errh flags topmod_name vfilenames0 afilenames cfilenames = do
    tStart <- getNow
    let t = tStart

    -- XXX (file, package, module) names for %-substitution in dump filenames
    let dumpnames = ("","","")

    pwd <- getCurrentDirectory
    let name = createEncodedFullFilePath "placeholder" pwd
        prefix = (dirName name) ++ "/"

    -- in case the user listed the same file twice
    let afilenames_unique = nub afilenames
    let cfilenames_unique = nub cfilenames

    -- check that .c and .o files listed on the command-line exist
    missing <- missingUserFiles flags cfilenames_unique
    when (not (null missing)) $
        bsError errh
            [(cmdPosition, EMissingUserFile f ["."]) | f <- missing]
    t <- timestampStr flags "confirm C files exist" t

    -- read in the abin files (check hash and that they are Verilog files)
    start flags DFreadelab
    let read_abin_fn = readAndCheckABin errh (Just Verilog)
    user_abis <- mapM read_abin_fn afilenames_unique

    -- see if .ba files exist for the top-level of this design
    let prim_names = map sb_name primBlocks
    mhier0 <- runExceptT $
              getABIHierarchy errh
                  (verbose flags) (ifcPath flags) (Just Verilog)
                  prim_names topmod_name user_abis

    mhier <- case mhier0 of
                  Left msgs -> return (Left msgs)
                  Right (a, b, c, d, e, f, emodinfos) -> do
                      mres <- runExceptT (assertNoSchedErr emodinfos)
                      case mres of
                        Left msgs -> return (Left msgs)
                        Right modinfos -> return $
                                          Right (a, b, c, d, e, f, modinfos)

    (ffuncs, mod_abmis) <-
        case (mhier) of
          Left _ -> do
            -- this design doesn't exist as .ba file
            --traceM("Elaboration files not loaded for this design")
            -- resort to what we know from the command line

            when ((null user_abis) && (not (null cfilenames))) $
                 bsError errh [(cmdPosition, EVPIFilesWithNoABin cfilenames)]

            -- identify which are ffunc and which are mods
            let (ffunc_abis, mod_abis) =
                    let isFF (ABinForeignFunc {}) = True
                        isFF _                    = False
                    in  partition (isFF . snd) user_abis

            -- confirm that there are no duplicate imports of
            -- the same link name
            let -- pair the ffunc name with the filename, for error reporting
                ff_pairs =
                    [ (name, filename)
                    | (filename, a@(ABinForeignFunc {})) <- ffunc_abis
                    , let name = ff_name (abffi_foreign_func (ab_ffuncinfo a))
                    ]
                ff_duplicates = filter ((>1) . length . snd) (joinByFst ff_pairs)
            case (ff_duplicates) of
              [] -> return ()
              ((link_id, file_names):_) ->
                  let link_name = getIdString link_id
                  in  bsError errh
                          [(cmdPosition,
                            EMultipleABinFilesForName link_name file_names)]

            -- XXX Until we allow re-generation of Verilog files,
            -- XXX the module .ba files are unused
            when (not (null (mod_abis))) $
                bsWarning errh
                    [(cmdPosition, WExtraABinFiles (map fst mod_abis))]

            let ffuncs = [ abffi_foreign_func abfi
                           | (_, (ABinForeignFunc abfi _)) <- ffunc_abis ]
                abmis  = [ (filename, abmi)
                           | (filename, (ABinMod abmi _)) <- mod_abis ]
            return (ffuncs, abmis)

          Right (_, _, _, ffuncmap, filemap, _, mod_infos) -> do
            --traceM("Elaboration files loaded for this design")
            let user_ffuncs = M.elems ffuncmap
                findModFilename m =
                    case (M.lookup m filemap) of
                      Just filename -> filename
                      Nothing -> internalError ("findModFilename: " ++
                                                ppReadable m)
                abmis = [ (findModFilename modname, abmi)
                          | (modname, (abmi, _)) <- mod_infos ]
            return (user_ffuncs, abmis)

    t <- dump errh flags t DFreadelab dumpnames
             (map (pfpString . ff_name) ffuncs ++ map fst mod_abmis)

{-
    -- generate Verilog for the module abis
    -- XXX only if the verilog doesn't exist or is older
    -- XXX print a message about reusing a file?
    (t, gen_vfilenames) <-
        if (updCheck flags)
        then vGenMods t flags mod_abmis
        else return (t, [])
    let vfilenames = vfilenames0  ++ gen_vfilenames
-}
    let vfilenames = vfilenames0

    -- generate files for the foreign functions
    start flags DFcompileVPI
    (t, ofiles) <- vGenFFuncs errh flags t prefix cfilenames_unique ffuncs
    t <- dump errh flags t DFcompileVPI dumpnames ofiles

    -- pass the info to vSimLink: array, location of files, -I, -L, -l
    start flags DFveriloglink
    vSimLink errh flags topmod_name prefix vfilenames ofiles
    t <- dump errh flags t DFveriloglink dumpnames
             ((map vfnString vfilenames) ++ ofiles)

    -- final verbose message
    _ <- timestampStr flags "total" tStart

    return ()

-- ===============

-- build a verilog simulator by calling bsc_build_vsim_simname with appropriate
-- arguments (where simname is the relevant simulator)
-- simname is determined from (in order of decreasing priority):
--   - the command-line flag -vsim
--   - the environment variable BSC_VERILOG_SIM
--   - any auto-detected simulator
vSimLink ::  ErrorHandle -> Flags ->
             String -> String -> [VFileName] -> [String] -> IO ()
vSimLink errh flags toplevel prefix vfiles ofiles = do
    build_script <- getVerilogSim errh flags
    let bsdir = bluespecDir flags
        libdirflags = map ("-L "++) (cLibPath flags)
        userlibs = map ("-l "++) (cLibs flags)
        macrodefs = map ("-D " ++) (defines flags)
        pathlibs = map ("-y "++) (vPath flags)
        outFile = oFile flags
        veriflags = map ("-Xv "++) (vFlags flags)
        linkerflags = map ("-Xl "++) (linkFlags flags)
        verboseflag = if (verbose flags) then ["-verbose"] else []
        dpiflag = if (useDPI flags) then ["-dpi"] else []
        args = (["link"
                , outFile
                , toplevel ] ++
                verboseflag ++
                dpiflag ++
                libdirflags ++
                userlibs ++
                linkerflags ++
                macrodefs ++
                pathlibs ++
                veriflags ++
                veriFiles bsdir ++
                (map vfnString vfiles) ++
                ofiles)
        cmd = unwords (build_script : args)
    when (verbose flags) $ putStrLnF ("exec: " ++ cmd)
    rc <- system cmd
    case rc of
        ExitSuccess -> unless (quiet flags) $ putStrLnF ("Verilog binary file created: " ++ outFile)
        ExitFailure n -> exitFailWith errh n

veriFiles :: String -> [String]
veriFiles path =
        map ((path ++ "/Verilog/") ++) ["main.v"]

-- return the path to a Verilog simulator or die with an error
getVerilogSim :: ErrorHandle -> Flags -> IO String
getVerilogSim errh flags = do
    vsim_env <- getEnvDef "BSC_VERILOG_SIM" ""
    let vsim_name_flags_or_env = maybe vsim_env id (vsim flags)
    vsim_name <- if vsim_name_flags_or_env == ""
                 then do avail_vsims <- findAllAvailableSims flags
                         if (null avail_vsims)
                          then return ""
                          else return $ head avail_vsims
                 else return vsim_name_flags_or_env
    when (vsim_name == "") $ give_error flags vsim_name
    let vsim_path | any (== '/') vsim_name = vsim_name
                  | otherwise = (bluespecDir flags ++ "/exec/bsc_build_vsim_" ++
                                 vsim_name)
    valid_path <- doesFileExist vsim_path
    when (not valid_path) $ give_error flags vsim_name
    isExec <- fileAccess vsim_path False False True
    when (not isExec) $ give_error flags vsim_name
    return vsim_path
  where give_error flags vsim_name =
            do avail_vsims <- findAllAvailableSims flags
               let no_sims_err = (cmdPosition, EUnknownVerilogSim vsim_name (sort avail_vsims) True)
               bsError errh [no_sims_err]

-- find all available simulators
findAllAvailableSims :: Flags -> IO [String]
findAllAvailableSims flags =
    do let script_dir = bluespecDir flags ++ "/exec"
       all_files <- getDirectoryContents script_dir
       let sim_scripts = filter ("bsc_build_vsim_" `isPrefixOf`) all_files
       sim_script_results <- mapM (checkSimScript script_dir) sim_scripts
       let successful_sim_scripts = map snd (filter fst sim_script_results)
       return (nub successful_sim_scripts)
    `CE.catch` return_empty_list
    where
    return_empty_list :: CE.SomeException -> IO [String]
    return_empty_list e = return []

-- XXX: replace this implementation with one using readProcessWithExitCode
-- XXX: once everyone is using GHC >= 6.10.
checkSimScript :: String -> String -> IO (Bool,String)
checkSimScript dir script =
    do (hin, hout, _, pid) <- runInteractiveProcess (dir ++ "/" ++ script) ["detect"] Nothing Nothing
       outMVar <- newEmptyMVar
       out <- hGetContents hout
       _ <- forkIO $ CE.evaluate (length out) >> putMVar outMVar ()
       hClose hin
       takeMVar outMVar
       hClose hout
       status <- waitForProcess pid
       let canonical_sim_name = takeWhile (not.isSpace) out
       return ((status == ExitSuccess),canonical_sim_name)

-- ===============

vGenFFuncs :: ErrorHandle -> Flags -> TimeInfo -> String ->
              [String] -> [ForeignFunction] ->
              IO (TimeInfo, [String])
vGenFFuncs errh flags t prefix cfilenames_unique [] = return (t,[])
vGenFFuncs errh flags t prefix cfilenames_unique ffuncs = do
      (t, vpiarray_filenames) <-
        if (useDPI flags) then return (t, [])
        else do
          -- generate the vpi_startup_array file
          blurb <- mkGenFileHeader flags
          filenames <- genVPIRegistrationArray errh flags prefix blurb ffuncs
          t <- timestampStr flags "generate VPI registration array" t
          return (t, filenames)

      -- compile user-supplied C files
      let (cfiles1, ofiles1) = partition (\f -> hasDotSuf cSuffix f   ||
                                                hasDotSuf cxxSuffix f ||
                                                hasDotSuf cppSuffix f ||
                                                hasDotSuf ccSuffix f
                                         )
                                         cfilenames_unique
      ofiles2 <- mapM (compileUserCFile errh flags True) cfiles1
      t <- timestampStr flags "compile user-provided C files" t

      (t, ofiles3) <-
        if (useDPI flags) then return (t, [])
        else do
          -- compile all necessary vpi wrapper files

          -- first, find the VPI wrapper files in the vsearch path
          let findVPIWrapperFile ffunc = do
                let ffunc_name = getIdString (ff_name ffunc)
                    vpiwrapper_filename = mkVPICName Nothing "" ffunc_name
                mfile <- readFilePath errh noPosition False vpiwrapper_filename (vPath flags)
                case mfile of
                  Nothing -> bsError errh [(noPosition, EMissingVPIWrapperFile vpiwrapper_filename False)]
                  Just (_, filename) -> return filename
          vpiwrapper_filenames <- mapM findVPIWrapperFile ffuncs

          -- collect the directories of the VPI wrapper files
          -- to use as a search path for header files when compiling
          -- the VPI registration array file
          let vpidirs = S.toList (S.fromList (map takeDirectory vpiwrapper_filenames))

          -- include the vpi registration array file
          wrapper_files <- mapM (compileVPICFile errh flags []) vpiwrapper_filenames
          array_files <- mapM (compileVPICFile errh flags vpidirs) vpiarray_filenames
          let files = wrapper_files ++ array_files
          t <- timestampStr flags "compile VPI wrapper files" t
          return (t, files)

      return (t, ofiles1 ++ ofiles2 ++ ofiles3)

-- ===============

{-
vGenMods :: TimeInfo -> Flags -> [(String, ABinModInfo)] ->
            IO (TimeInfo, [VFileName])
vGenMods t0 flags abmis = do
    -- function to generate an individual module
    let genV (t, vfilenames_so_far) (filename, abmi@(ABinModInfo {})) = do
            let modId = apkg_name (abmi_apkg abmi)
                modstr = getIdString (unQualId modId)
            -- XXX should the file and package name be set?
            let dumpnames = ("", "", modstr)
            -- verbose message
            when (verbose flags) $ putStrLnF ("*****")
            when (showCodeGen flags || verbose flags) $
                putStrLnF ("Verilog generation for " ++ modstr ++ " starts")
            -- prepare directory info
            pwd <- getCurrentDirectory
            let filename' = createEncodedFullFilePath filename pwd
                prefix = dirName filename' ++ "/"
            -- call into the regular flow
            blurb <- mkGenFileHeader flags
            let apkg = abmi_apkg abmi
                pps = abmi_pps abmi
                methodConflict = abmi_method_dump abmi
                methodConflictBlurb
                  | methodConf flags =
                      ["Method conflict info:"]
                      ++ lines (pretty 78 78
                                   (vcat (dumpMethodInfo flags methodConflict)))
                  | otherwise = []
                pathinfo = abmi_pathinfo abmi
                aschedinfo = abmi_aschedinfo abmi
            (t, _, _) <-
                genModuleVerilog pps flags dumpnames t prefix modstr
                    blurb methodConflictBlurb pathinfo aschedinfo apkg
            -- result
            return (t, vfilenames ++ vfilenames_so_far)

    -- generate the Verilog files
    foldM genV (t0,[]) abmis
-}

-- ===============

missingUserFiles :: Flags -> [String] -> IO [String]
missingUserFiles flags cSrcFiles = filterM cantFind cSrcFiles
  where cantFind f = do x <- readFileMaybe f
                        return $ isNothing x

-- ===============

compileCDefToIDef :: ErrorHandle -> Flags -> DumpNames -> SymTab ->
                     IPackage a -> CDefn -> IO (IDef a, Bool)
compileCDefToIDef errh flags dumpnames symt ipkg def =
 do
    let pkgid = ipkg_name ipkg
    let cpkg0 = CPackage pkgid (Left []) [] [] [def] []
    t <- getNow

    start flags DFctxreduce
    cpkg_ctx <- cCtxReduceIO errh flags symt cpkg0
    t <- dump errh flags t DFctxreduce dumpnames cpkg_ctx

    start flags DFtypecheck
    (cpkg_chk, tcErrors) <- cTypeCheck errh flags symt cpkg_ctx
    t <- dump errh flags t DFtypecheck dumpnames cpkg_chk

    start flags DFsimplified
    let cpkg_simp = simplify flags cpkg_chk
        def' = case cpkg_simp of
                 (CPackage _ _ _ _ [d] _) -> d
                 _ -> internalError "compileCDefToIDef: unexpected number of defs"
    t <- dump errh flags t DFsimplified dumpnames cpkg_simp

    start flags DFinternal
    let idef = iConvDef errh flags symt ipkg def'
    t <- dump errh flags t DFinternal dumpnames idef

    return (idef, not tcErrors)

-- ===============

iPCheck :: Flags -> SymTab -> IPackage a -> String -> IO ()
iPCheck flags symt ipkg desc = --rnf ipkg $
        if doICheck flags && not (tCheckIPackage flags symt ipkg)
            then internalError (
                "internal typecheck failed (iPCheck after " ++
                desc ++ ")")
            else
                if (verbose flags)
                    then putStrLnF "types OK"
                    else return ()

iMCheck :: Flags -> SymTab -> IModule a -> String -> IO ()
iMCheck flags symt imod desc =
    if doICheck flags && not (tCheckIModule flags symt imod)
        then internalError (
                "internal typecheck failed (iMCheck after " ++
                desc ++ ")")
        else
            if (verbose flags)
                then putStrLnF "types OK"
                else return ()

aCheck :: Flags -> APackage -> String -> IO ()
aCheck flags amod desc =
    if doICheck flags && not (aMCheck amod)
        then internalError (
                "internal typecheck failed (aCheck after " ++
                desc ++ ")")
        else
            if (verbose flags)
                then putStrLnF "types OK"
                else return ()

asCheck :: Flags -> ASPackage -> String -> IO ()
asCheck flags asmod desc
    | doICheck flags && not (aSMCheck asmod) =
        internalError ("internal typecheck failed (asCheck after "
                       ++ desc ++ ")")
    | verbose flags = putStrLnF "types OK"
    | otherwise = return ()

asMethCheck :: Flags -> ASPackage -> String -> IO ()
asMethCheck flags asmod desc =
    if (doICheck flags && not (aSMethCheck asmod))
    then internalError ("internal method check failed (asMethCheck after "
                        ++ desc ++ ")")
    else return ()  --putStrLnF "method check OK"

asSignalCheck :: Flags -> ASPackage -> String -> IO ()
asSignalCheck flags asmod desc =
    let undefined_names = aSignalCheck asmod
    in  if (doICheck flags) && (length undefined_names > 0)
        then internalError
                 ("internal signal check failed (asSignalCheck after "
                  ++ desc ++ "): " ++ ppReadable undefined_names)
        else if (verbose flags)
             then putStrLnF "signals OK"
             else return ()

-- ===============

-- builds a map from link name to ForeignFunction
buildForeignFunctionMap :: ErrorHandle -> [(String,ABin)] -> IO ForeignFuncMap
buildForeignFunctionMap errh abis = build abis M.empty
  where build [] ff_map = return ff_map
        build ((name, (ABinMod {})):_) _ =
          bsError errh [(noPosition, EWrongABinTypeExpectedForeignFunc name "")]
        build ((name, abi):abis) ff_map =
          do let ff = abffi_foreign_func (ab_ffuncinfo abi)
                 ff_map' = M.insert (getIdString (ff_name ff)) ff ff_map
             build abis ff_map'
