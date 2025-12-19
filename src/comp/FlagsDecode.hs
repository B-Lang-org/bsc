{-# LANGUAGE CPP #-}
module FlagsDecode(
             exitWithUsage,
             exitWithHelp, exitWithHelpHidden,

             Decoded(..),
             decodeArgs,

             updateFlags,

             defaultFlags,
             decodeFlags,
             adjustFinalFlags,

             showFlags, showFlagsRaw,
             showFlagsLst, showFlagsAllLst,
             getFlagValueString,
        ) where

import Data.List(nub, sort, intercalate, intersperse, partition)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Control.Exception as CE
import System.IO.Error(ioeGetErrorString)
import System.IO.Unsafe(unsafePerformIO)
import System.IO(hPutStr, hPutStrLn, stderr, stdout)
import System.FilePath(normalise, dropTrailingPathSeparator)
import System.Directory(getDirectoryContents, canonicalizePath)
import Control.Monad(when)
import Data.Char(isAlpha, isDigit, toUpper)

import Data.List.Split(splitWhen)
import Version(bluespec)
import Backend
import FileNameUtil(hasDotSuf, takeSuf,
                    bscSrcSuffix, bsvSrcSuffix,
                    cSuffix, cxxSuffix, cppSuffix, ccSuffix,
                    objSuffix, arSuffix,
                    verSuffix, verSuffix2, verSuffix3, verSuffix4, verSuffix5,
                    vhdlSuffix, vhdlSuffix2,
                    abinSuffix)

-- For error messages
import Error(internalError, EMsg, WMsg, ErrMsg(..),
             ErrorHandle, bsError, bsWarning, exitFail, exitOK)
import Position(Position, cmdPosition)
import VFileName
import Verilog(vIsValidIdent)
import Flags

catchIO :: IO a -> (IOError -> IO a) -> IO a
catchIO = CE.catch

-- -------------------------
-- File name testing

-- These could be FileUtil.hs
-- and used in place of calls to hasDotSuffix in other places
-- (like bsc.hs and Depend.hs)

isSrcFile :: String -> Bool
isSrcFile s = isBlueSrcFile s
           || isABinFile s
           || isHDLSrcFile s
           || isCSrcFile s

isBlueSrcFile :: String -> Bool
isBlueSrcFile s = hasDotSuf bscSrcSuffix s
               || hasDotSuf bsvSrcSuffix s

isABinFile :: String -> Bool
isABinFile s = hasDotSuf abinSuffix s

isHDLSrcFile :: String -> Bool
isHDLSrcFile s = isVerSrcFile s
              || isVhdlSrcFile s

isVerSrcFile :: String -> Bool
isVerSrcFile s = hasDotSuf verSuffix s
              || hasDotSuf verSuffix2 s
              || hasDotSuf verSuffix3 s
              || hasDotSuf verSuffix4 s
              || hasDotSuf verSuffix5 s

isVhdlSrcFile :: String -> Bool
isVhdlSrcFile s = hasDotSuf vhdlSuffix s
               || hasDotSuf vhdlSuffix2 s

isCSrcFile :: String -> Bool
isCSrcFile s = hasDotSuf cSuffix s
            || hasDotSuf cxxSuffix s
            || hasDotSuf cppSuffix s
            || hasDotSuf ccSuffix s
            || hasDotSuf objSuffix s
            || hasDotSuf arSuffix s

-- -------------------------
-- Usage message for BSC

-- Usage:
--   bsc -help                                to get help
--   bsc [flags] file.bsv                     to partially compile a Bluespec file
--   bsc [flags] -verilog -g mod file.bsv     to compile a module to Verilog
--   bsc [flags] -verilog -g mod -u file.bsv  to recursively compile modules to Verilog
--   bsc [flags] -verilog -e topmodule        to link Verilog into a simulation model
--   bsc [flags] -sim -g mod file.bsv         to compile to a Bluesim object
--   bsc [flags] -sim -g mod -u file.bsv      to recursively compile to Bluesim objects
--   bsc [flags] -sim -e topmodule            to link objects into a Bluesim binary
--   bsc [flags] -systemc -e topmodule        to link objects into a SystemC model

usage :: String -> String
usage prog =
  let mkUsage (cl,desc) =
          let lcol = "  " ++ prog ++ " " ++ cl
          in (take 41 (lcol ++ (repeat ' '))) ++ "  " ++ desc ++ "\n"
  in "Usage:\n" ++ concatMap mkUsage examples
  where examples =
            [ ("-help","to get help")
            , ("[flags] file." ++ bsvSrcSuffix, "to partially compile a Bluespec file")
            , ("[flags] -verilog -g mod file." ++ bsvSrcSuffix, "to compile a module to Verilog")
            , ("[flags] -verilog -g mod -u file." ++ bsvSrcSuffix, "to recursively compile modules to Verilog")
            , ("[flags] -verilog -e topmodule", "to link Verilog into a simulation model")
            , ("[flags] -sim -g mod file." ++ bsvSrcSuffix, "to compile to a Bluesim object")
            , ("[flags] -sim -g mod -u file." ++ bsvSrcSuffix, "to recursively compile to Bluesim objects")
            , ("[flags] -sim -e topmodule", "to link objects into a Bluesim binary")
            , ("[flags] -systemc -e topmodule", "to link objects into a SystemC model")
            ]

exitWithUsage :: ErrorHandle -> String -> IO ()
exitWithUsage errh prog =
    hPutStr stderr (usage prog) >> exitFail errh

-- -------------------------
-- Decoded use case for BSC based on the flags

data Decoded = DHelp Flags       -- Display the public help message
             | DHelpHidden Flags -- Display the full help message
             | DUsage            -- Display the usage message
             | DError [EMsg]     -- Report a list of errors
               -- No source is given, but print-flag or verbose
               -- flags were specified, so this is not an error and
               -- no usage message or error is required
             | DNoSrc Flags
               -- Bluespec source file
             | DBlueSrc Flags String
               -- entry, Verilog objects to be linked, and any ABin and C files
             | DVerLink Flags String [VFileName] [String] [String]
               -- entry, ABin files and C files to be generated and linked
             | DSimLink Flags String [String] [String]

decodeArgs :: String -> [String] -> String -> ([WMsg], Decoded)
decodeArgs prog args cdir =
    let (sets, warnings0, errors0, flags0, anames) =
            decodeFlags args ([], [], [], defaultFlags cdir)
        -- do some final adjustments
        (warnings, errors, flags) = adjustFinalFlags warnings0 errors0 flags0
    in if "help-hidden" `elem` sets
       then (warnings, DHelpHidden flags)
       else if "h" `elem` sets || "help" `elem` sets
            then (warnings, DHelp flags)
            else if (null errors)
                 then if (null anames)
                      then if ((printFlags flags) ||
                               (printFlagsHidden flags) ||
                               (printFlagsRaw flags))
                           then (warnings, DNoSrc flags)
                           else -- We allow the file names to be omitted if the
                                -- backend and entry point are both specified
                                case (entry flags) of
                                  (Just e) | (backend flags == Just Verilog)
                                    -> (warnings, DVerLink flags e [] [] [])
                                  (Just e) | (backend flags == Just Bluesim)
                                    -> (warnings, DSimLink flags e [] [])
                                  _ -> if (verbose flags)
                                       then -- handle -v without compilation
                                            (warnings, DNoSrc flags)
                                       else (warnings, DUsage)
                      else case (partition isBlueSrcFile anames) of
                             ([name], []) -> (warnings, checkBSrcFlags flags name)
                             ([name], names) ->
                                 -- This is the case of a Bluespec source name accompanied
                                 -- by more things which are not Bluespec source names.
                                 -- If any of those are flags, we issue an error that flags
                                 -- must go before source files.
                                 -- We used to attempt to support the "-e" flag along with
                                 -- "-g" via the "-u" flag (which would do the recompile),
                                 -- but it has been removed.  The feature could be added
                                 -- back, if it is properly implemented and regressed.
                                 -- Instead, we error that there is unrecognized text on
                                 -- the command-line.  (We could report this for the
                                 -- entire list "names", but that could be too much.
                                 -- We just report the first encountered unknown text.)
                                 let known_ext_names = filter isSrcFile names
                                 in  (warnings, checkNamesForFlag names $
                                              if (not (null known_ext_names))
                                              then -- XXX should we check that the user wasn't
                                                   -- XXX trying to link, but accidentally
                                                   -- XXX typed .bs or .bsv?
                                                  DError
                                                  [(cmdPosition,
                                                    ELinkFilesWithSrc name known_ext_names)]
                                              else DError [(cmdPosition,
                                                            EUnrecognizedCmdLineText (head names))])
                             -- Backwards support for optional -verilog.
                             ([], names) | all isHDLSrcFile names ->
                                 -- generation flag not supported during linking
                                 if (not (null (genName flags)))
                                 then (warnings, DError [(cmdPosition,
                                                          EGenNamesForLinking (genName flags))])
                                 else -- Verilog need not be specified, but another backend better not be
                                      case (backend flags) of
                                        Just be | be /= Verilog
                                          -> (warnings, DError [(cmdPosition,
                                                                 EWrongBackend "Verilog" "Bluesim")])
                                        _ -> case (entry flags) of
                                                  Nothing -> (warnings, DError [(cmdPosition, ENoEntryPoint)])
                                                  Just top ->
                                                      -- set the Verilog flag and go back into
                                                      -- the standard flow (so that any other
                                                      -- checks of the link flags are performed)
                                                      let flags' = flags { backend = Just Verilog }
                                                      in  (warnings, checkLinkFlags flags' names)
                             -- Catch-all for linking
                             ([], names) -> (warnings, checkLinkFlags flags names)
                             -- Multiple src files
                             -- XXX Do we want a different error if the user was linking
                             -- XXX and accidentally included multiple BSV files?
                             (bnames, _) -> (warnings, DError [(cmdPosition, EMultipleSrcFiles)])
                 else (warnings, DError errors)


-- check that the flags are OK for compiling Bluespec src file
checkBSrcFlags :: Flags -> String -> Decoded
checkBSrcFlags flags filename =
    -- if generate is requested, require a backend
    if not (null (genName flags)) && (backend flags == Nothing)
    then DError [(cmdPosition, ENoBackendCodeGen (genName flags))]
    else
    -- error if entry point is given
    case (entry flags) of
      Just e -> DError [(cmdPosition, EEntryForCodeGen e)]
      Nothing ->
        -- The -remove-dollar flag only applies to the Verilog backend
        if (removeVerilogDollar flags && (backend flags /= Just Verilog))
        then DError [(cmdPosition, EDollarNoVerilog)]
        else
        -- If the user hasn't allowed Bluesim/Verilog to diverge,
        -- then don't-cares can only be 2-state values
        if (not (optUndet flags) &&
            ( (unSpecTo flags == "X") || (unSpecTo flags == "Z") ))
        then DError [(cmdPosition, ENoOptUndetNoXZ (unSpecTo flags))]
        else
        -- Everything is OK for source compilation
        DBlueSrc flags filename


-- check that the flags are OK for linking generated files
-- filenames is guaranteed to be nonEmpty (and not contain .bs/.bsv files)
checkLinkFlags :: Flags -> [String] -> Decoded
checkLinkFlags flags names =
    let (anames, names') = partition isABinFile names
        (hdlnames, names'') = partition isHDLSrcFile names'
        (cnames, bad_names) = partition isCSrcFile names''
        errBadName name =
            if not (elem '.' name)
            then (cmdPosition, ENoSrcExt name)
            else (cmdPosition, EUnknownSrcExt (takeSuf name))
        bad_name_errs = map errBadName bad_names
    in  -- check for flags
        checkNamesForFlag bad_names $
        -- report bad file extensions
        if not (null bad_names)
        then DError bad_name_errs
        else
        -- generation flag not supported during linking
        if not (null (genName flags))
        then DError [(cmdPosition, EGenNamesForLinking (genName flags))]
        else
        if (removeVerilogDollar flags)
        then DError [(cmdPosition, EDollarLink)]
        else
        -- Verilog backend
        if (backend flags == Just Verilog)
        then -- An entry point must be specified
             case (entry flags) of
                 Nothing -> DError [(cmdPosition, ENoEntryPoint)]
                 Just top ->
                     -- Everything is OK for Verilog linking
                     DVerLink flags top (map VFileName hdlnames)
                                anames cnames
        else
        -- Bluesim backend
        if (backend flags == Just Bluesim)
        then -- Only 2-state values are allowed for don't-cares
             if ( (unSpecTo flags == "X") || (unSpecTo flags == "Z") )
             then DError [(cmdPosition, EBluesimNoXZ (unSpecTo flags))]
             else
             -- Verilog files cannot be provided
             if not (null hdlnames)
             then DError [(cmdPosition, EVerilogFilesWithSimBackend hdlnames)]
             else
             -- An entry point must be specified
             case (entry flags) of
                 Nothing -> DError [(cmdPosition, ENoEntryPoint)]
                 Just top ->
                     -- Everything is OK for Bluesim linking
                     DSimLink flags top anames cnames
        -- error if no backend chosen
        else DError [(cmdPosition, ENoBackendLinking)]


-- and, if so, error that flags must go before source files
checkNamesForFlag :: [String] -> Decoded -> Decoded
checkNamesForFlag bad_names dflt_result =
    let
        -- function to find the first non-match in "names"
        findFirst f (x:xs) = if (f x) then x else findFirst f xs
        findFirst f [] = internalError "decodeArgs.findFirst"
    in
        if (any isFlag bad_names)
        then DError [(cmdPosition,
                      EFlagAfterSrc (findFirst isFlag bad_names))]
        else dflt_result

-- -------------------------

-- This is used to parse the "option" pragma, which allows specifying
-- command-line options specific to one module (changing optimizations
-- or other generation behaviors).
-- XXX If there's a way to record the positions of the strings, that would
-- XXX be better to report, but at least we report the module's position
-- XXX in the code, rather than giving "cmdPosition" as the location.
updateFlags :: ErrorHandle -> Position -> [String] -> Flags -> IO Flags
updateFlags errh mod_pos args0 flags = do
        let args = concatMap words args0
        let (_, warnings, errs, flags', unknown) = decodeFlags args ([], [], [], flags)
        let updPos (_, m) = (mod_pos, m)
        when ((not . null) warnings) $ bsWarning errh (map updPos warnings)
        case (errs, unknown) of
          ([], []) -> return flags'
          ([], s:_) -> bsError errh [(mod_pos, EUnknownFlag s)]
          (msgs, _) -> bsError errh (map updPos msgs)

-- -------------------------
-- Help Message

exitWithHelp :: ErrorHandle -> String -> [String] -> String -> IO ()
exitWithHelp errh prog args cd =
    hPutStrLn stdout (helpMessage Visible prog args cd) >>
    exitOK errh

exitWithHelpHidden :: ErrorHandle -> String -> [String] -> String -> IO ()
exitWithHelpHidden errh prog args cd =
    hPutStrLn stdout (helpMessage Hidden prog args cd) >>
    exitOK errh

helpMessage :: HideExpose -> String -> [String] -> String -> String
helpMessage showHidden prog args cd =
    let flags = defaultFlags cd
    in
        unlines ([
        usage prog,
        "Compiler flags:"]
        ++
        sort (describeFlags showHidden)
        ++
        ["",
        "Most flags may be preceded by a `no-' to reverse the effect.",
        "Flags later on the command line override earlier ones.",
         "Path strings such as the import path may contain the character"
        ,"`%' representing the current " ++ bluespec ++ " directory, as well as"
        ,"`+' representing the current value of the path.",
        "Lists of error or warning tags may take the values `ALL' and `NONE'.",
        "",
        "Default flags:",
        bluespec ++ " directory: " ++ bluespecDir flags,
        "import path: " ++ unPath (ifcPath flags)
        ] ++
        if (Hidden == showHidden) then
                ["",
                 "Dump/kill after various passes:"] ++
                 -- describe the dump flags
                 (map (("-d" ++) . drop 2 . show)
                        ([minBound .. maxBound ] :: [DumpFlag])) ++
                ["",
                 "Dump to a file with -dpass=filename;" ++
                   "filename may contain the following digraphs:",
                 "  %f    file being compiled (without path or extension)",
                 "  %p    package name",
                 "  %m    module name" ++
                   " (empty for passes not involved in code generation)",
                 "  %%    the % character",
                 "% followed by any other character yields that character",
                 "You may substitute -KILL for -d" ++
                   " to stop compilation after the named pass",
                 "",
                 "The following trace flags are also available:",
                 unwords (map ("-"++) (sort traceflags))
                ]
         else
                []
        )

describeFlags :: HideExpose -> [String]
describeFlags showHidden =
    let getDataFromInfo :: String -> FlagType -> String
        getDataFromInfo f (Arg a1 _ _)     = f ++ " " ++ a1
        getDataFromInfo f (Arg2 a1 a2 _ _) = f ++ " " ++ a1 ++ " " ++ a2
        getDataFromInfo f (PassThrough a _ _) = f ++ " " ++ a
        getDataFromInfo f _                = f
    in
        sort [ "-" ++ flag ++ replicate (22 - length flag) ' ' ++ " " ++ desc |
               (f, (ft, desc, isHidden)) <- externalFlags,
-- Deprecated flags are never shown
               (showHidden == isHidden) || (Visible == isHidden),
               let flag = getDataFromInfo f ft ]

-- -------------------------
-- Trace flags
--
-- These are flags which are allowed on the command-line but are ignored
-- by the flag decoding.  BSC stages can query their existence by looking
-- for them in the "progArgs".  This allows for quick-and-dirty adding of
-- trace flags, without the overhead of updating the Flags structure, etc.

traceflags :: [String]
traceflags = [
          "debug-eval-free-vars",
          "no-use-layout",
          "trace-aopt",
          "trace-apaths",
          "trace-bs-mcd",
          "trace-cfmap",
          "trace-cfmaps",
          "trace-conAp",
          "trace-ctxreduce",
          "trace-debug",
          "trace-eq-witnesses",
          "trace-eval-steps",
          "trace-eval-types",
          "trace-eval-if",
          "trace-eval-nf",
          "trace-eval-trans",
          "trace-expand-batch-subst",
          "trace-full",
          "trace-fun-expand",
          "trace-genbin",
          "trace-heap",
          "trace-heap-alloc",
          "trace-heap-size",
          "trace-inst-tree",
          "trace-instance-overlap",
          "trace-kind-inference",
          "trace-lift",
          "trace-mergesched",
          "trace-mutatormap",
          "trace-ncsets",
          "trace-no-urgency-edge",
          "trace-port-types",
          "trace-profile",
          "trace-pcmap",
          "trace-pcmaps",
          "trace-ralloc",
          "trace-uugraph",
          "trace-scgraph",
          "trace-seqgraph",
          "trace-sched-steps",
          "trace-schedinfo",
          "trace-scmap",
          "trace-scmaps",
          "trace-skip-trim",
          "trace-simplify",
          "trace-smt-conv",
          "trace-smt-test",
          "trace-state-loc",
          "trace-syn",
          "trace-tcvar",
          "trace-tc-reducepred",
          "trace-tc-satisfy",
          "trace-type",
          "trace-type-expl",
          "trace-type-extsubst",
          "trace-usemap",
          "trace-disjoint-tests",
          "trace-a-definitions",
          "trace-clock",
          "trace-def-cache",
          "hack-disable-urgency-warnings",
          "hack-gate-clock-inputs",
          "hack-gate-default-clock",
          "hack-strict-inst-tree",
          "outlaw-sv-kws-as-classic-ids",
          "show-qualifiers",
          "show-raw-id",
          "warn-meth-arg-mismatch"
         ]

-- -------------------------
-- Default flag values

defaultFlags :: String -> Flags
defaultFlags bluespecdir = Flags {
        aggImpConds = False,
        allowIncoherentMatches = False,
        backend = Nothing,
        bdir = Nothing,
        biasMethodScheduling = False,
        bluespecDir = bluespecdir,
        cIncPath = [],
        cLibPath = [],
        cLibs = [],
        cDebug = False,
        cFlags = [],
        cxxFlags = [],
        cppFlags = [],
        linkFlags = [],
        cdir = Nothing,
        cpp = False,
        defines = [],
        demoteErrors = SomeMsgs [],
        disableAssertions = False,
        passThroughAssertions = False,
        doICheck = True,
        dumpAll = False,
        dumps = [],
        enablePoisonPills = False,
        entry = Nothing,
        expandATSlimit = 20,
        expandIf = False,
        fdir = Nothing,
        finalcleanup = 1,
        genABin = False,
        genABinVerilog = False,
        genName = [],
        genSysC = False,
        -- The ifcPath value will be produced from the raw value,
        -- by replacing the default-path token with the appropriate value
        -- once all the flag values are known, and adding bdir to the front,
        -- in adjustFinalFlags.
        ifcPathRaw = [ defaultPathToken ],
        -- ifcPath = [],
        -- XXX this value is for properly constructing the help message
        ifcPath = [ "."
                  , bluespecdir ++ "/Libraries"
                  ],
        infoDir = Nothing,
        inlineBool = True,
        inlineISyntax = True,
        inlineSimple = False,
        keepAddSize = False,
        keepFires = False,
        keepInlined = False,
        kill = Nothing,
        ifLift = True,
        maxTIStackDepth = 1000,
        methodBVI = False,
        methodConf = False,
        methodConditions = False,
        neatNames = False,
        oFile = "a.out",
        optAggInline = True,
        optATS = True,
        optAndOr = True,
        optBitConst = False,
        optBool = False,
        optFinalPass = True,
        optIfMux = False,
        optIfMuxSize = 256,
        optJoinDefs = True,
        optMux = True,
        optMuxExpand = False,
        optMuxConst = True,
        optSched = True,
        optUndet = False,
        crossInfo = False,
        parallelSimLink = 1,
        printFlags = False,
        printFlagsHidden = False,
        printFlagsRaw = False,
        preprocessOnly = False,
        promoteWarnings = SomeMsgs [],
        readableMux = True,
        redStepsWarnInterval = 100000,
        redStepsMaxIntervals = 10,
        relaxMethodEarliness = True,
        removeEmptyRules = True,
        removeFalseRules = True,
        removeInoutConnect = True,
        removePrimModules = True,
        removeCReg = True,
        removeReg = True,
        removeRWire = True,
        removeCross = True,
        removeStarvedRules = False,
        removeUnusedMods = False,
        removeVerilogDollar = False,
        resetName = "RST_N",
        resource = RFoff,
        rstGate = False,
        ruleNameCheck = True,
        satBackend = SAT_Yices,
        schedConds = False,
        schedDOT = False,
        schedQueries = [],
        showCSyntax = False,
        showCodeGen = False,
        showElabProgress = False,
        showIESyntax = False,
        showISyntax = False,
        showModuleUse = False,
        showRangeConflict = False,
        showSchedule = False,
        showStats = False,
        showUpds = True,
        simplifyCSyntax = False,
        strictMethodSched = True,
        suppressWarnings = SomeMsgs [],
        synthesize = False,
        systemVerilogTasks = False,
        tclShowHidden = False,
        testAssert = False,
        timeStamps = True,
        showVersion = True,
        unsafeAlwaysRdy = False,
        unSpecTo = "A",
        updCheck = False,
        useDPI = False,
        useNegate = True,
        usePrelude = True,
        useProvisoSAT = True,
        stdlibNames = False,
        v95 = False,
        vFlags = [],
        vdir = Nothing,
        -- The vPath value will be produced from the raw value,
        -- by replacing the default-path token with the appropriate value
        -- once the full ifcPath is known, and adding vdir to the front,
        -- in adjustFinalFlags.
        vPathRaw = [ defaultPathToken ],
        vPath = [],
        vpp = True,
        vsim = Nothing,
        verbosity = Normal,
        verilogDeclareAllFirst = True,
        verilogFilter = [],
        warnActionShadowing = True,
        warnMethodUrgency = True,
        warnUndetPred = False
        }

-- Default path value replaced in adjustFinalFlags
defaultPathToken :: String
defaultPathToken = "$DEFAULT_PATH"

-- -------------------------
-- decodeFlags
--
-- Function to parse a list of command-line arguments as flags

-- Returns a list of error messages, the result of processing flags,
-- and a list of non-flags (the trace flags) which were set.
decodeFlags :: [String] -> ([String],[WMsg], [EMsg], Flags) -> ([String],[WMsg], [EMsg], Flags, [String])
decodeFlags (('-':'-':s):ss) (sets, warnings, bad, flags) | (length s > 1) && (head s /= '-') =
    -- accept --option as a synonym for -option (for long options)
    decodeFlags (('-':s):ss) (sets, warnings, bad, flags)
decodeFlags (s@('-':'d':d):ss) (sets, warnings, bad, flags) | (isDumpName d) =
    case reads ("DF" ++ d) of
    [(df, "")]
      -> decodeFlags ss (sets, warnings, bad, flags { dumps = (df, Nothing) : dumps flags })
    [(df, '=':file)]
      -> decodeFlags ss (sets, warnings, bad, flags { dumps = (df, Just file) : dumps flags })
    _ -> internalError ("decodeFlags: isDumpName: " ++ ('d':d))
decodeFlags (s@('-':'K':'I':'L':'L':d):ss) (sets, warnings, bad, flags) =
    case (reads ("DF" ++ d), kill flags) of
    ([(df, "")], Nothing)
      -> decodeFlags ss (sets,warnings, bad, flags { kill = (Just (df, Nothing)) })
    ([(df, '=':package_or_mod_name)], Nothing)
      -> decodeFlags ss (sets,warnings, bad, flags { kill = (Just (df, Just package_or_mod_name)) })
    ([(df, "")], Just prev)
      -> let eDupKill = (cmdPosition, EDupKillFlag ("-KILL" ++ d) ("-KILL" ++ drop 2 (show prev)))
         in  decodeFlags ss (sets,warnings, eDupKill : bad, flags)
    _ -> decodeFlags ss (sets,warnings, badflag ("KILL"++d) bad, flags)
decodeFlags (('-':s):ss) (sets,warnings, bad, flags) =
    if take 3 s == "no-" then
      let drop3s = drop 3 s in
      case lookup drop3s flagsTable of
        Nothing ->  decodeFlags ss (sets, warnings, badflag s bad, flags)
        Just flagtype ->
          case flagtype of
-- this will report "Deprecated flag -foo" even if "-no-foo" is specified.
-- We do this to prevent the helpful message from being confusing.
            Toggle doflag _ -> decodeFlags ss
                 (drop3s:sets, (getDeprecation drop3s warnings), bad, doflag flags False)
            _ -> let eNonToggle = (cmdPosition, ENotToggleFlag ('-':drop3s))
                 in  decodeFlags ss (sets,warnings, eNonToggle : bad, flags)
    else
      case lookup s flagsTable of
        Nothing -> decodeFlags ss (sets, warnings, badflag s bad, flags)
        Just flagtype -> let
            perhaps_warn :: [WMsg]
            perhaps_warn = getDeprecation s warnings
-- We give a DEPRECATED warning even if the flag is otherwise used INcorrectly.
-- Of course we give a DEPRECATED warning if the flag is used correctly.
          in
          case flagtype of
            Toggle doflag _ -> decodeFlags ss (s:sets, perhaps_warn, bad, doflag flags True)
            NoArg dofunc _ ->
              if (null ss) || (isFlag (head ss)) || (isSrcFile (head ss)) then
                case (dofunc flags) of
                  Left flags' -> decodeFlags ss (s:sets, perhaps_warn, bad, flags')
                  Right emsg -> decodeFlags ss (sets, perhaps_warn, emsg:bad, flags)
              else
                  let eHasArg = (cmdPosition, ENoArgFlag ('-':s))
                  in  decodeFlags ss (sets,perhaps_warn, eHasArg : bad, flags)
            Arg _ dofunc _ ->
              let eExpectsArg = (cmdPosition, EOneArgFlag ('-':s))
              in  case ss of
                    (s2:ss') ->
                      if (isFlag s2) then
                        decodeFlags ss (sets, perhaps_warn, eExpectsArg : bad, flags)
                      else
                        case (dofunc flags s2) of
                            Left flags' -> decodeFlags ss' (s:sets, perhaps_warn, bad, flags')
                            Right emsg -> decodeFlags ss' (sets, perhaps_warn, emsg:bad, flags)
                    [] -> decodeFlags ss (sets, perhaps_warn, eExpectsArg : bad, flags)

            Arg2 _ _ dofunc _ ->
              let eExpectsArg2 = (cmdPosition, ETwoArgFlag ('-':s))
              in  case ss of
                    (s2:s3:ss') ->
                      if (isFlag s2) || (isFlag s3) then
                        decodeFlags ss (sets, perhaps_warn, eExpectsArg2 : bad, flags)
                      else
                        case (dofunc flags s2 s3) of
                            Left flags' -> decodeFlags ss' (s:sets, perhaps_warn, bad, flags')
                            Right emsg -> decodeFlags ss' (sets, perhaps_warn, emsg:bad, flags)
                    -- for the cases when there's only 1 or 0 elements left
                    _ -> decodeFlags ss (sets, perhaps_warn, eExpectsArg2 : bad, flags)
            PassThrough _ dofunc _ ->
              let eExpectsArg = (cmdPosition, EOneArgFlag ('-':s))
              in  case ss of
                    (s2:ss') ->
                        case (dofunc flags s2) of
                          Left flags' -> decodeFlags ss' (s:sets, perhaps_warn, bad, flags')
                          Right emsg -> decodeFlags ss' (sets, perhaps_warn, emsg:bad, flags)
                    [] -> decodeFlags ss (sets, perhaps_warn, eExpectsArg : bad, flags)

            Alias f2 -> decodeFlags (("-"++f2):ss) (sets, perhaps_warn, bad, flags)
            Resource rf -> decodeFlags ss (s:sets, perhaps_warn, bad, flags { resource = rf })
decodeFlags ss (sets, warnings, bad, flags) = (sets, warnings, bad, flags, ss)


isFlag :: String -> Bool
isFlag ('-':_) = True
isFlag _ = False

isDumpName :: String -> Bool
isDumpName s =
    case ((reads ("DF" ++ s)) :: [(DumpFlag, String)]) of
      [(df, "")] -> True
      [(df, '=':_)] -> True
      _ -> False

-- If the argument is not in the nonflags (the trace flags),
-- then it is added to the list of bad strings, otherwise the
-- list of bad strings is returned unchanged.
badflag ::String -> [EMsg] -> [EMsg]
badflag s bad
    | s `elem` traceflags = bad
    | otherwise = ((cmdPosition, EUnknownFlag ('-':s)) : bad)

getDeprecation :: String -> [WMsg] -> [WMsg]
-- second argument gives all the error messages so far
getDeprecation s bad = case (lookup s externalFlags) of
         Just (_, _, (Deprecated message))
              -> (cmdPosition, (WDeprecatedFlag s message)) : bad
         Just (_, _, _) -> bad
         _ -> internalError ("inconsistency in flag decoding")

-- -------------------------
-- adjustFinalFlags
--
-- Function to be used after "decodeFlags", to check the well-formedness
-- of the flags as a whole. (Decoding can only check flags as it goes.)

canonDir :: String -> Either String String
canonDir d =
    let handler ioe = return $ Left $ ioeGetErrorString ioe
        ioFn = do -- on some systems, canonicalise path doesn't error
                  -- so we explicitly check
                  _ <- getDirectoryContents d
                  -- Some versions of "canonicalizePath" don't drop the trailing path separator
                  canon_d <- canonicalizePath d >>= return . dropTrailingPathSeparator
                  return $ Right canon_d
    in  unsafePerformIO $ catchIO ioFn handler

filterPath :: [String] -> [String] -> [String]
filterPath rem_dirs0 path =
    let normFn d = either (const (normalise d)) id $ canonDir d
        rem_dirs = map normFn rem_dirs0
        keepDir d = (normFn d) `notElem` rem_dirs
    in  filter keepDir path

checkPath :: String -> String -> [String] -> Maybe String ->
             ([String], [WMsg], [EMsg])
checkPath path_flag_str dir_flag_str path mdir =
    let
        foldFn :: (M.Map String String, S.Set String, M.Map String (S.Set String), [String]) ->
                  String ->
                  (M.Map String String, S.Set String, M.Map String (S.Set String), [String])
        foldFn (fail_map, seen_set, dup_map, nub_path) dir
            | (dir == defaultPathToken) =
            -- skip default tokens
            (fail_map, seen_set, dup_map, (dir:nub_path))
        foldFn (fail_map, seen_set, dup_map, nub_path) dir =
            case (canonDir dir) of
              Left err_str ->
                  let -- at least normalise as much as possible,
                      -- so that we don't report duplicate warnings
                      dir' = normalise dir
                      fail_map' = M.insert dir' err_str fail_map
                  in (fail_map', seen_set, dup_map, nub_path)
              Right canon_dir ->
                  if (canon_dir `S.member` seen_set)
                  then let dup_map' = M.insertWith (S.union)
                                          canon_dir (S.singleton dir) dup_map
                       in  (fail_map, seen_set, dup_map', nub_path)
                  else let seen_set' = S.insert canon_dir seen_set
                       in  (fail_map, seen_set', dup_map, (dir:nub_path))

        (access_fail_map, path_seen_set, path_dups_map, rev_nub_path) =
            foldl foldFn (M.empty, S.empty, M.empty, []) path

        -- we use a map, to remove duplicate warnings
        access_warnings =
            let mkWarn (d, str) =
                    (cmdPosition, WOpenPathDirFailure path_flag_str d str)
            in  map mkWarn (M.toList access_fail_map)

        path_dups =
            -- use the canonical name
            M.keys path_dups_map
        (access_errors, dir_is_dup) =
            case (mdir) of
              Nothing -> ([], False)
              Just dir ->
                  case (canonDir dir) of
                    Left err_str ->
                        let emsg = (cmdPosition,
                                    EOpenOutputDirFailure dir_flag_str dir err_str)
                            -- attempt to still determine if it's a duplicate
                            dir' = normalise dir
                        in  ([emsg], dir' `S.member` path_seen_set)
                    Right canon_dir ->
                        ([], canon_dir `S.member` path_seen_set)
        dup_warnings =
            if (not (null path_dups))
            then [(cmdPosition, WDuplicatePathDirs path_flag_str dir_flag_str
                                    dir_is_dup path_dups)]
            else []
    in
       (reverse rev_nub_path, access_warnings ++ dup_warnings, access_errors)

-- combine the warnings from two passes
-- XXX this seems more readable than returning the raw warning data and
-- XXX constructing the warnings at the end
combinePathWarnings :: [WMsg] -> [WMsg]
combinePathWarnings warns0 =
    let
        -- assume cmdPosition
        foldFn (_, WDuplicatePathDirs s1 s2 b ds) (ws, dup_map) =
           let combFn (b1, ds1) (b2, ds2) = (b1 || b2, S.union ds1 ds2)
           in  (ws, M.insertWith combFn (s1, s2) (b, S.fromList ds) dup_map)
        foldFn w (ws, dup_map) = (w:ws, dup_map)

        mkDupWarn ((s1,s2), (b, ds)) =
           (cmdPosition, WDuplicatePathDirs s1 s2 b (S.toList ds))

        (other_warns, dup_map) = foldr foldFn ([], M.empty) warns0
        dup_warns = map mkDupWarn (M.toList dup_map)
    in
        other_warns ++ dup_warns

-- make some adjustments to flags, once all values are visible
adjustFinalFlags :: [WMsg] -> [EMsg] -> Flags -> ([WMsg], [EMsg], Flags)
adjustFinalFlags warns0 errs0 flags0 =
    let
        bspecdir = (bluespecDir flags0)

        checkDir :: String -> Maybe String -> ([WMsg], [EMsg])
        checkDir dir_flag_str mdir =
            case mdir of
              Nothing -> ([], [])
              Just dir ->
                  case (canonDir dir) of
                    Right _ -> ([], [])
                    Left err_str ->
                        let emsg = (cmdPosition,
                                    EOpenOutputDirFailure dir_flag_str dir err_str)
                        in  ([], [emsg])

        -- ==========
        -- -p / -bdir checks

        -- add bdir to the head of the import path.
        -- replace the default path with the Prelude and Libraries locations

        -- XXX make sure this is in sync with the default value (ifcPath)
        -- XXX displayed in the help message
        def_bpath = [ "."
                    , bspecdir ++ "/Libraries"
                    ]
        bdir_path = case (bdir flags0) of
                      Just dir -> [dir]
                      Nothing  -> []

        bpathraw = ifcPathRaw flags0
        -- warn about duplicates in the raw path
        (bpathraw_nub, b_warns1, b_errs1) =
            checkPath "p" "bdir" bpathraw Nothing

        -- construct the visible path
        bpath = bdir_path ++
                replacePathToken defaultPathToken bpathraw_nub def_bpath

        -- warn about duplicates introduced from the default (?)
        (bpath_nub, b_warns2, b_errs2) =
            checkPath "p" "bdir" bpath (bdir flags0)

        -- combine the errors and warnings
        b_warns = combinePathWarnings (b_warns1 ++ b_warns2)
        b_errs = b_errs1 ++ b_errs2

        -- update flags with the new path, removing duplicates
        flags1 = flags0 { ifcPathRaw = bpathraw_nub, ifcPath = bpath_nub }

        -- ==========
        -- -vsearch / -vdir checks

        -- add vdir to the head of the Verilog search path
        -- otherwise, add "."
        -- replace the default vsearch path token with
        -- the Verilog and Libraries locations if the token is
        -- still in the vPath.
        -- if vdir is not used, include every place in ifcPath, too.
        -- XXX The ifcPath should be included with "." at the head
        -- XXX because it's also conceptually the default "vdir".
        -- XXX Don't use "."! Use ifcPath plus the directory of all
        -- XXX source files provided on the command line!

        prim_path  = [bspecdir ++ "/Verilog"]
        azure_path = [bspecdir ++ "/Libraries"]
        (vdir_path,ifc_path) =
            case (vdir flags1) of
              Just dir -> ([dir],[])
              Nothing ->
                  -- use "." as the vdir
                  -- return the ifc path without "." (to avoid duplicates)
                  -- and remove the azure path (to place at the end?)
                  (["."], filterPath (".":azure_path) (ifcPath flags1))
        def_vpath = ifc_path ++ azure_path ++ prim_path

        vpathraw = vPathRaw flags1
        -- warn about duplicates in the raw path
        (vpathraw_nub, v_warns1, v_errs1) =
            checkPath "vsearch" "vdir" vpathraw Nothing

        -- construct the visible path
        vpath = vdir_path ++
                replacePathToken defaultPathToken vpathraw_nub def_vpath

        -- warn about duplicates introduced from the default (?)
        (vpath_nub, v_warns2, v_errs2) =
            checkPath "vsearch" "vdir" vpath (vdir flags1)

        -- combine the errors and warnings
        (v_warns, v_errs) =
            let ws = combinePathWarnings (v_warns1 ++ v_warns2)
                es = v_errs1 ++ v_errs2
            in  -- only warn, not error, if the vdir flag won't be used
                if (backend flags1 == Just Verilog)
                then (ws, es)
                else (ws ++ es, [])

        -- update flags with the new path, removing duplicates
        flags2 = flags1 { vPathRaw = vpathraw_nub, vPath = vpath_nub }

        -- ==========
        -- -simdir

        (s_warns, s_errs) =
            let (ws, es) = checkDir "simdir" (cdir flags2)
            in  -- only warn, not error, if the simdir flag won't be used
                if (backend flags2 == Just Bluesim)
                then (ws, es)
                else (ws ++ es, [])

        -- ==========
        -- -info-dir

        (i_warns, i_errs) = checkDir "info-dir" (infoDir flags2)

        -- ==========
        -- -fdir

        (f_warns, f_errs) = checkDir "fdir" (fdir flags2)

        -- ==========

        -- XXX Check the -i path?

        -- ==========
    in
        (warns0 ++ b_warns ++ v_warns ++ s_warns ++ i_warns ++ f_warns,
         errs0 ++ b_errs ++ v_errs ++ s_errs ++ i_errs ++ f_errs,
         flags2)

-- -------------------------
-- External Flag Info
--
-- The user-visible flag information, and how that maps to the internal flags

type FlagInfo = (FlagType, FlagDescr, HideExpose )

-- The first argument is a function that executes the flag,
-- The second argument is a function which displays the current value.
data FlagType =
      Toggle (Flags -> Bool -> Flags)   (Maybe (Flags -> (Bool,Bool)))
        -- sets a boolean internal flag; can be used with "-no"
        -- (Bool,Bool) result is (value,always_show)
    | NoArg  (Flags -> Either Flags EMsg)  (Maybe (Flags -> Bool))
        -- non-toggle flags with no argument
    | Arg  String  (Flags -> String -> Either Flags EMsg) (Maybe ArgReturnType)
        -- flags with one argument
    | Arg2  String  String  (Flags -> String -> String -> Either Flags EMsg) (Maybe Arg2ReturnType)
        -- flags with two arguments
    | PassThrough String  (Flags -> String -> Either Flags EMsg) (Maybe ArgReturnType)
        -- flags with one argument which can be another flag
    | Alias  String
        -- alias for another flag
    | Resource  ResourceFlag

type FlagDescr = String

-- the String argument to Deprecated gives some useful message of
-- what to do instead
data HideExpose = Hidden | Visible | Deprecated String
                deriving (Eq)

data ArgReturnType = FRTString (Flags -> String)
                   | FRTMaybeString (Flags -> Maybe String)
                   | FRTListString (Flags -> [String])

newtype Arg2ReturnType = FRTListPairString (Flags -> [(String,String)])

flagsTable :: [(String, FlagType)]
flagsTable = [(s,ft) | (s,(ft,_,_)) <- externalFlags]

showIfTrue :: (Flags -> Bool) -> Maybe (Flags -> (Bool,Bool))
showIfTrue fn = Just (\flags -> (fn flags,False))

showIfEq :: (Eq a) => (Flags -> a) -> a -> Maybe (Flags -> Bool)
showIfEq fn v = Just (\flags -> fn flags == v)

showPath :: (Flags -> [String]) -> Maybe ArgReturnType
showPath path_fn =
    let argFn flags = let p = unPath (path_fn flags)
                      in  if (p == "+") then Nothing else Just p
    in  Just (FRTMaybeString argFn)

showMsgList :: (Flags -> MsgListFlag) -> Maybe ArgReturnType
showMsgList fn =
    let argFn flags = case (fn flags) of
                        AllMsgs -> Just "ALL"
                        SomeMsgs [] -> Nothing
                        SomeMsgs msgs -> Just (unMsgList msgs)
    in  Just (FRTMaybeString argFn)

externalFlags :: [(String, FlagInfo)]
externalFlags = [
        ("aggressive-conditions",
         (Toggle (\f x -> f {aggImpConds=x}) (showIfTrue aggImpConds),
          "construct implicit conditions aggressively", Visible)),

        ("bdir",
         (Arg "dir" (\f s -> Left (f {bdir = Just s}))
                                        (Just (FRTMaybeString bdir)),
          "output directory for .bo and .ba files", Visible)),

        ("bias-method-scheduling",
         (Toggle (\f x -> f {biasMethodScheduling=x}) (showIfTrue biasMethodScheduling),
          "schedule methods before rules when possible", Hidden)),

        ("check-assert",
         (Toggle (\f x -> f {testAssert=x}) (showIfTrue testAssert),
          "test assertions with the Assert library", Visible)),

        ("continue-after-errors",
         (Toggle (\f x -> f {enablePoisonPills=x}) (showIfTrue enablePoisonPills),
          "aggressively continue compilation after an error has been detected", Visible)),

        ("cpp",
         (Toggle (\f x -> f {cpp=x}) (showIfTrue cpp),
          "preprocess the source with the C preprocessor", Visible)),

        ("cross-info",
         (Toggle (\f x -> f {crossInfo=x}) (showIfTrue crossInfo),
          "apply heuristics for preserving source code positions", Hidden)),

        ("D",
         (Arg "macro" (\f s -> Left (f {defines = defines f ++ [s]})) (Just (FRTListString defines)),
          "define a macro for the BSV or Verilog preprocessor", Visible)),

        ("demote-errors",
         (Arg "list"
              (\f s -> let updFn f s = f {demoteErrors = s}
                       in  addToMsgList f "-demote-errors" s demoteErrors updFn)
              (showMsgList demoteErrors),
          "treat a list of errors as warnings (`:' sep list of tags)", Visible)),

        ("dall",
         (NoArg (\f -> Left $ f {dumpAll=True}) (Just dumpAll),
          "dump after all passes", Hidden)),

        ("bug-icheck",
         (Toggle (\f x -> f {doICheck=x}) (showIfTrue doICheck),
          "type check internal representation", Hidden)),

        ("bug-debug",
         (Toggle (\f x -> f {cDebug=x}) (showIfTrue cDebug),
          "enable C debugging / profiling", Hidden)),

        ("ignore-assertions",
         (NoArg (\f -> Left $ f {disableAssertions=True}) (Just disableAssertions),
          "disable all assertions", Hidden)),

        ("passthrough-assertions",
         (NoArg (\f -> Left $ f {passThroughAssertions=True}) (Just passThroughAssertions),
          "pass SV assertions through to RTL", Hidden)),

        ("e",
         (Arg "module" (\f s -> Left (f {entry = Just s})) (Just (FRTMaybeString entry)),
          "top-level module for simulation", Visible)),

        ("elab",
         (Toggle (\f x -> f {genABin=x}) (showIfTrue genABin),
          "generate a .ba file after elaboration and scheduling", Visible)),

        ("elab-verilog",
         (Toggle (\f x -> f {genABinVerilog=x}) (showIfTrue genABinVerilog),
          "include generated Verilog in .ba files", Hidden)),

        ("expand-ATS-limit",
         (Arg "n"
          (\f s -> case (mread s) of
                     Nothing  -> Right (cmdPosition, EIntegerArgFlag "-expand-ATS-limit")
                     Just arg -> Left (f {expandATSlimit = arg}))
          (Just (FRTString (show . expandATSlimit))),
          "maximum depth of lookups when expanding ATS definitions", Hidden)),

        ("expand-if",
         (Toggle (\f x -> f {expandIf=x, aggImpConds=x}) (showIfTrue expandIf),
          "expand \"if\" in actions", Deprecated "Use \"-split-if\" instead.")),

        ("split-if",
         (Toggle (\f x -> f {expandIf=x, aggImpConds=x}) (showIfTrue expandIf),
          "split \"if\" in actions", Visible)),

        ("fdir",
         (Arg "dir" (\f s -> Left (f {fdir = Just s}))
                    (Just (FRTMaybeString fdir)),
          "working directory for relative file paths during elaboration",
          Visible)),

        ("final-cleanup",
         (Arg "level"
             (\f s -> case (mread s) of
                          Nothing -> Right (cmdPosition, EIntegerArgFlag "-final-cleanup")
                          Just arg -> Left (f {finalcleanup = arg}))
             (Just (FRTString (show .  finalcleanup))),
          "do another cleanup before Verilog generations", Hidden)),

        ("g",
         (Arg "module" (\f s -> Left (f {genName = genName f ++ [s]})) (Just (FRTListString genName)),
          "generate code for `module' (requires -sim or -verilog)", Visible)),

        ("help",
         (NoArg Left Nothing,
          "generate help message", Visible)),

        ("help-hidden",
         (NoArg Left Nothing,
          "generate help message (including hidden flags)", Hidden)),

        ("i",
         (Arg "dir" (\f s -> Left (f {bluespecDir = s})) (Just (FRTString bluespecDir)),
          "override $BLUESPECDIR", Visible)),

        ("I",
         (Arg "path" (\f s -> Left (f {cIncPath = cIncPath f ++ [s]})) (Just (FRTListString cIncPath)),
          "include path for compiling foreign C/C++ source", Visible)),

        ("info-dir",
         (Arg "dir" (\f s -> Left (f {infoDir = Just s})) (Just (FRTMaybeString infoDir)),
          "output directory for informational files", Visible)),

        ("incoherent-instance-matches",
         (Toggle (\f x -> f {allowIncoherentMatches=x}) (showIfTrue allowIncoherentMatches),
          "allow incoherent typeclass instance matches by default", Hidden)),

        ("inline-bool",
         (Toggle (\f x -> f {inlineBool=x}) (showIfTrue inlineBool),
          "inline Boolean operations", Hidden)),

        ("inline-isyntax",
         (Toggle (\f x -> f {inlineISyntax=x}) (showIfTrue inlineISyntax),
          "do internal inlining", Hidden)),

        ("inline-simple",
         (Toggle (\f x -> f {inlineSimple=x}) (showIfTrue inlineSimple),
          "inline simple ATS definitions", Hidden)),

        ("keep-add-size",
         (Toggle (\f x -> f {keepAddSize=x}) (showIfTrue keepAddSize),
          "do not zero extend arguments to add/sub", Hidden)),

        ("keep-fires",
         (Toggle (\f x -> f {keepFires=x}) (showIfTrue keepFires),
          "preserve CAN_FIRE and WILL_FIRE signals", Visible)),

        ("keep-inlined-boundaries",
         (Toggle (\f x -> f {keepInlined=x}) (showIfTrue keepInlined),
          "preserve inlined register and wire boundaries", Visible)),

        ("keep-method-conds",
         (Toggle (\f x -> f {methodConditions=x}) (showIfTrue methodConditions),
          "preserve as signals predicates on method calls inside rules", Hidden)),

        ("L",
         (Arg "path" (\f s -> Left (f {cLibPath = cLibPath f ++ [s]})) (Just (FRTListString cLibPath)),
          "library path for linking foreign C/C++ objects", Visible)),

        ("l",
         (Arg "library" (\f s -> Left (f {cLibs = cLibs f ++ [s]})) (Just (FRTListString cLibs)),
          "library to use when linking foreign C/C++ objects", Visible)),

        ("lift",
         (Toggle (\f x -> f {ifLift=x}) (showIfTrue ifLift),
          "lift method calls in \"if\" actions", Visible)),

        ("max-tcheck-stack-depth",
         (Arg "depth"
             (\f s -> case (mread s) of
                          Nothing -> Right (cmdPosition, EIntegerArgFlag "-max-tcheck-stack-depth")
                          Just arg -> Left (f {maxTIStackDepth = arg}))
             (Just (FRTString (show . maxTIStackDepth))),
          "maximum stack depth for fundep and SAT analysis in typecheck", Hidden)),

        ("o",
         (Arg "name" (\f s -> Left (f {oFile = s})) (Just (FRTString oFile)),
          "name of generated executable", Visible)),

        ("O",
         (Toggle (\f x -> f {optBool=x}) (showIfTrue optBool),
          "turn on various optimizations", Hidden)),

        ("opt-AndOr",
         (Toggle (\f x -> f {optAndOr=x}) (showIfTrue optAndOr),
          "An aggressive optimization of And Or expressions", Hidden)),

        ("opt-ATS",
         (Toggle (\f x -> f {optATS=x}) (showIfTrue optATS),
          "simplify ATS", Hidden)),

        ("opt-aggressive-inline",
         (Toggle (\f x -> f {optAggInline=x}) (showIfTrue optAggInline),
          "aggressive inline of verilog assignments", Hidden)),

        ("opt-bit-const",
         (Toggle (\f x -> f {optBitConst=x}) (showIfTrue optBitConst),
          "simplify bit operations with constants", Hidden)),

        ("opt-bool",
         (Toggle (\f x -> f {optBool=x}) (showIfTrue optBool),
          "use BDD simplifier on booleans (slow but good)", Hidden)),

        ("opt-final-pass",
         (Toggle (\f x -> f {optFinalPass=x}) (showIfTrue optFinalPass),
          "final pass optimization to unnest expression (et al)", Hidden)),

        ("opt-if-mux",
         (Toggle (\f x -> f {optIfMux=x}) (showIfTrue optIfMux),
          "turn nested \"if\" into one mux", Hidden)),

        ("opt-if-mux-size",
          (Arg "n"
               (\f s -> case (mread s) of
                          Nothing  -> Right (cmdPosition, EIntegerArgFlag "-opt-if-mux-size")
                          Just arg -> Left (f {optIfMuxSize = arg}))
               (Just (FRTString (show . optIfMuxSize))),
          "maximum mux size to inline when doing -opt-if-mux", Hidden)),

        ("opt-join-defs",
         (Toggle (\f x -> f {optJoinDefs=x}) (showIfTrue optJoinDefs),
          "join identical definitions", Hidden)),

        ("opt-mux",
         (Toggle (\f x -> f {optMux=x}) (showIfTrue optMux),
          "simplify muxes", Hidden)),

        ("opt-mux-expand",
         (Toggle (\f x -> f {optMuxExpand=x}) (showIfTrue optMuxExpand),
          "simplify muxes by blasting constants", Hidden)),

        ("opt-mux-const",
         (Toggle (\f x -> f {optMuxConst=x}) (showIfTrue optMuxConst),
          "simplify constants in muxes aggressively", Hidden)),

        ("opt-sched",
         (Toggle (\f x -> f {optSched=x}) (showIfTrue optSched),
          "simplify scheduler expressions", Hidden)),

        ("opt-undetermined-vals",
         (Toggle (\f x -> f {optUndet=x}) (showIfTrue optUndet),
          "aggressive optimization of undetermined values", Visible)),

        ("p",
         (Arg "path" (\f s -> Left (f {ifcPathRaw = splitPath' f s ifcPathRaw})) (showPath ifcPathRaw),
          "directory path (`:' sep.) for source and intermediate files", Visible)),

        ("parallel-sim-link",
         (Arg "jobs"
              (\f s -> case (mread s) of
                         Just j | (j > 0) -> Left (f {parallelSimLink=j})
                         _ -> Right (cmdPosition, EPositiveIntegerArgFlag "-parallel-sim-link"))
              (Just (FRTString (show . parallelSimLink))),
          "specify the # of simultaneous jobs when linking Bluesim", Visible)),

        ("print-flags",
         (Toggle (\f x -> f {printFlags=x}) (showIfTrue printFlags),
          "print flag values after command-line parsing", Visible)),

        ("print-flags-hidden",
         (Toggle (\f x -> f {printFlagsHidden=x}) (showIfTrue printFlagsHidden),
          "print all flag values after command-line parsing", Hidden)),

        ("print-flags-raw",
         (Toggle (\f x -> f {printFlagsRaw=x}) (showIfTrue printFlagsRaw),
          "print raw flag values after command-line parsing", Hidden)),

        ("promote-warnings",
         (Arg "list"
              (\f s -> let updFn f s = f {promoteWarnings = s}
                       in  addToMsgList f "-promote-warnings" s promoteWarnings updFn)
              (showMsgList promoteWarnings),
          "treat a list of warnings as errors (`:' sep list of tags)", Visible)),

        ("E",
         (NoArg (\f -> Left $ f {preprocessOnly=True}) (Nothing),
          "run just the preprocessor, dumping result to stdout", Visible)),

        ("readable-mux",
         (Toggle (\f x -> f {readableMux=x}) (showIfTrue readableMux),
          "use readable muxes in generated RTL", Hidden)),

        ("remove-empty-rules",
         (Toggle (\f x -> f {removeEmptyRules=x}) (showIfTrue removeEmptyRules),
          "remove rules whose bodies have no actions", Visible)),

        ("remove-false-rules",
         (Toggle (\f x -> f {removeFalseRules=x}) (showIfTrue removeFalseRules),
          "remove rules whose condition is provably false", Visible)),

        ("remove-starved-rules",
         (Toggle (\f x -> f {removeStarvedRules=x}) (showIfTrue removeStarvedRules),
          "remove rules that are never fired by the generated schedule", Visible)),

        ("remove-prim-modules",
         (Toggle (\f x -> f {removePrimModules=x}) (showIfTrue removePrimModules),
          "remove primitives that are local modules", Hidden)),

        ("inline-inout-connect",
         (Toggle (\f x -> f {removeInoutConnect=x}) (showIfTrue removeInoutConnect),
          "flatten InoutConnect module uses in the generated Verilog", Hidden)),

        ("inline-creg",
         (Toggle (\f x -> f {removeCReg=x}) (showIfTrue removeCReg),
          "flatten CReg* module uses in the generated Verilog", Hidden)),

        ("inline-reg",
         (Toggle (\f x -> f {removeReg=x}) (showIfTrue removeReg),
          "flatten Reg* module uses in the generated Verilog", Hidden)),

        ("inline-rwire",
         (Toggle (\f x -> f {removeRWire=x}) (showIfTrue removeRWire),
          "flatten RWire module uses in the generated Verilog", Hidden)),

        ("inline-cross",
         (Toggle (\f x -> f {removeCross=x}) (showIfTrue removeCross),
          "flatten NullCrossing module uses in the generated Verilog", Hidden)),

        ("relax-method-earliness",
         (Toggle (\f x -> f {relaxMethodEarliness=x}) (showIfTrue relaxMethodEarliness),
          "Allows rules to be scheduled before method calls", Hidden)),

        ("remove-unused-modules",
         (Toggle (\f x -> f {removeUnusedMods=x}) (showIfTrue removeUnusedMods),
          "remove unconnected modules from the Verilog", Visible)),

        ("resource-off",
         (Resource RFoff,
          "fail on insufficient resources", Visible)),

        ("resource-simple",
         (Resource RFsimple,
          "reschedule on insufficient resources", Visible)),

        ("remove-dollar",
         (Toggle (\f x -> f { removeVerilogDollar = x }) (showIfTrue removeVerilogDollar),
          "remove dollar signs from Verilog identifiers", Visible)),

        ("reset-prefix",
         (Arg "name" (\f s -> -- check for legal verilog name
                       if vIsValidIdent s
                          -- update both the flag and set a defined for the verilog/main.v
                       then Left f { resetName = s,
                                     defines = defines f ++ ["BSV_RESET_NAME=" ++ s] }
                       else Right (cmdPosition, EPortNotValidIdent s))
          (Just (FRTString resetName)),
          "reset name or prefix for generated modules",
          Visible)),

        ("rst-gate",
         (Toggle (\f x -> f {rstGate=x}) (showIfTrue rstGate),
          "gate rule fire signals with reset", Hidden)),

        ("rule-name-check",
         (Toggle (\f x -> f {ruleNameCheck=x}) (showIfTrue ruleNameCheck),
          "check that rule names are unique (when disabled unique numbers are assigned)", Hidden)),


        ("system-verilog-tasks",
         (Toggle (\f x -> f {systemVerilogTasks=x}) (showIfTrue systemVerilogTasks),
         "preserve SystemVerilog tasks (e.g. $error) in output code", Hidden)),

        ("sched-conditions",
         (Toggle (\f x -> f {schedConds=x}) (showIfTrue schedConds),
          "include method conditions when computing rule conflicts", Hidden)),

        ("sched-dot",
         (Toggle (\f x -> f {schedDOT=x}) (showIfTrue schedDOT),
          "generate .dot files with schedule information", Visible)),

        ("show-compiles",
         (Toggle (\f x -> f {showUpds=x}) (showIfTrue showUpds),
          "show recompilations", Visible)),

        ("show-csyntax",
         (Toggle (\f x -> f {showCSyntax = x}) (showIfTrue showCSyntax),
          "show CSyntax", Hidden)),

        ("show-elab-progress",
         (Toggle (\f x -> f {showElabProgress = x}) (showIfTrue showElabProgress),
          "display trace as modules, rules, methods are elaborated", Visible)),

        ("show-expanded-isyntax",
         (Toggle (\f x -> f {showIESyntax = x}) (showIfTrue showIESyntax),
          "show expanded ISyntax", Hidden)),

        ("show-isyntax",
         (Toggle (\f x -> f {showISyntax = x}) (showIfTrue showISyntax),
          "show ISyntax", Hidden)),

        ("show-method-bvi",
         (Toggle (\f x -> f {methodBVI=x}) (showIfTrue methodBVI),
          "show BVI format method schedule information in the generated code", Visible)),

        ("show-method-conf",
         (Toggle (\f x -> f {methodConf=x}) (showIfTrue methodConf),
          "show method conflict information in the generated code", Visible)),

        ("show-module-use",
         (Toggle (\f x -> f {showModuleUse=x}) (showIfTrue showModuleUse),
          "output instantiated Verilog modules names", Visible)),

        ("show-range-conflict",
         (Toggle (\f x -> f {showRangeConflict = x}) (showIfTrue showSchedule),
          "show predicates when reporting a parallel-composability error", Visible)),

        ("show-rule-rel",
         (Arg2 "r1" "r2" (\f s1 s2 -> Left (f {schedQueries = (s1,s2) : schedQueries f}))
             (Just (FRTListPairString schedQueries)),
          "display scheduling information about rules r1 and r2", Visible)),

        ("show-rule-rel-all",
         (NoArg (\f -> Left $ f { schedQueries = [("*","*")] }) (Nothing),
          "display scheduling information about all rules", Hidden)),

        ("show-schedule",
         (Toggle (\f x -> f {showSchedule = x}) (showIfTrue showSchedule),
          "show generated schedule", Visible)),

        ("show-stats",
         (Toggle (\f x -> f {showStats=x}) (showIfTrue showStats),
          "show package statistics", Visible)),

        ("show-timestamps",
         (Toggle (\f x -> f {timeStamps=x}) (showIfTrue timeStamps),
          "include timestamps in generated files", Visible)),

        ("show-version",
         (Toggle (\f x -> f {showVersion=x}) (showIfTrue showVersion),
          "include compiler version in generated files", Visible)),

        ("sim",
         let setFn f = case setBackend f Bluesim of
                         Left f' -> Left f' { genABin = True }
                         Right e -> Right e
             getFn f = backend f == Just Bluesim
         in  (NoArg setFn (Just getFn),
              "compile BSV generating Bluesim object", Visible)),

        ("simdir",
         (Arg "dir" (\f s -> Left (f {cdir = Just s})) (Just (FRTMaybeString cdir)),
          "output directory for Bluesim intermediate files", Visible)),

        ("sat-stp",
         (NoArg (\f -> Left $ f { satBackend = SAT_STP })
                (showIfEq satBackend SAT_STP),
          "use STP SMT for disjoint testing and SAT", Visible)),

        ("sat-yices",
         (NoArg (\f -> Left $ f { satBackend = SAT_Yices })
                (showIfEq satBackend SAT_Yices),
          "use Yices SMT for disjoint testing and SAT", Visible)),

        ("steps",
         (Arg "n"
             (\f s -> case (mread s) of
                          Nothing -> Right (cmdPosition, EIntegerArgFlag "-steps")
                          Just arg -> Left (f {redStepsWarnInterval = arg,
                                               redStepsMaxIntervals = 1 }))
             (Just (FRTString (show . redSteps))),
          "terminate elaboration after this many function unfolding steps", Visible)),

        ("steps-warn-interval",
         (Arg "n"
             (\f s -> case (mread s) of
                          Nothing -> Right (cmdPosition, EIntegerArgFlag "-steps-warn-interval")
                          Just arg -> Left (f {redStepsWarnInterval = arg}))
             (Just (FRTString (show . redStepsWarnInterval))),
          "issue a warning each time this many unfolding steps are executed", Visible)),

        ("steps-max-intervals",
         (Arg "n"
             (\f s -> case (mread s) of
                          Nothing -> Right (cmdPosition, EIntegerArgFlag "-steps-max-intervals")
                          Just arg -> Left (f {redStepsMaxIntervals = arg}))
             (Just (FRTString (show . redStepsMaxIntervals))),
          "terminate elaboration after this number of unfolding messages", Visible)),

        ("simplify-csyntax",
         (Toggle (\f x -> f {simplifyCSyntax=x}) (showIfTrue simplifyCSyntax),
          "simplify Concrete Syntax", Hidden)),

        ("strict-method-scheduling",
         (Toggle (\f x -> f {strictMethodSched=x}) (showIfTrue strictMethodSched),
          "compute method relationships allowing for conditional execution", Hidden)),

        ("suppress-warnings",
         (Arg "list"
              (\f s -> let updFn f s = f {suppressWarnings = s}
                       in  addToMsgList f "-suppress-warnings" s suppressWarnings updFn)
              (showMsgList suppressWarnings),
          "ignore a list of warnings (`:' sep list of tags)", Visible)),

        ("show-all-warnings",
         (NoArg (\f -> Left (f {suppressWarnings = SomeMsgs []})) (Nothing),
          "clear the list of warnings to ignore",
          Deprecated "Use \"-suppress-warnings NONE\" instead.")),

        ("synthesize",
         (Toggle (\f x -> f {synthesize=x, optBitConst=x}) (showIfTrue synthesize),
          "synthesize all primitives into simple boolean ops", Hidden)),

        ("systemc",
         let setFn f = case setBackend f Bluesim of
                         Left f' -> Left f' { genABin = True, genSysC = True }
                         Right e -> Right e
         in  (NoArg setFn (Just genSysC),
              "generate a SystemC model", Visible)),

        ("tcl-show-hidden",
         (Toggle (\f x -> f {tclShowHidden=x}) (showIfTrue tclShowHidden),
          "show hidden levels of instance hierarchy in bluetcl", Hidden)),

        ("u",
         (Toggle (\f x -> f {updCheck=x}) (showIfTrue updCheck),
          "check and recompile packages that are not up to date", Visible)),

        ("unsafe-always-ready",
         (Toggle (\f x -> f {unsafeAlwaysRdy=x}) (showIfTrue unsafeAlwaysRdy),
          "downgrade always_ready errors to warnings", Hidden)),

        ("unspecified-to",
         (Arg "val" (\f s -> case s of
                         "0" -> Left ( f {unSpecTo = s } )
                         "1" -> Left ( f {unSpecTo = s } )
                         "X" -> Left ( f {unSpecTo = s } )
                         "x" -> Left ( f {unSpecTo = map toUpper s } )
                         "A" -> Left ( f {unSpecTo = s } )
                         "a" -> Left ( f {unSpecTo = map toUpper s } )
                         "Z" -> Left ( f {unSpecTo = s } )
                         "z" -> Left ( f {unSpecTo = map toUpper s } )
                         _   -> Right (cmdPosition, EBadArgFlag "-unspecified-to" s ["0","1","X","Z","A"]))
              (Just (FRTString (unSpecTo))),
         "remaining unspecified values are set to: 'X', '0', '1', 'Z', or 'A'", Visible)),

        -- This should be Toggle, but instead, -no-use-layout is a
        -- trace flag and this exists just to be seen in the help message.
        -- It will be obsoleted eventually anyway.
        ("use-layout",
         (NoArg Left Nothing,
          "use layout rule", Hidden)),

        ("use-dpi",
         (Toggle (\f x -> f {useDPI=x}) (showIfTrue useDPI),
          "use DPI instead of VPI in generated Verilog", Visible)),

        ("use-negate",
         (Toggle (\f x -> f {useNegate=x}) (showIfTrue useNegate),
          "use negate in Verilog code", Hidden)),

        ("use-prelude",
         (Toggle (\f x -> f {usePrelude=x}) (showIfTrue usePrelude),
          "automatically import Prelude", Hidden)),

        ("use-proviso-sat",
         (Toggle (\f x -> f {useProvisoSAT=x}) (showIfTrue useProvisoSAT),
          "use SAT solver to resolve numeric provisos", Hidden)),

        ("stdlib-names",
         (Toggle (\f x -> f {stdlibNames=x}) (showIfTrue stdlibNames),
          "the source file is from the standard library", Hidden)),

        ("v95",
         (Toggle (\f x -> f {v95=x}) (showIfTrue v95),
          "generate strict Verilog 95 code", Visible)),

        ("vdir",
         (Arg "dir" (\f s -> Left (f {vdir = Just s})) (Just (FRTMaybeString vdir)),
          "output directory for .v files", Visible)),

        ("verbose",
         (NoArg (Left . moreTalkative) (Just verbose),
          "be more talkative", Visible)),
        ("v",
         (Alias "verbose", "same as -verbose", Visible)),

        ("quiet",
         (NoArg (Left . lessTalkative) (Just quiet),
          "be less talkative", Visible)),
        ("q",
         (Alias "quiet", "same as -quiet", Visible)),

        ("verilog",
         let setFn f = setBackend f Verilog
             getFn f = backend f == Just Verilog
         in  (NoArg setFn (Just getFn),
              "compile BSV generating Verilog file", Visible)),

        ("verilog-filter",
         (Arg "cmd" (\f s -> Left (f {verilogFilter = s:verilogFilter f}))
              (Just (FRTListString (reverse . verilogFilter))),
              "invoke a command to post-process the generated Verilog", Visible)),

        ("vsearch",
         (Arg "path" (\f s -> Left (f {vPathRaw = splitPath' f s vPathRaw})) (showPath vPathRaw),
          "search path (`:' sep.) for Verilog files", Visible)),

        ("vsim",
         let setFn f s = case setBackend f Verilog of
                           Left f' -> Left $ f' {vsim = Just s}
                           Right e -> Right e
             getFn = FRTMaybeString vsim
         in  (Arg "simulator" setFn (Just getFn),
              "specify which Verilog simulator to use", Visible)),

        ("verilog-declare-first",
         (Toggle (\f x -> f {verilogDeclareAllFirst=x}) (showIfTrue verilogDeclareAllFirst),
         "in generated Verilog, declare all signals first", Hidden)),

        ("vpp",
         (Toggle (\f x -> f {vpp=x}) (showIfTrue vpp),
          "preprocess the source with the SystemVerilog preprocessor", Hidden)),

        ("warn-action-shadowing",
         (Toggle (\f x -> f {warnActionShadowing=x}) (showIfTrue warnActionShadowing),
          "warn when a rule's action is overwritten by a later rule", Visible)),

        ("warn-method-urgency",
         (Toggle (\f x -> f {warnMethodUrgency=x}) (showIfTrue warnMethodUrgency),
          "warn when a method's urgency is arbitrarily chosen", Visible)),

        ("warn-undet-predicate",
         (Toggle (\f x -> f {warnUndetPred=x}) (showIfTrue warnUndetPred),
          "warn when a rule or method predicate has an undetermined value", Hidden)),

        ("Werror",
         (NoArg
            (\f -> let updFn f s = f {promoteWarnings = s}
                   in  addToMsgList f "-promote-warnings" "ALL" promoteWarnings updFn)
            Nothing,
          "make warnings to errors",
          Deprecated "Use \"-promote-warnings ALL\" instead.")),

        ("Xc",
         (PassThrough "arg" (\f s -> Left (f {cFlags = cFlags f ++ [s]})) (Just (FRTListString cFlags)),
          "pass argument to the C compiler", Visible)),

        ("Xc++",
         (PassThrough "arg" (\f s -> Left (f {cxxFlags = cxxFlags f ++ [s]})) (Just (FRTListString cxxFlags)),
          "pass argument to the C++ compiler", Visible)),

        ("Xcpp",
         (PassThrough "arg"
                      (\f s -> Left (f {cppFlags = cppFlags f ++ [s]}))
                      (Just (FRTListString cppFlags)),
          "pass argument to the C preprocessor", Visible)),

        ("Xl",
         (PassThrough "arg" (\f s -> Left (f {linkFlags = linkFlags f ++ [s]})) (Just (FRTListString linkFlags)),
          "pass argument to the C/C++ linker", Visible)),

        ("Xv",
         (PassThrough "arg" (\f s -> Left (f {vFlags = vFlags f ++ [s]})) (Just (FRTListString vFlags)),
          "pass argument to the Verilog link process", Visible))
        ]

-- -------------------------
-- Support for -print-flags

showFlagsLst :: Flags -> [[String]]
showFlagsLst flags =
    let showHidden = printFlagsHidden flags
        -- filter out the hidden if necessary
        flagsToBeShown = [ (f,ft) | (f,(ft,_,isHidden)) <- externalFlags,
                                    showHidden || (Visible == isHidden)]
        pprintedFlags = map (showFlag False flags) flagsToBeShown
    in (sort) pprintedFlags

showFlagsAllLst :: Flags -> [[String]]
showFlagsAllLst flags =
    let -- everything but deprecated
        flagsToBeShown = [ (f,ft) | (f,(ft,_,he)) <- externalFlags,
                                    he == Visible || he == Hidden]
        pprintedFlags = map (showFlag True flags) flagsToBeShown
    in sort pprintedFlags

showFlags :: Flags -> String
showFlags flags =
    let  pprintedFlags :: [[String]]
         pprintedFlags = filter ((/=) [] ) $ showFlagsLst flags
         showFlagStr :: [String] -> String
         showFlagStr ss = "     " ++ unwords (intersperse " " ss)
    in  unlines ("Flags:" : map showFlagStr pprintedFlags)

showFlag :: Bool -> Flags -> (String, FlagType) -> [String]
showFlag False flags (f, (Toggle _ (Just showf))) =
    case (showf flags) of
      (True,_)      -> [('-':f)]
      (False,True)  -> ["-no-" ++ f]
      (False,False) -> []
showFlag True flags (f, (Toggle _ (Just showf))) =
    case (showf flags) of
      (True,_)      -> [('-':f)]
      (False,True)  -> ["-no-" ++ f]
      (False,False) -> ["-no-" ++ f]

showFlag _ flags (f, (NoArg _ (Just showf))) =
    if (showf flags) then [('-':f)] else []
showFlag _ flags (f, (Arg _ _ (Just rt))) = showFlagArg flags f rt
showFlag _ flags (f, (Arg2 _ _ _ (Just (FRTListPairString showf)))) =
    map (\(a,b) -> ('-':f) ++ " " ++ a ++ " " ++ b) (showf flags)
showFlag _ flags (f, (Resource sf)) =
    if (resource flags) == sf then [('-':f)] else []
showFlag _ flags (f, (PassThrough _ _ (Just rt))) = showFlagArg flags f rt
showFlag _ flags _ = []

-- create the show string for one-arg flags which have a show function
showFlagArg :: Flags -> String -> ArgReturnType -> [String]
showFlagArg flags f (FRTString showf) =
    [('-':f), showf flags]
showFlagArg flags f (FRTMaybeString showf) =
    case (showf flags) of
        Just arg -> [('-':f), arg]
        Nothing -> []
showFlagArg flags f (FRTListString showf) =
  concatMap (\x -> ['-':f, x]) (showf flags)

-- -------------------------
-- Support for -print-flags-raw

-- This shows the raw flags, rather than showing them in terms of the
-- externally visible flags.  Use showFlags to display the flags in
-- user-understandable terms.
showFlagsRaw :: Flags -> String
showFlagsRaw flags =
    let render (k, v) = "\t" ++ k ++ " = " ++ v
        fields =
         [("aggImpConds", show (aggImpConds flags)),
          ("allowIncoherentMatches", show (allowIncoherentMatches flags)),
          ("backend", show (backend flags)),
          ("bdir", show (bdir flags)),
          ("biasMethodScheduling", show (biasMethodScheduling flags)),
          ("bluespecDir", show (bluespecDir flags)),
          ("cDebug", show (cDebug flags)),
          ("cFlags", show (cFlags flags)),
          ("cIncPath", show (cIncPath flags)),
          ("cLibPath", show (cLibPath flags)),
          ("cLibs", show (cLibs flags)),
          ("cdir", show (cdir flags)),
          ("cpp", show (cpp flags)),
          ("cppFlags", show (cppFlags flags)),
          ("crossInfo", show (crossInfo flags)),
          ("cxxFlags", show (cxxFlags flags)),
          ("defines", show (defines flags)),
          ("demoteErrors", show (demoteErrors flags)),
          ("disableAssertions", show (disableAssertions flags)),
          ("doICheck", show (doICheck flags)),
          ("dumpAll", show (dumpAll flags)),
          ("dumps", show (dumps flags)),
          ("enablePoisonPills", show (enablePoisonPills flags)),
          ("entry", show (entry flags)),
          ("expandATSlimit", show (expandATSlimit flags)),
          ("expandIf", show (expandIf flags)),
          ("extraVerbose", show (extraVerbose flags)),
          ("fdir", show (fdir flags)),
          ("finalcleanup", show (finalcleanup flags)),
          ("genABin", show (genABin flags)),
          ("genABinVerilog", show (genABinVerilog flags)),
          ("genName", show (genName flags)),
          ("genSysC", show (genSysC flags)),
          ("ifLift", show (ifLift flags)),
          ("ifcPath", show (ifcPath flags)),
          ("ifcPathRaw", show (ifcPathRaw flags)),
          ("infoDir", show (infoDir flags)),
          ("inlineBool", show (inlineBool flags)),
          ("inlineISyntax", show (inlineISyntax flags)),
          ("inlineSimple", show (inlineSimple flags)),
          ("keepAddSize", show (keepAddSize flags)),
          ("keepFires", show (keepFires flags)),
          ("keepInlined", show (keepInlined flags)),
          ("kill", show (kill flags)),
          ("linkFlags", show (linkFlags flags)),
          ("maxTIStackDepth", show (maxTIStackDepth flags)),
          ("methodBVI", show (methodBVI flags)),
          ("methodConditions", show (methodConditions flags)),
          ("methodConf", show (methodConf flags)),
          ("neatNames", show (neatNames flags)),
          ("oFile", show (oFile flags)),
          ("optATS", show (optATS flags)),
          ("optAggInline", show (optAggInline flags)),
          ("optAndOr", show (optAndOr flags)),
          ("optBitConst", show (optBitConst flags)),
          ("optBool", show (optBool flags)),
          ("optFinalPass", show (optFinalPass flags)),
          ("optIfMux", show (optIfMux flags)),
          ("optIfMuxSize", show (optIfMuxSize flags)),
          ("optJoinDefs", show (optJoinDefs flags)),
          ("optMux", show (optMux flags)),
          ("optMuxConst", show (optMuxConst flags)),
          ("optMuxExpand", show (optMuxExpand flags)),
          ("optSched", show (optSched flags)),
          ("optUndet", show (optUndet flags)),
          ("parallelSimLink", show (parallelSimLink flags)),
          ("passThroughAssertions", show (passThroughAssertions flags)),
          ("preprocessOnly", show (preprocessOnly flags)),
          ("printFlags", show (printFlags flags)),
          ("printFlagsHidden", show (printFlagsHidden flags)),
          ("printFlagsRaw", show (printFlagsRaw flags)),
          ("promoteWarnings", show (promoteWarnings flags)),
          ("readableMux", show (readableMux flags)),
          ("redStepsMaxIntervals", show (redStepsMaxIntervals flags)),
          ("redStepsWarnInterval", show (redStepsWarnInterval flags)),
          ("relaxMethodEarliness", show (relaxMethodEarliness flags)),
          ("removeCReg", show (removeCReg flags)),
          ("removeCross", show (removeCross flags)),
          ("removeEmptyRules", show (removeEmptyRules flags)),
          ("removeFalseRules", show (removeFalseRules flags)),
          ("removeInoutConnect", show (removeInoutConnect flags)),
          ("removePrimModules", show (removePrimModules flags)),
          ("removeRWire", show (removeRWire flags)),
          ("removeReg", show (removeReg flags)),
          ("removeStarvedRules", show (removeStarvedRules flags)),
          ("removeUnusedMods", show (removeUnusedMods flags)),
          ("removeVerilogDollar", show (removeVerilogDollar flags)),
          ("resetName", show (resetName flags)),
          ("resource", show (resource flags)),
          ("rstGate", show (rstGate flags)),
          ("ruleNameCheck", show (ruleNameCheck flags)),
          ("satBackend", show (satBackend flags)),
          ("schedConds", show (schedConds flags)),
          ("schedDOT", show (schedDOT flags)),
          ("schedQueries", show (schedQueries flags)),
          ("showCSyntax", show (showCSyntax flags)),
          ("showCodeGen", show (showCodeGen flags)),
          ("showElabProgress", show (showElabProgress flags)),
          ("showIESyntax", show (showIESyntax flags)),
          ("showISyntax", show (showISyntax flags)),
          ("showModuleUse", show (showModuleUse flags)),
          ("showRangeConflict", show (showRangeConflict flags)),
          ("showSchedule", show (showSchedule flags)),
          ("showStats", show (showStats flags)),
          ("showUpds", show (showUpds flags)),
          ("showVersion", show (showVersion flags)),
          ("simplifyCSyntax", show (simplifyCSyntax flags)),
          ("strictMethodSched", show (strictMethodSched flags)),
          ("suppressWarnings", show (suppressWarnings flags)),
          ("synthesize", show (synthesize flags)),
          ("systemVerilogTasks", show (systemVerilogTasks flags)),
          ("tclShowHidden", show (tclShowHidden flags)),
          ("testAssert", show (testAssert flags)),
          ("timeStamps", show (timeStamps flags)),
          ("unsafeAlwaysRdy", show (unsafeAlwaysRdy flags)),
          ("unSpecTo", show (unSpecTo flags)),
          ("updCheck", show (updCheck flags)),
          ("useDPI", show (useDPI flags)),
          ("useNegate", show (useNegate flags)),
          ("usePrelude", show (usePrelude flags)),
          ("useProvisoSAT", show (useProvisoSAT flags)),
          ("v95", show (v95 flags)),
          ("vFlags", show (vFlags flags)),
          ("vPath", show (vPath flags)),
          ("vPathRaw", show (vPathRaw flags)),
          ("vdir", show (vdir flags)),
          ("verbose", show (verbose flags)),
          ("verilogDeclareAllFirst", show (verilogDeclareAllFirst flags)),
          ("verilogFilter", show (verilogFilter flags)),
          ("vpp", show (vpp flags)),
          ("vsim", show (vsim flags)),
          ("warnActionShadowing", show (warnActionShadowing flags)),
          ("warnMethodUrgency", show (warnMethodUrgency flags)),
          ("warnUndetPred", show (warnUndetPred flags))
         ]
        in "Flags {\n" ++
               (intercalate ",\n" (map render fields)) ++
           "\n}"

-- -------------------------
-- Support for querying the flags in bluetcl

getFlagValueString :: Flags -> String -> IO [String]
getFlagValueString flags key = do
  case (lookup key flagsTable) of
    Nothing -> ioError $ userError ("Unknown flag \"" ++ key ++ "\" when looking up it value" )
    Just ft -> return $ flagTypeToString flags key ft

-- This is similar to showFlag, but it is more verbose -no options are shown
flagTypeToString :: Flags -> String -> FlagType -> [String]
flagTypeToString flags key (Toggle _ Nothing)  = []
flagTypeToString flags key (Toggle _ (Just f)) =
  [if (fst (f flags)) then ("-" ++ key) else ("-no-" ++ key)]
flagTypeToString flags key ft = showFlag False flags (key,ft)


-- -------------------------
-- Path Utilities
-- (colon-separated list with special symbols % and +)

makePath :: String -> [String]
makePath = splitWhen (==':')

unPath :: [String] -> String
unPath path =
    let convToken s = if (s == defaultPathToken) then "+" else s
    in intercalate ":" (map convToken path)

splitPath :: String -> [String] -> String -> [String]
splitPath bspecdir old_path s =
    let -- break on colons
        paths0 = makePath s
        -- expand symbols, and remove empty dirs
        paths = let expandPercent c = if (c == '%') then bspecdir else [c]
                    expandDir "+" = old_path
                    expandDir ""  = []
                    expandDir d   = [concatMap expandPercent d]
                in  concatMap expandDir paths0
    in
        paths

splitPath' :: Flags -> String -> (Flags -> [String]) -> [String]
splitPath' f s m = splitPath (bluespecDir f) (m f) s

replacePathToken :: String -> [String] -> [String] -> [String]
replacePathToken tok xs new = concatMap (helper new tok) xs
  where helper ys x x' | x == x'   = ys
                       | otherwise = [x']

-- -------------------------
-- Colon-separated List of error message tags,
-- allowing NONE and ALL as possible values

makeMsgList :: String -> [String]
makeMsgList = splitWhen (==':')

unMsgList :: [String] -> String
unMsgList = intercalate ":"

checkMsgList :: String -> [String] -> Either EMsg [String]
checkMsgList flag_name tags =
    let
        checkOneTag :: String -> Maybe String
        checkOneTag (ty:num@[_,_,_,_])
            | isAlpha ty && all isDigit num = Just ((toUpper ty):num)
        checkOneTag _ = Nothing

        mkErr badtag = (cmdPosition, EMsgListArgFlag flag_name badtag)

        -- XXX This only reports one invalid string (first from the end)
        foldfn tag res@(Left _) = res
        foldfn tag (Right acc) = case (checkOneTag tag) of
                                   Nothing -> Left (mkErr tag)
                                   Just tag' -> Right (tag':acc)
    in
        foldr foldfn (Right []) tags

addToMsgList :: Flags -> String -> String -> (Flags -> MsgListFlag) ->
                (Flags -> MsgListFlag -> Flags) -> Either Flags EMsg
addToMsgList flags flag_name arg_str flagFn updFn =
    case arg_str of
      "ALL" -> Left $ updFn flags (AllMsgs)
      "NONE" -> Left $ updFn flags (SomeMsgs [])
      _ -> let -- divide into separate strings, remove empty
               new_list0 = makeMsgList arg_str
           in  case (checkMsgList flag_name new_list0) of
                 Left errs -> Right errs
                 Right new_list ->
                     let res_list =
                             case (flagFn flags) of
                               AllMsgs -> AllMsgs
                               SomeMsgs cur_list ->
                                   -- put it together and remove duplicates
                                   SomeMsgs $ nub (cur_list ++ new_list)
                     in  Left $ updFn flags res_list

-- -------------------------
-- Other Utilities

mread :: Read a => String -> Maybe a
mread s =
    case reads s of
    [(x, "")] -> Just x
    _ -> Nothing

setBackend :: Flags -> Backend -> Either Flags EMsg
setBackend flags new_be =
    case backend flags of
      Just old_be | old_be /= new_be
        -> Right (cmdPosition, ETooManyBackends)
      _ -> Left $ flags { backend = Just new_be }

-- -------------------------
