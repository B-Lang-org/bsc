module Flags(
             Flags(..),
             redSteps,
             ResourceFlag(..), SATFlag(..), MsgListFlag(..),

             DumpFlag(..),
             hasDump, hasDumpStrict, dumpInfo,

             Verbosity(..), extraVerbose, verbose, quiet,
             moreTalkative, lessTalkative, setVerbose,
        ) where

import Data.Maybe(isJust)

import Backend

-- -------------------------
-- Internal flags
--
-- This is the data structure which will be carried through the program.

data Flags = Flags {
        aggImpConds :: Bool,
        allowIncoherentMatches :: Bool,
        backend :: Maybe Backend,
        bdir :: Maybe String,
        biasMethodScheduling :: Bool,
        bluespecDir :: String,
        cIncPath :: [String],
        cLibPath :: [String],
        cLibs :: [String],
        cDebug :: Bool,
        cFlags :: [String],
        cxxFlags :: [String],
        cppFlags :: [String],
        linkFlags :: [String],
        cdir :: Maybe String,
        cpp :: Bool,
        defines :: [String],
        demoteErrors :: MsgListFlag,
        disableAssertions :: Bool,
        passThroughAssertions :: Bool,
        doICheck :: Bool,
        dumpAll :: Bool,
        dumps :: [(DumpFlag, Maybe FilePath)], -- dump to file or stdout
        enablePoisonPills :: Bool,
        entry :: Maybe String,
        expandATSlimit :: Int,
        expandIf :: Bool,
        fdir :: Maybe String,
        finalcleanup :: Int,
        genABin :: Bool,
        genABinVerilog :: Bool,
        genName :: [String],
        genSysC :: Bool,
        ifcPathRaw :: [String],
        ifcPath :: [String],
        infoDir :: Maybe String,
        inlineBool :: Bool,
        inlineISyntax :: Bool,
        inlineSimple :: Bool,
        keepAddSize :: Bool,
        keepFires :: Bool,
        keepInlined :: Bool,
        kill :: Maybe (DumpFlag, Maybe String),
        ifLift :: Bool,
        maxTIStackDepth :: Int,
        methodBVI :: Bool,
        methodConf :: Bool,
        methodConditions :: Bool,
        neatNames :: Bool,
        oFile :: String,
        optAggInline :: Bool,
        optATS :: Bool,
        optAndOr :: Bool,
        optBitConst :: Bool,
        optBool :: Bool,
        optFinalPass :: Bool,
        optIfMux :: Bool,
        optIfMuxSize :: Integer,
        optJoinDefs :: Bool,
        optMux :: Bool,
        optMuxExpand :: Bool,
        optMuxConst :: Bool,
        optSched :: Bool,
        optUndet :: Bool,
        crossInfo :: Bool,
        parallelSimLink :: Integer,
        printFlags :: Bool,
        printFlagsHidden :: Bool,
        printFlagsRaw :: Bool,
        preprocessOnly :: Bool,
        promoteWarnings :: MsgListFlag,
        readableMux :: Bool,
        redStepsWarnInterval :: Integer,
        redStepsMaxIntervals :: Integer,
        relaxMethodEarliness :: Bool,
        removeEmptyRules :: Bool,
        removeFalseRules :: Bool,
        removeInoutConnect :: Bool,
        removePrimModules :: Bool,
        removeCReg :: Bool,
        removeReg :: Bool,
        removeRWire :: Bool,
        removeCross :: Bool,
        removeStarvedRules :: Bool,
        removeUnusedMods :: Bool,
        removeVerilogDollar :: Bool,
        resetName :: String,
        resource :: ResourceFlag,
        rstGate :: Bool,
        ruleNameCheck :: Bool,
        satBackend :: SATFlag,
        schedConds:: Bool,
        schedDOT :: Bool,
        schedQueries :: [(String,String)],
        showCSyntax :: Bool,
        showCodeGen :: Bool,
        showElabProgress :: Bool,
        showIESyntax :: Bool,
        showISyntax :: Bool,
        showModuleUse :: Bool,
        showRangeConflict :: Bool,
        showSchedule :: Bool,
        showStats :: Bool,
        showUpds :: Bool,
        simplifyCSyntax :: Bool,
        strictMethodSched :: Bool,
        suppressWarnings :: MsgListFlag,
        synthesize :: Bool,
        systemVerilogTasks :: Bool,
        tclShowHidden :: Bool,
        timeStamps :: Bool,
        showVersion :: Bool,
        testAssert :: Bool,
        unsafeAlwaysRdy :: Bool,
        unSpecTo :: String,
        updCheck :: Bool,
        useDPI :: Bool,
        useNegate :: Bool,
        usePrelude :: Bool,
        useProvisoSAT :: Bool,
        stdlibNames :: Bool,
        v95 :: Bool,
        vFlags :: [String],
        vdir :: Maybe String,
        vPathRaw :: [String],
        vPath :: [String],
        vpp :: Bool,
        vsim :: Maybe String,
        verbosity :: Verbosity,
        verilogDeclareAllFirst :: Bool,
        verilogFilter :: [String],
        warnActionShadowing :: Bool,
        warnMethodUrgency :: Bool,
        warnUndetPred :: Bool
        }
-- don't derive Show -- it causes an optimized ghc build to take a long time
--        deriving (Show)

data Verbosity = Quiet | Normal | Verbose | ExtraVerbose
   deriving(Eq, Show, Ord, Enum)

extraVerbose :: Flags -> Bool
extraVerbose = (== ExtraVerbose) . verbosity

verbose :: Flags -> Bool
verbose = (>= Verbose) . verbosity

setVerbose :: Bool -> Flags -> Flags
setVerbose False f = f
setVerbose True  f = f { verbosity = max Verbose (verbosity f) }

quiet :: Flags -> Bool
quiet = (== Quiet) . verbosity

moreTalkative :: Flags -> Flags
moreTalkative f =
  case verbosity f of
    ExtraVerbose -> f
    v            -> f { verbosity = succ v }

lessTalkative :: Flags -> Flags
lessTalkative f =
  case verbosity f of
    Quiet -> f
    v     -> f { verbosity = pred v }

data DumpFlag
        =
        -- Bluespec source file
          DFdepend
        | DFcpp
        | DFvpp
        | DFbsvlex
        | DFparsed
        | DFimports
        | DFopparse
        | DFsyminitial
        | DFsympostgenwrap
        | DFsympostderiving
        | DFsympostctxreduce
        | DFsympostbinary
        | DFgenfuncwrap
        | DFgenwrap
        | DFderiving
        | DFctxreduce
        | DFconvinst
        | DFtypecheck
        | DFgenforeign
        | DFgenVPI
        | DFsimplified
        | DFinternal
        | DFbinary
        | DFfixup
        | DFisimplify
        | DFwriteBin

        -- module generation
        | DFexpanded
        | DFnormtypes
        | DFinlineFmt
        | DFinline
        | DFtransform
        | DFsplitIf
        | DFlift
        | DFiparams
        | DFidroprules
        | DFATS
        | DFATSexpand
        | DFdumpLambdaCalculus
        | DFdumpSAL
        | DFATSperfspec
        | DFATSsplice
        | DFATSclean
        | DFpathsPreSched
        | DFschedule
        | DFresources
        | DFvschedinfo
        | DFscheduledefs
        | DFdumpschedule
        | DFcheckproofs
        | DFpathsPostSched
        | DFnoinline
        | DFaddSchedAssumps
        | DFremoveAssumps
        | DFdropundet
        | DFwriteABin
        | DFwrappergen
        | DFwrappercomp

        -- Generate Verilog
        | DFforeignMap
        | DFastate
        | DFrwire
        | DFcreg
        | DFrenameio
        | DFadropdefs
        | DFaopt
        | DFsynthesize
        | DFveriquirks
        | DFfinalcleanup
        | DFIOproperties
        | DFverilog
        | DFverilogDollar
        | DFwriteVerilog

        -- Link
        | DFreadelab

        -- Link Verilog
        | DFcompileVPI
        | DFveriloglink

        -- Generate/Link Bluesim
        | DFsimExpand
        | DFsimDepend
        | DFsimPackageOpt
        | DFsimMakeCBlocks
        | DFsimCOpt
        | DFsimBlocksToC
        | DFgenSystemC
        | DFwriteC
        | DFbluesimcompile
        | DFbluesimlink

        deriving (Eq, Read, Show, Enum, Bounded)

data ResourceFlag
       = RFoff    -- don't reschedule: fail if not enough resources
       | RFsimple -- reschedule: arbitrate resources (drop first edge in graph)
       deriving (Eq, Show)

data SATFlag
       = SAT_Yices
       | SAT_STP
       deriving (Eq, Show)

data MsgListFlag = AllMsgs | SomeMsgs [String]
                 deriving (Show, Eq)

-----

-- The number of reduction steps is defined based on the interval
redSteps :: Flags -> Integer
redSteps flags = (redStepsWarnInterval flags) *
                 (redStepsMaxIntervals flags)

-----

hasDump :: Flags -> DumpFlag -> Bool
hasDump f d = (dumpAll f) || (hasDumpStrict f d)

hasDumpStrict :: Flags -> DumpFlag -> Bool
hasDumpStrict f d = isJust $ lookup d (dumps f)

dumpInfo :: Flags -> DumpFlag -> Maybe (Maybe FilePath)
dumpInfo f d = if dumpAll f then Just Nothing else lookup d (dumps f)

-- -------------------------
