{-# LANGUAGE CPP #-}
module Main_showrules(main) where

import Exceptions(bsCatch)
import Version
import FileNameUtil(hasDotSuf, hasNoSuffix, vcdSuffix)
import ABinUtil(getABIHierarchy, assertNoSchedErr, InstModMap, HierMap)
import Position(noPosition)
import Id( Id, getIdString, getIdBaseString, getIdQualString
         , mkIdCanFire, mkIdWillFire, isIdCanFire, dropCanFirePrefixId
         , addToQual, setIdQualString, emptyId, mk_homeless_id
         )
import Error(internalError, EMsg, WMsg, ErrMsg(..),
             ErrorHandle, initErrorHandle,
             exitOK, exitFail, bsErrorNoExit, bsWarning,
             convExceptTToIO)
import Util(separate, headOrErr, fromJustOrErr, unconsOrErr)
import IOUtil(getEnvDef)
import TopUtils(dfltBluespecDir)
import ASyntax
import ASyntaxUtil
import ABin(ABinModInfo(..))
import AScheduleInfo(SchedNode(..))
import SimCCBlock(SimCCBlock(..), primBlocks)
import SimPrimitiveModules(isPrimitiveModule, isFIFO)
import SimExpand(simExpandSched)
import SimDomainInfo(DomainInfo(..))
import SimPackage(SimSchedule(..), DefMap)
import Wires(writeClockDomain)
import VCD
import CondTree
import ListUtil(dropRepeatsBy)
import APrims
import PPrint
import Eval
import qualified DynamicMap as DM

import System.Environment(getArgs)
import System.Console.GetOpt
import System.IO
import System.IO.Unsafe(unsafePerformIO)
import System.Time
import Control.Monad(when, msum, foldM)
import Control.Exception(bracket)
import Data.List( partition, intercalate, genericLength
                , sort, findIndex, sortBy, groupBy
                )
import Data.List.Split(wordsBy)
import Data.Maybe(isJust, fromJust, fromMaybe, mapMaybe, catMaybes)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.ByteString.Lazy.Char8 as C
import Text.Regex

-- import Debug.Trace

-- Version string (matches main BSC version numbering)
versionString :: String
versionString = versionStr True (bluespec ++ " showrules utility")

-- -------------------------------------------------------------------
-- Option processing

-- Structure which holds all option settings
data Options = Options { optVerbose      :: Bool
                       , optDebug        :: Maybe FilePath
                       , optShowVersion  :: Bool
                       , optShowHelp     :: Bool
                       , optShowProgress :: Bool
                       , optInputVCD     :: Maybe FilePath
                       , optOutputVCD    :: Maybe FilePath
                       , optOutputNovas  :: Maybe FilePath
                       , optTopModule    :: Maybe String
                       , optRoot         :: String
                       , optBAPath       :: [String]
                       }
  deriving (Show)

-- Default settings
defaultOptions :: String -> Options
defaultOptions bluespecdir =
    Options { optVerbose      = False
            , optDebug        = Nothing
            , optShowVersion  = False
            , optShowHelp     = False
            , optShowProgress = False
            , optInputVCD     = Nothing
            , optOutputVCD    = Nothing
            , optOutputNovas  = Nothing
            , optTopModule    = Nothing
            , optRoot         = "main.top"
            , optBAPath       = original_path bluespecdir
            }

original_path :: String -> [String]
original_path bluespecdir = [ "."
                            , bluespecdir ++ "/Libraries"
                            ]

-- Description of command-line options
options :: [OptDescr (Options -> Options)]
options =
    [ Option ['v']      ["verbose"]
             (NoArg (\opts -> opts { optVerbose = True }))
             "write verbose status messages"
    , Option []         ["debug"]
             (OptArg (\mf opts -> opts { optDebug = Just (fromMaybe "" mf) }) "FILE")
             "generate very detailed debug traces"
    , Option ['V']      ["version"]
             (NoArg (\opts -> opts { optShowVersion = True }))
             "show version information and exit"
    , Option ['h','?']  ["help"]
             (NoArg (\opts -> opts { optShowHelp = True }))
             "print usage information and exit"
    , Option ['o']      ["output"]
             (ReqArg (\f opts -> opts { optOutputVCD = Just f }) "FILE")
             "output VCD file"
    , Option []         ["novas"]
             (ReqArg (\f opts -> opts { optOutputNovas = Just f }) "FILE")
             "output alias file for Novas tools"
    , Option []         ["progress"]
             (NoArg (\opts -> opts { optShowProgress = True }))
             "show VCD conversion progress indicators"
    , Option ['p']      ["path"]
             (ReqArg (\s opts -> let p = optBAPath opts
                                 in opts { optBAPath = (s:p) }) "PATH")
             ".ba file search path (% = $BLUESPECDIR and + = original path)"
    , Option ['r']      ["root"]
             (ReqArg (\s opts -> opts { optRoot = s }) "NAME")
             "hierarchical name of top BSV module in hierarchy"
    ]

-- Header used in usage message
usage_header :: String
usage_header = "Usage: showrules [OPTIONS] <VCD> <MODULE>"

-- Parse the command line to produce the option structure, etc.
parseOpts :: [String] -> String -> (Options, [String], [EMsg])
parseOpts argv bluespecdir =
    let (opts,args0,errs) = getOpt Permute options argv
        options0 = foldl (flip id) (defaultOptions bluespecdir) opts
        (vcds,args1) = partition (hasDotSuf vcdSuffix) args0
        (mods,args2) = partition hasNoSuffix args1
        emsgs0 = map toEMsg errs
        (options1,emsgs1) = checkVCDs vcds (options0,emsgs0)
        (options2,emsgs2) = checkMods mods (options1,emsgs1)
        emsgs3 = if (null args2)
                 then emsgs2
                 else emsgs2 ++
                      [(noPosition, EUnrecognizedCmdLineText (unwords args2))]
        options3 = interpretPath options2
    in (options3, [], emsgs3)
    where checkVCDs fs (os,es) =
              if (length fs /= 1)
              then (os,es ++ [(noPosition, EExactlyOneArgRequired "input VCD file name" fs)])
              else (os { optInputVCD = Just (head fs) }, es)
          checkMods fs (os,es) =
              if (length fs /= 1)
              then (os,es ++ [(noPosition, EExactlyOneArgRequired "name for the top BSV module" fs)])
              else (os { optTopModule = Just (head fs) }, es)
          -- Path options are accumulated during option processing and
          -- and then must be analyzed to determine the resulting path.
          -- The optBAPath will have one element for each --path option,
          -- followed for the original path elements.  The elements from
          -- the user are split off, broken up at ':' separators and then
          -- interpreted in order (replacing '+' and '%') to determine
          -- the final path.
          interpretPath os = let n = length (original_path bluespecdir)
                                 n' = length (optBAPath os)
                                 (user_paths,orig_path) = splitAt (n'-n) (optBAPath os)
                                 new_path = foldr addPath orig_path user_paths
                             in os { optBAPath = new_path }
          addPath s ps = let xs = wordsBy (=='.') s
                             xs' = concatMap (\x -> if (x == "+") then ps else [x]) xs
                             xs'' = [ concatMap (\c -> if (c == '%') then bluespecdir else [c]) x
                                    | x <- xs'
                                    ]
                         in xs''

-- Produce a standard EMsg value from an option parser error string
toEMsg :: String -> EMsg
toEMsg s = fromMaybe (noPosition, EGeneric s) $
           msum [f s | f <- [ bad_option
                            , missing_arg
                            ]]
  where bad_option_regex = mkRegex "unrecognized option `(.*)'"
        bad_option x = do [opt] <- matchRegex bad_option_regex s
                          return (noPosition, EUnknownFlag opt)
        missing_arg_regex = mkRegex "option `(.*)' requires an argument .*"
        missing_arg x = do [opt] <- matchRegex missing_arg_regex s
                           return (noPosition, EOneArgFlag opt)

-- Validate command-line and process help requests
checkCmdLine :: ErrorHandle -> Options -> [String] -> [EMsg] -> IO ()
checkCmdLine errh opts args errs =
  do when (optShowVersion opts) $
          do hPutStrLn stdout versionString
             hPutStrLn stdout copyright
     when (optShowHelp opts) $
          hPutStrLn stdout (usageInfo usage_header options)
     when ((optShowVersion opts) || (optShowHelp opts)) $
          exitOK errh
     when (not (null errs)) $
          do bsErrorNoExit errh errs
             hPutStrLn stderr (usageInfo usage_header options)
             exitFail errh

-- -------------------------------------------------------------------
-- Main program routine

type RuleMap      = M.Map String Integer
type InvRuleMap   = M.Map Integer String
type SignalMap    = M.Map String (Code,Integer)
type InvSignalMap = M.Map Code String
type ClockMap     = M.Map Int ([String],[SchedNode])
type CodeSet      = S.Set Code
type CodeMap      = M.Map Code Signal
type ValueMap     = DM.Map Integer Code (VCDValue,ChangeReason)
type ClockEdgeMap = M.Map Code Integer
type RuleConds    = ([(String,AExpr)],Integer)
type ActionMap    = M.Map Int (M.Map (String,AMethodId) [RuleConds])
type Realignment  = [(Code,[RuleConds])]
type ModDefMap    = M.Map String DefMap

data ChangeReason = Stable | Changed | InTask String
  deriving (Eq,Ord,Show)

data Signal = ClockSignal { clk_domain     :: Int
                          , clk_name       :: String
                          , fired_code     :: Code
                          , blocked_code   :: Code
                          , virtual_width  :: Integer
                          , fire_signals   :: [(Code,Code,Integer)]
                          , realignment    :: Realignment
                          , rw_realignment :: Realignment
                          }
            | CFSignal
            | WFSignal
  deriving (Eq,Show)

-- The conversion is a lazy left-fold over a list of VCD commands, which
-- tracks the state of the fold using the ConvState structure.
data ConvState = ConvState { be_verbose     :: Bool
                           , debug_to       :: Maybe Handle
                           , root           :: String
                           , root_find      :: Maybe [String]
                           , time_factor    :: Integer
                           , current_time   :: Integer
                           , scope          :: [String]
                           , rule_map       :: RuleMap
                           , inv_rule_map   :: InvRuleMap
                           , signal_map     :: SignalMap
                           , inv_signal_map :: InvSignalMap
                           , clock_map      :: ClockMap
                           , code_map       :: CodeMap
                           , clk_edge_map   :: ClockEdgeMap
                           , value_map      :: ValueMap
                           , inst_map       :: InstModMap
                           , action_map     :: ActionMap
                           , edges          :: [(Code,Signal)]
                           , modified_set   :: CodeSet
                           , mod_def_map    :: ModDefMap
                           , prev_time      :: Double
                           , prev_bytes     :: Integer
                           , curr_bytes     :: Integer
                           , total_bytes    :: Integer
                           , progress_at    :: Maybe Integer
                           }

-- Type used to return errors, messages, etc. from conversion process
data Status = Err EMsg
            | Warn WMsg
            | Info String
  deriving (Show)

main :: IO ()
main = do
          hSetBuffering stdout LineBuffering
          hSetBuffering stderr LineBuffering
          hSetEncoding stdout utf8
          hSetEncoding stderr utf8
          argv <- getArgs
          -- catch errors, print them nicely, and exit
          bsCatch (hmain argv)

hmain :: [String] -> IO ()
hmain argv = do
          errh <- initErrorHandle
          bluespecdir <- getEnvDef "BLUESPECDIR" dfltBluespecDir
          -- parse command line arguments
          let (opts, args, emsgs) = parseOpts argv bluespecdir

          -- handle errors and/or request for help and version info
          checkCmdLine errh opts args emsgs

          -- read in .ba file data
          let top_mod = fromJust (optTopModule opts)
              verbose = optVerbose opts
              ba_path = optBAPath opts
          let prim_names = map sb_name primBlocks
          when (verbose) $ putStrLn "Reading design data from .ba files..."
          (_, hier_map, inst_map, _, _, _, abemis_by_name)
              <- convExceptTToIO errh $
                 getABIHierarchy errh verbose ba_path Nothing prim_names top_mod []
          abmis_by_name <- convExceptTToIO errh $ assertNoSchedErr abemis_by_name

          -- analyze design in preparation for VCD interpretation
          when (verbose) $ putStrLn "Analyzing design structure..."
          initState <- mkMorphState opts inst_map hier_map abmis_by_name top_mod

          -- write out debug info collected so far
          dbg (debug_to initState)
              ((unlines [ "---- PARSING COMMAND LINE ----"
                        , "ARGS:        " ++ (show argv)
                        , "BLUESPECDIR: " ++ (show bluespecdir)
                        ]) ++
               (show opts) ++ "\n" ++
               "-------\n")
          dbg (debug_to initState)
              ("---- BA FILE DATA ----\n" ++
               "INSTANCE MAP:\n" ++
               (unlines [ inst ++ " -> " ++ mod
                        | (inst,mod) <- M.toList inst_map
                        ]) ++
               "ABMI MAP:\n" ++
               (concat [ "ABMI FOR MODULE: " ++ mod ++ "\n" ++ (ppReadable abmi)
                       | (mod,abmi) <- abmis_by_name
                       ]) ++
               "-------\n")
          dbg (debug_to initState)
              ("---- RULE MAP ----\n" ++
               (unlines [ name ++ " -> " ++ (show rnum)
                        | (name,rnum) <- M.toList (rule_map initState)
                        ]) ++
               "-------\n")
          dbg (debug_to initState)
              ("---- CLOCK MAP ----\n" ++
               (unlines [ "Domain " ++ (show dom) ++ " " ++ (show clks) ++ "\n" ++
                          (unlines (map (\s -> "  " ++ (show s)) sched))
                        | (dom,(clks,sched)) <- M.toList (clock_map initState)
                        ]) ++
               "-------\n")

          -- process the input VCD file and write the output VCD file
          let vcd_in = fromJust (optInputVCD opts)
              vcd_out = fromMaybe "showrules.vcd" (optOutputVCD opts)
          when (verbose) $ putStrLn "Analyzing VCD hierarchy..."
          end_state <-
              bracket (openFile vcd_in ReadMode)
                      (\hIn -> do { hClose hIn; return Nothing })
                      (\hIn -> do st <- setupProgress (optShowProgress opts) hIn initState
                                  bracket (openFile vcd_out WriteMode)
                                          (\hOut -> do { hClose hOut; return Nothing })
                                          (\hOut -> processVCD errh hIn hOut st))

          -- generate the novas command file if requested
          when ((isJust (optOutputNovas opts)) && (isJust end_state)) $
               do let cmd_file = fromJust (optOutputNovas opts)
                  when (verbose) $ putStrLn "Writing Novas command file..."
                  bracket (openFile cmd_file WriteMode) hClose $ \hOut ->
                      do hPutStr hOut (formatNovas (fromJust end_state))
                         hFlush hOut

          -- done: exit normally
          when (verbose) $ putStrLn "VCD conversion is complete."
          case (maybe Nothing debug_to end_state) of
            Nothing    -> return ()
            (Just hdl) -> when (hdl /= stdout) $ hClose hdl
          -- XXX we may still reach this point if there were errors
          -- XXX because we use "bsErrorNoExit"
          exitOK errh


-- File operations and VCD conversion.  Performs IO and returns
-- Just the final conversion state.  This should be bracketed with
-- exception handlers that close the handles and return Nothing.
processVCD :: ErrorHandle -> Handle -> Handle -> ConvState ->
              IO (Maybe ConvState)
processVCD errh hIn hOut initState =
    do cs <- C.hGetContents hIn
       writeVCD hOut [Version versionString]
       let cmds = parseVCDSize cs
       finalState <- foldM (morphVCD errh hOut) initState cmds
       endOfVCD errh hOut finalState
       hFlush hOut
       return (Just finalState)

writeVCD :: Handle -> VCD -> IO ()
writeVCD hOut vcd = hPutStr hOut (formatVCD vcd)

-- -------------------------------------------------------------------
-- VCD conversion details


-- Create initial VCD conversion state
--
-- This requires analyzing some aspects of the design, particularly
-- the rules and the clocks.  We build a number of maps used to direct
-- the conversion process.
mkMorphState :: Options -> InstModMap -> HierMap ->
                [(String, (ABinModInfo, String))] -> String -> IO ConvState
mkMorphState opts instmap hiermap abmis_by_name top_mod =
    do let abmimap = M.fromList [ (mod,abmi)
                                | (mod, (abmi,_)) <- abmis_by_name
                                ]
       -- determine debug logging target
       dbg_target <- case (optDebug opts) of
                       Nothing   -> return Nothing
                       (Just "") -> return (Just stdout)
                       (Just f)  -> do hdl <- openFile f WriteMode
                                       return (Just hdl)

       -- generate a unique numeric Id for each rule
       let user_modules = [ (inst,abmi)
                          | (inst,mod) <- M.toList instmap
                          , not (isPrimitiveModule mod)
                          , let abmi = fromJustOrErr "mkMorphState: user_modules" $
                                         M.lookup mod abmimap
                          ]
           all_rules = [ (inst,rule)
                       | (inst,abmi) <- user_modules
                       , rule <- apkg_rules (abmi_apkg abmi)
                       ]
           rulemap = M.fromList [ (joinName inst (aRuleName rule), n)
                                | ((inst,rule),n) <- zip all_rules [0..]
                                ]
           invrulemap = M.fromList [ (n, joinName inst (aRuleName rule))
                                   | ((inst,rule),n) <- zip all_rules [0..]
                                   ]
           rule_count = fromIntegral (M.size rulemap)
       when (optVerbose opts) $ putStrLn $ "found " ++ (show rule_count) ++ " rules in the design"

       -- identify the clock signals and clock domains
       simscheds <- simExpandSched abmis_by_name hiermap instmap top_mod
       let clkmap = M.fromList [ (num, (clks, order))
                               | sched <- simscheds
                               , let dim = ss_domain_info_map sched
                               , let num = writeClockDomain . snd $ head (M.keys dim)
                               , let clks = mapMaybe (getClkName (optRoot opts))
                                                     (di_clocks $ head (M.elems dim))
                               , let order = ss_sched_order sched
                               ]
       when (optVerbose opts) $ putStrLn $ "found " ++ (show (M.size clkmap)) ++ " clock domains in the design"

       -- determine the expected scope for the root
       let root_scope = reverse (wordsBy (=='.') (optRoot opts))

       -- build the data-structures for determining which rule
       -- has updated each value
       let methmap = M.fromList [ ((inst,name),rules)
                                | (inst,abmi) <- user_modules
                                , aif <- apkg_interface (abmi_apkg abmi)
                                , let name = aIfaceName aif
                                , let rules = aIfaceRules aif
                                , not (null rules)
                                ]
       let getRuleActs i r = If (i,(arule_pred r)) (getActs i (arule_actions r))
           getActs i [] = []
           getActs i ((ACall o m args):acts) =
               let cond     = headOrErr "mkMorphState: getActs" args
                   sub_inst = joinName i o
                   m'       = setIdQualString m ""
                   sub_acts = case (M.lookup (sub_inst,m') methmap) of
                                (Just rs) -> map (getRuleActs sub_inst) rs
                                Nothing   -> [Leaf (sub_inst,m)]
               in if (null sub_acts)
                  then getActs i acts
                  else (If (i,cond) sub_acts):(getActs i acts)
           getActs i (_:acts) = getActs i acts
           dom_map = M.fromList [ (rule,dom)
                                | (dom,(_,sns)) <- M.toList clkmap
                                , rule <- [ rid | (Exec rid) <- sns ]
                                ]
           expr_to_bool e | isTrue e  = Just True
                          | isFalse e = Just False
                          | otherwise = Nothing
           err n = internalError $ "Unknown rule '" ++ n ++ "'"
           write_conds = [ (dom, M.singleton meth [(conds,rnum)])
                         | (inst,rule) <- all_rules
                         , let name = aRuleName rule
                         , let hname = joinName inst name
                         , let qname = addToQual inst name
                         , let rnum = M.findWithDefault (err hname) hname rulemap
                         , let dom = M.findWithDefault (-1) qname dom_map
                         , let cts = simplify (expr_to_bool . snd)
                                              (getRuleActs inst rule)
                         , let actions = map cf_to_wf cts
                         , (conds,meth) <- concatMap enumerate actions
                         ]
           actionmap = M.fromListWith (M.unionWith (++)) write_conds

           -- construct a map from defs to exprs
           mkDefMap abmi = M.fromList $ map (\d -> (adef_objid d,d))
                                            (apkg_local_defs (abmi_apkg abmi))
           moddefmap = M.map mkDefMap abmimap

       -- construct and return the initial conversion state
       return $ deepseq (rulemap, invrulemap, clkmap, instmap, actionmap, moddefmap)
                      ConvState { be_verbose     = optVerbose opts
                                , debug_to       = dbg_target
                                , root           = optRoot opts
                                , root_find      = Just root_scope
                                , time_factor    = ilog1000 rule_count
                                , current_time   = 0
                                , scope          = []
                                , rule_map       = rulemap
                                , inv_rule_map   = invrulemap
                                , signal_map     = M.empty
                                , inv_signal_map = M.empty
                                , clock_map      = clkmap
                                , code_map       = M.empty
                                , clk_edge_map   = M.empty
                                , value_map      = DM.empty
                                , inst_map       = instmap
                                , action_map     = actionmap
                                , edges          = []
                                , modified_set   = S.empty
                                , mod_def_map    = moddefmap
                                -- these get initialized in setupProgress
                                , prev_time      = 0
                                , prev_bytes     = 0
                                , curr_bytes     = 0
                                , total_bytes    = 0
                                , progress_at    = Nothing
                                }

setupProgress :: Bool -> Handle -> ConvState -> IO ConvState
setupProgress False hIn st = return st
setupProgress True  hIn st =
    do -- record the start time
       (TOD s ps) <- getClockTime
       let now = (fromInteger s) + (fromInteger ps / (10.0^(12 :: Int)))

       -- record the total input file size
       file_sz <- hFileSize hIn

       -- return the updated state
       return $ st { prev_time = now
                   , total_bytes = file_sz
                   , progress_at = Just (file_sz `div` 100)
                   }


-- One step of lazy VCD conversion
--
-- This function gets called on each VCD command in the input VCD stream.
-- It handles processing of the definition header as well as the value
-- changes.  When processing commands in the header it builds a symbol
-- table and correlates data from the .ba files with the symbols in the
-- VCD file.  Once an EndDefs command is encountered, we know that all of
-- the design data is known, so more processing is done to build efficient
-- structures for handling the value changes to come.

morphVCD :: ErrorHandle -> Handle -> ConvState -> (VCDCmd,Integer) ->
            IO ConvState
morphVCD errh hOut st (cmd,bytes) =
  do st' <- doProgress st bytes
     morphVCD' errh hOut st' cmd

-- These are all VCD commands in the header

-- expand timescale to accommodate microticks
morphVCD' :: ErrorHandle -> Handle -> ConvState -> VCDCmd -> IO ConvState
morphVCD' errh hOut st (Timescale n u) =
  do let u' = u + (time_factor st)
     writeVCD hOut [Timescale n u']
     return st

-- convert original version string to a comment
morphVCD' errh hOut st (Version s) =
  do let s' = unlines ["Original VCD version:",s]
     writeVCD hOut [Comment s']
     return st

-- add scope level for following Vars
morphVCD' errh hOut st cmd@(Scope _ s) =
  do let scope' = s:(scope st)
         root_find' = case (root_find st) of
                        (Just rs) -> if (scope' == rs) then Nothing else (Just rs)
                        Nothing   -> Nothing
         st' = st { scope = scope', root_find = root_find' }
     writeVCD hOut [cmd]
     return st'

-- record mapping of qualified name to VCD code and width
morphVCD' errh hOut st cmd@(Var _ w c s) =
  do let s' = strip_width_brackets s
         name = intercalate "." (reverse (s':(scope st)))
         smap = M.insert name (c,w) (signal_map st)
         st' = st { signal_map = smap }
     writeVCD hOut [cmd]
     return st'

-- pop off one scope level
morphVCD' errh hOut st UpScope =
  do let scope' = tail (scope st)
         st' = st { scope = scope' }
     writeVCD hOut [UpScope]
     return st'

-- end of definitions, prepare for value changes
morphVCD' errh hOut st EndDefs =
  do let -- do sanity checks now that we know all signals, hierarchy, etc.
         checks = [found_root_scope]
         results = concat [ f st | f <- checks ]

         -- determine the largest signal code in use
         smap = signal_map st
         max_code = if (M.null smap)
                    then 0
                    else maximum (map fst (M.elems smap))

         -- locate clock signals for each domain
         cmap = clock_map st
         (clks_not_found,clks_found) = separate (map (find_clk smap) (M.toList cmap))
         -- locate signals to associate with each clock edge
         -- and conditions used to realign state transitions
         (clock_info,ci_status) = mkClockInfo clks_found max_code st
         clock_code_map = M.fromList clock_info

         -- create virtual signals for each domain
         vsigs = concat [ [ (fired,(fc,w)), (blocked,(bc,w)) ]
                        | (_,ClockSignal _ s fc bc w _ _ _) <- clock_info
                        , let fired = "FIRED_RULE_" ++ s
                        , let blocked = "BLOCKED_RULE_" ++ s
                        ]
         virtual_vars = [ Var Wire width code name
                        | (name,(code,width)) <- vsigs
                        ]

         -- record all virtual firing codes as modified
         vcode_set = S.fromList [ code | (_,(code,_)) <- vsigs ]
         modified' = (modified_set st) `S.union` vcode_set

         -- create an inverted signal map for use in error messages
         invsigmap = M.fromList [ (c,n) | (n,(c,_)) <- M.toList smap ]

         -- inform user about any cross-rule CF/WF aliases
         fire_codes = concat [ [(cfc,S.singleton rn),(wfc,S.singleton rn)]
                             | (_, cs@(ClockSignal {})) <- clock_info
                             , (cfc,wfc,rn) <- fire_signals cs
                             ]
         fire_code_map = M.fromListWith (S.union) fire_codes
         cross_rule_aliases = [ Info $ unlines $ ["The input VCD aliases CAN_FIRE/WILL_FIRE signals for these rules:"] ++
                                                 (map ("  " ++) rule_names)
                              | (_,rs) <- M.toList fire_code_map
                              , (S.size rs) > 1
                              , let rule_names = map (\rn -> M.findWithDefault "?" rn invrulemap)
                                                     (S.toList rs)
                              ]

         -- compose debugging information related to the VCD header
         invrulemap = inv_rule_map st
         debug_msg = "---- SIGNAL MAP ----\n" ++
                     (unlines [ name ++ " -> " ++ (vcd_code_to_string code) ++ " (" ++ (show width) ++ " bits)"
                              | (name,(code,width)) <- M.toList smap
                              ]) ++
                     "-------\n" ++
                     "---- VIRTUAL SIGNALS ----\n" ++
                     (unlines [ name ++ " -> " ++ (vcd_code_to_string code) ++ " (" ++ (show width) ++ " bits)"
                              | (name,(code,width)) <- vsigs
                              ]) ++
                     "-------\n" ++
                     "---- CLOCK ACTION INFO ----\n" ++
                     (unlines (concat [ [ (clk_name cs) ++ " (Domain " ++ (show dom) ++ ")"
                                        , "  fired code   = " ++ (vcd_code_to_string (fired_code cs))
                                        , "  blocked code = " ++ (vcd_code_to_string (blocked_code cs))
                                        , "  CAN_FIRE and WILL_FIRE adjustments:"
                                        ] ++
                                        cf_wf_lines ++
                                        [ "  signal realignments:" ] ++
                                        realignment_lines
                                      | (dom, cs@(ClockSignal {})) <- clock_info
                                      , let cf_wf_lines = [ "    Rule " ++ rule_name ++ " CF: " ++ cf ++ " WF: " ++ wf
                                                          | (cfc,wfc,rn) <- fire_signals cs
                                                          , let cf = vcd_code_to_string cfc
                                                          , let wf = vcd_code_to_string wfc
                                                          , let rule_name = M.findWithDefault "?" rn invrulemap
                                                          ]
                                      , let realignment_lines =
                                                concat [ [ "    Signal: " ++ (vcd_code_to_string code) ++ " " ++ sig_name] ++ cond_lines
                                                       | (code,conds) <- (realignment cs) ++ (rw_realignment cs)
                                                       , let sig_name = M.findWithDefault "?" code invsigmap
                                                       , let cond_lines =
                                                                 [ "      [" ++ (intercalate ", " exprs) ++ "] => " ++ rule_name
                                                                 | (es,rn) <- conds
                                                                 , let exprs = [ inst ++ " " ++ (init (ppReadable e)) | (inst,e) <- es ]
                                                                 , let rule_name = M.findWithDefault "?" rn invrulemap

                                                                 ]
                                                       ]
                                      ])) ++
                     "-------\n"

         -- compose info messages
         info = if (be_verbose st)
                then map Info [ "found " ++ (show (M.size smap)) ++ " signals in the VCD file"
                              , "Processing VCD data..."
                              ]
                else []
     dbg (debug_to st) debug_msg
     handleMsgs errh (results ++ clks_not_found ++ info ++
                      ci_status ++ cross_rule_aliases)
     writeVCD hOut (virtual_vars ++ [EndDefs])
     let st' = deepseq (invsigmap,clock_code_map,modified')
                     st { inv_signal_map = invsigmap
                        , code_map       = clock_code_map
                        , action_map     = M.empty   -- not needed after EndDefs
                        , modified_set   = modified'
                        }
     return st'

-- These are all VCD commands in the value change section

-- update time, scale up timestamps to accommodate microticks, and
-- handle any clock edges at the previous time
morphVCD' errh hOut st (Timestamp t) =
  do let t' = t * (10 ^ (time_factor st))
         (cmds_out,status,st') = foldl handleClkEdge ([],[],st) (edges st)
         st'' = st' { current_time = t' }
     handleMsgs errh status
     writeVCD hOut cmds_out
     return st''

-- record all signal changes associated with the task
morphVCD' errh _ st cmd@(Task s cs) =
  do let t = current_time st
         valmap = foldl (\m (c,v) -> DM.insert t c (v, InTask s) m)
                        (value_map st)
                        [ (code,val)
                        | chg <- cs
                        , let code = signal_code chg
                        , let val = new_value chg
                        ]
         st' = st { value_map = valmap }
     return st'

-- record an individual signal change and detect if this change
-- represents a clock edge we need to process at the end of this
-- time's section
morphVCD' errh _ st cmd@(Change c) =
  do let -- record signal changes
         t = current_time st
         code = signal_code c
         val  = new_value c
         valmap = DM.insert t code (val, Changed) (value_map st)
         -- detect clock edges
         cmap = code_map st
         sig = M.lookup code cmap
         posedge_clk = case sig of
                         (Just (ClockSignal {})) -> val == (Scalar (Logic True))
                         _                       -> False
         st' = if (posedge_clk && (t > 0))
               then let edges' = (code, fromJust sig):(edges st)
                    in st { value_map = valmap
                          , edges = edges'
                          }
               else st { value_map = valmap }
     return st'

-- Handle VCD errors and unknown commands

morphVCD' errh _ st (VCDErr msg input) =
  do let -- compose an error message
         emsg = msg ++ " while parsing '" ++ input ++ "'"

     handleMsgs errh [Err (noPosition, EGeneric emsg)]
     return st

morphVCD' errh hOut st cmd =
    do writeVCD hOut [cmd] -- pass command through unchanged
       return st

-- Generate progress indicator
doProgress :: ConvState -> Integer -> IO ConvState
doProgress st bytes =
  let new_bytes = (curr_bytes st) + bytes
      st' = st { curr_bytes = new_bytes }
      show_it = case (progress_at st) of
                  Just tgt -> new_bytes >= tgt
                  Nothing  -> False
  in if (show_it)
     then do (TOD s ps) <- getClockTime
             let now = (fromInteger s) + (fromInteger ps / (10.0^(12 :: Int)))
                 bytes_per_sec = (fromInteger (new_bytes - (prev_bytes st))) / (now - (prev_time st))
                 percentage = ((100 * new_bytes) + ((total_bytes st) `div` 4)) `div` (total_bytes st)
                 next_progress = ((percentage + 1) * (total_bytes st)) `div` 100
                 msg = (show percentage) ++ "% complete    (" ++
                       (show ((round bytes_per_sec) :: Integer)) ++ " bytes/sec)"
             putStrLn msg
             return $ st' { prev_time = now
                          , prev_bytes = new_bytes
                          , progress_at = Just next_progress
                          }
     else return st'

-- Auxiliary routines used during VCD conversion

-- Check that the root scope was found
found_root_scope :: ConvState -> [Status]
found_root_scope st =
    case (root_find st) of
      (Just _) -> [Err (noPosition, EGeneric $ "Failed to locate root '" ++ (root st) ++ "' in VCD hierarchy")]
      Nothing  -> []

-- Find a clock signal in the VCD hierarchy
find_clk :: SignalMap -> (Int,([String],a)) -> Either Status (String,Code,Int)
find_clk smap (n,(xs,_)) = match xs
  where match [] = Left $ Err (noPosition, EGeneric msg)
        match (s:rest) = case (M.lookup s smap) of
                           Nothing -> match rest
                           (Just (c,_)) -> Right (s,c,n)
        msg = unlines $ ["Failed to locate any clock for a domain.  Candidates were:"] ++ (map ("  " ++) xs)


-- Create a list used for realigning signals by converting the key from
-- a method identifier to a set of signal codes which can toggle in response
-- to the method call.
mkRealignment :: InstModMap -> SignalMap -> ClockMap -> RuleMap -> String ->
                M.Map (String,AMethodId) [RuleConds] ->
                (Realignment,Realignment,[Status])
mkRealignment instmap sigmap clkmap rulemap root_name m =
    let -- partition methods into RWire wsets and non-RWire methods
        (rw_meths, normal_meths) = partition ((isRWireMethod instmap) . fst) (M.toList m)

        -- convert methods to signals affected by the method
        ls = [ (codes, xs, ss)
             | (meth, xs) <- normal_meths
             , let (codes,ss) = getMethodSignals instmap sigmap root_name meth
             ]

        -- convert RWire methods to signals affected by the method
        rw_ls = [ (codes, xs, ss)
                | (meth, xs) <- rw_meths
                , let (codes,ss) = getMethodSignals instmap sigmap root_name meth
                ]

        -- permute a list of conditions so that they match the
        -- urgency order of their associated rules
        err1 name = internalError $ "Unknown rule '" ++ name ++ "'"
        err2 rn = internalError $ "Unknown rule number " ++ (show rn)
        snodes = [ M.findWithDefault (err1 name) name rulemap
                 | (Sched r) <- concatMap snd (M.elems clkmap)
                 , let name = getIdString r
                 ]
        urg_map = M.fromList $ zip snodes [(0::Integer)..]
        reorder xs = map snd $ sort [ (urg,x)
                                    | x@(_,rn) <- xs
                                    , let urg = M.findWithDefault (err2 rn) rn urg_map
                                    ]
        rmap = M.fromListWith (++) [ (code, xs)
                                   | (codes, xs, _) <- ls
                                   , code <- codes
                                   ]
        rmap' = M.map reorder rmap

        rw_rmap = M.fromListWith (++) [ (code, xs)
                                      | (codes, xs, _) <- rw_ls
                                      , code <- codes
                                      ]
        rw_rmap' = M.map reorder rw_rmap
        status = concat [ ss | (_,_,ss) <- (ls ++ rw_ls) ]
    in (M.toList rmap', M.toList rw_rmap', status)

-- Get all signals which can be modified by a call to a given method
getMethodSignals :: InstModMap -> SignalMap -> String ->
                    (String,AMethodId) -> ([Code],[Status])
getMethodSignals instmap sigmap root_name (inst,mid) =
    let err = internalError $ "Unknown instance name '" ++ inst ++ "'"
        mod = M.findWithDefault (err inst) inst instmap
    in if (isPrimitiveModule mod)
       then let meth = getIdBaseString mid
                inst' = if (null root_name)
                        then inst
                        else root_name ++ "." ++ inst
                (signals,status) = methodSignals mod meth inst'
                codes = map fst $ mapMaybe (flip M.lookup sigmap) signals
            in (codes,status)
       else ([],[])

-- Create the ClockSignal data that aggregates all information needed
-- to process a clock edge
mkClockInfo :: [(String,Code,Int)] -> Code -> ConvState -> ([(Code,Signal)],[Status])
mkClockInfo clks_found max_code st =
    let root_name = root st
        clkmap = clock_map st
        instmap = inst_map st
        smap = signal_map st
        rmap = rule_map st
        amap = action_map st
        err1 s = "no signal named '" ++ s ++ "'"
        err2 r = "no rule named '" ++ (getIdString r) ++ "'"
        errs = concat [ concat es
                      | (_,_,n) <- clks_found
                      , let (_,sns) = M.findWithDefault ([],[]) n clkmap
                      , let es = [ cf_err ++ wf_err ++ rn_err
                                 | (Exec r) <- sns
                                 , let cf = root_name `joinName` (mkIdCanFire r)
                                 , let cf_err = if (M.notMember cf smap)
                                                then [err1 cf]
                                                else []
                                 , let wf = root_name `joinName` (mkIdWillFire r)
                                 , let wf_err = if (M.notMember wf smap)
                                                then [err1 wf]
                                                else []
                                 , let rn_err = if (M.notMember (getIdString r) rmap)
                                                then [err2 r]
                                                else []
                                 ]
                      ]
        info = [ ((c,ClockSignal n s fc bc w fs ral rw_ral), ral_status)
               | ((s,c,n),x) <- zip clks_found [1,3..]
               , let fc = max_code + x
               , let bc = max_code + x + 1
               , let (_,sns) = M.findWithDefault ([],[]) n clkmap
               , let fs = [ (cf_code, wf_code, num)
                          | (Exec r) <- sns
                          , let cf = root_name `joinName` (mkIdCanFire r)
                          , let mcf = M.lookup cf smap
                          , isJust mcf
                          , let cf_code = fst (fromJust mcf)
                          , let wf = root_name `joinName` (mkIdWillFire r)
                          , let mwf = M.lookup wf smap
                          , isJust mwf
                          , let wf_code = fst (fromJust mwf)
                          , let mnum = M.lookup (getIdString r) rmap
                          , isJust mnum
                          , let num = fromJust mnum
                          ]
               -- 1-bit signals show up differently in waves, so stay > 1
               , let w = if (null fs)
                         then 2
                         else max 2 (bitWidth (maximum (map (\(_,_,n) -> n) fs)))
               -- build the realignment data for this domain
               , let (ral, rw_ral, ral_status) =
                         mkRealignment instmap
                                       smap
                                       clkmap
                                       rmap
                                       root_name
                                       (M.findWithDefault M.empty n amap)
               ]
        (clock_info,status) = unzip info
    in (clock_info,
        (concat status) ++ [ Err (noPosition, EGeneric emsg) | emsg <- errs ])

-- Process stored change data in response to the posedge of a clock
handleClkEdge :: ([VCDCmd],[Status],ConvState) -> (Code,Signal) ->
                 ([VCDCmd],[Status],ConvState)
handleClkEdge (cmds,status,st) (code,clk) =
  let now = current_time st
      -- update edge data for this clock
      pos = M.findWithDefault 0 code (clk_edge_map st)
      new_edge_map = M.insert code now (clk_edge_map st)
      -- extract clock signal information
      fc = fired_code clk
      bc = blocked_code clk
      w = virtual_width clk
      fs = fire_signals clk
      ral = realignment clk
      rw_ral = rw_realignment clk
      -- determine which rules wrote signals which need realignment
      valmap0 = value_map st
      smap = signal_map st
      instmap = inst_map st
      root_name = root st
      moddefmap = mod_def_map st
      get_val inst e =
          let pfx = case (root_name, inst) of
                      ("","") -> ""
                      (x,"")  -> x
                      ("",y)  -> y
                      (x,y)   -> x ++ "." ++ y
          in case (M.lookup inst instmap) of
               (Just mod) -> case (M.lookup mod moddefmap) of
                               (Just defmap) -> getAExprValue smap valmap0 pfx inst defmap instmap (now-1) e
                               Nothing       -> Left $ "No definitions for module " ++ mod
               Nothing    -> Left $ "Unknown instance " ++ inst
      to_bool (inst,e) = case (get_val inst e) of
                           (Right v)  -> Right (vcd_is_true_bit v)
                           (Left err) -> Left err
      writers = [ (code,fired)
                | (code,tests) <- ral
                , changed_at now code valmap0
                , let fired = [ (rn,errs)
                              | (conds,rn) <- tests
                              , let ebs = map to_bool conds
                              , let (errs,bs) = separate ebs
                              , and bs
                              ]
                ]
      rw_writers = [ (code,fired)
                   | (code,tests) <- rw_ral
                   , not (x_at pos code valmap0)
                   , let fired = [ (rn,errs)
                                 | (conds,rn) <- tests
                                 , let ebs = map to_bool conds
                                 , let (errs,bs) = separate ebs
                                 , and bs
                                 ]
                   ]

      -- add virtual signal entries for this clock domain
      dflt = (Scalar X, Stable)
      rule_values = [ (n,(cfc,cfv),(wfc,wfv))
                    | (cfc,wfc,n) <- fs
                    , let cfv = fst $ DM.findWithDefault dflt (now-1) cfc valmap0
                    , let wfv = fst $ DM.findWithDefault dflt (now-1) wfc valmap0
                    ]
      rules_of_interest = filter (\(_,(_,cf),_) -> vcd_is_true_bit cf) rule_values
      fchgs = (fc, [ if (vcd_is_true_bit wfv)
                     then to_VCDValue w rn
                     else to_X_VCDValue w
                   | (rn,_,(_,wfv)) <- rules_of_interest
                   ])
      bchgs = (bc, [ if (vcd_is_true_bit wfv)
                     then to_X_VCDValue w
                     else to_VCDValue w rn
                   | (rn,_,(_,wfv)) <- rules_of_interest
                   ])
      valmap1 = foldl (fill pos now w) valmap0 [fchgs, bchgs]
      -- rewrite CAN_FIRE/WILL_FIRE signals
      period = now - pos
      time_slots = genericLength rules_of_interest
      low = Scalar (Logic False)
      new_cf_wf = concat [ if (cfc == wfc)
                           then [ (cfc,pos,low,t0,cfv,t1,low,now) ]
                           else [ (cfc,pos,low,t0,cfv,t1,low,now)
                                , (wfc,pos,low,t0,wfv,t1,low,now)
                                ]
                         | ((_,(cfc,cfv),(wfc,wfv)),n) <- zip rules_of_interest [0..]
                         , let t0 = pos + ((period * n) `quot` time_slots)
                         , let t1 = pos + ((period * (n+1)) `quot` time_slots)
                         ]
      valmap2 = foldl contract valmap1 (combineCFWF new_cf_wf)
      -- realign signals to microtick edges
      (no_writer, maybe_writers) = partition (null . snd) (writers ++ rw_writers)
      oneWriter (_,[(_,[])]) = True
      oneWriter _            = False
      (ws, maybe_multiple) = partition oneWriter maybe_writers
      noErrs (_,xs) = all (null . snd) xs
      (multiple_writers, undetermined) = partition noErrs maybe_multiple
      get_slot_num rn = fromJust $ findIndex (\(rn',_,_) -> rn' == rn) rules_of_interest
      single_writers = [ (c, get_slot_num rn) | (c,[(rn,_)]) <- ws ]
      (_,last_multiple_writers) =
          unzip $ [ ((c, minimum ns), (c, maximum ns))
                  | (c,rs) <- multiple_writers
                  , let ns = map (get_slot_num . fst) rs
                  ]
      writers' = single_writers ++ last_multiple_writers
      invrulemap = inv_rule_map st
      invsigmap  = inv_signal_map st
      ral_status = [ Info $ "No rule identified for change in " ++
                            sig_name ++ " at time " ++ (show now)
                   | (c,_) <- no_writer
                   , let sig_name = M.findWithDefault "?" c invsigmap
                   ] ++
                   [ Info $ "Multiple rules wrote to " ++ sig_name ++
                            " at time " ++ (show now) ++": " ++
                            (intercalate ", " rule_names)
                   | (c,rinfo) <- multiple_writers
                   , let sig_name = M.findWithDefault "?" c invsigmap
                   , let rule_names = [ M.findWithDefault "?" rn invrulemap
                                      | (rn,_) <- rinfo
                                      ]
                   ] ++
                   [ Info $ "Unable to determine which rule(s) changed " ++
                            sig_name ++ " at time " ++
                            (show now) ++ ": " ++
                            (intercalate "; " err_msgs)
                   | (c,rinfo) <- undetermined
                   , let sig_name = M.findWithDefault "?" c invsigmap
                   , let err_msgs = [ "For rule " ++ rule_name ++ ": " ++
                                      (intercalate ", " errs)
                                    | (rn,errs) <- rinfo
                                    , let rule_name = M.findWithDefault "?" rn invrulemap
                                    ]
                   ]
      rw_codes = S.fromList (map fst rw_writers)
      valmap3 = foldl (realign pos now time_slots rw_codes) valmap2 writers'
      -- update the set of modified signals
      mods = S.fromList $ concat [ if (cfc == wfc) then [cfc] else [cfc,wfc]
                                 | (_,(cfc,_),(wfc,_)) <- rules_of_interest
                                 ] ++
                          (map fst writers')
      new_mod_set = (modified_set st) `S.union` mods
      -- possibly flush VCD data prior to previous edge of this clock
      (new_cmds,new_status,new_st) =
          deepseq new_mod_set $
          flushChanges $ st { clk_edge_map = new_edge_map
                            , value_map    = valmap3
                            , edges        = []
                            , modified_set = new_mod_set
                            }

      -- compose a debugging message
      cond_records = [ [ "  For signal " ++ (vcd_code_to_string code) ++ " " ++ sig_name ] ++
                       [ "   " ++ (if ok then "* [" else "  [") ++
                         (intercalate ", " vals) ++ "] => " ++ rule_name
                       | (xs, rn) <- cond_values
                       , let ok = and [ b
                                      | ebs <- map snd xs
                                      , let b = case ebs of
                                                  (Left err) -> False
                                                  (Right x)  -> x
                                      ]
                       , let vals = [ inst ++ " " ++ (init (ppReadable e)) ++ " (" ++ desc ++ ")"
                                    | ((inst,e),ebs) <- xs
                                    , let desc = case ebs of
                                                   (Left err) -> err
                                                   (Right b)  -> show b
                                    ]
                       , let rule_name = M.findWithDefault "?" rn invrulemap
                       ]
                     | (code,tests) <- ral
                     , changed_at now code valmap0
                     , let cond_values = [ (zip conds bs, rn)
                                         | (conds,rn) <- tests
                                         , let bs = map to_bool conds
                                         ]
                     , let sig_name = M.findWithDefault "?" code invsigmap
                ]

      debug_msg = "---- PROCESSED " ++ (show (clk_domain clk)) ++ " CLOCK EDGE AT TIME " ++ (show now) ++ " ----\n" ++
                  (show rule_values) ++ "\n" ++
                  "CONDITIONS:\n" ++
                  (unlines (concat cond_records)) ++
                  "REALIGNMENT STATUS:" ++ "\n" ++
                  (unlines (map (\x -> "  " ++ (show x)) ral_status))
  in dbg_trace (debug_to new_st)
               debug_msg
               (cmds ++ new_cmds, status ++ ral_status ++ new_status, new_st)

-- flush value changes that are in their final form
flushChanges :: ConvState -> ([VCDCmd],[Status],ConvState)
flushChanges st =
  let -- find the current flush limit
      limit = minimum (M.elems (clk_edge_map st))
      -- split out all value changes below the limit
      (flush,keep) = DM.split limit (\(v,_) -> (v,Stable)) (value_map st)
      st' = st { value_map = keep }
      -- convert flushed changes to VCD commands
      chgs = M.fromListWith (M.unionWith S.union)
                            [ (t, M.singleton r (S.singleton (c,v)))
                            | (t,c,(v,r)) <- DM.toList flush
                            ]
      mkCmds (Changed,set) = map Change (S.toList set)
      mkCmds (InTask s,set) = [Task s (S.toList set)]
      mkCmds (Stable,_) = []
      cmds = concat [ (Timestamp t):(concatMap mkCmds (M.toList map))
                    | (t,map) <- M.toAscList chgs
                    ]
      info = []
  in (cmds, info, st')

-- Print the messages from the conversion stream
handleMsgs :: ErrorHandle -> [Status] -> IO ()
handleMsgs errh status =
  do let errs  = [ e | (Err e) <- status ]
         warns = [ w | (Warn w) <- status ]
         msgs  = [ s | (Info s) <- status ]
     when (not (null msgs))  $ mapM_ putStrLn msgs
     when (not (null warns)) $ bsWarning errh warns
     when (not (null errs))  $ bsErrorNoExit errh errs
     return ()

-- Handle termination of VCD data
endOfVCD :: ErrorHandle -> Handle -> ConvState -> IO ()
endOfVCD errh hOut s =
  do let t = (current_time s) + 1
         new_edge_map = M.map (const t) (clk_edge_map s)
         (cmds,status,_) = flushChanges (s { clk_edge_map = new_edge_map })
     handleMsgs errh status
     writeVCD hOut cmds

-- -------------------------------------------------------------------
-- Novas command generation

formatNovas :: ConvState -> String
formatNovas st =
  let -- Build an alias table of names for rule numbers.
      -- Shorten names to keep only enough suffix to uniquely identify rule.
      rmap = rule_map st
      full_names = [ (n, x, xs)
                   | (s,n) <- M.toList rmap
                   , let (x, xs) = unconsOrErr "formalNovas: full_names" $
                                     reverse (wordsBy (=='.') s)
                   ]
      lengthen n name [] = internalError "duplicate keys in map!?!?"
      lengthen n name (x:xs) = (n, x ++ "." ++ name, xs)
      try_to_add m [] = m
      try_to_add m ((n,name,dropped):rest) =
          case (M.lookup name m) of
            (Just (Just (n',dropped'))) -> -- collision
                let m' = M.insert name Nothing m
                    x1 = lengthen n name dropped
                    x2 = lengthen n' name dropped'
                in try_to_add m' (x1:x2:rest)
            (Just Nothing) -> -- multiple collision
                let x = lengthen n name dropped
                in try_to_add m (x:rest)
            Nothing -> -- no collision
                let m' = M.insert name (Just (n,dropped)) m
                in try_to_add m' rest
      abbrev_map = try_to_add M.empty full_names
      rule_tbl = unlines $ [ "# Setup rule name alias table"
                           , "wvAddAliasTable -table RuleNames"
                           ] ++
                           [ "wvAddAliasTable -table RuleNames -row " ++ s ++ " " ++ (show n)
                           | (s, Just (n,_)) <- M.toList abbrev_map
                           ]
      -- Add virtual signals to alias map
      sigs = M.toList (code_map st)
      alias_map = unlines $ [ "# Add aliases for virtual signals" ] ++
                            [ "set aliases(" ++ (toNovas s) ++ ") RuleNames"
                            | (_,ClockSignal { clk_name = name }) <- sigs
                            , s <- [ "\\FIRED_RULE_" ++ name ++ " "
                                   , "\\BLOCKED_RULE_" ++ name ++ " "
                                   ]
                            ]
      -- Add color entries for signals to the color map
      code_list = [ (s,c) | (s,(c,_)) <- M.toList (signal_map st) ]
      color_map = unlines $ [ "# Add color entries for signals" ] ++
                            [ "set colors(" ++ (toNovas s) ++ ") " ++ (fromJust color)
                            | (s,c) <- code_list
                            , let color = choose_sig_color st c
                            , isJust color
                            ]
  in rule_tbl ++ "\n" ++
     alias_map ++ "\n" ++
     color_map ++ "\n" ++
     add_signal_callback

-- Convert a signal name to Novas TCL format
toNovas :: String -> String
toNovas s@('\\':_) = '/':(esc s)
toNovas s          = '/':((esc . dotToSlash) s)

esc :: String -> String
esc = concatMap (\c -> if (c `elem` " $\\") then ['\\',c] else [c])

dotToSlash :: String -> String
dotToSlash = map (\c -> if (c == '.') then '/' else c)

-- Boilerplate common to all command scripts
add_signal_callback :: String
add_signal_callback = unlines $
  [ "# Setup event callback for setting signal properties"
  , "proc sigCB args {"
  , "    upvar aliases  aliases"
  , "    upvar colors   colors"
  , ""
  , "    # Get the list of signals being added"
  , "    set nargs [llength $args]"
  , "    set signals [lrange $args 4 [expr $nargs - 1]]"
  , ""
  , "    # Record the current selection set"
  , "    set selected [wvGetSelectedSignals]"
  , ""
  , "    # Consider each signal in turn"
  , "    foreach sig $signals {"
  , ""
  , "        # Set alias if one is specified"
  , "        if {[info exists aliases($sig)]} {"
  , "           wvDeselectAll"
  , "           wvSelectSignal $sig"
  , "           wvSetAliasTable -table $aliases($sig)"
  , "        }"
  , ""
  , "        # Set color if one is specified"
  , "        if {[info exists colors($sig)]} {"
  , "           wvDeselectAll"
  , "           wvSelectSignal $sig"
  , "           wvChangeDisplayAttr -color $colors($sig)"
  , "        }"
  , ""
  , "    }"
  , ""
  , "    # Restore the original selection"
  , "    wvSelectSignal $selected"
  , "}"
  , ""
  , "# Add the callback to handle signal adds"
  , "AddEventCallback [tk appname] sigCB wvAddSignal 1"
  ]


choose_sig_color :: ConvState -> Code -> Maybe String
choose_sig_color st code =
    let is_modified = S.member code (modified_set st)
        sig         = M.lookup code (code_map st)
        is_clock    = case sig of
                        (Just (ClockSignal {})) -> True
                        _                       -> False
    in if (is_modified || is_clock)
       then Nothing
       else Just "slategray"

-- -------------------------------------------------------------------
-- ValueMap manipulation functions

-- Test if there is a change at a particular time
changed_at :: Integer -> Code -> ValueMap -> Bool
changed_at t code valmap =
    case (DM.lookup t code valmap) of
      (Just (t',_)) -> (t == t')
      Nothing       -> False

-- Test if a value was X at a particular time
x_at :: Integer -> Code -> ValueMap -> Bool
x_at t code valmap =
    case (DM.lookup t code valmap) of
      (Just (_,(v,_))) -> vcd_is_x v
      Nothing          -> False

-- Given a time interval and a list of values for a code,
-- fill the interval in the value map with evenly spaced transitions
-- to each value in the list.  If the list if empty, the interval is
-- filled with an X value of the specified width.
fill :: Integer -> Integer -> Integer -> ValueMap -> (Code,[VCDValue]) -> ValueMap
fill t0 t1 width m (code,vs) =
    let slots = genericLength vs
        period = t1 - t0
        chgs = if (slots == 0)
               then [ (t0,(to_X_VCDValue width,Changed)) ]
               else [ (t,(v,Changed))
                    | (v,n) <- zip vs [0..]
                    , let t = t0 + ((period * n) `quot` slots)
                    ]
        chgs' = dropRepeatsBy (\(_,(v1,_)) (_,(v2,_)) -> v1 == v2) chgs
    in DM.adjust (M.union (M.fromList chgs')) code m

-- Shrink the duration of a a signal to a portion of the clock cycle,
-- filling in the gaps before and after the shrunken interval with
-- default values.
contract :: ValueMap ->
            (Code,Integer,VCDValue,Integer,VCDValue,Integer,VCDValue,Integer) ->
            ValueMap
contract m (c,t0,v_pre,t0',v,t1',v_post,t1) =
    DM.adjust (fixup (t0,v_pre,t0',v,t1',v_post,t1)) c m

fixup :: (Integer,VCDValue,Integer,VCDValue,Integer,VCDValue,Integer) ->
         M.Map Integer (VCDValue,ChangeReason) ->
         M.Map Integer (VCDValue,ChangeReason)
fixup (t0,v_pre,t0',v,t1',v_post,t1) m =
    let -- determine the value at the beginning of the interval
        -- and prior to the start of the interval
        c = M.lookupLE t0 m
        (val_before,at) = case c of
                            Nothing -> (Nothing,Nothing)
                            Just (t,v) | t == t0 -> (M.lookupLE (t0-1) m, Just v)
                                       | otherwise -> (c,Nothing)
        -- determine the value we want at t0
        t0_val = if (t0' == t0) then v else v_pre
        -- decide what to do at t0
        --   + if there is already a change at t0 to the correct value,
        --     we should keep it
        --   + if there is a previous value and it is the same as t0_val,
        --     then we don't need any change at t0
        --   + otherwise, we should add a new change to t0_val at t0
        (del_t0,t0_chg) = case at of
                            (Just val@(x,r)) | x == t0_val -> (False,Nothing)
                            (Just _) -> case val_before of
                                          (Just (_,(x,_))) | x == t0_val -> (True,Nothing)
                                          _ -> (True, Just (t0,(t0_val,Changed)))
                            Nothing ->  case val_before of
                                          (Just (_,(x,_))) | x == t0_val -> (False,Nothing)
                                          _ -> (False, Just (t0,(t0_val,Changed)))
        -- determine if we need a change at t0'
        t0'_chg = if ((t0' == t0) || (t0_val == v))
                  then Nothing
                  else Just (t0',(v,Changed))
        -- determine if we need a change at t1'
        t1'_chg = if ((v == v_post) || (t1' == t1))
                  then Nothing
                  else Just (t1',(v_post,Changed))
        -- determine if we need to restore the value at t1 (so that
        -- lookups will see the correct value as if it hadn't been
        -- contracted).
        t1_chg = if ((v == v_post) || (t1' == t1))
                 then Nothing
                 else Just (t1,(v,Changed))
        -- update the map to reflect the changes
        chgs = catMaybes [t0_chg, t0'_chg, t1'_chg, t1_chg]
        m' = (if del_t0 then M.delete t0 m else m) `M.union` (M.fromList chgs)
    in m'

-- Realign an edge at given time (if it exists) to another point
realign :: Integer -> Integer -> Integer -> S.Set Code ->
           ValueMap -> (Code,Int) -> ValueMap
realign _ _ 0 _ vmap _ = vmap
realign t0 t1 slots rwires vmap (c,n) =
    let t = t0 + (((t1 - t0) * (fromIntegral (n+1))) `div` slots)
        move_from = if (c `S.member` rwires) then t0 else t1
        move_edge m = case (M.lookup move_from m) of
                        (Just x) -> M.insert t x (M.delete move_from m)
                        Nothing  -> m
    in DM.adjust move_edge c vmap


-- Some simulators will generate VCD aliases in which CF/WF signals for
-- different rules use the same VCD signal code because they always
-- fire together.  This can lead to the same code appearing multiple times
-- in the CF/WF contraction list with different areas for each of the
-- rule aliases.  This routine is used to modify the CF/WF contraction
-- list so that these shared codes do not interfere with each other.
combineCFWF :: [(Code,Integer,VCDValue,Integer,VCDValue,Integer,VCDValue,Integer)] ->
               [(Code,Integer,VCDValue,Integer,VCDValue,Integer,VCDValue,Integer)]
combineCFWF cl =
    let get_code (c,_,_,_,_,_,_,_) = c
        cl' = sortBy (\x y -> (get_code x) `compare` (get_code y)) cl
        groups = groupBy (\x y -> (get_code x) == (get_code y)) cl'
        splice [x] = [x]
        splice xs  = let (starts,stops) = unzip [ (t0',t1')
                                                | (_,_,_,t0',_,t1',_,_) <- xs
                                                ]
                     in map (adjust_ends starts stops) xs
        adjust_ends starts stops (c,t0,v_pre,t0',v,t1',v_post,t1) =
            let before_t0' = filter (<t0') stops
                after_t1'  = filter (>t1') starts
                new_t0 = if (null before_t0')
                         then t0
                         else maximum before_t0'
                new_t1 = if (null after_t1')
                         then t1
                         else minimum after_t1'
            in (c,new_t0,v_pre,t0',v,t1',v_post,new_t1)
    in concat (map splice groups)

-- -------------------------------------------------------------------
-- Evaluating AExprs using VCD value

-- Get an Integer value associated with a signal, if there is one
lookupId :: SignalMap -> ValueMap -> Integer -> String -> AId -> Maybe Integer
lookupId smap vmap at pfx i =
    let name = case (getIdQualString (addToQual pfx i)) of
                 "" -> getIdBaseString i
                 s  -> s ++ "." ++ (getIdBaseString i)
    in do (code,_) <- M.lookup name smap
          (_,(val,_)) <- DM.lookup at code vmap
          vcd_to_integer val

-- Get the AExpr value associated with an identifier, if there is one
lookupAExpr :: String -> DefMap -> AId -> Maybe AExpr
lookupAExpr pfx defmap i =
    do let i' = setIdQualString i ""
       def <- M.lookup i' defmap
       return (adef_expr def)

-- Get a list of alternative AExprs in which to look for the value
-- of a method call.
lookupMeth :: String -> InstModMap -> (AId,AId) -> [AId]
lookupMeth pfx instmap (oid,mid) =
    let name = getIdString oid
        inst = if (null pfx)
               then name
               else pfx ++ "." ++ name
        meth = getIdBaseString mid
    in case (M.lookup inst instmap) of
         (Just mod) ->
             if (isPrimitiveModule mod)
             then map to_id (resolveMethodValue mod meth name)
             else []
         Nothing    -> []

-- Compute the value of an AExpr at a given time
getAExprValue :: SignalMap -> ValueMap -> String -> String ->
                 DefMap -> InstModMap -> Integer -> AExpr ->
                 Either String VCDValue
getAExprValue smap vmap pfx pfx_noroot defmap instmap at e =
    let valfn  = lookupId smap vmap at pfx
        exprfn = lookupAExpr pfx defmap
        methfn = lookupMeth pfx_noroot instmap
    in case (aType e) of
         (ATBit n) -> case (evalAExprToInteger valfn exprfn methfn e) of
                        (Right x)  -> Right $ to_VCDValue x n
                        (Left msg) -> Left msg
         _ -> Left "Cannot reconstruct non-bit types"

-- -------------------------------------------------------------------
-- Routines describing primitive module behaviors

isRWireMethod :: InstModMap -> (String,AMethodId) -> Bool
isRWireMethod instmap (inst,mid) =
    let err = internalError $ "Unknown instance name '" ++ inst ++ "'"
        mod = M.findWithDefault (err inst) inst instmap
        meth = getIdBaseString mid
    in (meth == "wset") &&
       ((mod == "RWire") || (mod == "RWire0")) &&
       (isPrimitiveModule mod)

-- Get the set of signals which might be changed due to an
-- Action method call on a primitive module.
methodSignals :: String -> String -> String -> ([String],[Status])
methodSignals "RegN"         "write" inst = ([inst],[])
methodSignals "RegUN"        "write" inst = ([inst],[])
methodSignals "RegA"         "write" inst = ([inst],[])
methodSignals "RWire"        "wset"  inst = ([inst],[])
methodSignals "RWire0"       "wset"  inst = ([inst],[])
methodSignals "SyncRegister" "write" inst = ([],[])
methodSignals "RegFile"      "upd"   inst = ([],[])
methodSignals "RegFileLoad"  "upd"   inst = ([],[])
methodSignals mod "enq"   inst | isFIFO mod = (map (inst ++) [".FULL_N",".EMPTY_N",".D_OUT"],[])
methodSignals mod "deq"   inst | isFIFO mod = (map (inst ++) [".FULL_N",".EMPTY_N",".D_OUT"],[])
methodSignals mod "clear" inst | isFIFO mod = (map (inst ++) [".FULL_N",".EMPTY_N",".D_OUT"],[])
methodSignals s m _ = ([],[Warn (noPosition, EGeneric $ "Unknown primitive Action method '" ++ s ++ "." ++ m ++ "'")])

-- Get a list of alternative signals for a value method call
-- on a primitive module.
resolveMethodValue :: String -> String -> String -> [String]
resolveMethodValue "RegN"         "read"      inst = [inst]
resolveMethodValue "RegUN"        "read"      inst = [inst]
resolveMethodValue "RegA"         "read"      inst = [inst]
resolveMethodValue "RWire"        "wget"      inst = [inst]
resolveMethodValue "RWire"        "whas"      inst = []
resolveMethodValue "RWire0"       "whas"      inst = [inst]
resolveMethodValue "SyncRegister" "RDY_write" inst = [inst ++ ".sRDY"]
resolveMethodValue "SyncRegister" "read"      inst = [inst ++ ".dD_OUT"]
resolveMethodValue mod "first" inst | isFIFO mod   = [inst ++ ".D_OUT"]
resolveMethodValue s m _ = internalError $ "Unknown primitive value method '" ++ s ++ "." ++ m ++ "'"

-- -------------------------------------------------------------------
-- Utility functions

ilog1000 :: Integer -> Integer
ilog1000 n = helper n 1 0
  where helper n x r = if (n <= x) then r else helper n (1000*x) (r+3)

bitWidth :: Integer -> Integer
bitWidth 0 = 1
bitWidth 1 = 1
bitWidth n = 1 + (bitWidth (n `quot` 2))

joinName :: String -> Id -> String
joinName "" i = getIdString i
joinName q  i = q ++ "." ++ (getIdString i)

getClkName :: String -> AClock -> Maybe String
getClkName "" clk = case (aclock_osc clk) of
                      (ASPort _ i) -> Just (getIdString i)
                      _            -> Nothing
getClkName root_name clk = case (aclock_osc clk) of
                             (ASPort _ i) -> Just (root_name ++ "." ++ (getIdString i))
                             _            -> Nothing

-- Convert a CondTree's CAN_FIRE conditions to WILL_FIRE conditions
cf_to_wf :: CondTree (String,AExpr) a -> CondTree (String,AExpr) a
cf_to_wf = map_cond conv_cf
    where conv_cf (inst,(ASDef t i)) | isIdCanFire i =
             (inst,ASDef t (mkIdWillFire (dropCanFirePrefixId i)))
          conv_cf c = c

-- Remove a width specifier in brackets ([7:0]) from a signal name
strip_width_brackets :: String -> String
strip_width_brackets s = takeWhile (/= '[') s

-- Turn a string into an AId
to_id :: String -> AId
to_id "" = emptyId
to_id s = let segs = wordsBy (=='.') s
              qual = intercalate "." (init segs)
              base = last segs
          in setIdQualString (mk_homeless_id base) qual

-- Write to a debug log, if one is active
dbg :: (Maybe Handle) -> String -> IO ()
dbg Nothing    _ = return ()
dbg (Just hdl) s = do hPutStr hdl s
                      hFlush hdl

-- Like dbg, but used in non-IO context (uses unsafePerformIO)
{-# NOINLINE dbg_trace #-}
dbg_trace :: (Maybe Handle) -> String -> a -> a
dbg_trace Nothing    _ x = x
dbg_trace (Just hdl) s x = unsafePerformIO $ do hPutStr hdl s
                                                hFlush hdl
                                                return x

-- ---------------
-- NFData instances

instance NFData Signal where
  rnf (ClockSignal d n fc bc vw fs r rw) = rnf8 d n fc bc vw fs r rw
  rnf CFSignal = ()
  rnf WFSignal = ()
