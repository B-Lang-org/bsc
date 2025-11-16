{-# LANGUAGE ScopedTypeVariables, ForeignFunctionInterface, CPP #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-binds -fno-warn-unused-matches #-}

-- Blue Tcl Shell
{-
-- TODO
   - Commands
-}

module BlueTcl where


import HTcl

import Control.Monad(foldM, when, mzero)
import Control.Monad.Trans(lift)
import Control.Monad.Except(ExceptT, runExceptT, throwError)
import Control.Concurrent
import qualified Control.Exception as CE
import System.IO.Error(ioeGetErrorString)
import Data.IORef
import Data.Word(Word64)
import Data.List(find, nub, partition, sort, sortBy, intercalate, isPrefixOf,
                 groupBy, intersect, nubBy, group, elemIndex)
import Data.Maybe
import Data.Ord(comparing)
import System.IO.Unsafe(unsafePerformIO)
import System.Environment(getEnv)
import System.Mem(performGC)
import System.Posix.Signals
import Text.Regex
import Data.Generics (listify)
import qualified Data.Map as M

-- Bluespec imports
import Util(quote, concatMapM, concatUnzip3, lastOrErr, fromJustOrErr,
            thd, readOrErr)
import IOUtil(getEnvDef)

import Util(mapFst, mapSnd)
import TclUtils
import GHCPretty()

import Version
import BuildVersion
import Classic
import Flags(Flags(..), verbose)
import FlagsDecode(defaultFlags, decodeFlags, adjustFinalFlags, updateFlags,
                   showFlagsLst, showFlagsAllLst, getFlagValueString)
import Error(internalError, EMsg, ErrMsg(..), showErrorList,
             ErrorHandle, initErrorHandle, convExceptTToIO)
import Id
import PPrint
import PFPrint
import FileNameUtil

import PreIds(idIsModule, idInout_, idClock, idReset, idInout,
              idPreludeRead, idPreludeWrite,
              idReg, id_read, id_write, idRWire, idWHas, idWGet, idWSet,
              idPulseWire, idSend, idFIFO, idFIFOF, idEnq, idDeq, idFirst,
              id_notFull, id_notEmpty)
import PreStrings(fsEmpty, fsLoop, fsBody)
import CSyntax
import CType
import Pred(Qual(..), expandSyn)
import ISyntax
import ISyntaxUtil(itBool, itClock, itReset)
import ASyntax
import ASyntaxUtil
import Pragma
import AScheduleInfo
import AUses(MethodId(..))
import VModInfo
import ADumpSchedule
import BackendNamingConventions

import TclParseUtils

import SymTab
import MakeSymTab
import Position(cmdPosition, noPosition)
import FStringCompat(mkFString, concatFString)
import TypeAnalysis
import TypeAnalysisTclUtil

import ABin
import ABinUtil
import BinUtil(BinMap, BinFile, HashMap, readBin, sortImports)
import ForeignFunctions(ForeignFuncMap)
import SimPrimitiveModules(isPrimitiveModule)
import SimCCBlock(SimCCBlock(..), primBlocks)
import PreStrings(fsPrelude, fsUnderscore)
import GlobPattern

import BluesimLoader
import Depend(genDepend,genFileDepend,chkDeps)
import InstNodes(InstNode(..), InstTree, isHidden, isHiddenKP, isHiddenAll, nodeChildren, comparein)
-- import Debug.Trace

-------------------------------------
foreign export ccall "blueshell_Init_Foreign" blueshell_Init :: TclInterp -> IO Int

--  1st call to haskell world (run time system has already been setup)
blueshell_Init :: TclInterp -> IO Int
blueshell_Init interp =
  let handler :: CE.IOException -> IO Int
      handler e = htcl_AddObjErrorInfo interp (ioeGetErrorString e)
                    >>= return . fromEnum
  in  CE.catch
         (do
             initTclPackage
             -- register commands
             _ <- htclRegCommands interp tclCommands
             -- setup a Ctrl-C handler
             mv <- newEmptyMVar
             _ <- forkIO (handleCtrlC mv)
             _ <- installHandler sigINT (Catch $ recordCtrlC mv) Nothing
             --
             -- syntax defaults to CLASSIC otherwise
             setSyntax BSV
             return 0)          -- TCL_OK
         handler

handleCtrlC :: MVar () -> IO ()
handleCtrlC mv = do _ <- takeMVar mv
                    putStrLn "Got Ctrl-C!"
                    handleCtrlC mv

recordCtrlC :: MVar () -> IO ()
recordCtrlC mv = do putStrLn "recording Ctrl-C..."
                    _ <- tryPutMVar mv ()
                    return ()

returnIO :: a -> IO a
returnIO = return

namespace :: String
namespace = "::Bluetcl"

-- List of all tcl commands provided by this module
tclCommands :: [HTclCmdDesc]
tclCommands =
    [ htclMakeCmdDesc showArgGrammar  showArgCmd
    , HTclCmdDesc helpGrammar (htclRawFnToTclCmd helpCmd)
    , htclMakeCmdDesc versionGrammar  versionNum
    , htclMakeCmdDesc syntaxGrammar   syntaxCmd
    , htclMakeCmdDesc flagsGrammar    tclFlags
    , htclMakeCmdDesc packageGrammar  tclPackage
    , htclMakeCmdDesc defsGrammar     tclDefs
    , htclMakeCmdDesc parseGrammar    tclParse
    , htclMakeCmdDesc typeGrammar     tclType
    , htclMakeCmdDesc moduleGrammar   tclModule
    , htclMakeCmdDesc scheduleGrammar tclSchedule
    , htclMakeCmdDesc submodGrammar   tclSubmodule
    , htclMakeCmdDesc ruleGrammar     tclRule
    , htclMakeCmdDesc debugGrammar    tclDebug
    , htclMakeCmdDesc bpackGrammar    tclBPack
    , htclMakeCmdDesc bmodGrammar     tclBMod
    , htclMakeCmdDesc btypeGrammar    tclBType
    , htclMakeCmdDesc simGrammar      tclSim
    , htclMakeCmdDesc dependGrammar   tclDepend
    , htclMakeCmdDesc binstGrammar    tclBrowseInst
    ]
-- NOTE   If you want the command exported out of the Bluetcl namespace add
-- export statement to /src/lib/tcllib/bluespec/bluespec.tcl


-----------------------
-- global data -- a TCL package
data TclP = TclP { tp_flags    :: Flags
                 , tp_binmap   :: !(BinMap Id)
                 , tp_hashmap  :: !HashMap
                 , tp_symtab   :: !SymTab
                 , tp_cpack    :: !CPackage
                 , tp_mods     :: !(Maybe ModInfo)
                 , tp_packView :: !(ExpandInfoBag BPackView)
                 , tp_modView  :: !(ExpandInfoBag BModView)
                 , tp_typeView :: !( [(CType, TypeAnalysis)]
                                  , ExpandInfoBag BTypeView )
                 , tp_instView :: !(ExpandInfoBag BInst)
                 , tp_bluesim  :: (Maybe BluesimModel)
                 }

instance Show TclP where
    show p = ( "{ TclP: "
               ++ "{ Imports: " ++ show (M.toList (tp_binmap p)) ++ "}"
               ++ "}" )

initState ::  TclP
initState =
    let
        pid = mk_homeless_id "BlueTcl"
    in TclP { tp_flags    = defaultFlags ""
            , tp_binmap   = M.empty
            , tp_hashmap  = M.empty
            , tp_symtab   = emptySymtab
            , tp_cpack    = (CPackage pid (Right []) [] [] [] [] [])
            , tp_mods     = Nothing
            , tp_packView = initExpandInfoBag
            , tp_modView  = initExpandInfoBag
            , tp_typeView = ([], initExpandInfoBag)
            , tp_instView = initExpandInfoBag
            , tp_bluesim  = Nothing
            }

-- -----

type ModInfo =
    (Id, -- topmodId
     HierMap,
     InstModMap,
     ForeignFuncMap,
     [String],
     [(String, ABinEitherModInfo)]    -- loaded ba files
    )

-- -----

lookupImport :: String -> IO (BinFile Id)
lookupImport pnm = do
  g <- readIORef globalVar
  case (M.lookup pnm (tp_binmap g)) of
    Just res -> return res
    Nothing -> lookupError "Package" pnm

ip_id :: BinFile Id -> Id
ip_id (_, _, _, ipkg, _) = ipkg_name ipkg

ip_path :: BinFile Id -> String
ip_path (fname, _, _, _, _) = (dirName fname) ++ "/"

ip_csig :: BinFile Id -> CSignature
ip_csig (_, _, bo_sig, _, _) = bo_sig

ip_ipkg :: BinFile Id -> IPackage Id
ip_ipkg (_, _, _, ipkg, _) = ipkg

-- return the imports in a sorted order (the dependency order in cpack)
-- so that "bpackage" commands return results in a consistent order
getImportsSorted :: IO [BinFile Id]
getImportsSorted = do
  imp_names <- getImportNamesSorted
  mapM lookupImport imp_names

getImportNamesSorted :: IO [String]
getImportNamesSorted = do
  g <- readIORef globalVar
  let (CPackage _ _ _ impsigs _ _ _) = tp_cpack g
      -- report the packages in reverse dependency order
      imp_names = reverse $ [ iname | (CImpSign iname _ _) <- impsigs ]
  return imp_names

-- -----

getGFlags :: IO (Flags)
getGFlags = readIORef globalVar >>= (return . tp_flags)

initTclPackage :: IO ()
initTclPackage = do
  let handler :: CE.IOException -> IO String
      handler e = ioError $ userError "BLUESPECDIR environment is not set."
  bsdir <- CE.catch (getEnv "BLUESPECDIR" ) handler

  bscopts <- getEnvDef "BSC_OPTIONS" ""
  flags <- updateFlags globalErrHandle cmdPosition (words bscopts) $ defaultFlags bsdir

  btopts <- getEnvDef "BLUETCL_OPTIONS" ""
  flags' <- updateFlags globalErrHandle  cmdPosition (words btopts) flags

  modifyIORef globalVar (\g -> g { tp_flags = flags' } )

{-# NOINLINE globalVar #-}
globalVar :: IORef TclP
globalVar = unsafePerformIO $ newIORef (initState)

{-# NOINLINE globalErrHandle #-}
globalErrHandle :: ErrorHandle
globalErrHandle = unsafePerformIO $ initErrorHandle

-------------------

showArgGrammar :: HTclCmdGrammar
showArgGrammar = (tclcmd "showArg" namespace helpStr "") .+.
                 (atLeast 1 (arg "arg" StringArg ""))
    where helpStr = "Describes the arguments of the command"

showArgCmd :: [String] -> IO ()
showArgCmd args = do _ <- foldM printer 0 args
                     return ()
    where printer :: Int -> String -> IO Int
          printer cnt s = do putStrLn $ show (cnt+1) ++ ": \"" ++ s ++ "\""
                             return $ cnt + 1

--------------------------------------------------------------------------------

helpGrammar :: HTclCmdGrammar
helpGrammar = (tclcmd "help" namespace helpStr longHelpStr) .+.
              (optional $ oneOf [arg "command" StringArg "command name"
                                , kw "list" "List commands" ""
                                ])
    where helpStr = "Get help on available commands"
          longHelpStr = init $ unlines
                        [ "Help with no arguments will list all available help topics."
                        , "Optionally, an argument can be provided to get help on a specific topic."
                        , "Also, 'help list' will return a string listing the names of all commands."
                        , ""
                        , "Examples:"
                        , "  help"
                        , "  help module"
                        , "  help {flags show}"
                        , "  help list"
                        ]

-- Note: the helpCmd is different from other commands, since it
-- is used "raw".  It takes TCL objects directly so that is can
-- make use of the grammar checking machinery.
helpCmd :: TclInterp -> [TclObj] -> IO String
helpCmd _ [_] =
    let cmds = sortBy (\x y -> compare (htclCmdName x) (htclCmdName y)) tclCommands
        cleanup ('_':rest) = rest
        cleanup x          = x
    in return $ init $ unlines $
       [ "Available commands:" ] ++
       [ "  " ++ name ++ desc
       | c <- cmds
       , (htclCmdName c) /= "debug"
       , let name = take 15 $ (cleanup (htclCmdName c)) ++ (repeat ' ')
       , let desc = htclGrammarShortDesc (grammar c)
       ] ++
       [ ""
       , "Use 'help <command>' to get help on a specific command."
       ]
----------
helpCmd interp [_,cmd] = do
  objs <- htclObjToList interp cmd
  case objs of
    [] -> return "Use 'help' to see available commands."
    (co:aos) -> do cname <- htclObjToString interp co
                   if ((cname == "list") && (null aos))
                    then let cmds = sortBy (\x y -> compare (htclCmdName x) (htclCmdName y)) tclCommands
                         in return $ intercalate " " $ map htclCmdName cmds
                    else let c = find (\d -> cname == (htclCmdName d)) tclCommands
                         in case c of
                              (Just cd) -> show_help cd (co:aos)
                              Nothing -> return $ init $ unlines $
                                         [ "There is no command named '" ++ cname ++ "'"
                                         , ""
                                         , "Use 'help' to see available commands."
                                         ]
    where show_help c os =
            do (matched, ws', g) <- htclMatchGrammar interp os (grammar c)
               let isArg (_,(Argument _ _ _))  = True
                   isArg _                     = False
                   isKW (Just (Keyword _ _ _)) = True
                   isKW _                      = False
                   isKWorNone Nothing          = True
                   isKWorNone e                = isKW e
                   matched' = dropWhile isArg matched
                   cmd_words = map fst (reverse matched')
               let cmd_objs = take (length cmd_words) os
                   prefix = unwords $ cmd_words
               (_, _, g') <- htclMatchGrammar interp cmd_objs (grammar c)
               let (sd,ld) = head $ [ (d,l)
                                      | (_,(Keyword _ d l)) <- matched'
                                    , not (null d)
                                    ] ++  [ (d,l)
                                      | (_,(Command _ d l _)) <- matched'
                                    , not (null d)
                                    ]
                   err = if (null ws')
                         then []
                         else [ "Note: invalid command form specified -- describing closest match", ""]
                   hdr = [ "Command: " ++ prefix ++
                           (if (null sd) then "" else (" - " ++ sd)) ]
                   grammar_desc = htclDescribeCmdGrammar g' 60
                   usage = [ "", "Usage: " ++ prefix ++ " " ++ grammar_desc ]
                   desc = if (null ld)
                          then []
                          else [ "", ld ]
                   subtopics = case g' of
                                 (ChooseFrom gs) ->
                                     if (all isKWorNone (map htclFirstCmdElem gs))
                                     then [ "", "Subcommands: " ] ++
                                          [ "  " ++ name ++ descr
                                          | gr <- gs
                                          , let name = take 30 $ (htclDescribeCmdGrammar gr 29) ++ (repeat ' ')
                                          , let descr = htclGrammarShortDesc gr
                                          ]
                                     else []
                                 (Sequence (ChooseFrom gs) g2) ->
                                     if (all isKW (map htclFirstCmdElem gs))
                                     then [ "", "Subcommands: " ] ++
                                          [ "  " ++ name ++ descr
                                          | gr <- gs
                                          , let name = take 30 $ (htclDescribeCmdGrammar (Sequence gr g2) 29) ++ (repeat ' ')
                                          , let descr = htclGrammarShortDesc gr
                                          ]
                                     else []
                                 _ -> []
               return $ init $ unlines $
                        err ++ hdr ++ usage ++ desc ++ subtopics
----------
helpCmd interp objs = htclCheckCmd helpGrammar fn interp objs
    where fn xs = internalError $ "helpCmd: grammar mismatch: " ++ (show xs)

--------------------------------------------------------------------------------

syntaxGrammar :: HTclCmdGrammar
syntaxGrammar = (tclcmd "syntax" namespace helpStr "") .+.
                (oneOf [ (kw "set" setHelpStr setLongHelpStr) .+.
                         (oneOf [ kw "bh" bhHelpStr ""
                                , kw "bsv" bsvHelpStr ""
                                ])
                       , (kw "get" getHelpStr "")
                       ])
  where helpStr = "Get or set the syntax for Bluetcl"
        setHelpStr = "Set the syntax for Bluetcl"
        getHelpStr = "Get the current syntax for Bluetcl"
        setLongHelpStr = "The argument 'bsv' or 'bh' is required"
        bhHelpStr = "Set Bluespec Haskell syntax"
        bsvHelpStr = "Set Bluespec SystemVerilog syntax"

syntaxCmd :: [String] -> IO HTclObj
syntaxCmd ["set", "bh" ] = do frozen <- isSyntaxFrozen
                              if not frozen then do
                                setSyntax CLASSIC
                                return $ TStr "Bluespec Haskell"
                              else ioError $ userError "Bluetcl::syntax set: syntax frozen"
syntaxCmd ["set", "bsv"] = do frozen <- isSyntaxFrozen
                              if not frozen then do
                                setSyntax BSV
                                return $ TStr "Bluespec SystemVerilog"
                              else ioError $ userError "Bluetcl::syntax set: syntax frozen"
syntaxCmd ["get"]
  | isClassic() = return $ TStr "Bluespec Haskell"
  | isBSV()     = return $ TStr "Bluespec SystemVerilog"
  | otherwise   = internalError $ "Bluetcl: unknown syntax"
syntaxCmd xs    = internalError $ "syntaxCmd: grammar mismatch: " ++ show xs

--------------------------------------------------------------------------------

versionGrammar :: HTclCmdGrammar
versionGrammar = (tclcmd "version" namespace helpStr longHelpStr) .+.
                 (optional $ oneOf [ kw "bsc" bscHelpStr ""
                                   , kw "ghc" ghcHelpStr ""
                                   ])
    where helpStr = "Returns version information for Bluespec software"
          longHelpStr = init $ unlines
                        [ "If no argument is provided, the subcommand 'bsc' is assumed." ]
          bscHelpStr = "Show BSC version information"
          ghcHelpStr = "Show the GHC version used to compile BSC"

versionNum :: [String] -> IO HTclObj
versionNum [] = versionNum ["bsc"]
versionNum ["bsc"] = return $ TLst [TStr versionname, TStr buildVersion]
versionNum ["ghc"] = return $ TStr ghcVersionStr
versionNum xs = internalError $ "versionNum: grammar mismatch: " ++ (show xs)

ghcVersionStr :: String
#if defined(__GLASGOW_HASKELL_FULL_VERSION__)
ghcVersionStr = __GLASGOW_HASKELL_FULL_VERSION__
#else
ghcVersionStr =
  let version_raw :: Int = __GLASGOW_HASKELL__
      (major, minor) :: (Int, Int) = version_raw `divMod` 100
#if defined(__GLASGOW_HASKELL_PATCHLEVEL1__)
      patch1 :: Int = __GLASGOW_HASKELL_PATCHLEVEL1__
  in  show major ++ "." ++ show minor ++ "." ++ show patch1
#else
  in  show major ++ "." ++ show minor
#endif
#endif

--------------------------------------------------------------------------------
-- flags

flagsGrammar :: HTclCmdGrammar
flagsGrammar = (tclcmd "flags" namespace helpStr "") .+.
               (oneOf [ (kw "set" setHelpStr longSetHelpStr) .+.
                        (atLeast 1 (arg "flag" StringArg "flag setting"))
                      , (kw "show" showHelpStr longShowHelpStr) .+.
                        (atLeast 0 (arg "flag" StringArg "flag"))
                      , (kw "reset" resetHelpStr resetHelpStr)
                      ])
    where helpStr = "Set or show a flag value"
          setHelpStr = "Set a flag value"
          longSetHelpStr = init $ unlines
                           [ "Set the value of a flag by giving its name along with any"
                           , "required or optional arguments.  Include the leading '-'"
                           , "character in the flag name."
                           , ""
                           , "Examples:"
                           , "  flags set -verbose"
                           , "  flags set {-scheduler-effort 0}"
                           , "  flags set {-scheduler-effort 0} -keep-fires"
                           ]
          showHelpStr = "Show a flag value"
          longShowHelpStr = init $ unlines
                            [ "Without an argument, shows the current settings of all flags."
                            , "With an argument, shows the current value of each flag named"
                            , "in the argument.  Flag names are given without the leading '-'"
                            , "character.  If a boolean flag is not currently set, an empty"
                            , "list ({}) is returned for its value, otherwise the name of the"
                            , "flag is returned."
                            , ""
                            , "Examples:"
                            , "  flags show"
                            , "  flags show verbose"
                            , "  flags show scheduler-effort"
                            , "  flags show steps steps-max-intervals steps-warn-interval"
                            ]
          resetHelpStr = "Reset all flags to an initial state"
{- -}
tclFlags :: [String] -> IO [String]
tclFlags ["show"] = do
  g <- readIORef globalVar
  (return . concat . showFlagsLst . tp_flags) g
----------
tclFlags ["show", "all"] = do
  g <- readIORef globalVar
  (return . concat . showFlagsAllLst . tp_flags) g
----------
tclFlags ("show":ss) = do
  g <- readIORef globalVar
  mapM (getFlagValueString (tp_flags g)) ss >>= return . concat
----------
tclFlags ("set":strs) = do
  g <- readIORef globalVar
  let (sets, ws0, es0 ,flags',sss) = decodeFlags strs ([], [], [], (tp_flags g))
      (ws, es, flags2) = adjustFinalFlags ws0 es0 flags'
  reportErrorsToTcl ws es
  checkEmptyList "Unexpected or unrecognized arguments." sss
  modifyIORef globalVar (\gv -> gv{ tp_flags=flags2})
  mapM (getFlagValueString flags2) (reverse sets) >>= return . concat
----------
tclFlags ["reset"] = do
  let handler :: CE.IOException -> IO String
      handler e = ioError $ userError "BLUESPECDIR environment is not set."
  bsdir <- CE.catch (getEnv "BLUESPECDIR") handler

  bscopts <- getEnvDef "BSC_OPTIONS" ""
  flags <- updateFlags globalErrHandle  cmdPosition (words bscopts) $ defaultFlags bsdir

  btopts <- getEnvDef "BLUETCL_OPTIONS" ""
  flags' <- updateFlags globalErrHandle  cmdPosition (words btopts) flags

  modifyIORef globalVar (\gv -> gv{ tp_flags=flags'})
  (return . concat . showFlagsLst) flags

tclFlags xs = internalError $ "tclFlags: grammar mismatch: " ++ (show xs)

-------------------------------------------------------------------------------
-- debug command
debugGrammar :: HTclCmdGrammar
debugGrammar = (tclcmd "debug" namespace helpStr "") .+.
               (oneOf [ gstateGrammar, importsGrammar, symtabGrammar
                      , errorGrammar, error2Grammar
                      , gcGrammar
                      ])
    where helpStr = "Internal debugging command"
          gstateGrammar  = kw "gstate"  "gstate" ""
          importsGrammar = kw "imports" "imports" ""
          symtabGrammar  = kw "symtab"  "symtab" ""
          errorGrammar   = kw "error"   "error" ""
          error2Grammar  = kw "error2"  "error2" ""
          gcGrammar      = kw "gc"      "gc" ""

tclDebug :: [String] -> IO String
tclDebug ["gstate"] = do
  g <- readIORef globalVar
  return (show g)
----------
tclDebug ["symtab"]= do
  g <- readIORef globalVar
  return $ show (pPrint PDReadable 0 (tp_symtab g))
----------
tclDebug ["imports"] = do
  g <- readIORef globalVar
  let imps = M.toList $ tp_binmap g
  mapM_ (putStrLn . show) imps
  return "Done"
----------
-- throws an error via the built-in error
tclDebug ["error"] = do
  let foo = ["dd", "ee", "ff", "sc" ]
  flags <- getGFlags
  return (foo !! 5) -- actually throws error
----------
-- throws an error using an explicit error call
tclDebug ["error2"] = do
  let foo = ["dd", "ee", "ff", "sc"] ++
            (replicate 10 (error "Index too big"))
  flags <- getGFlags
  return (foo !! 5) -- actually throws error
----------
tclDebug ["gc"] = do
  performGC
  return "Done"

----------
tclDebug xs = internalError $ "tclDebug: grammar mismatch: " ++ (show xs)

-------------------------------------------------------------------------------
-- Package commands

packageGrammar :: HTclCmdGrammar
packageGrammar = (tclcmd "bpackage" namespace helpStr "") .+.
                 (oneOf [ loadGrammar, clearGrammar, listGrammar
                        , pdependGrammar, typesGrammar, searchGrammar
                        , vsignalsGrammar
                        , positionGrammar
                        ])
    where helpStr = "Manipulate and query BSV packages"
          loadGrammar   = (kw "load" "Load packages" "") .+.
                          (atLeast 1 (arg "pkg" StringArg "package name"))
          clearGrammar  = kw "clear" "Clear all currently loaded packages" ""
          listGrammar   = kw "list" "List all currently loaded packages" ""
          pdependGrammar = kw "depend" "List package dependencies of all currently loaded packages" ""
          typesGrammar  = (kw "types" "List the types in a package" "") .+.
                          (arg "pkg" StringArg "package name")
          searchGrammar = (kw "search" "Search packages for names matching a regular expression" "") .+.
                          (arg "regex" StringArg "regular expression")
          vsignalsGrammar = kw "vsignals" "List signals corresponding to inlined Verilog modules" ""
          positionGrammar = (kw "position" "get position of definition" "") .+.
                            (arg "identifier" StringArg "identifier" )

tclPackage :: [String] -> IO HTclObj
tclPackage ("load":args) = do
  g <- readIORef globalVar
  let ids = nub $ map mk_homeless_id args

  -- load the packages and every package that they depend on
  let loadFn (binmap, hashmap, ps_read) p = do
          (binmap', hashmap', _, new_ps)
              <- readBin globalErrHandle (tp_flags g) Nothing binmap hashmap p
          return (binmap', hashmap', new_ps ++ ps_read)
  let binmap0 = tp_binmap g
      hashmap0 = tp_hashmap g
  (binmap, hashmap, ps_read) <- foldM loadFn (binmap0, hashmap0, []) ids

  let bininfos = let lookupFn i = fromJustOrErr "tclPackage load" $
                                    M.lookup (getIdString i) binmap
                 in  map lookupFn ps_read

  -- update the CImports and symbol table
  let (CPackage pid exps cimps impsigs cf defs incs) = tp_cpack g
      mkCImp (_, _, bo_sig, (IPackage iid _ _ _), _) =
          -- XXX is False OK here?
          CImpSign (getIdString iid) False bo_sig
      impsigs' = sortImports ((map mkCImp bininfos) ++ impsigs)
      cpack' = CPackage pid exps cimps impsigs' cf defs incs
  symtab <- mkSymTab globalErrHandle cpack'

  -- write back the new values
  modifyIORef globalVar (\gv -> gv {tp_binmap  = binmap,
                                    tp_hashmap = hashmap,
                                    tp_cpack   = cpack',
                                    tp_symtab  = symtab } )
  -- report the packages in a consistent order
  imp_names <- getImportNamesSorted
  return $ TLst (map TStr imp_names)
-----------
tclPackage ["list"] = do
  g <- readIORef globalVar
  -- report the packages in a consistent order
  imp_names <- getImportNamesSorted
  return $ TLst (map TStr imp_names)
----------
tclPackage ["depend"] = do
  g <- readIORef globalVar
  -- report the packages in a consistent order
  imps <- getImportsSorted
  let mkDep imp =
          let ipkg = ip_ipkg imp
              pId = ipkg_name ipkg
              dIds = map fst (ipkg_depends ipkg)
          in  tagManyStr (pfpString pId) (map pfpString dIds)
  -- XXX should the "bpackage" commands filter out Prelude, PreludeBSV,
  -- XXX and any internal packages like PrimArray ?
  return $ TLst (map mkDep imps)
----------
tclPackage ["clear"] = do
  let clrCPkg (CPackage pid _ _ _ _ _ _) = (CPackage pid (Right []) [] [] [] [] [])
  modifyIORef globalVar (\gv -> gv { tp_binmap  = M.empty,
                                     tp_hashmap = M.empty,
                                     tp_symtab  = emptySymtab,
                                     tp_cpack   = clrCPkg (tp_cpack gv) })
  return $ TLst []
---------
tclPackage ["types",pkg] = do
  g <- readIORef globalVar
  let symtab = tp_symtab g
      pid = mkFString pkg
      isFromPackage :: (Id,TypeInfo) -> Bool
      isFromPackage (i,_) = pid == getIdQual i
      --
      theseTypes = filter isFromPackage (getAllTypes symtab)
  let (is,tis) = unzip $ theseTypes
      is' = filter (not . hideId) is
  return $ TLst (map (TStr . pfpString . unQualId) is')
----------
tclPackage ["search",rex] = do
  g <- readIORef globalVar
  -- report the packages in a consistent order
  imps <- getImportsSorted
  let regex = mkRegex rex
      csigs = [ (ip_id imp, ip_csig imp) | imp <- imps ]
      lookinThisPack :: (Id, CSignature) -> [(Id,String)]
      lookinThisPack (imp_id, CSignature _ im cf ds) =
             [ (imp_id, name)
             | (Right i) <- map getName ds
             , let name = getIdBaseString i
             , isJust (matchRegex regex name)
             ]
      res = concatMap lookinThisPack csigs
  obj <- toTclObj res
  return $ TCL obj
----------
tclPackage ["position",idenstr] = do
  g <- readIORef globalVar
  let iden = genId idenstr
  -- if the Id isn't qualified, then look in all packages
  csigs <- if (fsEmpty == getIdQual iden)
           then do -- report the packages in a consistent order
                   imps <- getImportsSorted
                   return $ map ip_csig imps
           else do imp <- lookupImport (getIdQualString iden)
                   return [ip_csig imp]
  --
  let res = [(getPosition i) | (CSignature _ im cf ds) <- csigs,
                               (Right i) <- map getName ds,
                               qualEq iden i]
  return $ case res of
             []  -> toHTObj ()
             x:_ -> toHTObj (x)
----------
-- generate the mapping e.g.
-- {read Q_OUT} {first D_OUT} {notFull FULL_N} {i_notFull FULL_N} {notEmpty EMPTY_N} {i_notEmpty EMPTY_N} {wget WGET} {whas WHAS}
-- This is a bit of a hack, since we lose all type information.

tclPackage ["vsignals"] =
  readIORef globalVar >>=
  (return . toHTObj  . package_vsignals)
----------
tclPackage xs = internalError $ "tclPackage: grammar mismatch: " ++ (show xs)

-- Create a new CPackage after package load
addNewImports :: [(CSignature, IPackage a, String, String)] ->
                 CPackage -> CPackage
addNewImports ims (CPackage pid exps imps impsigs cf defs incs) =
    (CPackage pid exps imps impsigs' cf defs incs)
    where impsigs' = impsigs ++ map addOneImport ims
          addOneImport :: (CSignature, IPackage a, String, String) -> CImportedSignature
          addOneImport (cs, (IPackage iid _ _ _), _, _) =
              -- XXX Bool var for qual names?
              CImpSign (getIdString iid) False cs

-------------------------------------------------------------------------------
-- XX can this be merged with tclPackage command (only return id)

defsGrammar :: HTclCmdGrammar
defsGrammar = (tclcmd "defs" namespace helpStr "") .+.
              (oneOf [ allGrammar, tyGrammar, modGrammar, funcGrammar ]) .+.
              (arg "pkg" StringArg "package name")
    where helpStr = "Show the definitions in a package"
          allGrammar  = kw "all" "Show all definitions in a package" ""
          tyGrammar   = kw "type" "Show all types defined in a package" ""
          modGrammar  = kw "module" "Show all modules defined in a package" ""
          funcGrammar = kw "func" "Show all functions defined in a package" ""

tclDefs :: [String] -> IO HTclObj
tclDefs ("type":args) =
  let getOneTypes :: String -> IO [Id]
      getOneTypes pnm = do
        imp <- lookupImport pnm
        let (CSignature pid im cf ds) = ip_csig imp
        return [ i | (Right i) <- map getName (filter isTDef ds) ]
  in do tss <- mapM getOneTypes args
        let ts = filter (not . hideId) (concat tss)
        return $ TLst $ map (TStr . pfpString) ts
------
tclDefs ("module":args) =
  let getOneMods :: String -> IO [Id]
      getOneMods pnm = do
        imp <- lookupImport pnm
        let (IPackage _ _ pragmas _) = ip_ipkg imp
            getMods (Pnoinline fs) = fs
            getMods (Pproperties m pps) = if (PPverilog `elem` pps)
                                          then [m]
                                          else []
        return $ concatMap getMods pragmas
  in do mss <- mapM getOneMods args
        let ms = concat mss
        return $ TLst $ map (TStr . pfpString) ms
------
tclDefs ("func":args) =
  let getOneDefs :: String -> IO [HTclObj]
      getOneDefs pnm = do
        imp <- lookupImport pnm
        let (CSignature pid im cf ds) = ip_csig imp
            isOK d = case (getName d) of
                       Right i -> not (hideId i)
                       Left _ -> False
            ds' = filter isOK ds
        return $ concatMap displayCDefn ds'
  in do fss <- mapM getOneDefs args
        let fs = concat fss
        return $ TLst fs
------
tclDefs ("all":args) =
  let getOneDefs :: String -> IO [Id]
      getOneDefs pnm = do
        imp <- lookupImport pnm
        let (CSignature pid im cf ds) = ip_csig imp
        return [ i | (Right i) <- map getName ds, not (hideId i) ]
  in do dss <- mapM getOneDefs args
        let ds = concat dss
        return $ TLst $ map (TStr . pfpString) ds
------
tclDefs xs = internalError $ "tclDefs: grammar mismatch: " ++ (show xs)

------

-- XXX This displays a CDefn from a signature file.
-- XXX If we looked up the def in the IPackage, then it would have
-- XXX the argument names and we could display them.
displayCDefn :: CDefn -> [HTclObj]
displayCDefn (CIValueSign i cqt)  = [displayTypeSignature i cqt]
displayCDefn (Cforeign i cqt _ _) = [displayTypeSignature i cqt]
displayCDefn (Cprimitive i cqt)   = [displayTypeSignature i cqt]
displayCDefn (CValue i _) =
    internalError ("displayCDefn: unexpected CValue: " ++ ppReadable i)
displayCDefn (CValueSign cdef) =
    internalError ("displayCDefn: unexpected CValueSign: " ++ ppReadable cdef)
displayCDefn _ = []  -- don't display types, classes, instances

displayTypeSignature :: Id -> CQType -> HTclObj
displayTypeSignature i qt@(CQType ps ty) =
    let
        (args, res) = getArrows ty
        (con, conargs) = splitTAp res

        isModOfCon (CPred (CTypeclass isM) [m@(TVar _), _])
            | (isM == idIsModule) && (m == con) = True
        isModOfCon _ = False

        (mods, ps') = partition isModOfCon ps
    in
        case (mods, conargs) of
            ((_:_), [ifc]) -> displayModuleSignature i ps' args ifc
            _ -> -- XXX check if "con" is a concrete module type?
                 -- XXX like "Module"
                 displayFunctionSignature i ps args res

displayModuleSignature :: Id -> [CPred] -> [CType] -> CType -> HTclObj
displayModuleSignature i ps args ifc =
    tag "module" $
        [TStr (pfpString i),
         tagLst "interface" [TStr $ pfpString ifc]] ++
        (if (null args)
         then []
         else [tagManyStr "arguments" (map pfpString args)]) ++
        (if (null ps)
         then []
         else [tagManyStr "provisos" (map pfpString ps)]) ++
        showTaggedPosition i

displayFunctionSignature :: Id -> [CPred] -> [CType] -> CType -> HTclObj
displayFunctionSignature i ps args res =
    tag "function" $
        [TStr (pfpString i),
         tagLst "result" [TStr $ pfpString res]] ++
        (if (null args)
         then []
         else [tagManyStr "arguments" (map pfpString args)]) ++
        (if (null ps)
         then []
         else [tagManyStr "provisos" (map pfpString ps)]) ++
        showTaggedPosition i


-------------------------------------------------------------------------------

parseGrammar :: HTclCmdGrammar
parseGrammar = (tclcmd "parse" namespace helpStr "") .+.
               (kw "type" "" "") .+.
               (arg "arg" StringArg "string")
    where helpStr = "Parse a string and show its internal representation"

tclParse :: [String] -> IO [String]
tclParse ["type",s] = do
  flags <- getGFlags
  res <- parseTypeExpr globalErrHandle flags s
  case res of
    Right x -> return $ [(show x),show (pfPrint PDReadable  0 x)]
    Left x  -> return $ ["Error: " ++ (show x)]
------
tclParse xs = internalError $ "tclParse: grammar mismatch: " ++ (show xs)

-------------------------------------------------------------------------------

typeGrammar :: HTclCmdGrammar
typeGrammar = (tclcmd "type" namespace helpStr longHelpStr) .+.
              (oneOf [fullGrammar, constrGrammar,bitifyGrammar])
    where helpStr = "Display information about a type"
          longHelpStr = init $ unlines $
                        [ "Examples:"
                        , "  type constr Maybe"
                        , "  type full Maybe#(Int#(32))"
                        , "  type full [type constr Maybe]"
                        ]
          fullGrammar = (kw "full" "Describe the properties of a type" "") .+.
                        (arg "arg" StringArg "type")
          constrGrammar = (kw "constr" "Show the type associated with a type constructor" "") .+.
                          (arg "arg" StringArg "constructor")
          bitifyGrammar = (kw "bitify" "get bit information" "") .+.
                          (arg "arg" StringArg "type constructor")


tclType :: [String] -> IO HTclObj
tclType ["full",ty] = do
  -- get the state
  g <- readIORef globalVar
  let st    = tp_symtab g
      flags = tp_flags g
  -- read in the type
  et <- parseTypeExpr globalErrHandle flags ty
  -- do the analysis
  case et of
    Left err -> do reportErrorsToTcl [] err
                   return $ TLst [] -- reachable only if no errors
    Right t  -> case (analyzeType flags st t) of
                  Left errs -> do reportErrorsToTcl [] errs
                                  return $ TLst [] -- reachable only if no errors
                  Right ta -> -- convert a non-error result to HTclObj and return it
                              return $ typeAnalysisToHTclObj ta
----------
tclType ["constr",con] = do
  g <- readIORef globalVar
  let symtab = tp_symtab g
      flags  = tp_flags g
  --
  typeid <- parseQualConstructor globalErrHandle flags con
  let econs = either Left (lookupAndShowTypeInfo symtab) typeid
  case econs of
    Left err -> do reportErrorsToTcl [] err
                   return $ TLst [] -- reachable only if no errors
    Right x  -> return $ TStr x
----------
tclType ["bitify",con] = do
  -- get the state
  g <- readIORef globalVar
  let st    = tp_symtab g
      flags = tp_flags g
  -- read in the type
  et <- parseTypeExpr globalErrHandle flags con
  -- do the analysis
  case et of
    Left err -> do reportErrorsToTcl [] err
                   return $ TLst [] -- reachable only if no errors
    Right t  -> case (analyzeType flags st t) of
                  Left errs -> do reportErrorsToTcl [] errs
                                  return $ TLst [] -- reachable only if no errors
                  Right ta -> return $ typeAnalysisToBitify ta
----------
tclType xs = internalError $ "tclType: grammar mismatch: " ++ (show xs)

lookupAndShowTypeInfo :: SymTab -> Id -> Either [EMsg] String
lookupAndShowTypeInfo symtab tid =
          case (findType symtab tid) of
            Nothing -> Left [(cmdPosition,EUnboundTyCon (pfpString tid))]
            Just (TypeInfo _ kind vs tis _) -> Right (showType False tid kind vs)


----------------------------------------------------

moduleGrammar :: HTclCmdGrammar
moduleGrammar = (tclcmd "module" namespace helpStr "") .+.
                (oneOf [ loadGrammar, clearGrammar, submodsGrammar
                       , rulesGrammar, ifcGrammar, methodsGrammar
                       , bflagsGrammar
                       , portsGrammar, porttypesGrammar, listGrammar
                       , methodConditionsGrammar
                       ])
    where helpStr = "Load and query information on a module"
          argmod = (arg "module" StringArg "module name")
          loadGrammar = (kw "load" "Load a synthesized module" "") .+. argmod

          clearGrammar = kw "clear" "Clear all loaded modules" ""
          submodsGrammar = (kw "submods" "Show submodules of a module" "") .+. argmod
          rulesGrammar = (kw "rules" "Show rules in a module" "") .+.
                         argmod
          ifcGrammar = (kw "ifc" "Show the interface type of a module" "") .+.
                       argmod
          methodsGrammar = (kw "methods" "Show the flattened methods of a module" "") .+.
                           argmod
          portsGrammar = (kw "ports" "Show the ports of a module" "") .+.
                         argmod
          methodConditionsGrammar =
            (kw "methodconditions" "Show the method predicates of a module" "") .+.
            argmod
          listGrammar = (kw "list" "List the loaded modules" "")
          porttypesGrammar =
              (kw "porttypes" "Show the types of the ports of a module" "") .+.
              (arg "module" StringArg "module name")


bflagsGrammar :: HTclCmdGrammar
bflagsGrammar = (kw "flags" showHelpStr longShowHelpStr) .+.
                (arg "module" StringArg "module name")  .+.
                (atLeast 0 (arg "flag" StringArg "flag"))
    where showHelpStr = "Show the flag settings when the module was built"
          longShowHelpStr = init $ unlines
                            [ "With just the module name, shows the build settings of all flags."
                            , "With an added argument, shows the build value of each flag named"
                            , "in the argument.  Flag names are given without the leading '-'"
                            , "character.  If a boolean flag was not set, an empty"
                            , "list ({}) is returned for its value, otherwise the name of the"
                            , "flag is returned."
                            , ""
                            , "Examples:"
                            , "  flags modname"
                            , "  flags modname verbose"
                            , "  flags modname scheduler-effort"
                            , "  flags modname steps steps-max-intervals steps-warn-interval"
                            ]

tclModule :: [String] -> IO HTclObj
tclModule ["load",topname] = do
  g <- readIORef globalVar
  let flags = tp_flags g
  gen_backend <- case (backend flags) of
                   Just be -> return be
                   Nothing -> eMsgsToTcl [(cmdPosition, ENoBackendLinking)]
  let prim_names = map sb_name primBlocks
  -- when (isPrimitiveModule topname)
  when (topname `elem` prim_names) $
       ioError $ userError ("Cannot load " ++ quote topname ++
                            ": it is a primitive module")
  -- getABIHierarchy calls GenABin.readABinFile to read a .ba file
  (topmodId, hierMap, instModMap, ffuncMap, _, foreign_mods, abmis_by_name)
      <- convExceptTToIO globalErrHandle $
         getABIHierarchy globalErrHandle
                         (verbose flags) (ifcPath flags) (Just gen_backend)
                         prim_names topname []
  let modnames = map fst abmis_by_name
  let res = (topmodId, hierMap, instModMap, ffuncMap, foreign_mods,
             [(n,mi) | (n,(mi,_)) <- abmis_by_name])
  modifyIORef globalVar (\gv -> gv { tp_mods = Just res })

  -- now load the package in which the module was defined
  -- (so that its interface types are available)
  minfo <- findModule (getIdBaseString topmodId)
  case minfo of
    Nothing -> return ()
    Just abmi -> do let pkgName = abemi_src_name abmi
                    _ <- tclPackage ["load", pkgName]
                    return ()

  -- return the list of loaded module
  return $ TLst (map TStr modnames)
------
tclModule ["list"] = do
  g <- readIORef globalVar
  return $ TLst $ case (tp_mods g) of
                    Nothing -> []
                    Just (_, _, _, _, _, abmis) -> map (TStr . fst) abmis

------
tclModule ["clear"] = do
  modifyIORef globalVar (\gv -> gv { tp_mods = Nothing })
  return $ TLst []
------
tclModule ["submods",modname] = do
  if (isPrimitiveModule modname)
   then return $ tag "primitive" [TLst [], TLst []]
   else do
     minfo <- findModuleHier modname
     case minfo of
       Nothing -> return $ tag "import" [TLst [], TLst []]
       Just (mods, noinlines) -> do
           let mkpair (inst, m) = TLst [TStr inst, TStr m]
               mod_list = TLst (map mkpair mods)
               noinline_list = TLst (map mkpair noinlines)
           return $ tag "user" [mod_list, noinline_list]
------
tclModule ["rules",modname] = do
  if (isPrimitiveModule modname)
   then return $ TLst []
   else do
     minfo <- findModule modname
     case minfo of
       Nothing -> return $ TLst []
       Just abmi -> do
           let apkg = abemi_apkg abmi
               rule_names = map (pfpString . arule_id) (apkg_rules apkg)
           return $ TLst (map TStr rule_names)
------
tclModule ["ifc",modname] = do
  if (isPrimitiveModule modname)
   then return $ TLst []
   else do
     minfo <- findModule modname
     case minfo of
       Nothing -> return $ TLst []
       Just abmi -> do
           let ifcname = pfpString (getModuleIfc abmi)
           return $ TStr ifcname
------
tclModule ["methods",modname] = do
  if (isPrimitiveModule modname)
   then return $ TLst []
   else do
     minfo <- findModule modname
     case minfo of
       Nothing -> return $ TLst []
       Just abmi -> do
           let apkg = abemi_apkg abmi
               pps = abemi_pps abmi
               ifc = apkg_interface apkg
               ifc_map = [ (aIfaceName aif, rawIfcFieldFromAIFace pps aif)
                           | aif <- ifc ]
           let tifc = getModuleIfc abmi
           fs <- getIfcHierarchy Nothing ifc_map tifc
           return (dispIfcHierarchyNames fs)

------
tclModule ["ports",modname] = do
  if (isPrimitiveModule modname)
   then -- XXX we should be able to lookup the VModInfo for prim modules
        return $ TLst []
   else do
     minfo <- findModule modname
     case minfo of
       Nothing -> return $ TLst []  -- XXX can we do something for imports?
       Just abmi -> do
           let apkg = abemi_apkg abmi
               pps  = abemi_pps abmi
               tifc = getModuleIfc abmi
           (arginfo, ifcinfo) <- getModPortInfo apkg pps tifc
           return $ TLst [tagLst "interface" (map dispIfc ifcinfo),
                          tagLst "args" (map dispModArg arginfo)]
------
tclModule ["methodconditions", modname] = do
  if (isPrimitiveModule modname)
   then return $ TLst []
   else do
     minfo <- findModule modname
     case minfo of
       Nothing -> return $ TLst []
       Just abmi -> let
           defs :: [ADef]
           defs = apkg_local_defs $ abemi_apkg abmi
           ismethpred :: ADef -> Bool
           ismethpred d = hasIdProp (adef_objid d) IdPMethodPredicate
           doProp :: DefProp -> [HTclObj]
           doProp (DefP_Rule i) = [ tagStr "rule" (getIdBaseString i) ]
           doProp (DefP_Method i) = [ tagStr "method" (getIdBaseString i) ]
           doProp (DefP_Instance i) = [ tagStr "instance" (getIdBaseString i) ]
           doProp DefP_NoCSE = []
           convert :: ADef -> HTclObj
           convert (ADef i _t e ps) =
                TLst $ [ TStr (getIdBaseString i)
                       , TLst $ TStr "positions" :
                         (map toHTObj $ fromMaybe [] $ getIdInlinedPositions i)
                       ] ++ concatMap doProp ps
           -- sort the list, so that the output has a stable canonical order
           -- (we sort by the unique number, but we could also do alphabetical)
           cmpFn d1 d2 =
               let extractNum :: ADef -> Integer
                   extractNum d =
                       readOrErr ("MethodPred unique number") $
                       reverse $ takeWhile (/= '_') $ reverse $
                       getIdBaseString (adef_objid d)
               in  compare (extractNum d1) (extractNum d2)
         in return $ TLst $ map convert $ sortBy cmpFn $ filter ismethpred defs

------
tclModule ["porttypes",modname] = do
  if (isPrimitiveModule modname)
   then return $ TLst []
   else do
     minfo <- findModule modname
     case minfo of
       Nothing -> return $ TLst []
       Just abmi -> do
           let apkg = abemi_apkg abmi
               pps  = abemi_pps abmi
               tifc = getModuleIfc abmi
           (arginfo, ifcinfo) <- getModPortInfo apkg pps tifc
           let h_arg_types = concatMap dispPortsModArg arginfo
               h_ifc_types = concatMap dispPortsIfc ifcinfo
           return $ TLst $ nub (h_arg_types ++ h_ifc_types)
------
tclModule ["flags",modname] = do
  if (isPrimitiveModule modname)
   then return $ TLst []
   else do
     minfo <- findModule modname
     case minfo of
       Nothing   -> return $ TLst []
       Just abmi -> return $ TLst (map TStr (concat $ showFlagsLst (abemi_flags abmi)))

tclModule ["flags", modname, "all"] = do
  if (isPrimitiveModule modname)
   then return $ TLst []
   else do
     minfo <- findModule modname
     case minfo of
       Nothing   -> return $ TLst []
       Just abmi -> return $ TLst (map TStr (concat $ showFlagsAllLst (abemi_flags abmi)))

tclModule ("flags":modname:ss) = do
  if (isPrimitiveModule modname)
   then return $ TLst []
   else do
     minfo <- findModule modname
     case minfo of
       Nothing   -> return $ TLst []
       Just abmi -> do
                     strs <- mapM (getFlagValueString (abemi_flags abmi)) ss >>= return . concat
                     return $ TLst (map TStr strs)


------
tclModule xs = internalError $ "tclModule: grmap (TStr . pfpString) grammar mismatch: " ++ (show xs)


findModule :: String -> IO (Maybe ABinEitherModInfo)
findModule modname =
    do g <- readIORef globalVar
       (amods, fmods) <-
           case (tp_mods g) of
               Nothing -> lookupError "Module" modname
               Just (top, hiermap, instmodmap, ffuncmap, foreigns, abmis) ->
                   return (abmis, foreigns)
       case (lookup modname amods) of
         Just abmi -> return $ Just abmi
         Nothing -> if (modname `elem` fmods)
                    then return Nothing
                    else lookupError "Module" modname

findModuleHier :: String -> IO (Maybe ([(String,String)], [(String,String)]))
findModuleHier modname = do
  g <- readIORef globalVar
  (hmap, fmods) <-
      case (tp_mods g) of
          Nothing -> lookupError "Module" modname
          Just (top, hiermap, instmodmap, ffuncmap, foreigns, abmis) ->
              return (hiermap, foreigns)
  case (M.lookup modname hmap) of
      Just res -> return $ Just res
      Nothing -> if (modname `elem` fmods)
                 then return Nothing
                 else lookupError "Module" modname

-- error on bad names
-- Left name for primitives
-- Right otherwise
findModuleByInstance :: [String] -> IO (Either String (String, ABinModInfo))
findModuleByInstance insts = do
   let inst = intercalate "." insts
   g <- readIORef globalVar
   case (tp_mods g) of
     Nothing -> lookupError "Module Instance" inst
     Just (top, hiermap, instmodmap, ffuncmap, foreigns, abmis) ->
         do
           case (M.lookup inst instmodmap) of
             Nothing -> do mapM_ (putStrLn . show) $ M.toList instmodmap
                           putStrLn $ "Error looking up: " ++ inst
                           return (Left $ last insts)-- lookupError "Module Instance2" inst
             Just s | isPrimitiveModule s -> return (Left s)
             Just s ->
                 do minfo <- findModule s
                    case minfo of
                      Nothing -> return (Left s)
                      Just (Right info) -> return (Right (s, info))
                      -- submodules should not have scheduling errors
                      Just (Left info) ->
                          eMsgsToTcl [(cmdPosition,
                                       EABinModSchedErr s Nothing)]

getModuleIfc :: ABinEitherModInfo -> Type
getModuleIfc abmi =
    let (CQType _ ot) = abemi_oqt abmi
    in  case (getArrows ot) of
          (_, TAp _ t) -> t
          (_, tm) -> internalError ("getModuleIfc: tm = " ++ ppReadable tm)

----------------------------------------------------

scheduleGrammar :: HTclCmdGrammar
scheduleGrammar = (tclcmd "schedule" namespace helpStr "") .+.
                  (oneOf [ urgencyKW, execKW, methKW, pathKW, warnKW, errKW ]) .+.
                  (arg "module" StringArg "module name")
    where helpStr = "Query a module schedule"
          urgencyKW = kw "urgency"    "Show schedule urgency order" ""
          execKW    = kw "execution"  "Show schedule execution order" ""
          methKW    = kw "methodinfo" "Show schedule method info" ""
          pathKW    = kw "pathinfo"   "Show schedule path info" ""
          warnKW    = kw "warnings"   "Show scheduler warnings" ""
          errKW     = kw "errors"     "Show scheduler errors" ""

tclSchedule :: [String] -> IO HTclObj
tclSchedule ["urgency",modname] =
  if (isPrimitiveModule modname)
  then return $ TLst []
  else do
     minfo <- findModule modname
     case minfo of
       Nothing -> return $ TLst []
       Just abmi ->
           case (abemi_schedule abmi) of
             Nothing -> return $ TLst []
             Just asched -> do
                 let sched =
                         let extractEsposito (ASchedEsposito xs) = xs
                         in  concatMap extractEsposito (asch_scheduler asched)
                     h_sched =
                         let mkS (r, rs) = tagManyStr (pfpString r) (map pfpString rs)
                         in  map mkS sched
                 return $ TLst h_sched
------
tclSchedule ["execution",modname] =
  if (isPrimitiveModule modname)
  then return $ TLst []
  else do
     minfo <- findModule modname
     case minfo of
       Nothing -> return $ TLst []
       Just abmi ->
           case (abemi_schedule abmi) of
             Nothing -> do
                 -- Return just the rules in default order
                 let apkg = abemi_apkg abmi
                     rules = map arule_id (apkg_rules apkg)
                     h_rules = map (TStr . pfpString) rules
                 return $ TLst h_rules
             Just asched -> do
                 let -- turn around the order - first rule first.
                     exec_order = reverse $ asch_rev_exec_order asched
                     h_exec_order = map (TStr . pfpString) exec_order
                 return $ TLst h_exec_order
------
tclSchedule ["methodinfo",modname] =
  if (isPrimitiveModule modname)
  then return $ TLst []
  else do
     minfo <- findModule modname
     case minfo of
       Nothing -> return $ TLst []
       Just (Left abmsei) -> return $ TLst []
       Just (Right abmi) -> do
          let asi = abmi_aschedinfo abmi
              pkg = abmi_apkg abmi
              ifc = apkg_interface pkg
              vsi = asi_v_sched_info asi
              methmap = genMethodDumpMap vsi ifc
          let h_methmap =
                  let mkC (r,c) = TLst [TStr (pfpString r), TStr (show c)]
                      mkP (r,_,cs) = tagLst (pfpString r) (map mkC cs)
                  in  map mkP methmap
          return $ TLst h_methmap
------
tclSchedule ["pathinfo",modname] =
  if (isPrimitiveModule modname)
  then return $ TLst []
  else do
     minfo <- findModule modname
     case minfo of
       Nothing -> return $ TLst []
       Just (Left abmsei) -> return $ TLst []
       Just (Right abmi) -> do
          let pathinfo = abmi_pathinfo abmi
              -- join paths going to the same output
              joinPaths [] = []
              joinPaths zs@((_,o):_) =
                  case (partition ((== o) . snd) zs) of
                    (xs, ys) -> (map fst xs, o) : joinPaths ys
              joinedinfo = case pathinfo of
                             VPathInfo ps -> joinPaths ps
          -- format for tcl
          let h_pathinfo =
                  let mkP (ins, out) = TLst [TLst (map (TStr . pfpString) ins),
                                             TStr (pfpString out)]
                  in  map mkP joinedinfo
          return $ TLst h_pathinfo
------
tclSchedule ["warnings",modname] =
  if (isPrimitiveModule modname)
  then return $ TLst []
  else do
     minfo <- findModule modname
     case minfo of
       Nothing -> return $ TLst []
       Just abmi -> do
          let ws = abemi_warnings abmi
          let h_ws = let mkW (pos, t, str) =
                             TLst [TLst $ map TStr (tclPosition pos),
                                   TStr t,
                                   TStr str]
                     in  map mkW ws
          return $ TLst h_ws
------
tclSchedule ["errors",modname] =
  if (isPrimitiveModule modname)
  then return $ TLst []
  else do
     minfo <- findModule modname
     case minfo of
       Nothing -> return $ TLst []
       Just (Right r) -> return $ TLst []
       Just (Left abmsei) -> do
          let asi = abmsei_aschederrinfo abmsei
              es = asei_errors asi
          let h_es = let mkE (pos, t, str) =
                             TLst [TLst $ map TStr (tclPosition pos),
                                   TStr t,
                                   TStr str]
                     in  map mkE es
          return $ TLst h_es
------
tclSchedule xs = internalError $ "tclSchedule: grammar mismatch: " ++ (show xs)

----------------------------------------------------

submodGrammar :: HTclCmdGrammar
submodGrammar = (tclcmd "submodule" namespace helpStr "") .+.
                (oneOf [ (kw "full" "" "") .+.
                         (arg "module" StringArg "module name")
                       , (kw "ports" "" "") .+.
                         (arg "module" StringArg "module name")
                       , (kw "porttypes" "" "") .+.
                         (arg "module" StringArg "module name")
                       ])
    where helpStr = "Query submodules"

tclSubmodule :: [String] -> IO HTclObj
tclSubmodule ["full",modname] =
  if (isPrimitiveModule modname)
  then return $ TLst []
  else do
     minfo <- findModule modname
     case minfo of
       Nothing -> return $ TLst []
       Just abmi -> do
          flags <- getGFlags
          let hide = (not (tclShowHidden flags))
              apkg = abemi_apkg abmi
              avis = apkg_state_instances apkg
              docmap = M.fromList (mapFst getIdString (apkg_inst_comments apkg))
              findDocs submod = fromMaybe [] (M.lookup submod docmap)
          -- convert the method uses map into a subinst uses map
          let mumap = abemi_method_uses_map abmi
              sumap =
                  let edges = [ (getIdString instId, [(methId, uses)])
                              | (MethodId instId methId, uses) <- M.toList mumap ]
                  in  -- use "flip" to preserve the method order
                      M.fromListWith (flip (++)) edges
          -- mapping from submods to their ifc type
          let ifc_map = makeSubmoduleIfcMap hide (apkg_inst_tree apkg)
          -- make the result for an individual AVInst
          let mkInfo avi = do
                  let submodname = getVNameString $ vName $ avi_vmi avi
                      instId = avi_vname avi
                      instname = getIdString instId
                      instpos = getPosition instId
                      docs = findDocs submodname
                      -- some internal probes won't be found, so use Maybe
                      mtifc = M.lookup instId ifc_map
                  (arginfo, ifcinfo) <- getSubmodPortInfo mtifc avi
                  let vmethod_sis = get_method_to_signal_map (avi_vmi avi)
                  let h_ports = concatMap dispPortsModArg arginfo ++
                                concatMap dispPortsIfc ifcinfo
                      h_uses =
                          let mkMU (methId, (rs1, rs2, is)) =
                                  tag (getIdString methId)
                                      [TLst (map (TStr . getIdString) rs1),
                                       TLst (map (TStr . getIdString) rs2),
                                       TLst (map (TStr . getIdString) is)]
                              concatUses uses = concatUnzip3 (map snd uses)
                          in  case (M.lookup instname sumap) of
                                Nothing -> []
                                Just mus -> [tag "users"
                                                 (map mkMU (mapSnd concatUses mus))]
                  return $
                      TLst $ [TStr instname, TStr submodname] ++
                             (if (null docs)
                              then []
                              else [tagManyStr "doc" docs]) ++
                             [tagLst "ports" h_ports] ++
                             h_uses ++
                             [tagLst "mports"  (map toHTObj vmethod_sis)] ++
                             showTaggedPosition instpos
          infs <- mapM mkInfo avis
          return $ TLst infs
----------
tclSubmodule ["ports",modname] =
  if (isPrimitiveModule modname)
  then return $ TLst []
  else do
     minfo <- findModule modname
     case minfo of
       Nothing -> return $ TLst []
       Just abmi -> do
          flags <- getGFlags
          let hide = (not (tclShowHidden flags))
              apkg = abemi_apkg abmi
              avis = apkg_state_instances apkg
          -- mapping from submods to their ifc type
          let ifc_map = makeSubmoduleIfcMap hide (apkg_inst_tree apkg)
          -- make the result for an individual AVInst
          let mkInfo avi = do
                  let vmi = avi_vmi avi
                      submodname = getVNameString $ vName vmi
                      instId = avi_vname avi
                      instname = getIdString instId
                      -- some internal probes won't be found, so use Maybe
                      mtifc = M.lookup instId ifc_map
                  (arginfo, ifcinfo) <- getSubmodPortInfo mtifc avi
                  let hifcs = map dispIfc ifcinfo
                      hargs = map dispModArg arginfo
                  return $
                      TLst $ [TStr instname, TStr submodname,
                              tagLst "interface" hifcs,
                              tagLst "args" hargs]
          infs <- mapM mkInfo avis
          return $ TLst infs
----------
tclSubmodule ["porttypes",modname] =
  if (isPrimitiveModule modname)
  then return $ TLst []
  else do
     minfo <- findModule modname
     case minfo of
       Nothing -> return $ TLst []
       Just abmi -> do
          flags <- getGFlags
          let hide = (not (tclShowHidden flags))
              apkg = abemi_apkg abmi
              avis = apkg_state_instances apkg
          -- mapping from submods to their ifc type
          let ifc_map = makeSubmoduleIfcMap hide (apkg_inst_tree apkg)
          -- make the result for an individual AVInst
          let mkInfo avi = do
                  let vmi = avi_vmi avi
                      submodname = getVNameString $ vName vmi
                      instId = avi_vname avi
                      instname = getIdString instId
                      -- some internal probes won't be found, so use Maybe
                      mtifc = M.lookup instId ifc_map
                  (arginfo, ifcinfo) <- getSubmodPortInfo mtifc avi
                  let hargs = concatMap dispPortsModArg arginfo
                      hifcs = concatMap dispPortsIfc ifcinfo
                  return $
                      TLst $ [TStr instname, TStr submodname,
                              TLst [TStr "ports", TLst $ nub (hargs ++ hifcs)]]
          infs <- mapM mkInfo avis
          return $ TLst infs
----------
tclSubmodule xs = internalError $ "tclSubmodule: grammar mismatch: " ++ (show xs)

----------------------------------------------------

ruleGrammar :: HTclCmdGrammar
ruleGrammar = (tclcmd "rule" namespace helpStr "") .+.
              (oneOf [ fullGrammar, relGrammar ])
    where helpStr = "Query rules and rule relationships in a module"
          fullGrammar = (kw "full" "Show rule in a module" "") .+.
                        (arg "module" StringArg "module name") .+.
                        (arg "rule" StringArg "rule name")
          relGrammar = (kw "rel" "Show rule relationships" "") .+.
                       (arg "module" StringArg "module name") .+.
                       (arg "rule1" StringArg "rule name") .+.
                       (arg "rule2" StringArg "rule name")

tclRule :: [String] -> IO HTclObj
tclRule ["rel", modname, rule1, rule2] =
  if (isPrimitiveModule modname)
  then ioError $ userError ("Primitive modules cannot be queried")
  else do
     minfo <- findModule modname
     case minfo of
       Nothing -> ioError $ userError ("Imported modules cannot be queried")
       Just abmi ->
           case (abemi_rule_relation_db abmi) of
             Nothing -> return $
                            TStr "Rule relationship information not available"
             Just rrdb -> do
                 let apkg = abemi_apkg abmi
                     user_rule_names = map arule_id (apkg_rules apkg)
                     ifc_rule_names = concatMap aIfaceSchedNames
                                          (apkg_interface apkg)
                     rule_names = map pfpString (user_rule_names ++ ifc_rule_names)
                 let mkRuleErr r =
                         ioError $ userError (quote r ++
                                              " is not a rule in module " ++
                                              quote modname)
                 when (rule1 `notElem` rule_names) $ mkRuleErr rule1
                 when (rule2 `notElem` rule_names) $ mkRuleErr rule2
                 let rId1 = mk_homeless_id rule1
                     rId2 = mk_homeless_id rule2
                     (disj, rinfo) = getRuleRelation rrdb rId1 rId2
                 return $ TStr (ppDoc (printRuleRelationInfo rId1 rId2 disj rinfo))
----------
tclRule ["full",modname,rule] =
    if (isPrimitiveModule modname)
    then ioError $ userError ("Primitive modules cannot be queried")
    else do
     minfo <- findModule modname
     case minfo of
       Nothing -> ioError $ userError ("Imported modules cannot be queried")
       Just abmi -> do
            -- package contents
            let user_rules = apkg_rules (abemi_apkg abmi)
                ifcs = apkg_interface (abemi_apkg abmi)
                ds = apkg_local_defs (abemi_apkg abmi)
                pps = abemi_pps abmi
                mumap = M.toList $ abemi_method_uses_map abmi
            -- find the rule
            let user_rule_names = map pfpString $ map arule_id user_rules
                ifc_rule_names = map pfpString $ concatMap aIfaceSchedNames ifcs
                isIfcRule = rule `notElem` user_rule_names
            when ((rule `notElem` user_rule_names) &&
                  (rule `notElem` ifc_rule_names)) $
                 ioError $ userError (quote rule ++ " is not a rule in module " ++
                                      quote modname)
            let rId = mk_homeless_id rule
            let isARule r = (arule_id r == rId)
                (attrs, pos, predicate) =
                    if (isIfcRule)
                    then let cvtIfc (AIAction _ _ ifPred ifId ifRs _) =
                                 case (find isARule ifRs) of
                                   Nothing -> Nothing
                                   Just (ARule i ps _ _ rPred _ _ _) ->
                                       Just (ps, getPosition i, aAnds [ifPred, rPred])
                             cvtIfc (AIActionValue _ _ ifPred ifId ifRs _ _) =
                                 case (find isARule ifRs) of
                                   Nothing -> Nothing
                                   Just (ARule i ps _ _ rPred _ _ _) ->
                                       Just (ps, getPosition i, aAnds [ifPred, rPred])
                             cvtIfc (AIDef _ _ _ ifPred (ADef dId _ _ _) _ _) =
                                 if (dId == rId)
                                 then Just ([], getPosition dId, ifPred)
                                 else Nothing
                             cvtIfc _ = Nothing
                         in  case (catMaybes (map cvtIfc ifcs)) of
                               [] -> internalError ("tclRule full: method not found")
                               (res:_) -> res
                    else -- find the ARule
                        case (find isARule user_rules) of
                          Nothing -> internalError ("tclRule full: rule not found")
                          Just (ARule i ps _ _ p _ _ _) -> (ps, getPosition i, p)
            -- separate the doc attribute from the other attributes
            let (doc_attrs, other_attrs) =
                    let isDoc (RPdoc {}) = True
                        isDoc _          = False
                    in  partition isDoc attrs
            -- expand the predicate
            let methodRdys :: [ADef]
                methodRdys = [ v
                             | (AIDef { aif_name = mn, aif_value = v }) <- ifcs
                             , isRdyId mn ]
            let pred_expanded = ppeString (methodRdys ++ ds) bContext predicate
            -- method calls
            -- XXX flattening the MethodUsesMap is expensive?
            let pred_uses =
                    sort [ ppString mId
                            | (mId, uses) <- mumap
                            , (uu, (pred_users, _, _)) <- uses
                            , rId `elem` pred_users ]
                body_uses =
                    sort [ ppString mId
                            | (mId, uses) <- mumap
                            , (uu, (_, body_users, _)) <- uses
                            , rId `elem` body_users ]
            -- relation to other rules if left to the "rel" subcmd
            -- put it all together
            let h_kind = [TStr $ if (isIfcRule) then "method" else "rule"]
                h_pos = showTaggedPosition pos
                h_doc_attrs =
                    let cvtDoc (RPdoc x) = x
                        cvtDoc _ = internalError ("tclRule: cvtDoc")
                    in  if (null doc_attrs)
                        then []
                        else [tagManyStr "doc" (map cvtDoc doc_attrs)]
                h_other_attrs =
                    if (null other_attrs)
                    then []
                    else [tagManyStr "attrs" (map getRulePragmaName other_attrs)]
                h_pred = [tagStr "predicate" pred_expanded]
                h_methods = [tagLst "methods"
                                    [TLst (map TStr pred_uses),
                                     TLst (map TStr body_uses)]]
            return $ TLst $ h_kind ++
                            h_pos ++
                            h_other_attrs ++
                            h_doc_attrs ++
                            h_pred ++
                            h_methods
----------
tclRule xs = internalError $ "tclRule: grammar mismatch: " ++ (show xs)

----------------------------------------------------
data BPackView = BRoot
               | BDir String -- directory where .bo files were read
               | BPackage BPackSub Id
               | LeafType Id String -- Id is type name, and String is constr
               | LeafFunc Id
               | LeafId Id

data BPackSub = Top | Types | Funcs -- Should be able to break to Ifc and Modules

descPackElem :: BPackView -> String
descPackElem e = case e of
                   BRoot            -> "root"
                   BDir _           -> "Directory"
                   BPackage Top _   -> "Package"
                   BPackage Types _ -> "Type List"
                   BPackage Funcs _ -> "Function List"
                   LeafType _ _     -> "Type"
                   LeafFunc _       -> "Function"
                   LeafId _         -> "Unknown"

-- Instance of ExpandInfoHelper to for iwidget tree view
instance ExpandInfoHelper BPackView  where
    --
    getRootElem = return BRoot
    getChildrenf BRoot = do
      g <- readIORef globalVar
      let -- display all paths, not just the ones with loaded packages,
          -- and do it in the order they are specified in the user's path
          paths0 = ifcPath (tp_flags g)

          -- we rely on flag processing to remove empty & duplicate dirs
      return (map BDir paths0)

    --
    -- Find the children of the element
    -- getChildrenf :: BPackView -> IO [BPackView]
    getChildrenf (BDir p) = do
        g <- readIORef globalVar
        let -- make sure the paths end with '/'
            addSlash s = if (lastOrErr "addSlash" s) == '/'
                         then s
                         else s ++ "/"
            pkgs = sortBy cmpIdByName $
                   [ unQualId (ip_id imp)
                         | imp <- M.elems (tp_binmap g),
                           (ip_path imp) == (addSlash p) ]
        return (map (BPackage Top) pkgs)

    getChildrenf (BPackage Top   x) = return [BPackage Funcs x, BPackage Types x]
    getChildrenf (BPackage Types x) = do
        tids <- getPackageContents x True >>= return . (sortBy cmpIdByName)
        symtab <- readIORef globalVar >>= (return . tp_symtab)
        --
        let genLeafs :: Id -> BPackView
            genLeafs tid =
                let econstr = lookupAndShowTypeInfo symtab tid
                in either (const (LeafId tid)) (LeafType tid) econstr
        return $ map genLeafs tids

    getChildrenf (BPackage Funcs x) = do
      tids <- getPackageContents x False  >>= return . (sortBy cmpIdByName)
      return $ map (LeafFunc) tids
    getChildrenf _                  = return []
    --
    -- Get the display text in the tree
    -- getTextf :: BPackView -> IO String
    getTextf BRoot  = return ""
    getTextf  (BDir p)           = do
        g <- readIORef globalVar
        -- replace BLUESPECDIR with "%"
        let bscdir = bluespecDir (tp_flags g)
            replaceBluespecDir s =
                let -- handle bsdir with and without a slash;
                    -- if bsdir doesn't end in a slash, make sure the next
                    -- character is a slash (don't match a prefix);
                    -- remove any duplicate slashes after the bdir
                    rep ['/'] ('/':rs) = Just ("%/" ++ dropWhile (== '/') rs)
                    rep []    ('/':rs) = Just ("%/" ++ dropWhile (== '/') rs)
                    rep (b:bs) (r:rs) | (b == r) = rep bs rs
                    rep _ rest = Nothing
                in  fromMaybe s (rep bscdir s)
        return $ replaceBluespecDir p
    getTextf  (BPackage Top x )  =  return $ getIdBaseString x
    getTextf  (BPackage Types _) =  return $ "Types and Interfaces"
    getTextf  (BPackage Funcs _) =  return $ "Functions and Modules"
    getTextf  (LeafType tid s)   =  return $ getIdBaseString tid
    getTextf  (LeafFunc x)       =  return $ getIdBaseString x
    getTextf  (LeafId x)         =  return $ getIdBaseString x

    getTagsf  _                  = return []

    --
    -- Get the information for the selected element
    getInfof  (BRoot)            = return $ TLst []
    getInfof  (BDir p)           = return $ TStr p
    getInfof  (BPackage Top x )  = return $ tag (getIdBaseString x) (showTaggedPosition x)
    getInfof  (BPackage Types _) = return $ TStr "Types"
    getInfof  (BPackage Funcs _) = return $ TStr "Functions"

    getInfof  (LeafType tid s) = do
      g <- readIORef globalVar
      let flags = tp_flags g
          symtab = tp_symtab g
      et <- parseTypeExpr globalErrHandle flags s
      let es :: Either [EMsg] TypeAnalysis
          es = either Left (analyzeType flags symtab) et
      return $ case es of
                Left err -> TStr $ showErrorList err
                Right ty -> typeAnalysisToDetail ty

    getInfof  (LeafFunc fid) = do
      imp <- lookupImport (getIdQualString fid)
      let (CSignature _ _ _ ds) = ip_csig imp
          ds' = filter (\d -> getName d == Right fid) ds
      case (ds') of
          [d] -> case (displayCDefn d) of
                     [hobj] -> return hobj
                     _ -> return $ TStr (getIdBaseString fid)
          [] -> internalError ("tclBPack: getInfof: def not found: " ++
                               ppReadable fid)
          _  -> internalError ("tclBPack: getInfof: multiple defs: " ++
                               ppReadable fid)

    getInfof  (LeafId x) =
        return $ TStr (getIdBaseString x) -- XXX

-- test function for browsepackage search command
bpackSearchf :: String -> BPackView -> Bool
bpackSearchf rex (LeafType i s) = isJust (matchRegex regex s)
    where regex = mkRegex rex
bpackSearchf rex (LeafFunc i) = isJust (matchRegex regex s)
    where regex = mkRegex rex
          s = getIdBaseString i
bpackSearchf _ _ = False

hideId :: Id -> Bool
hideId i =  (isInternal i) || primFun || primType || underunder
    where primFun = getIdQual i == fsPrelude && take 4 (getIdBaseString i) == "prim"
          primType = getIdQual i == fsPrelude && take 4 (getIdBaseString i) == "Prim"
          underunder = getIdQual i == fsPrelude && take 2 (getIdBaseString i) == "__"


-- Used in bpackageview command
getPackageContents :: Id -> Bool -> IO [Id]
getPackageContents pid typesonly = do
  imp <- lookupImport (getIdBaseString pid)
  let (CSignature _ im cf ds) = ip_csig imp
      ds' = filter (\x -> typesonly == isTDef x) ds
      names = [ i | (Right i) <- map getName ds' ]
      -- names from other packages are include in this def,  filter them here
      names' = filter (\x -> (getIdQual x) == (getIdBase pid)) names
  return $ filter (not . hideId) names'

----

bpackGrammar :: HTclCmdGrammar
bpackGrammar = (tclcmd "browsepackage" namespace helpStr "") .+.
               (oneOf [ listGrammar, detailGrammar, refreshGrammar
                      , nodekindGrammar, searchGrammer, dbgGrammar
                      ])
    where helpStr = "Utility function for viewing package contents"
          listGrammar = (kw "list" "" "") .+. (arg "key" IntArg "integer")
          detailGrammar = (kw "detail" "" "") .+. (arg "key" IntArg "integer")
          refreshGrammar = kw "refresh" "" ""
          nodekindGrammar = (kw "nodekind" "" "") .+. (arg "key" IntArg "integer")
          searchGrammer  = (kw "search" "" "") .+. (arg "regex" StringArg "search regex")
          dbgGrammar = kw "debug" "" ""

tclBPack :: [String] -> IO HTclObj
tclBPack ["list", keystr] = do
  let key :: Int = read keystr
  g <- readIORef globalVar
  let b = tp_packView g
  (b',ro) <- getChildren  b key
  --
  modifyIORef globalVar (\gv -> gv {tp_packView=b'})
  return $ toHTObj ro
----------
tclBPack ["detail", keystr] = do
  let key :: Int = read keystr
  b <- readIORef globalVar >>= (return . tp_packView)
  getInfo b key
----------
tclBPack ["refresh"] = do
  g <- readIORef globalVar
  modifyIORef globalVar (\gv -> gv { tp_packView = initExpandInfoBag })
  return $ TLst []
----------
tclBPack ["nodekind", istr] = do
  let i :: Int = read istr
  g <- readIORef globalVar
  let b = tp_packView g
      e = getEIElement $ lookupEIElement b i
  return $ toHTObj $ descPackElem e
----------
tclBPack ["search",rex] = do
  b <- readIORef globalVar >>= (return . tp_packView)
  (b',fs) <- eieSearch (bpackSearchf rex) b
  modifyIORef globalVar (\gv -> gv {tp_packView=b'})
  return $ toHTObj (reverse fs)
----------
tclBPack ["debug"] = do
  b <- readIORef globalVar >>= (return . tp_packView)
  dmp <- eieDump b
  return $ toHTObj dmp

----------
tclBPack xs = internalError $ "tclBPack: grammar mismatch: " ++ (show xs)

----------------------------------------------------

data BModView = BModule String String

-- Instance of ExpandInfoHelper to for iwidget tree view
instance ExpandInfoHelper BModView  where
    --
    getRootElem = return $ BModule "" ""
    getChildrenf (BModule "" "" ) = do
      g <- readIORef globalVar
      case (tp_mods g) of
          Nothing -> return []
          Just (topmodId, _, _, _, _, _) ->
              let node = BModule "top" (getIdBaseString topmodId)
              in  return [node]
    --
    -- Find the children of the element
    -- getChildrenf :: BModView -> IO [BPackView]
    getChildrenf (BModule instname modname) =
      if (isPrimitiveModule modname)
      then return []
      else do
        minfo <- findModuleHier modname
        case minfo of
          Nothing -> return []
          Just (mods, noinlines) ->
              let mkNode (inst, m) = BModule inst m
              in  return (map mkNode (mods ++ noinlines))
    --
    -- Get the display text in the tree
    -- getTextf :: BModView -> IO String
    getTextf (BModule inst m) =  return $ inst ++ " (" ++ m ++ ")"
    getTagsf _                = return []
    --
    -- Get the information for the selected element
    getInfof  (BModule inst modname) =
      if (isPrimitiveModule modname)
      then return $ tag "primitive" []
      else do
        minfo <- findModule modname
        case minfo of
         Nothing -> return $ tag "import" []
         Just abmi -> do
          let apkg = abemi_apkg abmi
          -- interface type
          let ifcname = pfpString (getModuleIfc abmi)
          -- flattened ifc names
          let ifc_names = map pfpString $
                            filter (not . isRdyId) $
                              map (aIfaceName) (apkg_interface apkg)
          -- rules
          let rule_names = map (pfpString . arule_id) (apkg_rules apkg)
          -- schedule
          let sched = case (abemi_schedule abmi) of
                        Just s -> ppString s
                        Nothing -> ""
          return $
            tag "user"
              [tag "instance" $ [TStr inst],
               tag "module" $ [TStr modname],
               tag "interface" $ [TStr ifcname],
               tag "methods" $ [TLst (map TStr ifc_names)],
               tag "rules" $ [TLst (map TStr rule_names)],
               tag "schedule" $ [TStr sched]]

----

bmodGrammar :: HTclCmdGrammar
bmodGrammar = (tclcmd "browsemodule" namespace helpStr "") .+.
              (oneOf [ listGrammar, detailGrammar, refreshGrammar, dbgGrammar ])
    where helpStr = "Utility function for viewing module hierarchy"
          listGrammar = (kw "list" "" "") .+. (arg "key" IntArg "integer")
          detailGrammar = (kw "detail" "" "") .+. (arg "key" IntArg "integer")
          refreshGrammar = kw "refresh" "" ""
          dbgGrammar = kw "debug" "" ""

tclBMod :: [String] -> IO HTclObj
tclBMod ["list", keystr] =  do
  let key :: Int = read keystr
  g <- readIORef globalVar
  let b = tp_modView g
  (b',ro) <- getChildren b key
  --
  modifyIORef globalVar (\gv -> gv {tp_modView=b'})
  obj <- toTclObj ro
  return $ TCL obj
----------
tclBMod ["detail", keystr] = do
  let key :: Int = read keystr
  b <- readIORef globalVar >>= (return . tp_modView)
  getInfo b key
----------
tclBMod ["refresh"] =  do
  g <- readIORef globalVar
  modifyIORef globalVar (\gv -> gv { tp_modView = initExpandInfoBag })
  return $ TLst []
----------
tclBMod ["debug"] = do
  b <- readIORef globalVar >>= (return . tp_modView)
  dmp <- eieDump b
  return $ TLst dmp
----------
tclBMod xs = internalError $ "tclBMod: grammar mismatch: " ++ (show xs)


----------------------------------------------------
-- Hierarchy viewer using BSVInstance structures
data BInst = BInstRoot
            | BNode  {binst_sub     :: BInstSub
                     ,binst_mod     :: (String, ABinEitherModInfo)   -- containing module (ba file)
                     ,binst_name    :: String   -- this instance name
                     ,binst_bsvh    :: [String] -- full bsv hierarcry
                     ,binst_synth   :: [String] -- bsv generate hier (flattened)
                     ,binst_localh  :: [String] -- local path from synth to here
                     ,binst_hide     :: Bool     -- is instance hidden?
                     ,binst_hideall  :: Bool
                     }


data BInstSub = BTop   -- Top file -- no type information :-(
              | BMod  { bin_name :: Id
                       ,bin_uname :: Id
                       ,bin_type :: Maybe CType
                       ,bin_module :: (String,ABinModInfo)
                      } -- Synthesized child module,  string is this module (.ba) name
              | BINode { bin_name :: Id
                        ,bin_type :: Maybe CType
                        ,bin_children :: InstTree
                       } -- internal node
              | BLeaf { bin_name :: Id
                       ,bin_uname :: Id
                       ,bin_type :: Maybe CType
                       ,bin_prim :: String
                      } -- Rule with full name
              | BRule { bin_name :: Id
                       ,bin_uname :: Id
                      } -- local rule name, unique rule name

instance PPrint BInstSub where
    pPrint d p bin@(BTop) = text "BTop"
    pPrint d p bin@(BMod {}) = text "BMod" <+> pfPrint d p (bin_name bin) <+> pfPrint d p (bin_type bin)
    pPrint d p bin@(BINode {}) = text "BINode" <+> pfPrint d p (bin_name bin) <+> pfPrint d p (bin_type bin)
    pPrint d p bin@(BRule {}) = text "BRule" <+> pfPrint d p (bin_name bin) <+> parens (pfPrint d p (bin_uname bin))
    pPrint d p bin@(BLeaf {}) = text "BLeaf" <+> pfPrint d p (bin_name bin) <+> text (bin_prim bin) <+> pfPrint d p (bin_type bin)

comparebis ::   BInstSub -> BInstSub -> Ordering
comparebis BTop BTop = EQ
comparebis BTop _ = GT
comparebis _ BTop = LT
comparebis l r =
 let res = comparing (getPosition . bin_name) l r
 in if (res == EQ) then cmpSuffixedIdByName (bin_name l) (bin_name r) else res
-- comparebis l@(BRule {})  r@(BRule {}) = comparing bin_name l r
-- comparebis _ (BRule {}) = LT
-- comparebis (BRule {}) _ = GT
-- comparebis _ _ = EQ

comparebi :: BInst -> BInst -> Ordering
comparebi (BInstRoot) (BInstRoot) = EQ
comparebi (BInstRoot) (BNode {}) = LT
comparebi (BNode {}) (BInstRoot) = GT
comparebi (BNode {binst_sub = stl, binst_name = nl}) (BNode {binst_sub = str, binst_name = nr}) =
    let stc = comparebis stl str
    in if (stc == EQ) then compare nl nr else stc

bInstSearchf :: String -> BInst -> Bool
bInstSearchf _ BInstRoot = False
bInstSearchf rex x@(BNode {}) = minst || msub (binst_sub x)
    where match :: String -> Bool
          match = isJust . matchRegex (mkRegex rex)
          minst = match $ binst_name x
          msub :: BInstSub -> Bool
          msub s@(BMod {})   = (match $ getIdBaseString $ bin_name s)
          msub s@(BLeaf {})  = (match $ getIdBaseString $ bin_name s)
          msub s@(BRule {})  = (match $ getIdBaseString $ bin_name s)
          msub s@(BINode {}) = (match $ getIdBaseString $ bin_name s)
          msub _             = False


-- True for a synthesized hierarchy
addInst :: BInst -> (Maybe String) -> String -> BInst
addInst BInstRoot _ _ = BInstRoot
addInst b@(BNode {}) (Just unique)  inst = b {binst_name = inst
                                    ,binst_bsvh = inst:(binst_bsvh b)
                                    ,binst_synth = unique:(binst_synth b)
                                    ,binst_localh = []
                                    ,binst_hide = False
                                    ,binst_hideall = False}
addInst b@(BNode {}) Nothing inst = b {binst_name = inst
                                    ,binst_bsvh = inst:(binst_bsvh b)
                                    ,binst_localh = inst:(binst_localh b)
                                    ,binst_hide = False
                                    ,binst_hideall = False}

getBInstChildren :: BInst -> IO [BInst]
getBInstChildren BInstRoot = do
      g <- readIORef globalVar
      case (tp_mods g) of
          Nothing -> return []
          Just (topmodId, _, _, _, _, _) -> do
              mminfo <- findModule $ getIdBaseString topmodId
              let err = error "Could not find top module"
                  minfo = fromMaybe err mminfo
              let node = BNode { binst_sub = BTop,
                                 binst_mod = (getIdBaseString topmodId, minfo),
                                 binst_name = (getIdBaseString topmodId),
                                 binst_bsvh = [], binst_synth = [],
                                 binst_localh = [], binst_hide = False, binst_hideall = False}
              return [node]
getBInstChildren b@(BNode {binst_sub = sub}) =
       do flags <- getGFlags
          let hide = (not (tclShowHidden flags))
              nodeIgnore inode = (node_ignore inode) || (hide && isHiddenKP inode)
              getChildrenS :: BInstSub  -> IO [BInst]
              getChildrenS BTop =
                  do let (m, ba) = binst_mod b
                         nodes = getInstTreeList hide (apkg_inst_tree $ abemi_apkg ba)
                     nss <- mapM (mkChildIN (m,ba) False) nodes
                     return $ concat nss
              getChildrenS (BRule {}) = return []
              getChildrenS (BLeaf {}) = return []
              getChildrenS bs@(BMod {}) =
                  do let (m,ba0) = bin_module bs
                         ba = Right ba0
                         nodes = getInstTreeList' hide (apkg_inst_tree $ abemi_apkg ba)
                     nss <- mapM (mkChildIN (m,ba) False) nodes
                     return $ concat nss
              getChildrenS bs@(BINode {}) =
                  do let (m,ba) = binst_mod b
                         nodes = getInstTreeList hide (bin_children bs)
                         allowBody = isLoop bs
                     nss <- mapM (mkChildIN (m,ba) allowBody) nodes
                     return $ concat nss
              --
              isLoop :: BInstSub -> Bool
              isLoop BINode { bin_name = name } | (getIdBase name) == fsLoop = True
              isLoop _ = False
              --
              mkChildIN :: (String, ABinEitherModInfo) -> Bool -> InstNode -> IO [BInst]
              mkChildIN _ _ inodep | isSynthP hide inodep =
                do let unique = fromJustOrErr "bluetcl.mkChildIN: unique" $
                                  getSynthName hide inodep
                   mminfo <- findModuleByInstance (reverse $ (getIdBaseString $ unique) : binst_synth b)
                   let b_add = addInst b (Just  (getIdBaseString $ unique))
                                 (getIdBaseString $ node_name inodep)
                       hidden = isHidden inodep
                       hide_all = isHiddenAll inodep
                       b' = b_add {binst_hide = hidden, binst_hideall = hide_all}
                       b'' = case mminfo of
                                Left pname  -> let bsub = BLeaf { bin_name  = node_name inodep
                                                                , bin_uname = unique
                                                                , bin_type  = node_type inodep
                                                                , bin_prim  = pname }
                                               in b' { binst_sub = bsub }
                                Right minfo@(m,ba)
                                            -> let eminfo = (m, Right ba)
                                                   bsub = BMod { bin_module = minfo
                                                               , bin_type   = node_type inodep
                                                               , bin_name   = node_name inodep
                                                               , bin_uname  = unique
                                                               }
                                               in b' { binst_sub = bsub, binst_mod = eminfo }
                   return $ [b'']
              mkChildIN (m,ba) _ inode@(StateVar {}) = -- this case should be impossible
                internalError $ "mkChildIN: " ++ (show inode)
              --
              mkChildIN (m,ba) allowBody inode@(Loc { node_name = name } ) | nodeIgnore inode =
                do let nodes  = getInstTreeList hide (node_children inode)
                       keep_prop prop = not (isSuffixCountProp prop)
                       name'  = rmIdPropBy name keep_prop
                       name'' = setIdBase name' fsBody
                       inode' = inode { node_ignore = False, node_name = name'' }
                   nss <- concatMapM (mkChildIN (m,ba) False) nodes
                   nss' <- if (allowBody && ((length nss) > 1))
                           then (mkChildIN (m,ba) False inode')
                           else return nss
                   return $ nss'
              mkChildIN (m,ba) _ inode@(Rule {}) =
                  do let b' = addInst b Nothing  (getIdBaseString $ node_name inode)
                         bsub = BRule { bin_name = node_name inode,
                                        bin_uname = node_name inode }
                     return $ [b' { binst_sub = bsub, binst_mod = (m,ba)  }]
              -- rule with identical parent node
              mkChildIN (m,ba) _ inode | isRuleP hide inode =
                  do let b' = addInst b Nothing  (getIdBaseString $ node_name inode)
                         rule = node_name $ head $ (getInstTreeList hide (node_children inode))
                         bsub = BRule { bin_name = node_name inode,
                                        bin_uname = rule }
                     return $ [b' { binst_sub = bsub, binst_mod = (m,ba)  }]
              mkChildIN (m,ba) _ inode =
                  do let b' = addInst b Nothing (getIdBaseString $ node_name inode)
                         bsub = BINode { bin_children = node_children inode
                                      , bin_type = node_type inode
                                      , bin_name = node_name inode }
                     return $ [b' { binst_sub = bsub, binst_mod = (m,ba) }]
          children <- getChildrenS sub
          return children

instance ExpandInfoHelper BInst where
    getRootElem = return BInstRoot
    --
    getChildrenf b =
        do flags <- getGFlags
           let hide = (not (tclShowHidden flags))
               isEnd         BNode {binst_hideall = h} = h && hide
               isEnd         _                         = False
               isHiddenBInst BNode {binst_hide    = h} = h && hide
               isHiddenBInst _                         = False
               getList x | isEnd x = return []
               getList x | isHiddenBInst x = getBInstChildren x
               getList x = return [x]
           x <- getBInstChildren b
           concatMapM getList x
    --
    getTextf (BInstRoot) = return "ROOT"
    getTextf (BNode {binst_sub = st, binst_name = nm}) = return $ nm ++ subinfo st
        where ignores = []
              ptype :: Type -> String
              ptype t = let x = toPrintable $ docToOneLine (pfPrint PDNoqual 0 t)
                        in if (x `elem` ignores) then "" else "  " ++ x
              --
              subinfo :: BInstSub -> String
              subinfo (BMod {bin_type = Just t}) = ptype t
              subinfo (BINode {bin_type = Just t}) = ""
              subinfo (BLeaf {bin_type = Just t}) = ptype t
              subinfo (BRule {}) = ""
--              subinfo (BRule {}) = "  (rule)"
              subinfo _ = ""

    --
    getTagsf (BNode {binst_sub = sub}) | (getKind sub) == "Rule"        = return ["rule"]
                                       | (getKind sub) == "Synthesized" = return ["synth"]
                                       | (getKind sub) == "Primitive"   = return ["prim"]
    getTagsf _                                                          = return []
    --
    getInfof (BInstRoot) = return $ toHTObj ["Node", "ROOT"]
    getInfof b@(BNode {}) = return $
        TLst $ [TStr "Node",  toHTObj $ getKind $ binst_sub b
               ,TStr "Name",  toHTObj $ binst_name b
               ,TStr "BSVPath", toHTObj (reverse $ binst_bsvh b)
               ,TStr "SynthPath", toHTObj (reverse $ binst_synth b)
               ,TStr "LocalPath", toHTObj (reverse $ binst_localh b)
               ,TStr "BSVModule", toHTObj $ getBA $ binst_sub b
               ] ++ getPos (binst_sub b) ++ getAux (binst_sub b)
                 ++ [TStr "DEBUG", toHTObj $ getDebug (binst_sub b)]
        --
            where getBA :: BInstSub -> String
                  getBA (BMod {bin_module = (m,ba)} ) = m
                  getBA _        = let (m,ba) = binst_mod b in m
                  --
                  getPos :: BInstSub -> [HTclObj]
                  getPos (BTop) = []
                  getPos bin = getPositionPair $ bin_name bin
                  --
                  getAuxType :: Maybe CType -> [HTclObj]
                  getAuxType Nothing = []
                  getAuxType (Just t) = [TStr "Interface", toHTObj t]
                   ++ let p =  getPosition t
                      in if (isRealPosition p) then [TStr "IfcPosition", toHTObj $ tclPosition p] else []
                  --
                  getAux :: BInstSub -> [HTclObj]
                  getAux (BTop) =
                      [TStr "Module", toHTObj ""]
                      ++ [TStr "UniqueName", toHTObj ""]
                  getAux (BLeaf {bin_type = mt, bin_prim = prim, bin_uname = n}) =
                      [TStr "Module", toHTObj $ prim]
                      ++ [TStr "UniqueName", toHTObj n]
                      ++ getAuxType mt
                  getAux (BINode {bin_type = mt}) = getAuxType mt
                  getAux (BMod {bin_type = mt, bin_module = (m,ba), bin_uname = n}) =
                      [TStr "Module", toHTObj $ m]
                      ++ [TStr "UniqueName", toHTObj n]
                      ++ getAuxType mt
                  getAux (BRule {  bin_uname =rn }) =
                      [TStr "RuleName", toHTObj $ rn]
                  --
                  getDebug ::  BInstSub -> Doc
                  getDebug n = pPrint PDReadable 0 n
        --
    {- TODO  get at the position information
                  --
                  -- Auxiliary info
                  getIfcMod :: Bool -> BSVInstance -> [HTclObj]
                  getIfcMod False _ = []
                  getIfcMod True  i = [TStr "Interface",      toHTObj (bsvi_ifc_name i)
                                      ,TStr "IfcPosition",    fullPositionToTObj $ getPosition (bsvi_ifc_name i)
                                      ,TStr "Module",         toHTObj (bsvi_def_name i)
                                      ,TStr "ModulePosition", fullPositionToTObj $ getPosition (bsvi_def_name i)
                                      ]
-}

getKind :: BInstSub -> String
getKind (BTop {}) = "Synthesized"
getKind (BMod  {}) = "Synthesized"
getKind (BINode {}) = "Instance"
getKind (BRule {}) = "Rule"
getKind (BLeaf {}) = "Primitive"

getInstTreeList :: Bool -> InstTree -> [InstNode]
getInstTreeList hide t =
 let result = getInstTreeList' hide t
     getMyChildren x = concatMap promote (M.elems $ node_children x)
     promote x@(Loc {node_name = nm, node_ignore = True}) | isBadId nm = getMyChildren x
     promote x                                                         = [x]
 in case (result) of
    [x@(Loc {})] | (isHiddenAll x && hide) -> []
    [x@(Loc {})] | (isHidden x && hide)    -> sortBy comparein (getMyChildren x)
    _                                      -> result

getInstTreeList' :: Bool -> InstTree -> [InstNode]
getInstTreeList' False t = processInstNodes $ (sortBy comparein (M.elems t))
getInstTreeList' True  t =
  let getList x | isHiddenAll x = []
      getList x@(Loc {}) | isHiddenKP x    = concatMap getList (sortBy comparein (getMyChildren x))
      getList x | isHiddenKP x = []
      getList x = [x]
      getMyChildren x = concatMap promote (M.elems $ node_children x)
      promote x@(Loc {node_name = nm, node_ignore = True}) | isBadId nm = getMyChildren x
      promote x                                                         = [x]
  in processInstNodes $ concatMap getList (sortBy comparein (concatMap promote (M.elems t)))

-- sort before processing to get better orders
processInstNodes :: [InstNode] -> [InstNode]
processInstNodes = map processInstNode

processInstNode :: InstNode -> InstNode
processInstNode node@(Loc { node_name = name }) = node'
  where node' = node { node_name = (addIdDisplayName name) }
processInstNode node                            = node

isSynthP :: Bool -> InstNode -> Bool
isSynthP True i | isHiddenKP i  = False
isSynthP True i | isHiddenAll i = False
isSynthP hide i@(Loc {}) = case (nodeChildren hide i) of
                               [StateVar {}] -> True
                               _             -> False
isSynthP _ _ = False

isRuleP :: Bool -> InstNode -> Bool
isRuleP True i | isHiddenKP i = False
isRuleP hide i@(Loc {}) = case (nodeChildren hide i) of
                      [Rule {}] -> True -- should the name be contained?
                      _         -> False
isRuleP _ _ = False

getSynthName :: Bool -> InstNode -> Maybe Id
getSynthName hide i@(Loc {}) = case (nodeChildren hide i) of
                       [StateVar {node_name = name}] -> Just name
                       _ -> Nothing
getSynthName _ _ = Nothing

---------------------------
-- browseinstance  tcl command
binstGrammar :: HTclCmdGrammar
binstGrammar = (tclcmd "browseinst" namespace helpStr "") .+.
              (oneOf [ listGrammar, detailGrammar, refreshGrammar, dbgGrammar, searchGrammar ])
    where helpStr = "Utility function for viewing instance hierarchy"
          listGrammar = (kw "list" "" "") .+. (arg "key" IntArg "integer")
          detailGrammar = (kw "detail" "" "") .+. (arg "key" IntArg "integer")
          refreshGrammar = kw "refresh" "" ""
          dbgGrammar = kw "debug" "" ""
          searchGrammar = (kw "search"  "Search packages for names matching a regular expression" "") .+.
                          (arg "regex" StringArg "regular expression")

tclBrowseInst :: [String] -> IO HTclObj
tclBrowseInst ["list", keystr] = do
  g <- readIORef globalVar
  let b = tp_instView g
      key :: Int = read keystr
  (b',ro) <- getChildren b key
  --
  modifyIORef globalVar (\gv -> gv {tp_instView=b'})
  return (toHTObj ro)

----------
tclBrowseInst ["detail", keystr] = do
  g <- readIORef globalVar
  let b = tp_instView g
      key :: Int = read keystr
  getInfo b key
----------
tclBrowseInst ["refresh"] = do
  g <- readIORef globalVar
  modifyIORef globalVar (\gv -> gv { tp_instView = initExpandInfoBag })
  return $ TLst []
----------
tclBrowseInst ["debug"] = do
  g <- readIORef globalVar
  let b = tp_instView g
  eieDump b >>= (return . TLst)
----------
tclBrowseInst ["search",rex] = do
  b <- readIORef globalVar >>= (return . tp_instView)
  (b',fs) <- eieSearch (bInstSearchf rex) b
  modifyIORef globalVar (\gv -> gv {tp_instView=b'})
  return $ toHTObj (reverse fs)

----------
tclBrowseInst xs = internalError $ "tclBrowseInst: grammar mismatch: " ++ (show xs)


----------------------------------------------------

data BTypeView = BTypeViewRoot
               | BType CType TypeAnalysis
               | StructField Id (Qual Type) TypeAnalysis
               | UnionTag Id Type TypeAnalysis
               | InterfaceField Bool Id (Qual Type) [IfcPragma] TypeAnalysis
               | BTVUnknown

-- Instance of ExpandInfoHelper to for iwidget tree view
instance ExpandInfoHelper BTypeView  where
    --
    getRootElem = return BTypeViewRoot
    getChildrenf BTypeViewRoot = do
      g <- readIORef globalVar
      let ts = fst $ tp_typeView g
      return (map (\ (t,a) -> BType t a) ts)

    --
    -- Find the children of the element
    -- getChildrenf :: BTypeView -> IO [BTypeView]
    getChildrenf (BType _ ta) = getChildrenFromTypeA ta
    getChildrenf (StructField i (_ :=> t) ta) = getChildrenFromTypeA ta
    getChildrenf (UnionTag i t ta) = return [(BType t ta)]
    getChildrenf (InterfaceField is_subifc _ (_ :=> t) _ ta) =
        getChildrenFromTypeA ta
    getChildrenf (BTVUnknown) = return []

    --
    -- Get the display text in the tree
    -- getTextf :: BTypeView -> IO String
    getTextf (BTypeViewRoot) = return "root"
    getTextf (BType t ta) = return $ (pfpStringNQ t) ++ parenStr (typeAnalysisShort ta) ++ pwidth ta
    getTextf (StructField i t ta) = return $ pfpStringNQ i ++ " " ++ (pfpStringNQ t) ++ pwidth ta
    getTextf (UnionTag i t ta) = return $ "tagged " ++ pfpStringNQ  i ++ " " ++
                                           pfpStringNQ t ++ parenStr (typeAnalysisShort ta)++ pwidth ta
    getTextf (InterfaceField is_subifc i qt _ _) =
        if (is_subifc)
        then return $ "interface " ++ pfpStringNQ qt ++ " " ++ pfpStringNQ i
        else return $ "method " ++ pfpStringNQ i
    getTextf (BTVUnknown) = return "Unknown"

    getTagsf _            = return []
    --
    -- Get the detail information for the selected element
    -- format for workstation
    getInfof (BTypeViewRoot) = return $ TLst []
    getInfof (BType t a) = return $ typeAnalysisToDetail a
    getInfof (StructField i qt ta) =
        return $ tag "field" ( [TStr $ pfpString i,
                                tagLst "Type" [TStr $ pfpString qt]] ++
                               (showWidth $ getWidth ta))
    getInfof (UnionTag i t ta) =
        return $ tag "union" ([tagLst "tag" [TStr $ pfpString i],
                               tagLst "Type" [TStr $ pfpString t]] ++
                              (showWidth $ getWidth ta))
    getInfof (InterfaceField is_subifc fid qt ps ta) =
        if (is_subifc) then return $ typeAnalysisToDetail ta
        else return $ tag "method" [tagLst "" [interfaceFieldToDetail (is_subifc,fid,qt,ps)]]
    getInfof (BTVUnknown) = return (TStr "Unknown")

parenStr :: String -> String
parenStr [] = ""
parenStr s = " (" ++ s ++ ")"

pwidth :: TypeAnalysis -> String
pwidth a = maybe "" (parenStr . show) (getWidth a)

getChildrenFromTypeA :: TypeAnalysis -> IO [BTypeView]
getChildrenFromTypeA (List _ t) = do
  ma <- getTypeAnalysis t
  return $ case ma of
             Nothing ->  []
             Just a  ->  [(BType t a)]
getChildrenFromTypeA (Vector _ _ t _) = do
  ma <- getTypeAnalysis t
  return $ case ma of
             Nothing ->  []
             Just a  ->  [(BType t a)]
getChildrenFromTypeA (Alias _ _ _ t) = do
  ma <- getTypeAnalysis t
  return $ case ma of
             Nothing ->  []
             Just a  -> [(BType t a)]
getChildrenFromTypeA (Struct _ _ _ _ fs _ ) =  mapM mkField fs
    where mkField (i, qt@(_ :=> t), mw) = do
            mta <- getTypeAnalysis t
            return $ case mta of
                       Nothing -> BTVUnknown
                       Just ta -> StructField i qt ta
getChildrenFromTypeA (TaggedUnion _ _ _ _ ts _) =   mapM mkTag ts
    where mkTag (i, t, mi) = do
            ma <- getTypeAnalysis t
            return $ case ma of
                       Nothing -> BTVUnknown
                       Just a  -> UnionTag i t a
getChildrenFromTypeA (Interface _ _ _ _ fs _) = mapM mkField fs
    where  mkField (b, i, qt@(_ :=> t), ps) = do
             ma <- getTypeAnalysis t
             return $ case ma of
                       Nothing -> BTVUnknown
                       Just a  -> InterfaceField b i qt ps a
-- XXX Enum??
getChildrenFromTypeA _ = return []


getTypeAnalysis :: CType -> IO (Maybe TypeAnalysis)
getTypeAnalysis t = do
    g <- readIORef globalVar
    let flags = tp_flags g
        symtab = tp_symtab g
    case (analyzeType flags symtab t) of
        Left _  -> return $ Nothing
        Right a -> return $ Just a

getTypeAnalysis' :: CType -> Bool -> IO (Maybe TypeAnalysis)
getTypeAnalysis' t primpair_is_interface = do
    g <- readIORef globalVar
    let flags = tp_flags g
        symtab = tp_symtab g
    case (analyzeType' flags symtab t primpair_is_interface) of
        Left _  -> return $ Nothing
        Right a -> return $ Just a

----

btypeGrammar :: HTclCmdGrammar
btypeGrammar = (tclcmd "browsetype" namespace helpStr "") .+.
               (oneOf [ addGrammar, listGrammar, clearGrammar
                      , detailGrammar, refreshGrammar, dbgGrammar
                      ])
    where helpStr = "Utility function for viewing types"
          addGrammar = (kw "add" "" "") .+. (arg "type" StringArg "type")
          listGrammar = (kw "list" "" "") .+. (arg "key" IntArg "integer")
          clearGrammar = kw "clear" "" ""
          detailGrammar = (kw "detail" "" "") .+. (arg "key" IntArg "integer")
          refreshGrammar = kw "refresh" "" ""
          dbgGrammar = kw "debug" "" ""

tclBType :: [String] -> IO HTclObj
tclBType ["add",s] = do
  g <- readIORef globalVar
  let (ts, b) = tp_typeView g
      flags = tp_flags g
      symtab = tp_symtab g
  -- parse the type
  et <- parseTypeExpr globalErrHandle flags s
  let eta :: Either [EMsg] (CType, TypeAnalysis)
      eta = case (et) of
              Left errs -> Left errs
              Right t -> case (analyzeType flags symtab t) of
                           Left errs -> Left errs
                           Right a -> Right (t,a)
  case (eta) of
    Left errs -> do reportErrorsToTcl [] errs
                    -- not reachable if errs not null
                    return $ TLst []
    Right (t,a) -> do let ts' = ts ++ [(t,a)]
                          b' = initExpandInfoBag
                      modifyIORef globalVar (\gv -> gv { tp_typeView = (ts', b') })
                      return $ TLst []
----------
tclBType ["clear"] = do
  g <- readIORef globalVar
  modifyIORef globalVar (\gv -> gv { tp_typeView = ([], initExpandInfoBag) })
  return $ TLst []
----------
tclBType ["list", keystr] = do
  let key :: Int = read keystr
  g <- readIORef globalVar
  let (ts, b) = tp_typeView g
  (b',ro) <- getChildren  b key
  --
  modifyIORef globalVar (\gv -> gv { tp_typeView = (ts, b') })
  obj <- toTclObj ro
  return $ TCL obj
----------
tclBType ["detail", keystr] = do
  let key :: Int = read keystr
  b <- readIORef globalVar >>= (return . snd . tp_typeView)
  getInfo b key
----------
tclBType ["debug"] = do
  b <- readIORef globalVar >>= (return . snd . tp_typeView)
  dmp <- eieDump b
  return $ TLst dmp
----------
tclBType ["refresh"] = do
  g <- readIORef globalVar
  let (ts, _) = tp_typeView g
  modifyIORef globalVar (\gv -> gv { tp_typeView = (ts, initExpandInfoBag) })
  return $ TLst []
----------
tclBType xs = internalError $ "tclBType: grammar mismatch: " ++ (show xs)

----------------------------------------------------

cvtMaybe :: (TclObjCvt a) => Maybe a -> IO [HTclObj]
cvtMaybe Nothing  = return []
cvtMaybe (Just x) = toTclObj x >>= (\o -> (return [(TCL o)]))

cvtMaybeWith :: (TclObjCvt a) => HTclObj -> Maybe a -> IO [HTclObj]
cvtMaybeWith _ Nothing  = return []
cvtMaybeWith h (Just x) = toTclObj x >>= (\o -> (return [TLst [h,(TCL o)]]))



----------------------------------------------------
-- Bluesim simulation control command

simGrammar :: HTclCmdGrammar
simGrammar = (tclcmd "sim" namespace helpStr "") .+.
             (oneOf [ argGrammar, cdGrammar, clockGrammar, configGrammar
                    , describeGrammar, getGrammar, getRangeGrammar, loadGrammar
                    , lookupGrammar, lsGrammar, nextEdgeGrammar, pwdGrammar
                    , runGrammar, runToGrammar
                    , stepGrammar, stopGrammar, syncGrammar, timeGrammar
                    , timescaleGrammar
                    , unloadGrammar, upGrammar, vcdGrammar, verGrammar
                    ])
    where helpStr = "Control Bluesim simulation"
          argGrammar = (kw "arg" "Set a simulation plus-arg" "") .+.
                       (atLeast 1 $ arg "arg" StringArg "plus-arg string")
          cdGrammar = (kw "cd" "Change location in hierarchy" "") .+.
                       (optional $ arg "path" StringArg "target instance")
          clockGrammar = (kw "clock" "Show or select current clock domain" "") .+.
                         (optional $ arg "name" StringArg "clock domain name")
          configGrammar = (kw "config" "Show or change simulator configuration" "") .+.
                          (optional $ oneOf [ (kw "interactive" "Include edges with no logic" "")
                                            ])
          describeGrammar = (kw "describe" "Describe the object to which a symbol handle refers" "") .+.
                            (atLeast 1 $ arg "handle" PtrArg "symbol handle")
          getGrammar = (kw "get" "Get simulation value" "") .+.
                       (atLeast 1 $ arg "handle" PtrArg "symbol handle")
          getRangeGrammar = (kw "getrange" "Get simulation values from a range" "") .+.
                       (arg "handle" PtrArg "symbol handle") .+.
                       (arg "addr1" IntArg "address or start address") .+.
                       (optional $ arg "addr2" IntArg "end address")
          loadGrammar = (kw "load" "Load a bluesim model object" "") .+.
                        (arg "model" StringArg "Bluesim model file") .+.
                        (arg "top" StringArg "Top-level module name")
          lookupGrammar = (kw "lookup" "Lookup symbol handles" "") .+.
                          (arg "pattern" StringArg "Symbol name (wildcards allowed)") .+.
                          (optional $ arg "root" PtrArg "Starting point for lookup")
          lsGrammar = (kw "ls" "List symbols" "") .+.
                       (atLeast 0 $ arg "pattern" StringArg "Symbol name (wildcards allowed)")
          nextEdgeGrammar = (kw "nextedge" "Advance simulation to the next clock edge in any domain" "")
          pwdGrammar = (kw "pwd" "Print current location in hierarchy" "")
          runGrammar = (kw "run" "Run simulation to completion" "") .+.
                       (optional $ kw "async" "" "")
          runToGrammar = (kw "runto" "Run simulation to a given time" "") .+.
                         (arg "time" IntArg "Time at which to stop simulation") .+.
                       (optional $ kw "async" "" "")
          stepGrammar = (kw "step" "Advance simulation a given number of cycles" "") .+.
                        (optional $ arg "cycles" IntArg "Number of cycles to advance") .+.
                        (optional $ kw "async" "" "")
          stopGrammar = kw "stop" "Stop a running simulation" ""
          syncGrammar = kw "sync" "Wait for simulator execution to complete" ""
          timeGrammar = kw "time" "Display current simulation time" ""
          timescaleGrammar = (kw "timescale" "Specify simulation timescale" "") .+.
                             (arg "timescale" StringArg "simulation timescale (Verilog-format)")
          unloadGrammar = kw "unload" "Unload the current bluesim model" ""
          upGrammar = (kw "up" "Move up the module hierarchy" "") .+.
                      (optional $ arg "N" IntArg "number of levels")
          vcdGrammar = (kw "vcd" "Control dumping waveforms to a VCD file" "") .+.
                       (optional $ oneOf [ (kw "on" "Turn on VCD dumping" "")
                                         , (kw "off" "Turn off VCD dumping" "")
                                         , (arg "file" StringArg "Dump to named VCD file")
                                         ])
          verGrammar = kw "version" "Show Bluesim model version information" ""

tclSim :: [String] -> IO HTclObj
----------
tclSim ("arg":ss) = do
  g <- readIORef globalVar
  case (tp_bluesim g) of
    Just bs -> do mapM_ (bk_append_argument bs) ss
                  return $ TLst []
    Nothing -> ioError $ userError ("There is no bluesim model loaded")
----------
tclSim ("cd":args) = do
  g <- readIORef globalVar
  case (tp_bluesim g) of
    Just bs -> if (null args)
               then do top_sym <- bk_top_symbol bs
                       let mbs = Just (bs { current_directory = [top_sym] })
                       modifyIORef globalVar (\gv -> gv { tp_bluesim = mbs })
                       return $ TLst []
               else do dirs <- lookupSymbols bs (head args) Nothing
                       case dirs of
                         [] -> ioError $ userError ("No such instance: " ++ (head args))
                         [dir'] -> do let mbs = Just (bs { current_directory = dir' })
                                      modifyIORef globalVar (\gv -> gv { tp_bluesim = mbs })
                                      return $ TLst []
                         _ -> do let base = current_directory bs
                                 dnames <- mapM (mkDirString bs base) dirs
                                 ioError $ userError $ unlines
                                  ("Ambiguous directory specification could match:":dnames)
    Nothing -> ioError $ userError ("There is no bluesim model loaded")
----------
tclSim ("clock":args) = do
  g <- readIORef globalVar
  case (tp_bluesim g, args) of
    (Just bs, [])    -> do cs <- getClockInfo bs
                           obj <- toTclObj cs
                           return $ TCL obj
    (Just bs, [clk]) -> do mbs <- setActiveClock bs clk
                           when (isNothing mbs) $
                                ioError $ userError ("'" ++ clk ++ "' is not a valid clock name")
                           modifyIORef globalVar (\gv -> gv { tp_bluesim = mbs })
                           return $ TLst []
    (Just bs, _)     -> internalError $ "tclSim: grammar mismatch: " ++ (show args)
    (Nothing,_)      -> ioError $ userError ("There is no bluesim model loaded")
----------
tclSim ("config":args) = do
  g <- readIORef globalVar
  case (tp_bluesim g, args) of
    (Just bs, [])    -> do obj <- toTclObj ("interactive", is_interactive bs)
                           return $ TLst [TCL obj]
    (Just bs, ["interactive"]) -> do let bs' = bs { is_interactive = True }
                                     bk_set_interactive bs
                                     modifyIORef globalVar (\gv -> gv { tp_bluesim = Just bs' })
                                     return $ TLst []
    (Just bs, _)     -> internalError $ "tclSim: grammar mismatch: " ++ (show args)
    (Nothing,_)      -> ioError $ userError ("There is no bluesim model loaded")
--------------------
tclSim ("describe":hdls) = do
  g <- readIORef globalVar
  case (tp_bluesim g,hdls) of
    (Just bs,[]) -> internalError $ "tclSim: grammar mismatch: " ++ (show hdls)
    (Just bs,_)  -> do let syms = map read hdls
                       names <- mapM (bk_get_key bs) syms
                       descs <- mapM (describeSym bs) syms
                       objs  <- mapM toTclObj (zip names descs)
                       return $ case objs of
                                 [o] -> TCL o
                                 os  -> TLst (map TCL os)
    (Nothing,_)  -> ioError $ userError ("There is no bluesim model loaded")
--------------------
tclSim ("get":hdls) = do
  g <- readIORef globalVar
  case (tp_bluesim g, hdls) of
    (Just bs, []) -> internalError $ "tclSim: grammar mismatch: " ++ (show hdls)
    (Just bs, _)  -> do ptrs <- mapM (handleModuleRedirect bs) (map read hdls)
                        vs <- mapM (bk_peek_symbol_value bs) ptrs
                        let bad = [ (p,v) | (p,v) <- zip ptrs vs, v == NoValue ]
                        when (not (null bad)) $
                             do let bad_syms = map fst bad
                                bad_names <- mapM (bk_get_key bs) bad_syms
                                let msg = "Cannot get value for symbol(s): " ++
                                          (intercalate ", " bad_names)
                                ioError $ userError msg
                        return $ case (map show vs) of
                                   [x] -> TStr x
                                   xs  -> TLst (map TStr xs)
    (Nothing,_)   -> ioError $ userError ("There is no bluesim model loaded")
--------------------
tclSim ("getrange":args) = do
  g <- readIORef globalVar
  case (tp_bluesim g, args) of
    (Just bs, [hdl,addr]) ->
        do sym <- handleModuleRedirect bs (read hdl)
           let idx = read addr
           lo <- bk_get_range_min_addr bs sym
           hi <- bk_get_range_max_addr bs sym
           let range_str = "(" ++ (show lo) ++ ":" ++ (show hi) ++ ")"
           when ((idx < lo) || (idx > hi)) $
                ioError $ userError $ (show idx) ++ " is not in the range " ++ range_str
           v <- bk_peek_range_value bs sym idx
           when (v == NoValue) $
                do name <- bk_get_key bs sym
                   let msg = "Cannot get value for symbol '" ++ name ++
                             "' at index " ++ (show idx)
                   ioError $ userError msg
           return $ TStr (show v)
    (Just bs, [hdl,addr1,addr2]) ->
        do sym <- handleModuleRedirect bs (read hdl)
           let idx1 = read addr1
               idx2 = read addr2
           lo <- bk_get_range_min_addr bs sym
           hi <- bk_get_range_max_addr bs sym
           let range_str = "(" ++ (show lo) ++ ":" ++ (show hi) ++ ")"
           when ((idx1 < lo) || (idx1 > hi)) $
                ioError $ userError $ (show idx1) ++ " is not in the range " ++ range_str
           when ((idx2 < lo) || (idx2 > hi)) $
                ioError $ userError $ (show idx2) ++ " is not in the range " ++ range_str
           vs <- mapM (bk_peek_range_value bs sym) [idx1..idx2]
           case (find ((== NoValue) . fst) (zip vs [idx1..idx2])) of
             (Just idx) ->
                 do name <- bk_get_key bs sym
                    let msg = "Cannot get value for symbol '" ++ name ++
                              "' at index " ++ (show idx)
                    ioError $ userError msg
             Nothing -> return $ TLst (map (TStr . show) vs)
    (Just bs, _) -> internalError $ "tclSim: grammar mismatch: " ++ (show args)
    (Nothing,_)   -> ioError $ userError ("There is no bluesim model loaded")
--------------------
tclSim ["load", fname, top_name] = do
  g <- readIORef globalVar
  let mbs0 = tp_bluesim g
  when (isJust mbs0) $ unloadBluesimModel (fromJust mbs0)
  mbs1 <- loadBluesimModel fname top_name
  when (isNothing mbs1) $
       ioError $ userError ("Unable to load model " ++ fname)
  modifyIORef globalVar (\gv -> gv { tp_bluesim = mbs1 })
  return $ TLst []
--------------------
tclSim ("lookup":args) = do
  g <- readIORef globalVar
  case (tp_bluesim g) of
    Just bs -> do let root = case args of
                               [_,r] -> Just [read r]
                               _     -> Nothing
                  dirs <- lookupSymbols bs (head args) root
                  when (null dirs) $
                       ioError $ userError ("No such symbol: " ++ (head args))
                  objs <- mapM toTclObj (map hierLeaf dirs)
                  return $ TLst (map TCL objs)
    Nothing -> ioError $ userError ("There is no bluesim model loaded")
----------
tclSim ("ls":args) = do
  g <- readIORef globalVar
  case (tp_bluesim g) of
    Just bs -> do let pats = if (null args) then ["*"] else args
                  dlsts <- mapM (flip (lookupSymbols bs) Nothing) pats
                  entries <- mapM (getLsEntry bs) (concat dlsts)
                  return $ TLst (catMaybes entries)
    Nothing -> ioError $ userError ("There is no bluesim model loaded")
--------------------
tclSim ["nextedge"] = do
  g <- readIORef globalVar
  case (tp_bluesim g) of
    Just bs -> do -- check that $finish hasn't been called
                  fin <- bk_finished bs
                  when (fin) $ ioError $ userError ("$finish has been called -- cannot advance to next edge")
                  -- put a limit at the next edge of every clock
                  num_clks <- bk_num_clocks bs
                  clks <- mapM (bk_get_nth_clock bs) [0..(num_clks-1)]
                  let add_limit hdl =
                          do pc <- bk_clock_edge_count bs hdl POSEDGE
                             nc <- bk_clock_edge_count bs hdl NEGEDGE
                             _ <- bk_quit_after_edge bs hdl POSEDGE (pc+1)
                             _ <- bk_quit_after_edge bs hdl NEGEDGE (nc+1)
                             return ()
                  mapM_ add_limit clks
                  -- advance time
                  _ <- bk_advance bs False
                  -- remove limits from clock edges
                  let remove_limit hdl =
                          do pc <- bk_clock_edge_count bs hdl POSEDGE
                             nc <- bk_clock_edge_count bs hdl NEGEDGE
                             _ <- bk_quit_after_edge bs hdl POSEDGE pc
                             _ <- bk_quit_after_edge bs hdl NEGEDGE nc
                             return ()
                  mapM_ remove_limit clks
                  return $ TLst []
    Nothing -> ioError $ userError ("There is no bluesim model loaded")
--------------------
tclSim ["pwd"] = do
  g <- readIORef globalVar
  case (tp_bluesim g) of
    Just bs -> do str <- getCurDirStr bs
                  obj <- toTclObj str
                  return $ TCL obj
    Nothing -> ioError $ userError ("There is no bluesim model loaded")
----------
tclSim ("run":args) = do
  g <- readIORef globalVar
  case (tp_bluesim g) of
    Just bs -> do -- check that $finish hasn't been called
                  fin <- bk_finished bs
                  when (fin) $ ioError $ userError ("$finish has been called -- cannot run anymore")
                  -- advance with no pre-set limit
                  _ <- bk_advance bs (args == ["async"])
                  return $ TLst []
    Nothing -> ioError $ userError ("There is no bluesim model loaded")
----------
tclSim ("runto":time:args) = do
  g <- readIORef globalVar
  case (tp_bluesim g) of
    Just bs -> do let target = read time
                  -- get current time
                  now <- bk_now bs
                  -- check that the time argument makes sense
                  when (target <= now) $
                    ioError $ userError ("target time must be in the future")
                  -- check that $finish hasn't been called
                  fin <- bk_finished bs
                  when (fin) $ ioError $ userError ("$finish has been called -- cannot run anymore")
                  -- schedule a UI event for the given time and then advance
                  _ <- bk_schedule_ui_event bs target
                  let async = args == ["async"]
                  _ <- bk_advance bs async
                  if (async)
                   then -- setup a cleanup handler
                        do let hdlrs = cleanup_handlers bs
                               hdlrs' = (remove_yield target):hdlrs
                               bs' = bs { cleanup_handlers = hdlrs' }
                           modifyIORef globalVar (\gv -> gv { tp_bluesim = (Just bs') })
                   else -- remove the UI event if we didn't reach the target time
                       do now' <- bk_now bs
                          when (now' /= target) $
                               do _ <- bk_remove_ui_event bs target
                                  return ()
                  return $ TLst []
    Nothing -> ioError $ userError ("There is no bluesim model loaded")
----------
tclSim ("step":args) = do
  g <- readIORef globalVar
  case (tp_bluesim g) of
    Just bs -> let (cycles,async) = case args of
                                      []          -> (1,False)
                                      ["async"]   -> (1,True)
                                      [n]         -> (read n,False)
                                      [n,_]       -> (read n,True)
                                      _ -> internalError $ "tclSim: grammar mismatch: " ++ (show args)
               in if (cycles < 1)
                  then ioError $ userError ("Cycle count must be > 0")
                  else do -- check that $finish hasn't been called
                          fin <- bk_finished bs
                          when (fin) $ ioError $ userError ("$finish has been called -- cannot step")
                          -- gather information on current time & clock value
                          let clk = current_clock bs
                          clk_val <- bk_clock_val bs clk
                          let dir = if (clk_val == CLK_LOW) then NEGEDGE else POSEDGE
                          now <- bk_now bs
                          count <- bk_clock_cycle_count bs clk
                          let dir' = -- If we are before logic has executed at
                                     -- time 0, then a step from here should go
                                     -- to the first edge, not the next edge
                                     -- that returns to the current clock value
                                     if (now == 0 && count == 0)
                                     then case dir of
                                            POSEDGE -> NEGEDGE
                                            NEGEDGE -> POSEDGE
                                     else dir
                          -- compute the new stopping point
                          ec <- bk_clock_edge_count bs clk dir'
                          let limit = ec + cycles
                          s <- bk_quit_after_edge bs clk dir' limit
                          when (s < 0) $ ioError $ userError ("No clock to step")
                          -- advance to the computed point
                          _ <- bk_advance bs async
                          if (async)
                           then -- setup a cleanup handler
                                do let hdlrs = cleanup_handlers bs
                                       hdlrs' = (restore_edge_limit clk dir' ec):hdlrs
                                       bs' = bs { cleanup_handlers = hdlrs' }
                                   modifyIORef globalVar (\gv -> gv { tp_bluesim = (Just bs') })
                           else -- restore the edge limit if we didn't reach it
                               do ec' <- bk_clock_edge_count bs clk dir'
                                  when (ec' /= limit) $
                                       do _ <- bk_quit_after_edge bs clk dir' ec
                                          return ()
                          return $ TLst []
    Nothing -> ioError $ userError ("There is no bluesim model loaded")
----------
tclSim ["stop"] = do
  g <- readIORef globalVar
  case (tp_bluesim g) of
    Just bs -> do -- stop the simulation thread
                  bk_abort_now bs
                  t <- bk_sync bs
                  obj <- toTclObj t
                  -- run any cleanup handlers
                  sequence_ (cleanup_handlers bs)
                  let bs' = bs { cleanup_handlers = [] }
                  modifyIORef globalVar (\gv -> gv { tp_bluesim = (Just bs') })
                  return $ TCL obj
    Nothing -> ioError $ userError ("There is no bluesim model loaded")
----------
tclSim ["sync"] = do
  g <- readIORef globalVar
  case (tp_bluesim g) of
    Just bs -> do t <- bk_sync bs
                  obj <- toTclObj t
                  return $ TCL obj
    Nothing -> ioError $ userError ("There is no bluesim model loaded")
----------
tclSim ["time"] = do
  g <- readIORef globalVar
  case (tp_bluesim g) of
    Just bs -> do t <- bk_now bs
                  obj <- toTclObj t
                  return $ TCL obj
    Nothing -> ioError $ userError ("There is no bluesim model loaded")
----------
tclSim ("timescale":args) = do
  g <- readIORef globalVar
  case (tp_bluesim g) of
      Just bs ->
        case args of
          [timescale] ->
            case parseTimescale timescale of
              Just (timeprecision, scale_factor) -> do
                _ <- bk_set_timescale bs timeprecision scale_factor
                return $ TLst []
              _ -> ioError $ userError ("Invalid timescale: " ++ timescale)
          _ -> internalError $ "tclSim: 'sim timescale' grammar mismatch: " ++ (show args)
      Nothing -> ioError $ userError ("There is no bluesim model loaded")
tclSim ["unload"] = do
  g <- readIORef globalVar
  case (tp_bluesim g) of
    Just bs -> do modifyIORef globalVar (\gv -> gv { tp_bluesim = Nothing })
                  unloadBluesimModel bs
                  return $ TLst []
    Nothing -> ioError $ userError ("There is no bluesim model loaded")
----------
tclSim ("up":args) = do
  g <- readIORef globalVar
  case (tp_bluesim g) of
    Just bs -> do top_sym <- bk_top_symbol bs
                  let n = if (null args) then 1 else read (head args)
                      dirs = drop n (current_directory bs)
                      dirs' = if (null dirs) then [top_sym] else dirs
                      mbs = Just (bs { current_directory = dirs' })
                  modifyIORef globalVar (\gv -> gv { tp_bluesim = mbs })
                  return $ TLst []
    Nothing -> ioError $ userError ("There is no bluesim model loaded")
----------
tclSim ("vcd":args) = do
  g <- readIORef globalVar
  case (tp_bluesim g) of
    Just bs -> case args of
                 []      -> -- return name of active VCD file, if any
                            do l <- toTclObj $ maybeToList (active_vcd_file bs)
                               return $ TCL l
                 ["on"]  -> -- turn on VCD dumping
                            do _ <- bk_enable_VCD_dumping bs
                               when (isNothing $ active_vcd_file bs) $
                                    let bs' = bs { active_vcd_file = Just "dump.vcd" }
                                    in modifyIORef globalVar (\gv -> gv { tp_bluesim = Just bs' })
                               return $ TLst []
                 ["off"] -> -- turn off VCD dumping
                            do bk_disable_VCD_dumping bs
                               return $ TLst []
                 [file]  -> -- dump to named file
                            do _ <- bk_set_VCD_file bs file
                               _ <- bk_enable_VCD_dumping bs
                               let bs' = bs { active_vcd_file = Just file }
                               modifyIORef globalVar (\gv -> gv { tp_bluesim = Just bs' })
                               return $ TLst []
                 _ -> internalError $ "tclSim: grammar mismatch: " ++ (show args)

    Nothing -> ioError $ userError ("There is no bluesim model loaded")
----------
tclSim ["version"] = do
  g <- readIORef globalVar
  case (tp_bluesim g) of
    Just bs -> do vi <- bk_version bs
                  obj <- toTclObj vi
                  return $ TCL obj
    Nothing -> ioError $ userError ("There is no bluesim model loaded")
----------
tclSim xs = internalError $ "tclSim: grammar mismatch: " ++ (show xs)

-- We treat a list of symbols (starting with leaf, going back to root)
-- as a hierarchical path structure.
type Hier = [BSSymbol]

hierLeaf :: Hier -> BSSymbol
hierLeaf []    = bad_symbol
hierLeaf (s:_) = s

hierAdd :: Hier -> BSSymbol -> Hier
hierAdd syms s = s:syms

mkDirString :: BluesimModel -> Hier -> Hier -> IO String
mkDirString bs relative_to syms =
    do let above_root = if (null relative_to)
                        then bad_symbol
                        else head relative_to
           ds = reverse $ takeWhile (/= above_root) syms
       names <- mapM (bk_get_key bs) ds
       return $ intercalate "." names

describeSym :: BluesimModel -> BSSymbol -> IO String
describeSym bs sym =
    do ismod <- bk_is_module bs sym
       isrule <- bk_is_rule bs sym
       isvalue <- bk_is_single_value bs sym
       isrange <- bk_is_value_range bs sym
       kind <- case (ismod, isvalue, isrule, isrange) of
                 (True,_,_,_) -> return "module"
                 (_,True,_,_) -> return "signal"
                 (_,_,True,_) -> return "rule"
                 (_,_,_,True) -> return "signal"
                 _            -> return "?"
       redir_sym <- handleModuleRedirect bs sym
       isvalue' <- bk_is_single_value bs redir_sym
       isrange' <- bk_is_value_range bs redir_sym
       range <- case (isvalue', isrange') of
                  (True,_) -> return $ if isvalue then "" else " with value"
                  (_,True) -> do lo <- bk_get_range_min_addr bs redir_sym
                                 hi <- bk_get_range_max_addr bs redir_sym
                                 return $ " range(" ++ (show lo) ++ ":" ++ (show hi) ++ ")"
                  _        -> return ""
       return $ kind ++ range

-- A module (like MOD_Reg, etc.) can have an entry for "" which will be
-- used to supply a value for that module, if it exists.
handleModuleRedirect :: BluesimModel -> BSSymbol -> IO BSSymbol
handleModuleRedirect bs sym =
    do ismod <- bk_is_module bs sym
       hdl <- if ismod
              then bk_lookup_symbol bs sym ""
              else return sym
       return $ if (hdl /= bad_symbol) then hdl else sym

getLsEntry :: BluesimModel -> Hier -> IO (Maybe HTclObj)
getLsEntry _ [] = internalError "getLsEntry: empty symbol hierarchy list"
getLsEntry bs dir  =
    do name <- mkDirString bs (current_directory bs) dir
       symtag <- describeSym bs (hierLeaf dir)
       obj <- toTclObj (name,symtag)
       return $ Just (TCL obj)

-- -------
-- Utilities for handling wildcard patterns in hierarchical names


data Segment = Exact String
             | Pattern String
  deriving (Eq, Show)

-- Break up a hierarchical path into segments.
segmentPath :: String -> ([Segment],Bool)
segmentPath path =
    let segments = map removeDot $ groupBy (\_ x-> x /= '.') path
        segments' = case segments of
                      []   -> []
                      [""] -> []
                      _    -> map tagSegment segments
        is_absolute = "." `isPrefixOf` path
    in (segments',is_absolute)
    where removeDot ('.':x) = x
          removeDot x       = x

-- Parse a segment specifier
tagSegment :: String -> Segment
tagSegment s =
    let rs = reverse s
    in if (null ("*?[\\" `intersect` s))
       then Exact s
       else Pattern s

-- Expand a list of symbols down one level based on a segment specifier
doSegment :: BluesimModel -> Hier -> [Hier] -> Segment -> IO [Hier]
doSegment bs rel ds seg =
    do let showDir d = mkDirString bs rel d
       ismod <- mapM ((bk_is_module bs) . hierLeaf) ds
       let (ok,bad) = partition fst $ zip ismod ds
       when (not (null bad)) $
            do names <- mapM (showDir . snd) bad
               let str = intercalate ", " names
                   msg = if (length names == 1)
                         then "Not a module: " ++ str
                         else "Not modules: " ++ str
               ioError $ userError msg
       hdls <- case seg of
                 (Exact name)  -> mapM (doName bs name) ds
                 (Pattern pat) -> do let p = parseGlobPattern pat
                                     when (isJust (getGlobErr p)) $
                                          ioError $ userError (fromJust (getGlobErr p))
                                     mapM (doPattern bs p) ds
       let new_ds = concat hdls
           (bad2,ok2) = partition ((== bad_symbol) . hierLeaf) new_ds
       when (not (null bad2)) $
            do names <- mapM (showDir . tail) bad2
               let str = intercalate ", " names
                   to_match = case (seg) of
                                (Exact name) -> name
                                (Pattern pat) -> pat
                   msg = "No match for '" ++ to_match ++
                         (if (null str) then "'" else ("' in: " ++ str))
               ioError $ userError msg
       return ok2

doName :: BluesimModel -> String -> Hier -> IO [Hier]
doName _ _ [] = internalError "doName: empty symbol hierarchy list"
doName bs name dir =
    do hdl <- bk_lookup_symbol bs (hierLeaf dir) name
       return [hierAdd dir hdl]

doPattern :: BluesimModel -> GlobPattern -> Hier -> IO [Hier]
doPattern _ _ [] = internalError "doPattern: empty symbol hierarchy list"
doPattern bs pat dir =
    do count <- bk_num_symbols bs (hierLeaf dir)
       syms <- if (count == 0)
               then return []
               else mapM (bk_get_nth_symbol bs (hierLeaf dir)) [0..(count-1)]
       ns <- mapM (bk_get_key bs) syms
       let hdls = [ sym
                  | (sym,name) <- zip syms ns
                  , matchGlobPattern pat name
                  ]
       return [ hierAdd dir hdl | hdl <- hdls ]

-- Get the list of symbol lists matching a full hierarchical path
-- The resulting list is bottom-up, with the deepest symbol at the head of the list
lookupSymbols :: BluesimModel -> String -> (Maybe Hier) -> IO [Hier]
lookupSymbols bs path root =
    do top <- bk_top_symbol bs
       let (segments,is_absolute) = segmentPath path
           start = if is_absolute
                   then [top]
                   else case root of
                          (Just r) -> r
                          Nothing  -> current_directory bs
       foldM (doSegment bs start) [start] segments


----------------------------------------------------
-- Utilities for cleaning up after async execution

restore_edge_limit :: BSClock -> BSEdgeDirection -> Word64 -> IO ()
restore_edge_limit clk dir count =
    do g <- readIORef globalVar
       case (tp_bluesim g) of
         (Just bs) -> do _ <- bk_quit_after_edge bs clk dir count
                         return ()
         Nothing -> return ()


remove_yield :: BSTime -> IO ()
remove_yield t =
    do g <- readIORef globalVar
       case (tp_bluesim g) of
         (Just bs) -> do _ <- bk_remove_ui_event bs t
                         return ()
         Nothing -> return ()

----------------------------------------------------
-- Submodule interface types

makeSubmoduleIfcMap :: Bool -> InstTree -> M.Map Id Type
makeSubmoduleIfcMap hide inst_tree =
    M.fromList (concatMap getTypes (M.elems inst_tree))
 where
   getTypes i@(Loc { node_type = mt }) =
       case (nodeChildren hide i) of
         [(StateVar x)] ->
             case mt of
               Just t -> [(x, t)]
               Nothing -> internalError ("makeSubmoduleIfcMap: no type: " ++
                                         ppReadable i)
         nodes -> concatMap getTypes nodes
   getTypes (Rule {}) = []
   getTypes (StateVar x) =
       internalError ("makeSubmoduleIfcMap: no wrapper: " ++ ppReadable x)


----------------------------------------------------
-- Interface hierarchy

-- raw info about an ifc field, which is common to APackage and AVInst
data RawIfcField =
         RawMethod Id                     -- name
                   Integer                -- multiplicity
                   (Maybe Id) (Maybe Id)  -- associated clk and rst
                   [(Maybe Id, AType)]    -- arguments
                   [VPort]                -- argument ports
                   (Maybe (VPort, AType)) -- return value
                   (Maybe VPort)          -- enable signal
                   -- Note: no ready signal at this stage
       | RawClock Id
       | RawReset Id
       | RawInout Id AType VName
                  (Maybe Id) (Maybe Id)   -- associated clk and rst

rawIfcFieldName :: RawIfcField -> Id
rawIfcFieldName (RawMethod i _ _ _ _ _ _ _) = i
rawIfcFieldName (RawClock i) = i
rawIfcFieldName (RawReset i) = i
rawIfcFieldName (RawInout i _ _ _ _) = i


rawIfcFieldFromAIFace :: [PProp] -> AIFace -> RawIfcField
rawIfcFieldFromAIFace _
    (AIDef i args _ _ def
     (Method _ clk rst mult ins mo@(Just out) Nothing) _) =
    let -- include the type in the "mo"
        mo' = Just (out, adef_type def)
    in  RawMethod i mult clk rst (mapFst Just args) ins mo' Nothing
rawIfcFieldFromAIFace pps
    (AIAction args _ _ i _
     (Method _ clk rst mult ins Nothing me@(Just _))) =
    let -- filter out inhigh enable ports
        -- XXX is there a better way to do this?
        me' = if (isAlwaysEn pps i) then Nothing else me
    in  RawMethod i mult clk rst (mapFst Just args) ins Nothing me'
rawIfcFieldFromAIFace pps
    (AIActionValue args _ _ i _ def
     (Method _ clk rst mult ins mo@(Just out) me@(Just _))) =
    let -- filter out inhigh enable ports
        -- XXX is there a better way to do this?
        me' = if (isAlwaysEn pps i) then Nothing else me
        -- include the type in the "mo"
        mo' = Just (out, adef_type def)
    in  RawMethod i mult clk rst (mapFst Just args) ins mo' me'
rawIfcFieldFromAIFace _ (AIClock i _ (Clock _)) = RawClock i
rawIfcFieldFromAIFace _ (AIReset i _ (Reset _)) = RawReset i
rawIfcFieldFromAIFace _ (AIInout i (AInout e) (Inout _ vn mclk mrst)) =
    RawInout i (ae_type e) vn mclk mrst
rawIfcFieldFromAIFace _ aif =
    internalError ("rawIfcFieldFromAIFace: unexpected AIFace combo: " ++
                   ppReadable aif)

rawIfcFieldFromAVInst :: ([AType], Maybe AType, Maybe AType) ->
                         VFieldInfo -> RawIfcField
rawIfcFieldFromAVInst (arg_tys,_,mo_type) (Method i clk rst mult ins mo me) =
    let -- XXX AVInst doesn't record argument names
        args = zip (repeat Nothing) arg_tys
        -- add the return bit-type to the mo
        mo' = case (mo, mo_type) of
                (Just o, Just o_type) -> Just (o, o_type)
                (Nothing, Nothing) -> Nothing
                _ -> internalError ("rawIfcFieldFromAVInst: unexpected mo: " ++
                                    ppReadable (mo, mo_type))
    in  RawMethod i mult clk rst args ins mo' me
rawIfcFieldFromAVInst _ (Clock i) = RawClock i
rawIfcFieldFromAVInst _ (Reset i) = RawReset i
rawIfcFieldFromAVInst (_,_,mt) (Inout i vn mclk mrst) =
    let t = fromJustOrErr ("getIfc: no type for Inout") mt
    in  RawInout i t vn mclk mrst

-- ---------------

data IfcField =
         Field Id RawIfcField (Maybe RawIfcField) -- name, def, maybe RDY def
       | SubIfc Id [IfcField]                     -- name, subfields
       -- XXX Vector of Ifc?
       -- XXX field multiplicity?


getIfcHierarchy :: Maybe Id -> [(Id, RawIfcField)] -> Type -> IO [IfcField]
getIfcHierarchy instId raw_fields tifc = do
    mres <- runExceptT (mgetIfcHierarchy instId raw_fields tifc)
    case mres of
      Right res -> return res
      Left msg  -> internalError msg

mgetIfcHierarchy :: Maybe Id -> [(Id, RawIfcField)] -> Type ->
                    ExceptT String IO [IfcField]
mgetIfcHierarchy instId raw_fields tifc = do
    -- use "expandSyn" to avoid getting back "Alias" as the type analysis
    maifc <- lift $ getTypeAnalysis' (expandSyn tifc) True
    case (maifc) of
      Just (Interface _ _ _ _ ifc_fs _) -> mapM (getField emptyId) ifc_fs
          where
            ifc_map = M.fromList raw_fields

            -- get the AIF for a flattened name
            lookupAIF :: Id -> ExceptT String IO RawIfcField
            lookupAIF i =
                case (M.lookup i ifc_map) of
                  Just aif -> return aif
                  _ -> throwError ("getIfcHierarhcy: not in map: " ++
                                   ppReadable (instId, i, M.keys ifc_map))
            -- get the AIF for its RDY method, if it exists
            lookupRdyAIF i =
                let -- XXX is there a better way to find the rdy name?
                    rdy_i = mkRdyId i
                in  M.lookup rdy_i ifc_map

            -- append to the prefix
            addToPrefix pre suf =
                if (isEmptyId pre)
                then setIdBase pre (getIdBase suf)
                else setIdBase pre (concatFString [getIdBase pre,
                                                   fsUnderscore, getIdBase suf])

            -- get the IfcField for one field
            getField :: Id -> (Bool, Id, Qual Type, [IfcPragma]) ->
                        ExceptT String IO IfcField
            getField prefix (_, fId, (_ :=> t), _) = getField' prefix fId t

            getField' :: Id -> Id -> Type -> ExceptT String IO IfcField
            getField' prefix fId t = do
                -- Function for expanding Vectors of subinterfaces
                -- (or pseudo-interfaces like Clock, Reset, Inout)
                -- Returns Nothing if this is not a Vector of interfaces
                -- or Just (sizes, fields) where "sizes" is the sizes of
                -- the Vector wrappers and "fs" the fields of the interface.
                -- Pseudo-interfaces are treated like interfaces with a
                -- single unnamed field.
                let expandVectors lenTy elemTy = do
                       -- ("expandSyn" not needed, since it was applied to "t")
                      maelem <- lift $ getTypeAnalysis' elemTy True
                      let sz = getTNum (expandSyn lenTy)
                      case (maelem) of
                        Just (Interface _ _ _ _ fs _) ->
                            return (Just ([sz], fs))
                        Just (Vector _ lenTy2 elemTy2 _) -> do
                            maybe_subifc <- expandVectors lenTy2 elemTy2
                            case (maybe_subifc) of
                              Nothing -> return Nothing
                              Just (szs, fs) ->
                                  return (Just ((sz:szs), fs))
                        Just (Primary i _ _ _ _)
                            | (i == idClock) || (i == idReset) || (i == idInout)
                            -> let fs = [(True, emptyId, [] :=> elemTy, [])]
                               in  return (Just ([sz], fs))
                        _ -> return Nothing
                -- Function to take the output of "expandVectors" and
                -- construct the IfcField result
                let mkVecSubIfc fs pfx [] n = do
                       let pfx_n = addToPrefix pfx n
                       ffs <- mapM (getField pfx_n) fs
                       return (SubIfc n ffs)
                    mkVecSubIfc fs pfx (sz:rest) n = do
                       let pfx_n = addToPrefix pfx n
                           prefs = if (sz == 0)
                                   then []
                                   else map mkNumId [0..(sz-1)]
                       vfs <- mapM (mkVecSubIfc fs pfx_n rest) prefs
                       return (SubIfc n vfs)
                -- expand this field
                ma <- lift $ getTypeAnalysis' (expandSyn t) True
                let prefix' = if (isEmptyId fId)
                              then prefix -- indicates a Clock/Reset/Inout
                              else addToPrefix prefix fId
                -- default result (if the type is not a subifc to be expanded)
                let mkDefault = do aif <- lookupAIF prefix'
                                   let mrdy_aif = lookupRdyAIF prefix'
                                   return (Field fId aif mrdy_aif)
                case (ma) of
                  Just (Interface _ _ _ _ fs _) -> do
                        ffs <- mapM (getField prefix') fs
                        return (SubIfc fId ffs)
                  Just (Vector _ lenTy elemTy _) -> do
                      -- find out if it's a vector of ifcs
                      maelem <- expandVectors lenTy elemTy
                      case (maelem) of
                        Just (sz:rest, fs) -> do
                            let prefs = if (sz == 0)
                                        then []
                                        else map mkNumId [0..(sz-1)]
                            vfs <- mapM (mkVecSubIfc fs prefix' rest) prefs
                            return (SubIfc fId vfs)
                        _ -> mkDefault
                  _ -> mkDefault  -- not an interface to expand
      Nothing ->
          -- return [ Field fId inf Nothing | (fId, inf) <- raw_fields ]
          throwError ("getIfcHierarchy: ifc type not found: " ++
                      ppReadable tifc)
      _ -> throwError ("getIfcHierarchy: not an ifc: " ++ ppReadable tifc)


dispIfcHierarchyNames :: [IfcField] -> HTclObj
dispIfcHierarchyNames ifc_fs = TLst (map dispField ifc_fs)
 where
   dispField (Field fId inf mrdy_inf) =
       TLst $ [TStr (getIdBaseString fId),
               TStr (pfpString (rawIfcFieldName inf))] ++
              case (mrdy_inf) of
                Nothing -> []
                Just rdy_inf ->
                    [tagStr "ready" (pfpString (rawIfcFieldName rdy_inf))]
   dispField (SubIfc fId fs) =
       tagLst (getIdBaseString fId) (map dispField fs)


----------------------------------------------------
-- Extract and display info about module arguments and interface
-- (common to the "module" and "submodule" commands)

-- define a datatype for the extracted info
data PortIfcInfo =
  -- first Id is the field name at the current level of the hierarchy,
  -- while the second Id is the flattened name
    PIMethod Id Id
             (Maybe Id) (Maybe Id)  -- associated clk and rst
             [(Maybe Id, AType, (String, IType))]  -- arguments
             (Maybe (String, AType, IType))        -- return value
             (Maybe (String, IType))               -- enable signal
             (Maybe (String, IType))               -- ready signal
  | PIClock Id Id (Maybe ((String, IType), Maybe (String, IType)))
  | PIReset Id Id (Maybe (String, IType)) (Maybe Id)
  | PIInout Id Id AType (String, IType) (Maybe Id) (Maybe Id)
  | PISubIfc Id [PortIfcInfo]

data PortArgInfo =
    PAParam Id AType String
  | PAPort Id AType (String, IType) (Maybe Id) (Maybe Id)
  | PAClock Id (Maybe ((String, IType), Maybe (String, IType)))
  | PAReset Id (Maybe (String, IType)) (Maybe Id)
  | PAInout Id Integer (String, IType) (Maybe Id) (Maybe Id)


getModPortInfo :: APackage -> [PProp] -> Type ->
                  IO ([PortArgInfo], [PortIfcInfo])
getModPortInfo apkg pps tifc = do
    -- port type map
    let ptmap = apkg_external_wire_types apkg

    -- interface fields (with VFieldInfo)
    let ifc' :: [AIFace]
        ifc' = apkg_interface apkg
        -- need to filter out ready methods that are always ready
        notAlwaysRdy :: AIFace -> Bool
        notAlwaysRdy aif = let mid = aif_name aif
                           in not $ (isRdyId mid) && (isAlwaysRdy pps mid)
        ifc = filter notAlwaysRdy ifc'

    -- interface hierarchy
    let -- map from flattened ifc name to its raw info
        ifc_map = [ (aIfaceName aif, rawIfcFieldFromAIFace pps aif)
                    | aif <- ifc ]
    ifc_hier <- getIfcHierarchy Nothing ifc_map tifc

    -- module arguments
    let inps :: [(AAbstractInput, VArgInfo)]
        inps = getAPackageInputs apkg

    -- clock and reset info
    let
        wires = apkg_external_wires apkg
        -- clockinfo
        out_clkinfo = output_clocks (wClk wires)
        in_clkinfo = input_clocks (wClk wires)
        -- resetinfo
        out_rstinfo = output_resets (wRst wires)
        in_rstinfo = input_resets (wRst wires)

    -- construct port info for the interface fields
    let getIfcHier = getPortsIfc ptmap out_clkinfo out_rstinfo

    -- construct port info for a module argument
    let
        getModArg (AAI_Port (i,t), Param v) =
            [getPortsModArgParam i t v]
        getModArg (AAI_Port (i,t), Port v mclk mrst) =
            getPortsModArgPort ptmap i t v mclk mrst
        getModArg (AAI_Clock {}, ClockArg i) =
            [getPortsModArgClock in_clkinfo i]
        getModArg (AAI_Reset {}, ResetArg i) =
            [getPortsModArgReset in_rstinfo i]
        getModArg (AAI_Inout i sz, InoutArg vn mclk mrst) =
            getPortsModArgInout ptmap i sz vn mclk mrst
        getModArg a = internalError ("getModArg: unexpected arg combo: " ++
                                     ppReadable a)

    return
        (concatMap getModArg inps,
         concatMap getIfcHier ifc_hier)


getSubmodPortInfo :: Maybe Type -> AVInst -> IO ([PortArgInfo], [PortIfcInfo])
getSubmodPortInfo mtifc avi = do
    -- port type map
    let ptmap = avi_port_types avi

    -- clock and reset info
    let vmi = avi_vmi avi
        -- clockinfo
        out_clkinfo = output_clocks (vClk vmi)
        in_clkinfo = input_clocks (vClk vmi)
        -- resetinfo
        out_rstinfo = output_resets (vRst vmi)
        in_rstinfo = input_resets (vRst vmi)

    -- module arguments
    let -- VArgInfo
        modargs = vArgs vmi
        -- XXX is there a better way to get the types?
        modarg_tys = map ae_type (avi_iargs avi)

    -- interface fields
    let -- VFieldInfo and method bit-types
        vfts0 = (vFields vmi, avi_meth_types avi)
        -- adjust primitives
        (vfi, fts) = adjustPrimFields mtifc avi vfts0

    -- interface hierarchy
    let -- map from flattened ifc name to its raw info
        ifc_map = [ (vf_name vf, rawIfcFieldFromAVInst ft vf)
                    | (ft, vf) <- zip fts vfi ]
    ifc_hier <-
      let defl_ifc_hier = [ (Field fId inf Nothing) | (fId, inf) <- ifc_map ]
      in case mtifc of
           Just tifc -> do
              mres <- runExceptT $
                      mgetIfcHierarchy (Just (avi_vname avi)) ifc_map tifc
              case mres of
                Right res -> return res
                Left _ -> -- the wrapped ifc didn't match the inst ifc,
                          -- so use the inst's ifc
                          return defl_ifc_hier
           Nothing -> return defl_ifc_hier

    -- construct port info for the interface fields
    let getIfcHier = getPortsIfc ptmap out_clkinfo out_rstinfo

    -- construct port info for a module argument
    let
        getModArg t (Param v) =
            let i = vName_to_id v
            in  [getPortsModArgParam i t v]
        getModArg t (Port v mclk mrst) =
            let i = vPort_to_id v
            in  getPortsModArgPort ptmap i t v mclk mrst
        getModArg _ (ClockArg i) =
            [getPortsModArgClock in_clkinfo i]
        getModArg _ (ResetArg i) =
            [getPortsModArgReset in_rstinfo i]
        getModArg t (InoutArg vn mclk mrst) =
            let sz = case t of
                       (ATAbstract c [n])
                           | c `qualEq` idInout_ -> n
                       _ -> internalError ("getModArg: " ++
                                           "bad Inout type: " ++
                                           ppReadable t)
                i = vName_to_id vn
            in  getPortsModArgInout ptmap i sz vn mclk mrst

    return
      (concat $ zipWith getModArg modarg_tys modargs,
       concatMap getIfcHier ifc_hier)

adjustPrimFields :: Maybe Type -> AVInst ->
                    ([VFieldInfo], [([AType], Maybe AType, Maybe AType)]) ->
                    ([VFieldInfo], [([AType], Maybe AType, Maybe AType)])
adjustPrimFields Nothing _ vfts = vfts
adjustPrimFields (Just tifc) avi vfts =
    if (leftCon tifc == Just idReg)
    then -- wrapper type is Reg
         if (isRegAligned avi)
         then adjustRegAlignedFields vfts
         else if (isRegInst avi)
         then adjustRegFields vfts
         else if (isRWire0 avi)
         then adjustWireFields (adjustRWire0Fields vfts)
         else if (isRWire avi)
         then adjustWireFields vfts
         else if (isBypassWire0 avi)
         then adjustBypassWireFields (adjustRWire0Fields vfts)
         else if (isBypassWire avi)
         then adjustBypassWireFields vfts
         else if (isClockCrossingBypassWire avi)
         then adjustBypassWireFields vfts
         else if (isSyncReg avi)
         then adjustSyncRegFields vfts
         else vfts
    else if (leftCon tifc == Just idRWire)
    then -- wrapper type is RWire
         if (isRWire0 avi)
         then adjustRWireFields (adjustRWire0Fields vfts)
         else if (isRWire avi)
         then adjustRWireFields vfts
         else vfts
    else if (leftCon tifc == Just idPulseWire)
    then -- wrapper type is PulseWire
         if (isRWire0 avi)
         then adjustPulseWireFields vfts
         else vfts
    else if (leftCon tifc == Just idFIFO) || (leftCon tifc == Just idFIFOF)
    then -- wrapper type is FIFO or FIFOF
         if (isFIFO0 avi)
         then adjustFIFOFields (adjustFIFO0Fields vfts)
         else if (isFIFO avi)
         then adjustFIFOFields vfts
         else vfts
    else vfts

-- This is a no-op but it does add some error checking
adjustRegAlignedFields :: ([VFieldInfo], [([AType], Maybe AType, Maybe AType)]) ->
                   ([VFieldInfo], [([AType], Maybe AType, Maybe AType)])
adjustRegAlignedFields (vfi, fts) =
    let renameField vf@(Method {vf_name = i })
            | (i `qualEq` id_read noPosition)  = vf
            | (i `qualEq` id_write noPosition) = vf
        renameField vf = internalError ("adjustRegAlignedFields: unknown field: " ++
                                        ppReadable (vf_name vf))
    in  (map renameField vfi, fts)


adjustRegFields :: ([VFieldInfo], [([AType], Maybe AType, Maybe AType)]) ->
                   ([VFieldInfo], [([AType], Maybe AType, Maybe AType)])
adjustRegFields (vfi, fts) =
    let renameField vf@(Method {vf_name = i })
            | (i `qualEq` idPreludeRead)  = vf { vf_name = id_read noPosition }
            | (i `qualEq` idPreludeWrite) = vf { vf_name = id_write noPosition }
        renameField vf = internalError ("adjustRegFields: unknown field: " ++
                                        ppReadable (vf_name vf))
    in  (map renameField vfi, fts)

adjustFIFOFields :: ([VFieldInfo], [([AType], Maybe AType, Maybe AType)]) ->
                    ([VFieldInfo], [([AType], Maybe AType, Maybe AType)])
adjustFIFOFields (vfi, fts) =
    let enq_rdy   = mkRdyId idEnq
        deq_rdy   = mkRdyId idDeq
        first_rdy = mkRdyId idFirst
        renameField (vf@(Method {vf_name = i }), ts)
            | (i `qualEq` id_notFull)  = [ (vf { vf_name = enq_rdy }, ts) ]
            | (i `qualEq` id_notEmpty) = [ (vf { vf_name = deq_rdy }, ts),
                                           (vf { vf_name = first_rdy }, ts) ]
        renameField vft = [vft]
    in  unzip $ concatMap renameField $ zip vfi fts

adjustFIFO0Fields :: ([VFieldInfo], [([AType], Maybe AType, Maybe AType)]) ->
                      ([VFieldInfo], [([AType], Maybe AType, Maybe AType)])
adjustFIFO0Fields (vfi, fts) =
    let (clk, rst) =
            case vfi of
              -- get the clk/rst from the deq method (just in case)
              (_:d@(Method _ c r _ _ _ _):_) -> (c, r)
              _ -> internalError ("adjustFIFO0Fields: vfi = " ++
                                  ppReadable vfi)
        first_vfi = Method idFirst clk rst 1 [] Nothing Nothing
        first_fts = ([], Nothing, Nothing)
    in  (first_vfi:vfi, first_fts:fts)

adjustSyncRegFields :: ([VFieldInfo], [([AType], Maybe AType, Maybe AType)]) ->
                       ([VFieldInfo], [([AType], Maybe AType, Maybe AType)])
adjustSyncRegFields (vfi, fts) =
    let renameField vf@(Method {vf_name = i })
            -- XXX these are qualified Clock, not Prelude
            | (i `qualEq` idPreludeRead)  = vf { vf_name = id_read noPosition }
            | (i `qualEq` idPreludeWrite) = vf { vf_name = id_write noPosition }
            | (i `qualEq` (mkRdyId idPreludeWrite)) =
                vf { vf_name = mkRdyId (id_write noPosition) }
        renameField vf = internalError ("adjustRegFields: unknown field: " ++
                                        ppReadable (vf_name vf))
    in  (map renameField vfi, fts)

adjustRWireFields :: ([VFieldInfo], [([AType], Maybe AType, Maybe AType)]) ->
                     ([VFieldInfo], [([AType], Maybe AType, Maybe AType)])
adjustRWireFields (vfi, fts) =
    let renameField vf@(Method {vf_name = i })
            | (i `qualEq` idWHas)  = vf { vf_name = unQualId $ mkRdyId idWGet }
        renameField vf = vf
    in  (map renameField vfi, fts)

adjustRWire0Fields :: ([VFieldInfo], [([AType], Maybe AType, Maybe AType)]) ->
                      ([VFieldInfo], [([AType], Maybe AType, Maybe AType)])
adjustRWire0Fields (vfi, fts) =
    let (clk, rst) =
            case vfi of
              ((Method _ c r _ _ _ _):_) -> (c, r)
              _ -> internalError ("adjustRWire0Fields: vfi = " ++
                                  ppReadable vfi)
        wget_vfi = Method (unQualId idWGet) clk rst 1 [] Nothing Nothing
        wget_fts = ([], Nothing, Nothing)
    in  (wget_vfi:vfi, wget_fts:fts)

adjustWireFields :: ([VFieldInfo], [([AType], Maybe AType, Maybe AType)]) ->
                    ([VFieldInfo], [([AType], Maybe AType, Maybe AType)])
adjustWireFields (vfi, fts) =
    let readId  = id_read noPosition
        writeId = id_write noPosition
        renameField vf@(Method {vf_name = i })
            | (i `qualEq` idWGet) = vf { vf_name = readId }
            | (i `qualEq` idWSet) = vf { vf_name = writeId }
            | (i `qualEq` idWHas) = vf { vf_name = mkRdyId readId }
        renameField vf = internalError ("adjustWireFields: unknown field: " ++
                                        ppReadable (vf_name vf))
    in  (map renameField vfi, fts)

adjustPulseWireFields ::
    ([VFieldInfo], [([AType], Maybe AType, Maybe AType)]) ->
    ([VFieldInfo], [([AType], Maybe AType, Maybe AType)])
adjustPulseWireFields (vfi, fts) =
    let renameField vf@(Method {vf_name = i })
            | (i `qualEq` idWSet) = vf { vf_name = unQualId idSend }
            | (i `qualEq` idWHas) = vf { vf_name = id_read noPosition }
        renameField vf =
            internalError ("adjustPulseWireFields: unknown field: " ++
                           ppReadable (vf_name vf))
    in  (map renameField vfi, fts)

adjustBypassWireFields ::
    ([VFieldInfo], [([AType], Maybe AType, Maybe AType)]) ->
    ([VFieldInfo], [([AType], Maybe AType, Maybe AType)])
adjustBypassWireFields (vfi, fts) =
    let renameField vf@(Method {vf_name = i })
            | (i `qualEq` idWGet) = vf { vf_name = id_read noPosition }
            | (i `qualEq` idWSet) = vf { vf_name = id_write noPosition }
        renameField vf =
            internalError ("adjustBypassWireFields: unknown field: " ++
                           ppReadable (vf_name vf))
    in  (map renameField vfi, fts)

-- ---------------

getVNameType :: M.Map VName IType -> VName -> (String, IType)
getVNameType ptmap vn =
    case (M.lookup vn ptmap) of
        Just t -> (getVNameString vn, t)
        Nothing -> internalError ("getVNameType: " ++ ppReadable vn)

getMVNameType :: M.Map VName IType -> Maybe VName -> Maybe (String, IType)
getMVNameType ptmap mvn = mvn >>= Just . getVNameType ptmap

getMVPortType :: M.Map VName IType -> Maybe VPort -> Maybe (String, IType)
getMVPortType ptmap mvp = mvp >>= (\ (vn,_) ->  Just (getVNameType ptmap vn) )

addMVNameType :: Maybe VName -> IType -> Maybe (String, IType)
addMVNameType Nothing _ = Nothing
addMVNameType (Just vn) t = Just (getVNameString vn, t)

addMVPortType :: Maybe VPort -> IType -> Maybe (String, IType)
addMVPortType Nothing _ = Nothing
addMVPortType (Just (vn,_)) t = Just (getVNameString vn, t)

isSizeZero :: AType -> Bool
isSizeZero (ATBit sz) = (sz == 0)
isSizeZero (ATAbstract c [sz]) | (c `qualEq` idInout_) = (sz == 0)
isSizeZero _          = False


getPortsModArgParam :: Id -> AType -> VName -> PortArgInfo
getPortsModArgParam i t vn = (PAParam i t (getVNameString vn))

getPortsModArgPort ::
    M.Map VName IType ->
    Id -> AType -> VPort -> Maybe Id -> Maybe Id -> [PortArgInfo]
getPortsModArgPort ptmap i t (vn,_) mclk mrst =
    if (isSizeZero t)
    then []
    else [PAPort i t (getVNameType ptmap vn) mclk mrst]

getPortsModArgClock :: [InputClockInf] -> Id -> PortArgInfo
getPortsModArgClock in_clkinfo i =
    case (lookup i in_clkinfo) of
        Nothing -> internalError ("getPortsModArgClock: clock not found: " ++
                                  ppReadable (i, in_clkinfo))
        Just (Nothing) -> (PAClock i Nothing)
        Just (Just (osc, mgate)) ->
            let osc' = (getVNameString osc, itClock)
                mgate' = case mgate of
                             Left _ -> Nothing
                             Right vn -> Just (getVNameString vn, itBool)
            in  (PAClock i (Just (osc', mgate')))

getPortsModArgReset :: [ResetInf] -> Id -> PortArgInfo
getPortsModArgReset in_rstinfo i =
    case (lookup i in_rstinfo) of
        Nothing -> internalError ("getPortsModArgReset: reset not found: " ++
                                  ppReadable (i, in_rstinfo))
        Just (mport, mclk) ->
            (PAReset i (addMVNameType mport itReset) mclk)

getPortsModArgInout ::
    M.Map VName IType ->
    Id -> Integer -> VName -> Maybe Id -> Maybe Id -> [PortArgInfo]
getPortsModArgInout ptmap i sz vn mclk mrst =
    if (sz == 0)
    then []
    else [PAInout i sz (getVNameType ptmap vn) mclk mrst]


getPortsIfc :: M.Map VName IType ->
               [OutputClockInf] -> [ResetInf] ->
               IfcField -> [PortIfcInfo]
getPortsIfc ptmap out_clkinfo out_rstinfo (SubIfc fId fs) =
    let fs' = concatMap (getPortsIfc ptmap out_clkinfo out_rstinfo) fs
    in  if (null fs')
        then []
        else [PISubIfc fId fs']
getPortsIfc ptmap _ _
            (Field fId (RawMethod i mult mclk mrst args ins mo me) mrdy_inf) =
    getPortsIfcMethod ptmap fId i mult mclk mrst args ins mo me mr
 where mr = case (mrdy_inf) of
              Nothing -> Nothing
              (Just (RawMethod ri m _ _ [] [] (Just (vp@(vn,_), t)) Nothing))
               | ((m == 0) || (m == 1)) ->
                  if (t == aTBool)
                  then Just vp
                  else internalError ("getPortsIfc: Rdy wrong size: " ++
                                      ppReadable (ri,t))
              (Just (RawMethod ri m _ _ as is mout men)) ->
                  internalError ("getPortsIfc: not Rdy: " ++
                                 ppReadable (ri, m, as, is, mout, men))
              (Just d) -> internalError ("getPortsIfc: not Rdy: " ++
                                         ppReadable (rawIfcFieldName d))
getPortsIfc _ out_clkinfo _ (Field fId (RawClock i) Nothing) =
    [getPortsIfcClock out_clkinfo fId i]
getPortsIfc _ _ out_rstinfo (Field fId (RawReset i) Nothing) =
    [getPortsIfcReset out_rstinfo fId i]
getPortsIfc ptmap _ _ (Field fId (RawInout i t vn mclk mrst) Nothing) =
    getPortsIfcInout ptmap fId i t vn mclk mrst
getPortsIfc _ _ _ (Field fId rf (Just rdy_rf)) =
    internalError ("getPortsIfc: subifc should not have a Rdy: " ++
                   ppReadable (rawIfcFieldName rf, rawIfcFieldName rdy_rf))


getPortsIfcMethod :: M.Map VName IType ->
                  Id -> Id -> Integer ->
                  Maybe Id -> Maybe Id ->
                  [(Maybe Id, AType)] -> [VPort] -> Maybe (VPort, AType) ->
                  Maybe VPort -> Maybe VPort ->
                  [PortIfcInfo]
getPortsIfcMethod ptmap fId methId mult mClk mRst args ins mOut mEn mRdy =
    let
        -- get the port-type pair for an argument
        getPortsArg (mi, bit_type) (vn, _) =
            if (isSizeZero bit_type)
            then []
            else [(mi, bit_type, getVNameType ptmap vn)]
        -- get the port-type pair for the output
        getPortsOut Nothing = Nothing
        getPortsOut (Just ((vn, _), bit_type)) =
            if (isSizeZero bit_type)
            then Nothing
            else
            -- XXX since IExpand is not recording types for rdy methods
            if (isRdyId methId)
            then Just (getVNameString vn, bit_type, itBool)
            else let (s,t) = getVNameType ptmap vn
                 in  Just (s, bit_type, t)
        -- get the port-type pair for the enable
        getPortsEn Nothing = Nothing
        getPortsEn (Just (vn, ps)) =
            -- filter out inhigh ports
            if (VPinhigh `elem` ps)
            then Nothing
            else Just (getVNameString vn, itBool)
        -- get the port-type pair for the ready
        getPortsRdy Nothing = Nothing
        getPortsRdy (Just (vn, _)) = Just (getVNameString vn, itBool)

        -- the default result (multiplicity of 1)
        def_res = PIMethod fId methId mClk mRst
                      (concat (zipWith getPortsArg args ins))
                      (getPortsOut mOut) (getPortsEn mEn) (getPortsRdy mRdy)

        -- the result if multiplicity > 1
        mkMulRes n =
            let s = "_" ++ show n
                ins' = map (dupVPort s) ins
            in  PIMethod (dupId s fId) -- XXX handle mults differently?
                    (dupId s methId) mClk mRst
                    (concat (zipWith getPortsArg args ins'))
                    (getPortsOut (dupMVPortType s mOut))
                    (getPortsEn (dupMVPort s mEn))
                    (getPortsRdy (dupMVPort s mRdy))

        dupId suf i = mkIdPost i (mkFString suf)
        dupVName suf (VName s) = VName (s ++ suf)
        dupVPort suf (vn, ps) = (dupVName suf vn, ps)
        dupMVPort :: String -> Maybe VPort -> Maybe VPort
        dupMVPort suf mvp = mvp >>= Just . dupVPort suf
        dupMVPortType :: String -> Maybe (VPort, AType) -> Maybe (VPort, AType)
        dupMVPortType suf mvpt =
            mvpt >>= (\ (vp, t) -> Just (dupVPort suf vp, t) )
    in
        if (mult == 1) || (mult == 0)
        then [def_res]
        else map mkMulRes [1..mult]

getPortsIfcClock :: [OutputClockInf] -> Id -> Id -> PortIfcInfo
getPortsIfcClock out_clkinfo fId i =
    case (lookup i out_clkinfo) of
        Nothing -> internalError ("getPortsIfcClock: clock not found: " ++
                                  ppReadable (i, out_clkinfo))
        Just (Nothing) -> (PIClock i fId Nothing)
        Just (Just (osc, mgate)) ->
            let osc' = (getVNameString osc, itClock)
                mgate' = addMVPortType mgate itBool
            in  (PIClock fId i (Just (osc', mgate')))

getPortsIfcReset :: [ResetInf] -> Id -> Id -> PortIfcInfo
getPortsIfcReset out_rstinfo fId i =
    case (lookup i out_rstinfo) of
        Nothing -> internalError ("getPortsIfcReset: reset not found: " ++
                                  ppReadable (i, out_rstinfo))
        Just (mport, mclk) ->
            (PIReset fId i (addMVNameType mport itReset) mclk)

getPortsIfcInout ::
    M.Map VName IType ->
    Id -> Id -> AType -> VName -> Maybe Id -> Maybe Id -> [PortIfcInfo]
getPortsIfcInout ptmap fId i t vn mclk mrst =
    if (isSizeZero t)
    then []
    else [PIInout fId i t (getVNameType ptmap vn) mclk mrst]


----------------------------------------------------
-- module argument and interface display functions
-- common to the "module" and "submodule" commands


-- display clock
dispClockedBy :: Maybe Id -> HTclObj
dispClockedBy Nothing  = tagStr "clock" "no_clock"
dispClockedBy (Just c) = tagStr "clock" (pfpString c)

-- display reset
dispResetBy :: Maybe Id -> HTclObj
dispResetBy Nothing  = tagStr "reset" "no_reset"
dispResetBy (Just r) = tagStr "reset" (pfpString r)

-- display maybe a port name
-- (The first argument is the tag, like "port", "gate", etc)
dispMPort :: String -> Maybe String -> [HTclObj]
dispMPort s mport =
    case mport of
        Nothing -> []
        Just p -> [tagStr s p]

dispMPortWithType :: String -> Maybe (String, IType) -> [HTclObj]
dispMPortWithType s mport =
    case mport of
      Nothing -> []
      Just (p, _) -> [tagStr s p]

dispMPortWithTypes :: String -> Maybe (String, AType, IType) -> [HTclObj]
dispMPortWithTypes s mport =
    case mport of
      Nothing -> []
      Just (p, _, _) -> -- XXX we have the opportunity to display the size
                        [tagStr s p]

-- display AType
dispSize :: AType -> [HTclObj]
dispSize (ATBit sz) = [tagInt "size" (fromInteger sz)]
dispSize _          = []

-- display a numeric size
dispNSize :: Integer -> HTclObj
dispNSize sz = tagInt "size" (fromInteger sz)


-- display module arguments
dispModArg :: PortArgInfo -> HTclObj
dispModArg (PAParam i _ name) =
    TLst $ [TStr "parameter", TStr (pfpString i)] ++
           [tagStr "param" name]
dispModArg (PAPort i bit_type (port, _) mclk mrst) =
    TLst $ [TStr "port", TStr (pfpString i)] ++
           [tagStr "port" port] ++
           [dispClockedBy mclk] ++
           [dispResetBy mrst] ++
           dispSize bit_type
dispModArg (PAClock i Nothing) =
    TLst [TStr "clock", TStr (pfpString i)]
dispModArg (PAClock i (Just ((osc, _), mgate))) =
    TLst $ [TStr "clock", TStr (pfpString i),
            tagStr "osc" osc] ++
           dispMPortWithType "gate" mgate
dispModArg (PAReset i mport mclk) =
    TLst $ [TStr "reset", TStr (pfpString i)] ++
           (dispMPortWithType "port" mport) ++
           [dispClockedBy mclk]
dispModArg (PAInout i sz (port,_) mclk mrst) =
    TLst $ [TStr "inout", TStr (pfpString i)] ++
           [tagStr "port" port] ++
           [dispClockedBy mclk] ++
           [dispResetBy mrst] ++
           [dispNSize sz]


dispMethodArgs :: [(Maybe Id, AType, (String, IType))] -> HTclObj
dispMethodArgs as =
    let dispMName Nothing = []
        dispMName (Just i) = [tagStr "name" (pfpString i)]
        dispArg (mi, bit_type, (port, _)) =
            TLst $ (dispMName mi) ++
                   [tagStr "port" port] ++
                   dispSize bit_type
    in  TLst (map dispArg as)


dispIfc :: PortIfcInfo -> HTclObj
dispIfc (PIMethod fId i mClk mRst ins mOut mEn mRdy) =
    TLst $ [TStr "method",
            TStr (getIdBaseString fId),
            TStr (pfpString i),
            dispClockedBy mClk,
            dispResetBy mRst,
            tag "args" [dispMethodArgs ins]] ++
           dispMPortWithTypes "result" mOut ++
           dispMPortWithType "enable" mEn ++
           dispMPortWithType "ready" mRdy
dispIfc (PIClock fId i Nothing) =
    TLst [TStr "clock", TStr (getIdBaseString fId), TStr (pfpString i)]
dispIfc (PIClock fId i (Just ((osc, _), mgate))) =
    TLst $ [TStr "clock", TStr (getIdBaseString fId), TStr (pfpString i),
            tagStr "osc" osc] ++
           dispMPortWithType "gate" mgate
dispIfc (PIReset fId i mport mclk) =
    TLst $ [TStr "reset", TStr (getIdBaseString fId), TStr (pfpString i)] ++
           (dispMPortWithType "port" mport) ++
           [dispClockedBy mclk]
dispIfc (PIInout fId i bit_type (port,_)  mclk mrst) =
    TLst $ [TStr "inout", TStr (getIdBaseString fId), TStr (pfpString i)] ++
           [tagStr "port" port] ++
           [dispClockedBy mclk] ++
           [dispResetBy mrst] ++
           (dispSize bit_type)
dispIfc (PISubIfc fId fs) =
    TLst $ [TStr "interface", TStr (getIdBaseString fId),
            TLst (map dispIfc fs)]

-- ---------------

-- Display just the ports and their types

dispPortType :: (String, IType) -> HTclObj
dispPortType (p,t) = TLst [TStr p, TStr (pfpString t)]

dispMPortType :: Maybe (String, IType) -> [HTclObj]
dispMPortType Nothing = []
dispMPortType (Just pt) = [dispPortType pt]

dispMPortTypes :: Maybe (String, AType, IType) -> [HTclObj]
dispMPortTypes Nothing = []
dispMPortTypes (Just (p, at, it)) = [dispPortType (p, it)]


dispPortsModArg :: PortArgInfo -> [HTclObj]
dispPortsModArg (PAParam _ _ _) = []
dispPortsModArg (PAPort _ _ pt _ _) = [dispPortType pt]
dispPortsModArg (PAClock _ Nothing) = []
dispPortsModArg (PAClock _ (Just (osc, mgate))) =
    [dispPortType osc] ++ dispMPortType mgate
dispPortsModArg (PAReset _ mpt _) = dispMPortType mpt
dispPortsModArg (PAInout _ _ pt _ _) = [dispPortType pt]


dispPortsIfc :: PortIfcInfo -> [HTclObj]
dispPortsIfc (PIMethod _ _ _ _ ins mOut mEn mRdy) =
    (map (dispPortType . thd) ins) ++
    dispMPortTypes mOut ++ dispMPortType mEn ++ dispMPortType mRdy
dispPortsIfc (PIClock _ _ Nothing) = []
dispPortsIfc (PIClock _ _ (Just (osc, mgate))) =
    [dispPortType osc] ++ dispMPortType mgate
dispPortsIfc (PIReset _ _ mpt _) = dispMPortType mpt
dispPortsIfc (PIInout _ _ _ pt _ _) = [dispPortType pt]
dispPortsIfc (PISubIfc _ fs) = concatMap dispPortsIfc fs


----------------------------------------------------

-- Depend functions
dependGrammar :: HTclCmdGrammar
dependGrammar =
    ((tclcmd "depend" namespace helpStr "") .+.
     (oneOf [(kw "make" makeHelpStr "") .+. (arg "file" StringArg "file name")
            ,(kw "file" fileHelpStr "") .+. (arg "file" StringArg "file name")
            ,(kw "recomp" recompHelpStr "") .+. (arg "file" StringArg "file name")
            ]))
     where helpStr = "Show the file and package dependencies for a given file."
           makeHelpStr = "Show dependency for top file and all sub packages in a make compatible format"
           fileHelpStr = "Lists only the files and not package dependencies"
           recompHelpStr = "List all files which need to be recompiled based on file."


replaceBSDir :: Flags -> String -> String -> String
replaceBSDir flags substr s =
    let dirregex = mkRegex $ bluespecDir  flags
    in subRegex dirregex s substr

tclDepend :: [String] -> IO HTclObj
tclDepend ["make",fname] = do
  flags <- getGFlags
  (errs,dep) <- genDepend globalErrHandle flags fname
  reportErrorsToTcl (nubBy (\l r -> snd l == snd r) errs) []
  let dep' = mapSnd (map (replaceBSDir flags "$(BLUESPECDIR)")) dep
  return $ toHTObj $ reverse dep'
--
tclDepend ["file",fname]= do
    flags <- getGFlags
    (errs,fl) <- genFileDepend globalErrHandle flags fname
    reportErrorsToTcl (nubBy (\l r -> snd l == snd r) errs) []
    return $ toHTObj $ reverse fl

--
tclDepend ["recomp",fname]= do
    flags <- getGFlags
    fnames <- chkDeps globalErrHandle flags fname
    return $ toHTObj fnames

tclDepend xs = internalError $ "tclDepend: grammar mismatch: " ++ (show xs)

find_vmodinfo :: (IPackage Id) -> [VModInfo]
find_vmodinfo = listify
                (let
                    tagVMI :: VModInfo -> Bool
                    tagVMI _ = True
                 in tagVMI)

package_vsignals :: TclP -> [(Id,String)]
package_vsignals tclp =
  (map head) $ group $ sort $ -- equivalent to nub, but faster hopefully
  (M.elems (tp_binmap tclp))
  >>= (return . ip_ipkg) >>= find_vmodinfo >>= get_method_to_signal_map

get_method_to_signal_map :: VModInfo -> [(Id,String)]
get_method_to_signal_map vmod = do
  f <- vFields vmod
  case f of
       Method {} -> return ()
       _ -> mzero -- failure, as in the guard function
  port <- (vf_inputs f) ++ (maybeToList $ vf_output f) ++ (maybeToList $ vf_enable f)
  count <- case (vf_mult f) of
    1 -> return Nothing
    k -> map Just [1..k]

  return (vf_name f, make_numbered_port (fst port) count)

-- needed for RegFiles
make_numbered_port :: VName -> Maybe Integer -> String
make_numbered_port v Nothing = getVNameString v
-- xxx use something like ASyntax.mkMethId
make_numbered_port v (Just i) = (getVNameString v) ++ "_" ++ (show i)

parseTimescale :: String -> Maybe (String, BSTime)
parseTimescale timescale = do
  separatorIndex <- elemIndex '/' timescale
  let timeunitStr      = take separatorIndex timescale
      timeprecisionStr = drop (separatorIndex + 1) timescale -- drop '/' too
  timeunit <- timeOf timeunitStr
  timeprecision <- timeOf timeprecisionStr
  if (timeunit >= timeprecision)
  then return (timeprecisionStr, timeunit `quot` timeprecision)
  else Nothing

timeOf :: String -> Maybe BSTime -- number of femtoseconds
timeOf timeStr =
  case words timeStr of
    ["1", unitStr]   -> getTimeUnitSize unitStr
    ["10", unitStr]  -> fmap (10 *)  $ getTimeUnitSize unitStr
    ["100", unitStr] -> fmap (100 *) $ getTimeUnitSize unitStr
    _                -> Nothing
  where getTimeUnitSize "fs" = Just 1
        getTimeUnitSize "ps" = fmap (1000 *) $ getTimeUnitSize "fs"
        getTimeUnitSize "ns" = fmap (1000 *) $ getTimeUnitSize "ps"
        getTimeUnitSize "us" = fmap (1000 *) $ getTimeUnitSize "ns"
        getTimeUnitSize "ms" = fmap (1000 *) $ getTimeUnitSize "us"
        getTimeUnitSize "s"  = fmap (1000 *) $ getTimeUnitSize "ms"
        getTimeUnitSize _    = Nothing
