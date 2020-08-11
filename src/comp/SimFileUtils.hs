module SimFileUtils ( analyzeBluesimDependencies
                    , codeGenOptionDescr
                    ) where

import Id(Id,getIdBaseString)
import Flags(Flags(..))
import SimPackage
import SimPrimitiveModules(isPrimitiveModule)
import ASyntax(AVInst(..))
import ABinUtil(ABinMap)
import VModInfo(VModInfo(..), getVNameString)
import Version(bscVersionStr)
import FileNameUtil
import ErrorUtil(internalError)

import System.Posix.Files
import System.Posix.Types(EpochTime)
import System.IO(openFile, hGetContents, hClose, IOMode(..))
import Control.Monad(filterM)
import Control.Exception(bracketOnError)
import Data.List(delete,find,isPrefixOf)
import qualified Data.Map as M

-- import Debug.Trace(traceM)

getModTime :: FilePath -> IO (Maybe EpochTime)
getModTime f =
    do ok <- fileExist f
       if ok
        then do s <- getFileStatus f
                return $ Just (modificationTime s)
        else return Nothing

codeGenOptionDescr :: Flags -> Bool -> String
codeGenOptionDescr flags is_top =
    unwords $ [ "Generation options:" ] ++
              (if (keepFires flags) then ["keep-fires"] else []) ++
              (if (is_top && (genSysC flags)) then ["sysc-top"] else [])

readCodeGenOptionDescr :: FilePath -> IO (Maybe String)
readCodeGenOptionDescr f =
    do ok <- fileExist f
       if ok
        then do bracketOnError (openFile f ReadMode)
                               (\hdl -> do hClose hdl
                                           return Nothing)
                               (\hdl -> do content <- hGetContents hdl
                                           let search_window = take 15 (lines content)
                                               comment = find ("/* Generation options: " `isPrefixOf`) search_window
                                           comment `seq` hClose hdl
                                           return comment)
        else return Nothing

isStale :: Flags -> FilePath -> ABinMap -> Id -> SimPackage -> IO Bool
isStale flags prefix ba_map top_pkg pkg =
    if (sp_version pkg /= bscVersionStr True)
    then return True
    else let name = getIdBaseString (sp_name pkg)
         in case (M.lookup name ba_map) of
              Nothing        -> internalError $ "isStale: unknown package " ++ name
              (Just ba_file) -> do h_file <- genFileName mkHName (cdir flags) "" name
                                   o_file <- genFileName mkObjName (cdir flags) "" name
                                   ba_time <- getModTime ba_file
                                   h_time <- getModTime h_file
                                   obj_time <- getModTime o_file
                                   let stale_time =
                                        case (ba_time, h_time, obj_time) of
                                          (Just t1, Just t2, Just t3) -> (t2 < t1) || (t3 < t1)
                                          _                           -> True
                                   cg_opt <- readCodeGenOptionDescr h_file
                                   let is_top = (sp_name pkg) == top_pkg
                                       cg_tgt = Just ("/* " ++ (codeGenOptionDescr flags is_top) ++ " */")
                                       stale_options = cg_opt /= cg_tgt
                                   return $ stale_time || stale_options

remove_stale :: M.Map String [String] -> [String] -> [String] -> [String]
remove_stale _     []   _      = []
remove_stale _     pkgs []     = pkgs
remove_stale feeds pkgs (x:xs) =
    if (x `elem` pkgs)
    then let invalidated = maybe [] id (M.lookup x feeds)
         in remove_stale feeds (delete x pkgs) (invalidated ++ xs)
    else remove_stale feeds pkgs xs

analyzeBluesimDependencies :: Flags -> SimSystem -> FilePath -> IO [String]
analyzeBluesimDependencies flags sim_system prefix =
    do let pkgs = M.elems (ssys_packages sim_system)
           ba_map = ssys_filemap sim_system
           influences pkg = let pname = getIdBaseString (sp_name pkg)
                                insts = [ name
                                        | i <- M.elems (sp_state_instances pkg)
                                        , let name = getVNameString (vName (avi_vmi i))
                                        , not (isPrimitiveModule name)
                                        ]
                            in map (\x -> (x,[pname])) insts
           feeds = M.fromListWith (++) (concatMap influences pkgs)
           top_mod = ssys_top sim_system
       stale_pkgs <- filterM (isStale flags prefix ba_map top_mod) pkgs
       let all_pkg_names = map (getIdBaseString . sp_name) pkgs
           stale_pkg_names = map (getIdBaseString . sp_name) stale_pkgs
           reusable = remove_stale feeds all_pkg_names stale_pkg_names
       return reusable
