{-# LANGUAGE CPP #-}
module FileIOUtil
    (readFilePath
    ,readBinFilePath
    ,readFilePathOrAbs
    ,readFilesPath
    ,readFileMaybe
    ,readFileCatch
    ,readBinaryFileMaybe
    ,readBinaryFileCatch
    ,writeFileCatch
    ,writeBinaryFileCatch
    ,appendFileCatch
    ,removeFileCatch
    ,copyFileCatch
    ,checkDirectory
    ,createDirectoryCatch
    ,openFileCatch
    ,hCloseCatch
    ,hFlushCatch
    ,hGetBufferingCatch
    ,hSetBufferingCatch
    ,hPutStrCatch
    ,hGetLineCatch
    ,hGetCharCatch
    ,hIsEOFCatch
    ,hIsReadableCatch
    ,hIsWritableCatch
    ,maxBufferSize
    ,putStrHandles
    )
 where

-- ==================================================
-- FileIOUtil
--
-- This module contains functions for reading and writing files
-- and catching IO failures and reporting them as BSC errors.
--
-- ==================================================

-- GHC 6.12 and beyond honor the default character encoding
-- based on the current locale.  We have to set it explicitly
-- to Latin1 for backward compatibility.
#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 611)
#define SET_LATIN1_ENCODING
#endif

import Data.List(foldl')
import Data.Maybe(isJust)
import System.IO
import System.Directory
import qualified Control.Exception as CE
import System.IO.Error(ioeGetErrorString)
import Control.Monad(when)

import Util(concatMapM)
import BinaryIO
import FileNameUtil(dirName, getRelativeFilePath)

import Position
import Error(ErrMsg(..), ErrorHandle, MsgContext, emptyContext,
             bsError, bsErrorWithContext, bsWarning)

-- hack around base-3 and base-4 incompatibility
#if !defined(__GLASGOW_HASKELL__) || (__GLASGOW_HASKELL__ >= 609)
catchIO = CE.catch
#else
import qualified System.IO.Error as IOE (catch)
catchIO = IOE.catch
#endif

-- =====
-- Searching for a file to read

--
-- Arguments:
--   verb = whether to write reads to a file
--   msg  = error handler in case the file is not found
--   name = filename (with relative or no path) to search for
--   path = list of paths to search for the file in
--
-- Returns:
--   (file contents, file name)
--
readFilePath :: ErrorHandle -> Position ->
                Bool -> String -> [String] -> IO (Maybe (String, String))
readFilePath errh pos verb name path =
    readFilesPath' errh pos False verb [name] path

readBinFilePath :: ErrorHandle -> Position ->
                   Bool -> String -> [String] -> IO (Maybe (String, String))
readBinFilePath errh pos verb name path =
    readFilesPath' errh pos True verb [name] path

-- for this variant, the file name can have an absolute path
readFilePathOrAbs :: ErrorHandle -> Position ->
                     Bool -> String -> [String] -> IO (Maybe (String, String))
readFilePathOrAbs errh pos verb name@('/':_) _ = do
    -- it's an absolute filename, so just try to read it
    exists <- doesFileExist name
    if (not exists)
      then return Nothing
      else readFilePath_tryFile errh pos False verb name
readFilePathOrAbs errh pos verb name path =
    -- relative file name, so search each directory in the path
    readFilesPath' errh pos False verb [name] path

-- look for multiple file names
-- (the first name is searched first in all paths, then the second name, etc)
readFilesPath :: ErrorHandle -> Position ->
                 Bool -> [String] -> [String] -> IO (Maybe (String, String))
readFilesPath errh pos verb names path =
    readFilesPath' errh pos False verb names path

-- Use one of the above entry points.  This is the internal function.
readFilesPath' :: ErrorHandle -> Position ->
                  Bool -> Bool -> [String] -> [String] ->
                  IO (Maybe (String, String))
readFilesPath' errh pos binary verb names [] = return Nothing
readFilesPath' errh pos binary verb names path = do
    found_files <- concatMapM (flip existsFilePath path) names
    case found_files of
      [] -> return Nothing
      [file] -> readFilePath_tryFile errh pos binary verb file
      _ -> do
          -- find the first file that can be read
          let findFn [] = return Nothing
              findFn (f:fs) = do
                  mfile <- readFilePath_tryFile errh pos binary verb f
                  if (isJust mfile) then return mfile else findFn fs
          res <- findFn found_files
          case (res) of
            Nothing -> return res
            Just (_, name) -> do
                let other_names = filter (/= name) found_files
                multipleFilesWarning errh pos name other_names
                return res


-- this is used by readFilePath' to try reading one filename
readFilePath_tryFile :: ErrorHandle -> Position ->
                        Bool -> Bool -> String -> IO (Maybe (String, String))
readFilePath_tryFile errh pos binary verb name =
    let
        handler :: CE.IOException -> IO (Maybe (String, String))
        handler ioe = do let io_msg = ioeGetErrorString ioe
                         existsButUnreadableWarning errh pos name io_msg
                         return Nothing

        rdFn = if binary then readBinaryFile else readFile
        rdFile = do file <- rdFn name
                    when (verb) $ putStr ("read "++name++"\n")
                    return $ Just (file, name)
    in
        catchIO rdFile handler


-- returns the files that were found
existsFilePath :: String -> [String] -> IO [String]
existsFilePath fname [] = return []
existsFilePath fname (p:paths) = do
    let name = p ++ "/" ++ fname
    exists <- doesFileExist name
    rest <- existsFilePath fname paths
    return $ if exists then (name:rest) else rest


multipleFilesWarning :: ErrorHandle -> Position -> String -> [String] -> IO ()
multipleFilesWarning errh pos chosen_file other_files =
    let wmsg = (pos, WMultipleFilesInPath chosen_file other_files)
    in  bsWarning errh [wmsg]

existsButUnreadableWarning :: ErrorHandle -> Position -> String -> String -> IO ()
existsButUnreadableWarning errh pos file io_msg =
    let wmsg = (pos, WFileExistsButUnreadable file io_msg)
    in  bsWarning errh [wmsg]


-- =====
-- Catch versions of file IO

#ifdef SET_LATIN1_ENCODING
readFileCompat :: FilePath -> IO String
readFileCompat fname = do hdl <- openFile fname ReadMode
                          hSetEncoding hdl latin1
                          hGetContents hdl

writeFileCompat :: FilePath -> String -> IO ()
writeFileCompat fname txt =
    withFile fname WriteMode (\hdl -> do hSetEncoding hdl latin1
                                         hPutStr hdl txt)

appendFileCompat :: FilePath -> String -> IO ()
appendFileCompat fname txt =
    withFile fname AppendMode (\hdl -> do hSetEncoding hdl latin1
                                          hPutStr hdl txt)
#else
readFileCompat :: FilePath -> IO String
readFileCompat = readFile

writeFileCompat :: FilePath -> String -> IO ()
writeFileCompat = writeFile

appendFileCompat :: FilePath -> String -> IO ()
appendFileCompat = appendFile
#endif

-- This returns whether the read was successful,
-- for callers who will move on if the file is not available
readFileMaybe :: FilePath -> IO (Maybe String)
readFileMaybe fname =
    let
        handler :: CE.IOException -> IO (Maybe String)
        handler ioe = return Nothing

        rdFile = do  file <- readFileCompat fname
                     return (Just file)
    in
        catchIO rdFile handler

-- This produces an error if the read is unsuccessful,
-- for callers which expect the file to be there.
readFileCatch :: ErrorHandle -> Position -> FilePath -> IO String
readFileCatch errh pos fname = do
    catchIO (readFileCompat fname) (fileReadError errh emptyContext pos fname)

-- This returns whether the read was successful,
-- for callers who will move on if the file is not available
readBinaryFileMaybe :: FilePath -> IO (Maybe String)
readBinaryFileMaybe fname =
    let
        handler :: CE.IOException -> IO (Maybe String)
        handler ioe = return Nothing

        rdFile = do  file <- readBinaryFile fname
                     return (Just file)
    in
        catchIO rdFile handler

-- This produces an error if the read is unsuccessful,
-- for callers which expect the file to be there
readBinaryFileCatch :: ErrorHandle -> Position -> FilePath -> IO String
readBinaryFileCatch errh pos fname =
    catchIO (readBinaryFile fname) (fileReadError errh emptyContext pos fname)

-- If the file writing fails, a BSC error message is reported
writeFileCatch :: ErrorHandle -> FilePath -> String -> IO ()
writeFileCatch errh fname content = do
    -- check if the directory exists, and report an error if not
    checkDirectory fname (fileWriteError errh emptyContext noPosition fname)
    -- try to write the file
    catchIO (writeFileCompat fname content)
            (fileWriteError errh emptyContext noPosition fname)

writeBinaryFileCatch :: ErrorHandle -> FilePath -> String -> IO ()
writeBinaryFileCatch errh fname content = do
    -- check if the directory exists, and report an error if not
    checkDirectory fname (fileWriteError errh emptyContext noPosition fname)
    -- try to write the file
    catchIO (writeBinaryFile fname content)
            (fileWriteError errh emptyContext noPosition fname)

appendFileCatch :: ErrorHandle -> FilePath -> String -> IO ()
appendFileCatch errh fname content = do
    -- check if the directory exists, and report an error if not
    checkDirectory fname (fileWriteError errh emptyContext noPosition fname)
    -- try to append to the file
    catchIO (appendFileCompat fname content)
            (fileWriteError errh emptyContext noPosition fname)

removeFileCatch :: ErrorHandle -> FilePath -> IO ()
removeFileCatch errh fname =
    catchIO (removeFile fname) (fileRemoveError errh fname)

copyFileCatch :: ErrorHandle -> FilePath -> FilePath -> IO ()
copyFileCatch errh src dst =
    catchIO (copyFile src dst) (fileCopyError errh src dst)

-- check whether the directory for the file exists
checkDirectory :: FilePath -> (CE.IOException -> IO ()) -> IO ()
checkDirectory fname handler = do
    exists <- doesDirectoryExist (dirName fname)
    if (not exists)
        then catchIO (fail "Directory does not exist") handler
        else return ()

createDirectoryCatch :: ErrorHandle -> FilePath -> IO ()
createDirectoryCatch errh dirname =
    catchIO (createDirectory dirname) (dirCreateError errh dirname)

openFileCatch :: ErrorHandle -> MsgContext -> FilePath -> IOMode -> IO Handle
openFileCatch errh ctx fp mode =
    let fileOpenError = case mode of
                          ReadMode -> fileReadError
                          _ -> fileWriteError
    in  catchIO (openFile fp mode) (fileOpenError errh ctx noPosition fp)

hCloseCatch :: ErrorHandle -> MsgContext -> Position -> Handle -> IO ()
hCloseCatch errh ctx pos hdl =
    catchIO (hClose hdl) (fileHandleError errh ctx pos)

hFlushCatch :: ErrorHandle -> MsgContext -> Position -> Handle -> IO ()
hFlushCatch errh ctx pos hdl =
    catchIO (hFlush hdl) (fileHandleError errh ctx pos)

hGetBufferingCatch :: ErrorHandle -> MsgContext -> Position ->
                      Handle -> IO BufferMode
hGetBufferingCatch errh ctx pos hdl =
    catchIO (hGetBuffering hdl) (fileHandleError errh ctx pos)

hSetBufferingCatch :: ErrorHandle -> MsgContext -> Position ->
                      Handle -> BufferMode -> IO ()
hSetBufferingCatch errh ctx pos hdl mode =
    catchIO (hSetBuffering hdl mode) (fileHandleError errh ctx pos)

hPutStrCatch :: ErrorHandle -> MsgContext -> Position ->
                Handle -> String -> IO ()
hPutStrCatch errh ctx pos hdl str =
    catchIO (hPutStr hdl str) (fileHandleError errh ctx pos)

hGetLineCatch :: ErrorHandle -> MsgContext -> Position -> Handle -> IO String
hGetLineCatch errh ctx pos hdl =
    catchIO (hGetLine hdl) (fileHandleError errh ctx pos)

hGetCharCatch :: ErrorHandle -> MsgContext -> Position -> Handle -> IO Char
hGetCharCatch errh ctx pos hdl =
    catchIO (hGetChar hdl) (fileHandleError errh ctx pos)

hIsEOFCatch :: ErrorHandle -> MsgContext -> Position -> Handle -> IO Bool
hIsEOFCatch errh ctx pos hdl =
    catchIO (hIsEOF hdl) (fileHandleError errh ctx pos)

hIsReadableCatch :: ErrorHandle -> MsgContext -> Position -> Handle -> IO Bool
hIsReadableCatch errh ctx pos hdl =
    catchIO (hIsReadable hdl) (fileHandleError errh ctx pos)

hIsWritableCatch :: ErrorHandle -> MsgContext -> Position -> Handle -> IO Bool
hIsWritableCatch errh ctx pos hdl =
    catchIO (hIsWritable hdl) (fileHandleError errh ctx pos)


-- =====
-- Error messages

fileReadError :: ErrorHandle -> MsgContext -> Position ->
                 FilePath -> CE.IOException -> IO a
fileReadError errh ctx pos fname e =
    let fname_rel = getRelativeFilePath fname
        io_msg = ioeGetErrorString e
        emsg = (pos, EFileReadFailure fname_rel io_msg)
    in  bsErrorWithContext errh ctx [emsg]

fileWriteError :: ErrorHandle -> MsgContext -> Position ->
                  FilePath -> CE.IOException -> IO a
fileWriteError errh ctx pos fname e =
    let fname_rel = getRelativeFilePath fname
        io_msg = ioeGetErrorString e
        emsg = (pos, EFileWriteFailure fname_rel io_msg)
    in  bsErrorWithContext errh ctx [emsg]

fileRemoveError :: ErrorHandle -> FilePath -> CE.IOException -> IO a
fileRemoveError errh fname e =
    let fname_rel = getRelativeFilePath fname
        io_msg = ioeGetErrorString e
        emsg = (noPosition, EFileRemoveFailure fname_rel io_msg)
    in  bsError errh [emsg]

fileCopyError :: ErrorHandle -> FilePath -> FilePath -> CE.IOException -> IO a
fileCopyError errh src dst e =
    let src_rel = getRelativeFilePath src
        dst_rel = getRelativeFilePath dst
        io_msg = ioeGetErrorString e
        emsg = (noPosition, EFileCopyFailure src_rel dst_rel io_msg)
    in  bsError errh [emsg]

dirCreateError :: ErrorHandle -> FilePath -> CE.IOException -> IO a
dirCreateError errh dname e =
    let io_msg = ioeGetErrorString e
        emsg = (noPosition, EDirCreateFailure dname io_msg)
    in  bsError errh [emsg]

fileHandleError :: ErrorHandle -> MsgContext -> Position ->
                   CE.IOException -> IO a
fileHandleError errh ctx pos e =
    let io_msg = ioeGetErrorString e
        emsg = (pos, EFileHandleFailure io_msg)
    in  bsErrorWithContext errh ctx [emsg]


-- =====

maxBufferSize :: [Handle] -> IO Int
maxBufferSize hdls = do
   bufModes <- mapM hGetBuffering hdls
   let sizes = map modeSize bufModes
   return (foldl' max 1 sizes)
 where modeSize NoBuffering               = 1
       modeSize LineBuffering             = 80
       modeSize (BlockBuffering (Just n)) = n
       -- we'll guess if the buffer size is implementation-dependent
       modeSize (BlockBuffering Nothing)  = 8192

-- write more than one handle in parallel
-- optimized so that the string can be
-- garbage-collected as it is consumed
putStrHandles :: [Handle] -> String -> IO ()
putStrHandles hdls str = do
  size <- maxBufferSize hdls
  putStrHandles' size hdls str

putStrHandles' size hdls str = loop str
  where loop []  = return ()
        loop str = do
          let (front, rest) = splitAt size str
          mapM_ (\h -> hPutStr h front) hdls
          loop rest
