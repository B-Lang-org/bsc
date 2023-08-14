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

import Data.List(foldl')
import Data.Maybe(isJust)
import System.IO
import System.Directory
import qualified Control.Exception as CE
import System.IO.Error(ioeGetErrorString)
import Control.Monad(when)
import Control.Exception(handle)
import Data.Word
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.Encoding as TE
import qualified Data.Text.Encoding.Error as TEE
import qualified Data.ByteString.Lazy as B

import Util(concatMapM, mapFst)
import FileNameUtil(dirName, getRelativeFilePath)
import FStringCompat

import Position
import Error(ErrMsg(..), ErrorHandle, MsgContext, emptyContext,
             bsError, bsErrorWithContext, bsWarning)

catchIO :: IO a -> (CE.IOException -> IO a) -> IO a
catchIO = CE.catch

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
    readFilesPath' errh pos verb [name] path >>= mapM (decodeUtf8orError errh name)

readBinFilePath :: ErrorHandle -> Position ->
                   Bool -> String -> [String] -> IO (Maybe ([Word8], String))
readBinFilePath errh pos verb name path =
    readFilesPath' errh pos verb [name] path >>= return . mapFst B.unpack

-- for this variant, the file name can have an absolute path
readFilePathOrAbs :: ErrorHandle -> Position ->
                     Bool -> String -> [String] -> IO (Maybe (String, String))
readFilePathOrAbs errh pos verb name@('/':_) _ = do
    -- it's an absolute filename, so just try to read it
    exists <- doesFileExist name
    if (not exists)
      then return Nothing
      else readFilePath_tryFile errh pos verb name >>= mapM (decodeUtf8orError errh name)
readFilePathOrAbs errh pos verb name path =
    -- relative file name, so search each directory in the path
    readFilesPath' errh pos verb [name] path >>= mapM (decodeUtf8orError errh name)

-- look for multiple file names
-- (the first name is searched first in all paths, then the second name, etc)
readFilesPath :: ErrorHandle -> Position ->
                 Bool -> [String] -> [String] -> IO (Maybe (String, String))
readFilesPath errh pos verb names path =
    readFilesPath' errh pos verb names path >>= mapM decode
  where decode (bs, name) = decodeUtf8orError errh name (bs, name)

decodeUtf8orError :: ErrorHandle -> FilePath -> (B.ByteString, String) -> IO (String, String)
decodeUtf8orError errh fn (bs, name) = handle handleErr $ pure (T.unpack $ TE.decodeUtf8With TEE.strictDecode bs, name)
    where handleErr :: TEE.UnicodeException  -> IO a
          handleErr _ = bsError errh [(filePosition $ mkFString fn, ENotUTF8)]

-- Use one of the above entry points.  This is the internal function.
readFilesPath' :: ErrorHandle -> Position ->
                  Bool -> [String] -> [String] ->
                  IO (Maybe (B.ByteString, String))
readFilesPath' errh pos verb names [] = return Nothing
readFilesPath' errh pos verb names path = do
    found_files <- concatMapM (flip existsFilePath path) names
    case found_files of
      [] -> return Nothing
      [file] -> readFilePath_tryFile errh pos verb file
      _ -> do
          -- find the first file that can be read
          let findFn [] = return Nothing
              findFn (f:fs) = do
                  mfile <- readFilePath_tryFile errh pos verb f
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
                        Bool -> String -> IO (Maybe (B.ByteString, String))
readFilePath_tryFile errh pos verb name =
    let
        handler :: CE.IOException -> IO (Maybe (B.ByteString, String))
        handler ioe = do let io_msg = ioeGetErrorString ioe
                         existsButUnreadableWarning errh pos name io_msg
                         return Nothing

        rdFile = do file <- B.readFile name
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

readFileCompat :: FilePath -> IO String
readFileCompat fname = do hdl <- openFile fname ReadMode
                          hSetEncoding hdl utf8
                          hGetContents hdl

writeFileCompat :: FilePath -> String -> IO ()
writeFileCompat fname txt =
    withFile fname WriteMode (\hdl -> do hSetEncoding hdl utf8
                                         hPutStr hdl txt)

appendFileCompat :: FilePath -> String -> IO ()
appendFileCompat fname txt =
    withFile fname AppendMode (\hdl -> do hSetEncoding hdl utf8
                                          hPutStr hdl txt)

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
readBinaryFileMaybe :: FilePath -> IO (Maybe [Word8])
readBinaryFileMaybe fname =
    let
        handler :: CE.IOException -> IO (Maybe [Word8])
        handler ioe = return Nothing

        rdFile = do  file <- B.unpack <$> B.readFile fname
                     return (Just file)
    in
        catchIO rdFile handler

-- This produces an error if the read is unsuccessful,
-- for callers which expect the file to be there
readBinaryFileCatch :: ErrorHandle -> Position -> FilePath -> IO [Word8]
readBinaryFileCatch errh pos fname =
    catchIO (B.unpack <$> B.readFile fname) (fileReadError errh emptyContext pos fname)

-- If the file writing fails, a BSC error message is reported
writeFileCatch :: ErrorHandle -> FilePath -> String -> IO ()
writeFileCatch errh fname content = do
    -- check if the directory exists, and report an error if not
    checkDirectory fname (fileWriteError errh emptyContext noPosition fname)
    -- try to write the file
    catchIO (writeFileCompat fname content)
            (fileWriteError errh emptyContext noPosition fname)

writeBinaryFileCatch :: ErrorHandle -> FilePath -> [Word8] -> IO ()
writeBinaryFileCatch errh fname content = do
    -- check if the directory exists, and report an error if not
    checkDirectory fname (fileWriteError errh emptyContext noPosition fname)
    -- try to write the file
    catchIO (B.writeFile fname $ B.pack content)
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

putStrHandles' :: Int -> [Handle] -> String -> IO ()
putStrHandles' size hdls str = loop str
  where loop []  = return ()
        loop str = do
          let (front, rest) = splitAt size str
          mapM_ (`hPutStr` front) hdls
          loop rest
