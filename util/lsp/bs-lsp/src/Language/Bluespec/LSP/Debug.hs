{-# LANGUAGE ScopedTypeVariables #-}

-- | Debug logging for bs-lsp: tees all LSP JSON-RPC traffic to a log file.
--
-- Activated by the @BS_LSP_DEBUG@ environment variable (set to a path,
-- or to @1@ / empty to use the default @\/tmp\/bs-lsp-debug.log@).
--
-- Each line in the log looks like:
--
-- > [2026-03-15T10:30:00] --> {"jsonrpc":"2.0","id":1,"method":"textDocument/hover",...}
-- > [2026-03-15T10:30:00] <-- {"jsonrpc":"2.0","id":1,"result":null}
--
-- @-->@ = VS Code → server (incoming),  @\<--@ = server → VS Code (outgoing).
module Language.Bluespec.LSP.Debug
  ( withDebugLogging,
  )
where

import Control.Concurrent (forkIO)
import Control.Exception (SomeException, catch)
import Control.Monad (void)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as BSC
import Data.Time (UTCTime, defaultTimeLocale, formatTime, getCurrentTime)
import System.IO (BufferMode (..), Handle, IOMode (..), hFlush, hIsEOF,
                  hPutStrLn, hSetBinaryMode, hSetBuffering, hSetEncoding,
                  openFile, stdin, stdout, utf8)
import System.Posix.IO (createPipe, fdToHandle)

-- | Default path used when @BS_LSP_DEBUG@ is set to @1@ or empty.
defaultLogPath :: FilePath
defaultLogPath = "/tmp/bs-lsp-debug.log"

-- | Open a debug log at @logPath@ and tee all LSP traffic through it.
--
-- The action receives tee'd @(stdinHandle, stdoutHandle)@ to pass to
-- 'Language.LSP.Server.runServerWithHandles' instead of the real
-- 'stdin'\/'stdout'.
withDebugLogging :: FilePath -> (Handle -> Handle -> IO a) -> IO a
withDebugLogging rawPath action = do
  let path = if null rawPath then defaultLogPath else rawPath
  logH <- openFile path AppendMode
  hSetEncoding logH utf8
  hSetBuffering logH LineBuffering

  t <- getCurrentTime
  hPutStrLn logH (replicate 72 '=')
  hPutStrLn logH ("bs-lsp debug session started at " ++ fmtTime t)
  hPutStrLn logH (replicate 72 '=')
  hFlush logH

  -- Raw binary I/O on the real terminal handles
  hSetBinaryMode stdin True
  hSetBinaryMode stdout True

  -- Pipe: real-stdin → [tee thread] → stdinWrite → (server reads stdinRead)
  (stdinReadFd, stdinWriteFd) <- createPipe
  stdinRead  <- fdToHandle stdinReadFd
  stdinWrite <- fdToHandle stdinWriteFd
  hSetBinaryMode stdinRead True
  hSetBinaryMode stdinWrite True
  hSetBuffering stdinRead NoBuffering
  hSetBuffering stdinWrite NoBuffering

  -- Pipe: (server writes stdoutWrite) → stdoutRead → [tee thread] → real-stdout
  (stdoutReadFd, stdoutWriteFd) <- createPipe
  stdoutRead  <- fdToHandle stdoutReadFd
  stdoutWrite <- fdToHandle stdoutWriteFd
  hSetBinaryMode stdoutRead True
  hSetBinaryMode stdoutWrite True
  hSetBuffering stdoutRead NoBuffering
  hSetBuffering stdoutWrite NoBuffering

  -- Incoming: VS Code → server
  void $
    forkIO $
      pumpMessages stdin stdinWrite logH "-->"
        `catch` \(e :: SomeException) ->
          logLine logH "**" ("stdin pump died: " ++ show e)

  -- Outgoing: server → VS Code
  void $
    forkIO $
      pumpMessages stdoutRead stdout logH "<--"
        `catch` \(e :: SomeException) ->
          logLine logH "**" ("stdout pump died: " ++ show e)

  action stdinRead stdoutWrite

-- ---------------------------------------------------------------------------
-- Internal helpers
-- ---------------------------------------------------------------------------

-- | Read complete LSP messages from @src@, log them, and forward to @dst@.
pumpMessages :: Handle -> Handle -> Handle -> String -> IO ()
pumpMessages src dst logH dir = go
  where
    go = do
      mMsg <- readLspMessage src
      case mMsg of
        Nothing -> logLine logH dir "<stream closed>"
        Just (hdr, body) -> do
          logLine logH dir (summarizeBody body)
          BS.hPut dst hdr
          BS.hPut dst body
          hFlush dst
          go

-- | Summarize a message body for logging.
-- Large bodies (file content in didOpen/didChange) are truncated so the
-- log stays readable.  The body forwarded to the server is always intact.
summarizeBody :: ByteString -> String
summarizeBody body
  | BSC.length body <= maxLogBytes = BSC.unpack body
  | otherwise =
      BSC.unpack (BSC.take maxLogBytes body)
        ++ "...[" ++ show (BSC.length body) ++ " bytes total, truncated]"
  where
    maxLogBytes = 2048

-- | Read one complete LSP message: @(header_bytes_including_separator, body)@.
-- Returns 'Nothing' on EOF or a malformed\/missing @Content-Length@ header.
readLspMessage :: Handle -> IO (Maybe (ByteString, ByteString))
readLspMessage h = do
  mHdr <- readUntilSeparator h
  case mHdr of
    Nothing -> return Nothing
    Just hdr -> case parseContentLength hdr of
      Nothing -> return Nothing
      Just n -> do
        body <- BS.hGet h n
        return (Just (hdr, body))

-- | Read bytes from @h@ until the @\\r\\n\\r\\n@ header\/body separator
-- (inclusive), returning all bytes including the separator.
-- Returns 'Nothing' on EOF before the separator is found.
readUntilSeparator :: Handle -> IO (Maybe ByteString)
readUntilSeparator h = go BS.empty
  where
    sep = BSC.pack "\r\n\r\n"
    go acc = do
      eof <- hIsEOF h `catch` \(_ :: SomeException) -> return True
      if eof
        then return Nothing
        else do
          b <- BS.hGet h 1
          let acc' = acc <> b
          if BSC.isSuffixOf sep acc'
            then return (Just acc')
            else go acc'

-- | Extract the numeric payload size from raw header bytes.
parseContentLength :: ByteString -> Maybe Int
parseContentLength hdr =
  let ls = BSC.lines hdr
      prefix = BSC.pack "Content-Length:"
      matches = filter (BSC.isPrefixOf prefix) ls
   in case matches of
        [] -> Nothing
        (l : _) ->
          let rest = BSC.drop (BSC.length prefix) l
              trimmed = BSC.dropWhile (\c -> c == ' ' || c == '\r' || c == '\n') rest
           in case BSC.readInt trimmed of
                Just (n, _) -> Just n
                Nothing -> Nothing

-- | Write a timestamped entry to the debug log.
logLine :: Handle -> String -> String -> IO ()
logLine logH dir msg = do
  t <- getCurrentTime
  hPutStrLn logH ("[" ++ fmtTime t ++ "] " ++ dir ++ " " ++ msg)
  hFlush logH

fmtTime :: UTCTime -> String
fmtTime = formatTime defaultTimeLocale "%Y-%m-%dT%H:%M:%S"
