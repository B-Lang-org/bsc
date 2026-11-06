{-# LANGUAGE CPP, ForeignFunctionInterface, ScopedTypeVariables #-}

-- Optional Tcl initialization for callers outside the Bluetcl executable.
-- Loading is deferred until 'withTcl' is called, so ordinary compiler tools
-- acquire no Tcl dependency. The library stays loaded for the process lifetime.
module HTclRuntime (withTcl, evalTcl) where

import Control.Concurrent
    (MVar, forkOS, isCurrentThreadBound, modifyMVar, newEmptyMVar, newMVar, putMVar,
     rtsSupportsBoundThreads, takeMVar, throwTo)
import Control.Exception
    (IOException, SomeException, catch, finally, mask, mask_, onException, throwIO, try,
     uninterruptibleMask_)
import Control.Monad (unless, void, when)
import Data.Char (chr, ord)
import Data.IORef (newIORef, readIORef, writeIORef)
import Foreign.C.String (CString, withCString)
import Foreign.C.Types (CChar, CInt(..))
#ifdef TCL9
import Foreign.C.Types (CPtrdiff(..))
#else
import Foreign.C.Types (CUShort)
#endif
import Foreign.Marshal.Alloc (alloca, allocaBytes)
import Foreign.Marshal.Array (peekArray)
import Foreign.Ptr (FunPtr, Ptr, nullPtr, plusPtr)
import Foreign.Storable (peek, pokeByteOff)
import System.Environment (getExecutablePath)
import System.IO.Unsafe (unsafePerformIO)
import System.Posix.DynamicLinker (DL, RTLDFlags(..), dlopen, dlsym)

import HTcl (TclInterp, htclReleaseObjs, withTclCallbacks)

#ifdef TCL9
type TclSize = CPtrdiff
type TclChar = CInt
type FindResult = CString
#else
type TclSize = CInt
type TclChar = CUShort
type FindResult = ()
#endif

data Runtime = Runtime
    { _library :: DL
    , createInterp :: IO TclInterp
    , initInterp :: TclInterp -> IO CInt
    , deleteInterp :: TclInterp -> IO ()
    , evalEx :: TclInterp -> CString -> TclSize -> CInt -> IO CInt
    , getObjResult :: TclInterp -> IO (Ptr ())
    , getUnicode :: Ptr () -> Ptr TclSize -> IO (Ptr TclChar)
    , charToUtf :: CInt -> CString -> IO TclSize
    , finalizeThread :: IO ()
    }

-- Evaluation, initialization and deletion can invoke Haskell Tcl callbacks.
foreign import ccall safe "dynamic"
    callFindExecutable :: FunPtr (CString -> IO FindResult) -> CString -> IO FindResult
foreign import ccall safe "dynamic"
    callCreateInterp :: FunPtr (IO TclInterp) -> IO TclInterp
foreign import ccall safe "dynamic"
    callInitInterp :: FunPtr (TclInterp -> IO CInt) -> TclInterp -> IO CInt
foreign import ccall safe "dynamic"
    callDeleteInterp :: FunPtr (TclInterp -> IO ()) -> TclInterp -> IO ()
foreign import ccall safe "dynamic"
    callFinalizeThread :: FunPtr (IO ()) -> IO ()
foreign import ccall safe "dynamic"
    callEvalEx :: FunPtr (TclInterp -> CString -> TclSize -> CInt -> IO CInt)
               -> TclInterp -> CString -> TclSize -> CInt -> IO CInt
foreign import ccall unsafe "dynamic"
    callGetObjResult :: FunPtr (TclInterp -> IO (Ptr ())) -> TclInterp -> IO (Ptr ())
foreign import ccall unsafe "dynamic"
    callGetUnicode :: FunPtr (Ptr () -> Ptr TclSize -> IO (Ptr TclChar))
                   -> Ptr () -> Ptr TclSize -> IO (Ptr TclChar)
foreign import ccall unsafe "dynamic"
    callCharToUtf :: FunPtr (CInt -> CString -> IO TclSize)
                  -> CInt -> CString -> IO TclSize

{-# NOINLINE runtimeCache #-}
runtimeCache :: MVar (Maybe Runtime)
runtimeCache = unsafePerformIO (newMVar Nothing)

getRuntime :: IO Runtime
getRuntime = mask_ $ modifyMVar runtimeCache $ \cached ->
    case cached of
        Just runtime -> pure (cached, runtime)
        Nothing -> do
            library <- openLibrary libraryNames []
            findExecutable <- callFindExecutable <$> dlsym library "Tcl_FindExecutable"
            runtime <- Runtime library
                <$> (callCreateInterp <$> dlsym library "Tcl_CreateInterp")
                <*> (callInitInterp <$> dlsym library "Tcl_Init")
                <*> (callDeleteInterp <$> dlsym library "Tcl_DeleteInterp")
                <*> (callEvalEx <$> dlsym library "Tcl_EvalEx")
                <*> (callGetObjResult <$> dlsym library "Tcl_GetObjResult")
                <*> (callGetUnicode <$> dlsym library "Tcl_GetUnicodeFromObj")
                <*> (callCharToUtf <$> dlsym library "Tcl_UniCharToUtf")
                <*> (callFinalizeThread <$> dlsym library "Tcl_FinalizeThread")
            executable <- getExecutablePath
            void (withCString executable findExecutable)
            pure (Just runtime, runtime)
  where
    openLibrary [] errors = throwIO . userError $
        "Cannot load Tcl " ++ tclVersion ++ ":\n" ++ unlines (reverse errors)
    openLibrary (name:names) errors = do
        result <- try (dlopen name [RTLD_NOW, RTLD_GLOBAL]) :: IO (Either IOException DL)
        case result of
            Right library -> pure library
            Left err -> openLibrary names ((name ++ ": " ++ show err) : errors)

tclVersion :: String
#if defined(TCL9)
tclVersion = "9.0"
#elif defined(TCL85)
tclVersion = "8.5"
#else
tclVersion = "8.6"
#endif

libraryNames :: [FilePath]
#ifdef darwin_HOST_OS
-- Match platform.sh: use Apple's Tcl, rather than a Homebrew installation.
libraryNames = [ "/usr/lib/libtcl" ++ tclVersion ++ ".dylib"
               , "/System/Library/Frameworks/Tcl.framework/Versions/" ++ tclVersion ++ "/Tcl"
               ]
#else
libraryNames = ["libtcl" ++ version ++ ".so" | version <- [tclVersion, filter (/= '.') tclVersion]]
#endif

-- Create and initialize an interpreter, and delete it even if the callback
-- throws. The callback runs on one bound OS thread. Do not return the
-- interpreter or Tcl objects from it, or use them from a forked thread, and
-- run one interpreter at a time: released Tcl objects are queued for
-- whichever interpreter's thread runs next (HTcl.htclReleaseObjs).
-- Other interpreters remain valid: this never calls Tcl_Finalize.
withTcl :: (TclInterp -> IO a) -> IO a
withTcl action = do
    runtime <- getRuntime
    inBoundThread (finalizeThread runtime) $ mask $ \restore -> do
        needsDelete <- newIORef True
        interp <- createInterp runtime
        when (interp == nullPtr) $ throwIO (userError "Tcl_CreateInterp failed")
        let delete = do
                writeIORef needsDelete False
                htclReleaseObjs
                -- what the session wrote to Tcl's channels leaves with it
                _ <- try (evalTcl interp "catch {flush stdout}; catch {flush stderr}")
                    :: IO (Either SomeException String)
                deleteInterp runtime interp
            work = do
                status <- initInterp runtime interp
                unless (status == 0) $ tclError runtime interp "Tcl_Init" status
                action interp
            cleanup = readIORef needsDelete >>= flip when delete
        -- Tcl's deletion callbacks still need their Haskell function pointers.
        -- The outer handler also covers failure to acquire the callback scope.
        withTclCallbacks interp (restore work `finally` delete)
            `onException` cleanup

-- Like 'runInBoundThread', but an asynchronous exception to the waiting
-- caller (Ctrl-C, 'System.Timeout.timeout', 'killThread') is passed on to
-- the bound thread, as 'runInUnboundThread' does in the other direction;
-- that thread receives it once any Tcl call in progress returns.  Once the
-- thread has finished, the last exception the caller received is raised
-- here, whatever the action's own outcome was, as an exception that
-- interrupts a plain 'takeMVar' would be.  The epilogue runs on the thread
-- made here after the action, to release what Tcl keeps per thread.  A
-- caller already on a bound thread, or the one thread of a program without
-- -threaded, runs the action in place and keeps its own thread's state.
inBoundThread :: IO () -> IO a -> IO a
inBoundThread epilogue action = do
    bound <- isCurrentThreadBound
    if bound || not rtsSupportsBoundThreads then action else do
        result <- newEmptyMVar
        mask $ \restore -> do
            -- forkOS waits for the new OS thread to report, an interruptible
            -- point: an exception there would leave the thread running the
            -- action with nobody to forward to or wait for it.
            worker <- uninterruptibleMask_ $
                forkOS (try (restore action `finally` epilogue) >>= putMVar result)
            -- The handler runs masked; throwTo and takeMVar are the points
            -- where another exception can still arrive, and it then takes
            -- over from the one being forwarded.
            let relay (e :: SomeException) = do
                    again <- try (throwTo worker e >> takeMVar result)
                    case again of
                        Left (e' :: SomeException) -> relay e'
                        Right _ -> throwIO e
            outcome <- takeMVar result `catch` relay
            either (\(e :: SomeException) -> throwIO e) pure outcome

-- Evaluate Tcl within the callback passed to 'withTcl'. Tcl failures become
-- IO exceptions containing the interpreter's error message. Strings use Tcl's
-- own UTF encoding; embedded NULs and non-BMP characters are preserved.
evalTcl :: TclInterp -> String -> IO String
evalTcl interp script = do
    runtime <- getRuntime
    withScript runtime script $ \bytes count -> do
        status <- evalEx runtime interp bytes count 0
        htclReleaseObjs
        unless (status == 0) $ tclError runtime interp "Tcl_EvalEx" status
        resultString runtime interp

tclError :: Runtime -> TclInterp -> String -> CInt -> IO a
tclError runtime interp operation status = do
    message <- resultString runtime interp
    throwIO (userError (operation ++ " (status " ++ show status ++ "): " ++ message))

resultString :: Runtime -> TclInterp -> IO String
resultString runtime interp = alloca $ \lengthPtr -> do
    object <- getObjResult runtime interp
    chars <- getUnicode runtime object lengthPtr
    count <- peek lengthPtr
    when (count < 0 || toInteger count > toInteger (maxBound :: Int)) $
        throwIO (userError "Tcl result is too large")
    decodeChars <$> peekArray (fromIntegral count) chars

-- Tcl 8 uses UTF-16 code units and a modified UTF-8 representation; Tcl 9
-- uses full Unicode code points. Let Tcl encode both, including its NUL form.
withScript :: Runtime -> String -> (CString -> TclSize -> IO a) -> IO a
withScript runtime script action = do
    let units = encodeChars script
        count = length units
        limit = min (toInteger (maxBound :: Int)) (toInteger (maxBound :: TclSize))
    when (toInteger count > (limit - 1) `div` 6) $
        throwIO (userError "Tcl script is too large")
    allocaBytes (6 * count + 1) $ \buffer -> do
        let fill offset [] = pure offset
            fill offset (c:cs) = do
                written <- charToUtf runtime c (buffer `plusPtr` offset)
                fill (offset + fromIntegral written) cs
        written <- fill 0 units
        pokeByteOff buffer written (0 :: CChar)
        action buffer (fromIntegral written)

encodeChars :: String -> [CInt]
decodeChars :: [TclChar] -> String
#ifdef TCL9
encodeChars = map (fromIntegral . ord)
decodeChars = map (chr . fromIntegral)
#else
encodeChars = concatMap encode
  where
    encode c
        | n <= 0xffff = [fromIntegral n]
        | otherwise = map fromIntegral [0xd800 + (n - 0x10000) `div` 0x400,
                                        0xdc00 + (n - 0x10000) `mod` 0x400]
      where n = ord c
decodeChars = decode . map fromIntegral
  where
    decode (hi:lo:rest)
        | hi >= 0xd800 && hi <= 0xdbff && lo >= 0xdc00 && lo <= 0xdfff =
            chr (0x10000 + (hi - 0xd800) * 0x400 + lo - 0xdc00) : decode rest
    decode (c:rest) = chr c : decode rest
    decode [] = []
#endif
