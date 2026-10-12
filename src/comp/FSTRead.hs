{-# LANGUAGE ForeignFunctionInterface #-}
module FSTRead(readFST) where

-- Read an FST waveform file into the VCD command representation:
-- the hierarchy as Scope/UpScope/Var commands, the timescale, and the
-- value changes as Timestamp/Change commands.  This lets tools built
-- on the VCD representation (the WaveCheck engine behind vcdcheck
-- and fstcheck) work on FST files.
--
-- The FST reading is done by libfst (the src/vendor/libfst
-- submodule), which is compiled into the executable; fstscopes_hier.c
-- provides flat accessors for libfst's fstHier record, which contains
-- a union that the FFI cannot express.
--
-- libfst delivers value changes through a callback, so the change
-- stream is materialized in memory (unlike VCD text, which is parsed
-- lazily); this reader is suited to testsuite-sized files.

import VCD

import Data.IORef
import Data.Word(Word32, Word64)
import Foreign.Ptr
import Foreign.C.Types
import Foreign.C.String

data FstReader
data FstHier

foreign import ccall unsafe "fstReaderOpen"
    fstReaderOpen :: CString -> IO (Ptr FstReader)
foreign import ccall unsafe "fstReaderClose"
    fstReaderClose :: Ptr FstReader -> IO ()
foreign import ccall unsafe "fstReaderIterateHier"
    fstReaderIterateHier :: Ptr FstReader -> IO (Ptr FstHier)
foreign import ccall unsafe "fstReaderGetTimescale"
    fstReaderGetTimescale :: Ptr FstReader -> IO CSChar
foreign import ccall unsafe "fstReaderSetFacProcessMaskAll"
    fstReaderSetFacProcessMaskAll :: Ptr FstReader -> IO ()

-- The value-change callback: (user data, time, handle, value chars)
type ValueCB = Ptr () -> Word64 -> Word32 -> Ptr CChar -> IO ()

foreign import ccall "wrapper"
    mkValueCB :: ValueCB -> IO (FunPtr ValueCB)

-- Value-change iteration is callback-driven (the last argument is an
-- optional FILE* for fstapi's own VCD regeneration, unused here)
foreign import ccall "fstReaderIterBlocks"
    fstReaderIterBlocks :: Ptr FstReader -> FunPtr ValueCB -> Ptr ()
                        -> Ptr () -> IO CInt

-- flat accessors from fstscopes_hier.c
foreign import ccall unsafe "bsc_fsthier_kind"
    hierKind :: Ptr FstHier -> IO CInt
foreign import ccall unsafe "bsc_fsthier_scope_name"
    hierScopeName :: Ptr FstHier -> IO CString
foreign import ccall unsafe "bsc_fsthier_var_name"
    hierVarName :: Ptr FstHier -> IO CString
foreign import ccall unsafe "bsc_fsthier_var_length"
    hierVarLength :: Ptr FstHier -> IO CUInt
foreign import ccall unsafe "bsc_fsthier_var_handle"
    hierVarHandle :: Ptr FstHier -> IO Word32

-- Read an FST file as a list of VCD commands.
-- Returns Nothing if the file cannot be opened.
readFST :: FilePath -> IO (Maybe VCD)
readFST fname = do
  ctx <- withCString fname fstReaderOpen
  if (ctx == nullPtr)
    then return Nothing
    else do ts <- getTimescale ctx
            hier <- getHierarchy ctx
            chgs <- getChanges ctx
            fstReaderClose ctx
            return $ Just (ts : hier ++ [EndDefs] ++ chgs)

-- FST stores the timescale as a power-of-ten exponent; the VCD
-- representation is a magnitude (1/10/100) and a positive decade
-- (ns is 9, us is 6, ...)
getTimescale :: Ptr FstReader -> IO VCDCmd
getTimescale ctx = do
  e <- fstReaderGetTimescale ctx
  let ex = toInteger e
      unit_exp = 3 * (ex `div` 3)
      mag = 10 ^ (ex - unit_exp)
  return $ Timescale mag (negate unit_exp)

getHierarchy :: Ptr FstReader -> IO [VCDCmd]
getHierarchy ctx = loop id
  where
    loop acc = do
      h <- fstReaderIterateHier ctx
      if (h == nullPtr)
        then return (acc [])
        else do kind <- hierKind h
                case kind of
                  0 -> do name <- hierScopeName h >>= peekCString
                          loop (acc . (Scope Module name :))
                  1 -> loop (acc . (UpScope :))
                  2 -> do name <- hierVarName h >>= peekCString
                          len <- hierVarLength h
                          handle <- hierVarHandle h
                          let cmd = Var Reg (toInteger len)
                                        (toInteger handle)
                                        (stripRange name)
                          loop (acc . (cmd :))
                  _ -> loop acc

-- Some FST writers append an array range to variable names
-- ("sig [7:0]"); strip it, matching how VCD names are handled
stripRange :: String -> String
stripRange name =
    case (reverse name) of
      (']':rest) -> case (span (/= '[') rest) of
                      (_, '[':' ':base) -> reverse base
                      (_, '[':base)     -> reverse base
                      _                 -> name
      _          -> name

getChanges :: Ptr FstReader -> IO [VCDCmd]
getChanges ctx = do
  accum <- newIORef []
  let record _ t handle valp = do
        val <- peekCString valp
        modifyIORef' accum ((t, toInteger handle, val) :)
  cb <- mkValueCB record
  fstReaderSetFacProcessMaskAll ctx
  _ <- fstReaderIterBlocks ctx cb nullPtr nullPtr
  freeHaskellFunPtr cb
  entries <- readIORef accum
  return $ toCmds Nothing (reverse entries)

-- Convert the (time, handle, value) entries into Timestamp/Change
-- commands; the callback delivers them in time order
toCmds :: Maybe Word64 -> [(Word64, Integer, String)] -> [VCDCmd]
toCmds _ [] = []
toCmds prev ((t, code, val) : rest) =
    let change = Change (code, toValue val)
        cmds   = toCmds (Just t) rest
    in if (prev == Just t)
       then change : cmds
       else Timestamp (toInteger t) : change : cmds

-- FST value strings have one character per bit ('0', '1', 'x', 'z',
-- ...), most-significant bit first, at the declared width; real
-- values arrive as the printed representation of a double
toValue :: String -> VCDValue
toValue [c] | isBitChar c    = Scalar (toBit c)
toValue cs | all isBitChar cs = Vector (map toBit cs)
toValue cs = Real (readDouble cs)
  where readDouble s = case reads s of
                         [(d, "")] -> d
                         _         -> 0

isBitChar :: Char -> Bool
isBitChar c = c `elem` "01xXzZhHlLuUwW-"

toBit :: Char -> VCDBitType
toBit '0' = Logic False
toBit '1' = Logic True
toBit 'z' = Z
toBit 'Z' = Z
toBit _   = X
