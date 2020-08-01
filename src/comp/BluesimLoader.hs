{-# LANGUAGE ForeignFunctionInterface, ScopedTypeVariables, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
module BluesimLoader ( BluesimModel(..)
                     , loadBluesimModel
                     , unloadBluesimModel
                     , BSClock, bad_clock_handle
                     , BSClockValue(..)
                     , BSValue(..)
                     , BSEdgeDirection(..)
                     , BSTime
                     , BSStatus(..)
                     , BSSymbol, BSIndex, bad_symbol
                     , getClockInfo
                     , setActiveClock
                     , getCurDirStr
                     , getCurDirSym
                     ) where

-- This module allows dynamically loading a Bluesim shared object
-- into a Haskell program, and exposes the API of the model as a
-- BluesimModel structure.

import FileNameUtil(dirName,baseName)
import ErrorUtil(internalError)
import HTcl
import SimCCBlock(pfxModel)

import System.Posix.DynamicLinker
import Data.Bits
import Data.List(intercalate, isPrefixOf)
import Data.Int
import Data.Word
import Data.Time.Clock
import Data.Time.Clock.POSIX
import Foreign.C
import Foreign.Ptr
import Foreign.Storable
import Foreign.Marshal
import Numeric(showHex)

-- import Debug.Trace

-- Some Haskell versions of Bluesim kernel types and constants

type BSClock = Word32

bad_clock_handle :: BSClock
bad_clock_handle = complement 0

data BSClockValue = CLK_LOW | CLK_HIGH
  deriving (Eq,Show)

data BSEdgeDirection = NEGEDGE | POSEDGE
  deriving (Eq,Show)

type BSTime = Word64

data BSStatus = OK | Error Int32
  deriving (Eq)

type BSSymbol = WordPtr
type BSIndex  = Word64

bad_symbol :: BSSymbol
bad_symbol = ptrToWordPtr (nullPtr)

data BSValue = Value { num_bits :: !Word32, value :: !Integer }
             | NoValue
  deriving (Eq)

instance Show BSValue where
  show NoValue = "**NOVALUE**"
  show v = (show (num_bits v)) ++ "'h" ++ (showHex (value v) "")

read_value :: CUInt -> Ptr CUInt -> IO Integer
read_value bits ptr =
    do let uint_bytes = sizeOf (undefined :: CUInt)
           uint_bits  = 8 * uint_bytes
           num_uints  = ((fromIntegral bits) + uint_bits - 1) `quot` uint_bits
           offs = [0..(num_uints-1)]
           get_piece n = do { x <- peekElemOff ptr n; return (toInteger x) }
       vals <- mapM get_piece offs
       let i = foldl (.|.) 0 (zipWith shiftL vals [0,uint_bits..])
           mask = (1 `shiftL` (fromIntegral bits)) - 1
       return (i .&. mask)

data BSSymTag = SYM_UNKNOWN | SYM_MODULE   | SYM_DEF
              | SYM_PARAM   | SYM_PORT     | SYM_RULE
              | SYM_RANGE   | SYM_COMPUTED
  deriving (Eq)

instance Show BSSymTag where
  show SYM_UNKNOWN  = "?"
  show SYM_MODULE   = "module"
  show SYM_DEF      = "signal"
  show SYM_PARAM    = "parameter"
  show SYM_PORT     = "port"
  show SYM_RULE     = "rule"
  show SYM_RANGE    = "array"
  show SYM_COMPUTED = "value"

instance Read BSSymTag where
  readsPrec _ x
      | "module" `isPrefixOf` x    = [(SYM_MODULE,drop 6 x)]
      | "signal" `isPrefixOf` x    = [(SYM_DEF,drop 6 x)]
      | "parameter" `isPrefixOf` x = [(SYM_PARAM,drop 9 x)]
      | "port" `isPrefixOf` x      = [(SYM_PORT,drop 4 x)]
      | "rule" `isPrefixOf` x      = [(SYM_RULE,drop 4 x)]
      | "array" `isPrefixOf` x     = [(SYM_RANGE,drop 5 x)]
      | "value" `isPrefixOf` x     = [(SYM_COMPUTED,drop 5 x)]
      | "?" `isPrefixOf` x         = [(SYM_UNKNOWN,drop 1 x)]
      | otherwise                  = []

instance  TclObjCvt BSClockValue where
    toTclObj v = toTclObj (v == CLK_HIGH)

instance  TclObjCvt BSValue where
    toTclObj v = toTclObj (show v)

instance  TclObjCvt BSSymTag where
    toTclObj t = toTclObj (show t)

-- Some useful constants for working with C types

type C_tBool          = CUChar
type C_tClock         = CUInt
type C_tClockValue    = CInt
type C_tEdgeDirection = CInt
type C_tTime          = CULLong
type C_tStatus        = CInt
type C_tSymTag        = CUChar

-- Utilities for working with C structures

field :: (Storable a) => a -> (Int,Int)
field x = (sizeOf x, alignment x)

compute_offsets :: [(Int,Int)] -> [Int]
compute_offsets fs = helper nullPtr fs
    where helper _   []         = []
          helper ptr ((s,a):xs) =
              let off = (alignPtr ptr a) `minusPtr` nullPtr
              in off:(helper (ptr `plusPtr` s) xs)

get_ptr :: [Int] -> Int -> Ptr a -> Ptr b
get_ptr offs n ptr = castPtr (ptr `plusPtr` (offs!!n))

fromCString :: CString -> IO String
fromCString cs | cs == nullPtr = return ""
               | otherwise     = peekCString cs

-- Storable definition for CVersionInfo structure

data CVersionInfo = CVersionInfo { cvi_year  :: CUInt
                                 , cvi_month :: CUInt
                                 , cvi_annot :: CString
                                 , cvi_build :: CString
                                 , cvi_time  :: CTime
                                 }
cvi_fields :: [(Int,Int)]
cvi_fields = [ field (undefined :: CUInt)
             , field (undefined :: CUInt)
             , field (undefined :: CString)
             , field (undefined :: CString)
             , field (undefined :: CTime)
             ]

cvi_offsets :: [Int]
cvi_offsets = compute_offsets cvi_fields

instance Storable CVersionInfo where
  sizeOf    _ = (last cvi_offsets) + (fst (last cvi_fields))
  alignment _ = snd (head cvi_fields)
  peek ptr = do yr    <- peek (get_ptr cvi_offsets 0 ptr)
                mth   <- peek (get_ptr cvi_offsets 1 ptr)
                annot <- peek (get_ptr cvi_offsets 2 ptr)
                build <- peek (get_ptr cvi_offsets 3 ptr)
                t     <- peek (get_ptr cvi_offsets 4 ptr)
                return $ CVersionInfo yr mth annot build t
  poke ptr cvi = do poke (get_ptr cvi_offsets 0 ptr) (cvi_year cvi)
                    poke (get_ptr cvi_offsets 1 ptr) (cvi_month cvi)
                    poke (get_ptr cvi_offsets 2 ptr) (cvi_annot cvi)
                    poke (get_ptr cvi_offsets 3 ptr) (cvi_build cvi)
                    poke (get_ptr cvi_offsets 4 ptr) (cvi_time cvi)

-- A typeclass useful for converting values from Haskell to C and back

class AutoC h c where
  toC   :: h -> c
  fromC :: c -> h

instance AutoC Bool C_tBool where
  toC False = 0
  toC True  = 1
  fromC 0 = False
  fromC _ = True

instance AutoC BSStatus C_tStatus where
  toC OK        = 0
  toC (Error n) = toC n
  fromC 0 = OK
  fromC n = Error (fromC n)

instance AutoC Int32 CInt where
  toC   = fromInteger . toInteger
  fromC = fromInteger .toInteger

instance AutoC Word32 CUInt where
  toC   = fromInteger . toInteger
  fromC = fromInteger .toInteger

instance AutoC Word64 CULLong where
  toC   = fromInteger . toInteger
  fromC = fromInteger . toInteger

instance (AutoC a c, AutoC b d) => AutoC (a -> b) (c -> d) where
  toC   f = toC . f . fromC
  fromC f = fromC . f . toC

instance AutoC BSClockValue C_tClockValue where
  toC CLK_LOW = 0
  toC CLK_HIGH = 1
  fromC 0 = CLK_LOW
  fromC 1 = CLK_HIGH
  fromC n = internalError $ "BSClockValue.fromC: invalid enum value: " ++ (show n)

instance AutoC BSEdgeDirection C_tEdgeDirection where
  toC NEGEDGE = 0
  toC POSEDGE = 1
  fromC 0 = NEGEDGE
  fromC 1 = POSEDGE
  fromC n = internalError $ "BSEdgeDirection.fromC: invalid enum value: " ++ (show n)

-- this magic came from Simon Marlow
instance AutoC UTCTime CTime where
  toC   t = error "cannot convert from UTCTime to CTime"
  fromC t = posixSecondsToUTCTime (fromRational (toRational t))

-- Note: can't have instance AutoC a a because AutoC (IO h) (IO c) would
-- overlap.

instance AutoC () () where
  toC   = id
  fromC = id

instance AutoC CUInt CUInt where
  toC   = id
  fromC = id

instance AutoC CULLong CULLong where
  toC   = id
  fromC = id

instance AutoC WordPtr (Ptr CUInt) where
  toC   = wordPtrToPtr
  fromC = ptrToWordPtr

instance (AutoC h c) => AutoC (IO h) (IO c) where
  toC   x = x >>= (return . toC)
  fromC x = x >>= (return . fromC)

instance AutoC BSSymTag C_tSymTag where
  toC SYM_UNKNOWN  = 0
  toC SYM_MODULE   = 1
  toC SYM_DEF      = 2
  toC SYM_PARAM    = 3
  toC SYM_PORT     = 4
  toC SYM_RULE     = 5
  toC SYM_RANGE    = 6
  toC SYM_COMPUTED = 7
  fromC 1 = SYM_MODULE
  fromC 2 = SYM_DEF
  fromC 3 = SYM_PARAM
  fromC 4 = SYM_PORT
  fromC 5 = SYM_RULE
  fromC 6 = SYM_RANGE
  fromC 7 = SYM_COMPUTED
  fromC _ = SYM_UNKNOWN

-- FFI routines for importing various kinds of dynamically-loaded C functions

-- returning void
foreign import ccall "dynamic"
  dl_ptr_ret_void :: FunPtr (Ptr CUInt -> IO ()) -> (Ptr CUInt -> IO ())

foreign import ccall "dynamic"
  dl_ptr_str_ret_void :: FunPtr (Ptr CUInt -> CString -> IO ()) ->
                         (Ptr CUInt -> CString -> IO ())

foreign import ccall "dynamic"
  dl_ptr_str_ullong_ret_int :: FunPtr (Ptr CUInt -> CString -> CULLong -> IO CInt) ->
                               (Ptr CUInt -> CString -> CULLong -> IO CInt)

foreign import ccall "dynamic"
  dl_ptr_version_ret_void :: FunPtr (Ptr CUInt -> Ptr CVersionInfo -> IO ()) ->
                             (Ptr CUInt -> Ptr CVersionInfo -> IO ())

-- returning uchar
foreign import ccall "dynamic"
  dl_ptr_ret_uchar :: FunPtr (Ptr CUInt -> IO CUChar) -> (Ptr CUInt -> IO CUChar)

-- returning uint
foreign import ccall "dynamic"
  dl_ptr_uint_ret_uint :: FunPtr (Ptr CUInt -> CUInt -> IO CUInt) ->
                          (Ptr CUInt -> CUInt -> IO CUInt)

foreign import ccall "dynamic"
  dl_ptr_str_ret_uint :: FunPtr (Ptr CUInt -> CString -> IO CUInt) ->
                         (Ptr CUInt -> CString -> IO CUInt)

foreign import ccall "dynamic"
  dl_ptr_ret_uint :: FunPtr (Ptr CUInt -> IO CUInt) -> (Ptr CUInt -> IO CUInt)

-- returning int
foreign import ccall "dynamic"
  dl_ptr_ret_int :: FunPtr (Ptr CUInt -> IO CInt) -> (Ptr CUInt -> IO CInt)

foreign import ccall "dynamic"
  dl_ptr_uchar_ret_int :: FunPtr (Ptr CUInt -> CUChar -> IO CInt) ->
                          (Ptr CUInt -> CUChar -> IO CInt)

foreign import ccall "dynamic"
  dl_ptr_uint_ret_int :: FunPtr (Ptr CUInt -> CUInt -> IO CInt) ->
                         (Ptr CUInt -> CUInt -> IO CInt)

foreign import ccall "dynamic"
  dl_ptr_ullong_ret_int :: FunPtr (Ptr CUInt -> CULLong -> IO CInt) ->
                           (Ptr CUInt -> CULLong -> IO CInt)

foreign import ccall "dynamic"
  dl_ptr_str_ret_int :: FunPtr (Ptr CUInt -> CString -> IO CInt) ->
                        (Ptr CUInt -> CString -> IO CInt)

foreign import ccall "dynamic"
  dl_ptr_uchar_ret_ptr :: FunPtr (Ptr CUInt -> CUChar -> IO (Ptr CUInt)) ->
                          (Ptr CUInt -> CUChar -> IO (Ptr CUInt))

foreign import ccall "dynamic"
  dl_ptr_uint_int_ullong_ret_int :: FunPtr (Ptr CUInt -> CUInt -> CInt -> CULLong -> IO CInt) ->
                                    (Ptr CUInt -> CUInt -> CInt -> CULLong -> IO CInt)

-- returning ullong
foreign import ccall "dynamic"
  dl_ptr_ret_ullong :: FunPtr (Ptr CUInt -> IO CULLong) -> (Ptr CUInt -> IO CULLong)

foreign import ccall "dynamic"
  dl_ptr_uint_ret_ullong :: FunPtr (Ptr CUInt -> CUInt -> IO CULLong) ->
                            (Ptr CUInt -> CUInt -> IO CULLong)

foreign import ccall "dynamic"
  dl_ptr_uint_int_ret_ullong :: FunPtr (Ptr CUInt -> CUInt -> CInt -> IO CULLong) ->
                                (Ptr CUInt -> CUInt -> CInt -> IO CULLong)

-- returning str
foreign import ccall "dynamic"
  dl_ptr_ret_str :: FunPtr (Ptr CUInt -> IO CString) -> (Ptr CUInt -> IO CString)

foreign import ccall "dynamic"
  dl_ptr_uint_ret_str :: FunPtr (Ptr CUInt -> CUInt -> IO CString) -> (Ptr CUInt -> CUInt -> IO CString)

-- returning ptr
foreign import ccall "dynamic"
  dl_ret_ptr :: FunPtr (IO (Ptr CUInt)) -> IO (Ptr CUInt)

foreign import ccall "dynamic"
  dl_ptr_ret_ptr :: FunPtr (Ptr CUInt -> IO (Ptr CUInt)) -> (Ptr CUInt -> IO (Ptr CUInt))

foreign import ccall "dynamic"
  dl_ptr_uint_ret_ptr :: FunPtr (Ptr CUInt -> CUInt -> IO (Ptr CUInt)) ->
                         (Ptr CUInt -> CUInt -> IO (Ptr CUInt))

foreign import ccall "dynamic"
  dl_ptr_ullong_ret_ptr :: FunPtr (Ptr CUInt -> CULLong -> IO (Ptr CUInt)) ->
                           (Ptr CUInt -> CULLong -> IO (Ptr CUInt))

foreign import ccall "dynamic"
  dl_ptr_str_ret_ptr :: FunPtr (Ptr CUInt -> CString -> IO (Ptr CUInt)) ->
                        (Ptr CUInt -> CString -> IO (Ptr CUInt))

-- returning other types
type DefClkFn = Ptr CUInt -> CString -> C_tClockValue -> CUChar -> C_tTime -> C_tTime -> C_tTime -> IO C_tClock
foreign import ccall "dynamic"
  dl_def_clk_fn :: FunPtr DefClkFn -> DefClkFn

-- Definition of the BluesimModel structure
-- The fields of the model represent Bluesim kernel API functions for
-- the model which have been dynamically linked and converted to use
-- normal Haskell types, so that it presents an abstract Haskell view
-- of the Bluesim model.

data BluesimModel =
    BS { model_so               :: DL
       , model_hdl              :: WordPtr
       , sim_hdl                :: WordPtr
       , current_clock          :: BSClock
       , active_vcd_file        :: Maybe String
       , current_directory      :: [BSSymbol]
       , cleanup_handlers       :: [IO ()]
         -- configuration state
       , is_interactive         :: Bool
         -- imported API functions
       , bk_now                 :: IO BSTime
       , bk_set_timescale       :: String -> BSTime -> IO BSStatus
       , bk_version             :: IO (Word32, Word32, String, String, UTCTime)
       , bk_append_argument     :: String -> IO ()
       , bk_define_clock        :: String -> BSClockValue -> Bool -> BSTime -> BSTime -> BSTime -> IO BSClock
       , bk_num_clocks          :: IO Word32
       , bk_get_nth_clock       :: Word32 -> IO BSClock
       , bk_get_clock_by_name   :: String -> IO BSClock
       , bk_clock_name          :: BSClock -> IO String
       , bk_clock_initial_value :: BSClock -> IO BSClockValue
       , bk_clock_first_edge    :: BSClock -> IO BSTime
       , bk_clock_duration      :: BSClock -> BSClockValue -> IO BSTime
       , bk_clock_val           :: BSClock -> IO BSClockValue
       , bk_clock_cycle_count   :: BSClock -> IO Word64
       , bk_clock_edge_count    :: BSClock -> BSEdgeDirection -> IO Word64
       , bk_clock_last_edge     :: BSClock -> IO BSTime
       , bk_quit_after_edge     :: BSClock -> BSEdgeDirection -> Word64 -> IO Int32
       , bk_schedule_ui_event   :: BSTime -> IO BSStatus
       , bk_remove_ui_event     :: BSTime -> IO BSStatus
       , bk_set_interactive     :: IO ()
       , bk_advance             :: Bool -> IO BSStatus
       , bk_is_running          :: IO Bool
       , bk_sync                :: IO BSTime
       , bk_abort_now           :: IO ()
       , bk_finished            :: IO Bool
       , bk_exit_status         :: IO Int32
       , bk_top_symbol          :: IO BSSymbol
       , bk_lookup_symbol       :: BSSymbol -> String -> IO BSSymbol
       , bk_get_key             :: BSSymbol -> IO String
       , bk_is_module           :: BSSymbol -> IO Bool
       , bk_is_rule             :: BSSymbol -> IO Bool
       , bk_is_single_value     :: BSSymbol -> IO Bool
       , bk_is_value_range      :: BSSymbol -> IO Bool
       , bk_peek_symbol_value   :: BSSymbol -> IO BSValue
       , bk_get_range_min_addr  :: BSSymbol -> IO BSIndex
       , bk_get_range_max_addr  :: BSSymbol -> IO BSIndex
       , bk_peek_range_value    :: BSSymbol -> BSIndex -> IO BSValue
       , bk_num_symbols         :: BSSymbol -> IO Word32
       , bk_get_nth_symbol      :: BSSymbol -> Word32 -> IO BSSymbol
       , bk_set_VCD_file        :: String -> IO BSStatus
       , bk_enable_VCD_dumping  :: IO Bool
       , bk_disable_VCD_dumping :: IO ()
       , bk_shutdown            :: IO ()
       }

-- Routine which dynamically loads a Bluesim .so file and creates
-- a BluesimModel value which allows access to the Bluesim object.
-- Returns Nothing if an error occurs during loading

loadBluesimModel :: String -> String -> IO (Maybe BluesimModel)
loadBluesimModel fname top_name = do
  -- load the shared object
  let fname' = (dirName fname) ++ "/" ++ (baseName fname)
  dl <- dlopen fname' [RTLD_NOW]
  -- lookup symbols in the shared object
  c_new_model              <- dlsym dl ("new_" ++ pfxModel ++ top_name)
  c_bk_init                <- dlsym dl "bk_init"
  c_bk_now                 <- dlsym dl "bk_now"
  c_bk_set_timescale       <- dlsym dl "bk_set_timescale"
  c_bk_version             <- dlsym dl "bk_version"
  c_bk_append_argument     <- dlsym dl "bk_append_argument"
  c_bk_define_clock        <- dlsym dl "bk_define_clock"
  c_bk_num_clocks          <- dlsym dl "bk_num_clocks"
  c_bk_get_nth_clock       <- dlsym dl "bk_get_nth_clock"
  c_bk_clock_name          <- dlsym dl "bk_clock_name"
  c_bk_get_clock_by_name   <- dlsym dl "bk_get_clock_by_name"
  c_bk_clock_initial_value <- dlsym dl "bk_clock_initial_value"
  c_bk_clock_first_edge    <- dlsym dl "bk_clock_first_edge"
  c_bk_clock_duration      <- dlsym dl "bk_clock_duration"
  c_bk_clock_val           <- dlsym dl "bk_clock_val"
  c_bk_clock_cycle_count   <- dlsym dl "bk_clock_cycle_count"
  c_bk_clock_edge_count    <- dlsym dl "bk_clock_edge_count"
  c_bk_clock_last_edge     <- dlsym dl "bk_clock_last_edge"
  c_bk_quit_after_edge     <- dlsym dl "bk_quit_after_edge"
  c_bk_schedule_ui_event   <- dlsym dl "bk_schedule_ui_event"
  c_bk_remove_ui_event     <- dlsym dl "bk_remove_ui_event"
  c_bk_set_interactive     <- dlsym dl "bk_set_interactive"
  c_bk_advance             <- dlsym dl "bk_advance"
  c_bk_is_running          <- dlsym dl "bk_is_running"
  c_bk_sync                <- dlsym dl "bk_sync"
  c_bk_abort_now           <- dlsym dl "bk_abort_now"
  c_bk_finished            <- dlsym dl "bk_finished"
  c_bk_exit_status         <- dlsym dl "bk_exit_status"
  c_bk_top_symbol          <- dlsym dl "bk_top_symbol"
  c_bk_lookup_symbol       <- dlsym dl "bk_lookup_symbol"
  c_bk_get_size            <- dlsym dl "bk_get_size"
  c_bk_get_key             <- dlsym dl "bk_get_key"
  c_bk_is_module           <- dlsym dl "bk_is_module"
  c_bk_is_rule             <- dlsym dl "bk_is_rule"
  c_bk_is_single_value     <- dlsym dl "bk_is_single_value"
  c_bk_is_value_range      <- dlsym dl "bk_is_value_range"
  c_bk_peek_symbol_value   <- dlsym dl "bk_peek_symbol_value"
  c_bk_get_range_min_addr  <- dlsym dl "bk_get_range_min_addr"
  c_bk_get_range_max_addr  <- dlsym dl "bk_get_range_max_addr"
  c_bk_peek_range_value    <- dlsym dl "bk_peek_range_value"
  c_bk_num_symbols         <- dlsym dl "bk_num_symbols"
  c_bk_get_nth_symbol      <- dlsym dl "bk_get_nth_symbol"
  c_bk_set_VCD_file        <- dlsym dl "bk_set_VCD_file"
  c_bk_enable_VCD_dumping  <- dlsym dl "bk_enable_VCD_dumping"
  c_bk_disable_VCD_dumping <- dlsym dl "bk_disable_VCD_dumping"
  c_bk_shutdown            <- dlsym dl "bk_shutdown"
  -- convert functions to Haskell types and build BluesimModel
  let new_model :: IO WordPtr
      new_model = fromC $ dl_ret_ptr c_new_model
      bk_init :: WordPtr -> Bool -> IO WordPtr
      bk_init = fromC $ dl_ptr_uchar_ret_ptr c_bk_init
      -- string return must be handled specially for bk_clock_name, etc.
      clk_name_fn :: WordPtr -> BSClock -> IO String
      clk_name_fn simHdl c =
          do cstr <- dl_ptr_uint_ret_str c_bk_clock_name (toC simHdl) (toC c)
             fromCString cstr
      sym_name_fn ptr =
          if (ptr == bad_symbol)
          then return "BAD_SYMBOL"
          else do cstr <- dl_ptr_ret_str c_bk_get_key (toC ptr)
                  fromCString cstr
      -- string argument must be handled specially for bk_define_clock, etc.
      def_clk_fn :: WordPtr -> String -> BSClockValue -> Bool -> BSTime -> BSTime -> BSTime -> IO BSClock
      def_clk_fn simHdl s iv hi st fe ne =
          let fn = dl_def_clk_fn c_bk_define_clock
          in withCString s (\cs -> fromC $ fn (toC simHdl) cs (toC iv) (toC hi) (toC st) (toC fe) (toC ne))
      get_clk_fn :: WordPtr -> String -> IO BSClock
      get_clk_fn simHdl s =
          let fn = dl_ptr_str_ret_uint c_bk_get_clock_by_name
          in withCString s (fromC . fn (toC simHdl))
      set_vcd_fn :: WordPtr -> String -> IO BSStatus
      set_vcd_fn simHdl s =
          let fn = dl_ptr_str_ret_int c_bk_set_VCD_file
          in withCString s (fromC . fn (toC simHdl))
      plusarg_fn :: WordPtr -> String -> IO ()
      plusarg_fn simHdl s =
          let fn = dl_ptr_str_ret_void c_bk_append_argument
          in withCString s (fromC . fn (toC simHdl))
      set_timescale_fn :: WordPtr -> String -> BSTime -> IO BSStatus
      set_timescale_fn simHdl ts_unit ts_factor =
          let fn = dl_ptr_str_ullong_ret_int c_bk_set_timescale
          in withCString ts_unit
               (\cs -> fromC $ fn (toC simHdl) cs (toC ts_factor))
      lookup_fn :: BSSymbol -> String -> IO BSSymbol
      lookup_fn sym s =
          withCString s
            (fromC . dl_ptr_str_ret_ptr c_bk_lookup_symbol (toC sym))
      -- version structure needs full-on Storable support
      version_fn :: WordPtr -> IO (Word32, Word32, String, String, UTCTime)
      version_fn simHdl =
          do let fn = dl_ptr_version_ret_void c_bk_version
             alloca (\ptr -> do fn (toC simHdl) ptr
                                (CVersionInfo yr mth astr bstr t) <- peek ptr
                                annot <- fromCString astr
                                build <- fromCString bstr
                                return (fromC yr, fromC mth, annot, build, fromC t))
      -- bk_peek_symbol_value
      peek_symbol_fn :: BSSymbol -> IO BSValue
      peek_symbol_fn p =
          do let size_fn = dl_ptr_ret_uint c_bk_get_size
                 peek_fn = dl_ptr_ret_ptr c_bk_peek_symbol_value
             sz <- size_fn (toC p)
             vptr <- peek_fn (toC p)
             if (fromC vptr /= bad_symbol)
              then do v <- read_value sz vptr
                      return $ Value { num_bits = (fromC sz), value = v }
              else return NoValue
      -- bk_peek_range_value
      peek_range_fn :: BSSymbol -> BSIndex -> IO BSValue
      peek_range_fn p addr =
          do let size_fn = dl_ptr_ret_uint c_bk_get_size
                 peek_fn = dl_ptr_ullong_ret_ptr c_bk_peek_range_value
             sz <- size_fn (toC p)
             vptr <- peek_fn (toC p) (toC addr)
             if (fromC vptr /= bad_symbol)
              then do v <- read_value sz vptr
                      return $ Value { num_bits = (fromC sz), value = v }
              else return NoValue
  model_hdl <- new_model
  sim_hdl <- bk_init model_hdl True
  if (sim_hdl == ptrToWordPtr nullPtr)
   then return Nothing
   else do
        top_symbol <- (fromC $ dl_ptr_ret_ptr c_bk_top_symbol) sim_hdl
        return $ Just (BS { model_so               = dl
                          , model_hdl              = model_hdl
                          , sim_hdl                = sim_hdl
                          , current_clock          = 0  -- default clock handle
                          , active_vcd_file        = Nothing
                          , current_directory      = [top_symbol]
                          , cleanup_handlers       = []
                          , is_interactive         = False
                          , bk_now                 = (fromC $ dl_ptr_ret_ullong c_bk_now) sim_hdl
                          , bk_set_timescale       = set_timescale_fn sim_hdl
                          , bk_version             = version_fn sim_hdl
                          , bk_append_argument     = plusarg_fn sim_hdl
                          , bk_define_clock        = def_clk_fn sim_hdl
                          , bk_num_clocks          = (fromC $ dl_ptr_ret_uint c_bk_num_clocks) sim_hdl
                          , bk_get_nth_clock       = (fromC $ dl_ptr_uint_ret_uint c_bk_get_nth_clock) sim_hdl
                          , bk_get_clock_by_name   = get_clk_fn sim_hdl
                          , bk_clock_name          = clk_name_fn sim_hdl
                          , bk_clock_initial_value = (fromC $ dl_ptr_uint_ret_int c_bk_clock_initial_value) sim_hdl
                          , bk_clock_first_edge    = (fromC $ dl_ptr_uint_ret_ullong c_bk_clock_first_edge) sim_hdl
                          , bk_clock_duration      = (fromC $ dl_ptr_uint_int_ret_ullong c_bk_clock_duration) sim_hdl
                          , bk_clock_val           = (fromC $ dl_ptr_uint_ret_int c_bk_clock_val) sim_hdl
                          , bk_clock_cycle_count   = (fromC $ dl_ptr_uint_ret_ullong c_bk_clock_cycle_count) sim_hdl
                          , bk_clock_edge_count    = (fromC $ dl_ptr_uint_int_ret_ullong c_bk_clock_edge_count) sim_hdl
                          , bk_clock_last_edge     = (fromC $ dl_ptr_uint_ret_ullong c_bk_clock_last_edge) sim_hdl
                          , bk_quit_after_edge     = (fromC $ dl_ptr_uint_int_ullong_ret_int c_bk_quit_after_edge) sim_hdl
                          , bk_schedule_ui_event   = (fromC $ dl_ptr_ullong_ret_int c_bk_schedule_ui_event) sim_hdl
                          , bk_remove_ui_event     = (fromC $ dl_ptr_ullong_ret_int c_bk_remove_ui_event) sim_hdl
                          , bk_set_interactive     = (fromC $ dl_ptr_ret_void c_bk_set_interactive) sim_hdl
                          , bk_advance             = (fromC $ dl_ptr_uchar_ret_int c_bk_advance) sim_hdl
                          , bk_is_running          = (fromC $ dl_ptr_ret_uchar c_bk_is_running) sim_hdl
                          , bk_sync                = (fromC $ dl_ptr_ret_ullong c_bk_sync) sim_hdl
                          , bk_abort_now           = (fromC $ dl_ptr_ret_void c_bk_abort_now) sim_hdl
                          , bk_finished            = (fromC $ dl_ptr_ret_uchar c_bk_finished) sim_hdl
                          , bk_exit_status         = (fromC $ dl_ptr_ret_int c_bk_exit_status) sim_hdl
                          , bk_top_symbol          = (fromC $ dl_ptr_ret_ptr c_bk_top_symbol) sim_hdl
                          , bk_lookup_symbol       = lookup_fn
                          , bk_get_key             = sym_name_fn
                          , bk_is_module           = (fromC . dl_ptr_ret_uchar c_bk_is_module . toC)
                          , bk_is_rule             = (fromC . dl_ptr_ret_uchar c_bk_is_rule . toC)
                          , bk_is_single_value     = (fromC . dl_ptr_ret_uchar c_bk_is_single_value . toC)
                          , bk_is_value_range      = (fromC . dl_ptr_ret_uchar c_bk_is_value_range . toC)
                          , bk_peek_symbol_value   = peek_symbol_fn
                          , bk_get_range_min_addr  = (fromC . dl_ptr_ret_ullong c_bk_get_range_min_addr . toC)
                          , bk_get_range_max_addr  = (fromC . dl_ptr_ret_ullong c_bk_get_range_max_addr . toC)
                          , bk_peek_range_value    = peek_range_fn
                          , bk_num_symbols         = (fromC . dl_ptr_ret_uint c_bk_num_symbols . toC)
                          , bk_get_nth_symbol      = (fromC . dl_ptr_uint_ret_ptr c_bk_get_nth_symbol . toC)
                          , bk_set_VCD_file        = set_vcd_fn sim_hdl
                          , bk_enable_VCD_dumping  = (fromC $ dl_ptr_ret_uchar c_bk_enable_VCD_dumping) sim_hdl
                          , bk_disable_VCD_dumping = (fromC $ dl_ptr_ret_void c_bk_disable_VCD_dumping) sim_hdl
                          , bk_shutdown            = (fromC $ dl_ptr_ret_void c_bk_shutdown) sim_hdl
                          })

unloadBluesimModel :: BluesimModel -> IO ()
unloadBluesimModel bs = do bk_shutdown bs
                           dlclose (model_so bs)

-- fields are: clock handle, currently active, name, initial value,
--             first edge, low duration, high_duration, cycles elapsed,
--             current value, last edge time
getClockInfo :: BluesimModel -> IO [(BSClock,Bool,String,BSClockValue,BSTime,BSTime,BSTime,Word64,BSClockValue,BSTime)]
getClockInfo bs =
    do n <- bk_num_clocks bs
       mapM helper [0..n-1]
    where helper x = do clk <- bk_get_nth_clock bs x
                        let is_active = (current_clock bs == clk)
                        name <- bk_clock_name bs clk
                        ival <- bk_clock_initial_value bs clk
                        delay <- bk_clock_first_edge bs clk
                        lo <- bk_clock_duration bs clk CLK_LOW
                        hi <- bk_clock_duration bs clk CLK_HIGH
                        cycles <- bk_clock_cycle_count bs clk
                        val <- bk_clock_val bs clk
                        etime <- bk_clock_last_edge bs clk
                        return ( clk
                               , is_active
                               , name
                               , ival
                               , delay
                               , lo
                               , hi
                               , cycles
                               , val
                               , etime
                               )

setActiveClock :: BluesimModel -> String -> IO (Maybe BluesimModel)
setActiveClock bs name =
    do clk <- bk_get_clock_by_name bs name
       if (clk == bad_clock_handle)
        then return Nothing
        else return $ Just (bs { current_clock = clk })

getCurDirStr :: BluesimModel -> IO String
getCurDirStr bs =
    do let ds = current_directory bs
       segments <- mapM (bk_get_key bs) ds
       let dir = intercalate "." (reverse segments)
       return $ if (null dir) then "." else dir

getCurDirSym :: BluesimModel -> IO BSSymbol
getCurDirSym bs =
    do let ds = current_directory bs
       return $ head ds
