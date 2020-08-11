{-# LANGUAGE ForeignFunctionInterface   #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE CPP #-}

module Yices (

    -- * Types
    Expr,
    Type,
    Context,
    Status(..),
    Model,

    -- * Version numbers
    version,
    buildArch, buildMode, buildDate,

    -- Check that version is not a stub
    checkVersion,

    -- * Global initialization and cleanup
    --yicesInit, yicesExit, yicesReset,

    -- * Error reporting
    -- ...

    -- * Type constructors
    mkBoolType,
    mkBitVectorType,
    mkIntType,

    -- * Term constructors
    mkTrue, mkFalse,
    mkConst,
    mkUninterpretedTerm,
    mkVar,

    -- ** Logical operators
    mkIte,
    mkEq, mkNEq,
    mkNot,

    mkOr, mkAnd, mkXor,
    mkOr2, mkAnd2, mkXor2,

    mkIff,
    mkImplies,
    mkDistinct,
    mkForAll, mkExists,

    -- * Arithmetic term constructors
    mkZero,
    mkIntFromInt32, mkIntFromInt64,
    mkIntFromInteger,

    mkAdd, mkSub, mkNeg, mkMul,
    mkSquare, mkPower,

    mkArithEq, mkArithNEq,
    mkArithGTE, mkArithLTE, mkArithGT, mkArithLT,

    mkArithEq0, mkArithNEq0,
    mkArithGTE0, mkArithLTE0, mkArithGT0, mkArithLT0,

    -- * Bit vector term constructors
    mkBVConstantFromWord32, mkBVConstantFromWord64,
    mkBVConstantFromInteger,

    mkBVConstantZero, mkBVConstantOne, mkBVConstantMinusOne,

    -- ** Arithmetic
    mkBVAdd, mkBVSub, mkBVMul,
    mkBVMinus,
    mkBVDiv, mkBVRem,

    -- ** Logical
    mkBVNot,
    mkBVAnd, mkBVOr, mkBVXOr,
    mkBVNAnd, mkBVNOr, mkBVXNOr,

    -- ** Shifting
    mkBVShiftLeft,
    mkBVShiftRightArith, mkBVShiftRightLogical,

    -- ** Strings
    mkBVExtract, mkBVConcat,
    mkBVSignExtend, mkBVZeroExtend,

    -- ** Bitwise
    mkBVReduceAnd, mkBVReduceOr, mkBVReduceComp,

    -- ** Boolean conversions
    mkBoolsToBitVector, mkBVBoolExtract,

    -- ** Comparisons
    mkBVEq, mkBVNEq,

    mkBVGe, mkBVGt,
    mkBVLe, mkBVLt,

    mkBVSge, mkBVSgt,
    mkBVSle, mkBVSlt,

    -- * Parsing
    -- ...

    -- * Substitutions
    -- ...

    -- * Names
    -- ...

    -- * Pretty printing
    --ppType,
    --ppExpr,

    -- * Checks on terms
    getType,
    isBool, isBitVector,
    getBVSize,

    -- * Contexts
    mkContext,
    ctxStatus,
    ctxReset,
    ctxPush,
    ctxPop,

    assert, assertMany,

    -- * Models
    getModel,
    printModel

    --getModelBool,
    --getBodelBitVector

    ) where

import YicesFFI

import Foreign
import Foreign.C.Types
import Foreign.C.String
import qualified Foreign.Concurrent as F

import Control.Monad(when)
import qualified Control.Exception as CE
import MVarStrict

import Data.IORef(IORef, newIORef, readIORef, modifyIORef)
import Data.List(isPrefixOf)
import System.IO.Unsafe(unsafePerformIO)

import ErrorUtil

word32_size, word64_size :: Int
word32_size = finiteBitSize (0 :: Word32)
word64_size = finiteBitSize (0 :: Word64)

------------------------------------------------------------------------
-- Types

-- A Yices /context/
--
-- Notes:
--
-- * The resource is automatically managed by the Haskell garbage
-- collector, and the structure is automatically deleted once it is out
-- of scope (no need to call 'c_del_context').
--
-- * Improving on the C API, we maintain a stack depth, to prevent errors
-- relating to uneven numbers of 'push' and 'pop' operations. 'pop' on a
-- zero depth stack leaves the stack at zero.
--
data Context = Context { yContext :: ForeignPtr YContext
                       , yConfig :: Ptr YContextConfig
                       -- We have a semaphore to prevent push/pop errors
                       , yDepth   :: !(MVar Integer)
                       }
    deriving Eq

-- A Yices /model/
--
newtype Model = Model { unModel :: Ptr YModel }
    deriving (Eq, Ord, Show, Storable)

-- Yices /expressions/
--
newtype Expr = Expr { unExpr :: YExpr }
    deriving (Eq, Ord, Show, Storable)

-- Yices /types/
--
newtype Type = Type { unType :: YType }
    deriving (Eq, Ord, Show, Storable)

-- Context status
data Status
    = Idle
    | Searching
    | Unknown
    | Satisfiable
    | Unsatisfiable
    | Interrupted
    | Error
    deriving (Eq, Ord, Enum, Bounded, Read, Show)

------------------------------------------------------------------------
-- Version numbers

version :: IO String
version = peek yices_version >>= peekCString

buildArch :: IO String
buildArch = peek  yices_build_arch >>= peekCString

buildMode :: IO String
buildMode = peek yices_build_arch >>= peekCString

buildDate :: IO String
buildDate = peek yices_build_arch >>= peekCString

-- Throw an error if the version is a stub
checkVersion :: IO (String)
checkVersion = do
  v <- version
  if isPrefixOf "2." v
    then return v
    else CE.ioError $ userError $ "Incorrect Yices library version " ++ v

------------------------------------------------------------------------
-- Global initialization and cleanup

{-
yicesInit :: IO ()
yicesInit = yices_init

yicesExit :: IO ()
yicesExit = yices_exit

yicesReset :: IO ()
yicesReset = yices_reset
-}

-- "yices_init" must only be called once.  And we want to make sure that
-- memory is freed in a timely manner, so we'd like to call "yices_reset"
-- when a context is finished.

-- Instead of having the user manually handle the above calls, we require
-- that creating a context be the first thing that the user does, and the
-- init/reset is built into mkContext.  And we'll settle for not putting
-- a reset in the finalizer for the context, but instead just call reset
-- when the next context is created, relying on the assumption that only
-- one context is ever in use.

-- XXX We should probably keep a count of the number of outstanding contexts
-- XXX and do a reset only when deleting the last one (in the finalizer),
-- XXX and avoid doing a reset while there are outstanding context pointers?

{-# NOINLINE globalInit #-}
globalInit :: IORef Bool
globalInit = unsafePerformIO $ newIORef False

doInit :: IO ()
doInit = do
  isInit <- readIORef globalInit
  if (isInit)
     then yices_reset
     else do yices_init
             modifyIORef globalInit (const True)

------------------------------------------------------------------------
-- Error reporting

-- ...

------------------------------------------------------------------------
-- Type constructors

mkBoolType :: IO Type
mkBoolType = mkTypeRes "mkBoolType" $ yices_bool_type

mkBitVectorType :: Word32 -> IO Type
mkBitVectorType 0 = internalError "Yices.mkBitVectorType: size must be positive"
mkBitVectorType n = mkTypeRes "mkBitVectorType" $
                    yices_bv_type n

mkIntType :: IO Type
mkIntType = mkTypeRes "mkIntType" $ yices_int_type

------------------------------------------------------------------------
-- Term constructors

mkTrue :: IO Expr
mkTrue = mkExprRes "mkTrue" $ yices_true

mkFalse :: IO Expr
mkFalse = mkExprRes "mkFalse" $ yices_false

mkConst :: Type -> Int32 -> IO Expr
mkConst t n = mkExprRes "mkConst" $ yices_constant (unType t) n

mkUninterpretedTerm :: Type -> IO Expr
mkUninterpretedTerm t =
  mkExprRes "mkUninterpretedTerm" $ yices_new_uninterpreted_term (unType t)

mkVar :: Type -> IO Expr
mkVar t = mkExprRes "mkVar" $ yices_new_variable (unType t)

mkIte :: Expr -> Expr -> Expr -> IO Expr
mkIte b e1 e2 = mkExprRes "mkIte" $ yices_ite (unExpr b) (unExpr e1) (unExpr e2)

mkEq :: Expr -> Expr -> IO Expr
mkEq e1 e2 = mkExprRes "mkEq" $ yices_eq (unExpr e1) (unExpr e2)

mkNEq :: Expr -> Expr -> IO Expr
mkNEq e1 e2 = mkExprRes "mkNEq" $ yices_neq (unExpr e1) (unExpr e2)

mkNot :: Expr -> IO Expr
mkNot e = mkExprRes "mkNot" $ yices_not (unExpr e)

mkOr :: [Expr] -> IO Expr
mkOr [] = internalError "Yices.mkOr: empty list of expressions"
mkOr es =
  withArray (map unExpr es) $ \aptr ->
  mkExprRes "mkOr" $ yices_or (fromIntegral (length es)) aptr

mkAnd :: [Expr] -> IO Expr
mkAnd [] = internalError "Yices.mkAnd: empty list of expressions"
mkAnd es =
  withArray (map unExpr es) $ \aptr ->
  mkExprRes "mkAnd" $ yices_and (fromIntegral (length es)) aptr

mkXor :: [Expr] -> IO Expr
mkXor [] = internalError "Yices.mkXor: empty list of expressions"
mkXor es =
  withArray (map unExpr es) $ \aptr ->
  mkExprRes "mkXor" $ yices_xor (fromIntegral (length es)) aptr

mkOr2 :: Expr -> Expr -> IO Expr
mkOr2 e1 e2 = mkExprRes "mkOr2" $ yices_or2 (unExpr e1) (unExpr e2)

mkAnd2 :: Expr -> Expr -> IO Expr
mkAnd2 e1 e2 = mkExprRes "mkAnd2" $ yices_and2 (unExpr e1) (unExpr e2)

mkXor2 :: Expr -> Expr -> IO Expr
mkXor2 e1 e2 = mkExprRes "mkXor2" $ yices_xor2 (unExpr e1) (unExpr e2)

mkIff :: Expr -> Expr -> IO Expr
mkIff e1 e2 = mkExprRes "mkIff" $ yices_iff (unExpr e1) (unExpr e2)

mkImplies :: Expr -> Expr -> IO Expr
mkImplies e1 e2 = mkExprRes "mkImplies" $ yices_implies (unExpr e1) (unExpr e2)

mkDistinct :: Expr -> Expr -> IO Expr
mkDistinct e1 e2 = mkExprRes "mkDistinct" $ yices_distinct (unExpr e1) (unExpr e2)

mkForAll :: [Expr] -> Expr -> IO Expr
mkForAll [] body = internalError "Yices.mkForAll: empty list of variables"
mkForAll vs body =
  withArray (map unExpr vs) $ \aptr ->
  mkExprRes "mkForAll" $ yices_forall (fromIntegral (length vs)) aptr (unExpr body)

mkExists :: [Expr] -> Expr -> IO Expr
mkExists [] body = internalError "Yices.mkExists: empty list of variables"
mkExists vs body =
  withArray (map unExpr vs) $ \aptr ->
  mkExprRes "mkExists" $ yices_exists (fromIntegral (length vs)) aptr (unExpr body)

------------------------------------------------------------------------
-- Arithmetic term constructors

mkZero :: IO Expr
mkZero = mkExprRes "mkZero" $ yices_zero

mkIntFromInt32 :: Int32 -> IO Expr
mkIntFromInt32 v =
  mkExprRes "mkIntFromInt32" $ yices_int32 v

mkIntFromInt64 :: Int64 -> IO Expr
mkIntFromInt64 v =
  mkExprRes "mkIntFromInt64" $ yices_int64 v

mkIntFromInteger :: Integer -> IO Expr
mkIntFromInteger 0 = mkZero
-- XXX More efficient to just always use Word64?
mkIntFromInteger v | fitsInInt32 = mkIntFromInt32 (fromInteger v)
  where fitsInInt32 = (v <= toInteger (maxBound::Int32)) &&
                      (v >= toInteger (minBound::Int32))
mkIntFromInteger v | fitsInInt64 = mkIntFromInt64 (fromInteger v)
  where fitsInInt64 = (v <= toInteger (maxBound::Int64)) &&
                      (v >= toInteger (minBound::Int64))
mkIntFromInteger v =
  internalError ("mkIntFromInteger: too large: " ++ show v)

mkAdd :: Expr -> Expr -> IO Expr
mkAdd e1 e2 = mkExprRes "mkAdd" $ yices_add (unExpr e1) (unExpr e2)

mkSub :: Expr -> Expr -> IO Expr
mkSub e1 e2 = mkExprRes "mkSub" $ yices_sub (unExpr e1) (unExpr e2)

mkNeg :: Expr -> IO Expr
mkNeg e = mkExprRes "mkNeg" $ yices_neg (unExpr e)

mkMul :: Expr -> Expr -> IO Expr
mkMul e1 e2 = mkExprRes "mkMul" $ yices_mul (unExpr e1) (unExpr e2)

mkSquare :: Expr -> Expr -> IO Expr
mkSquare e1 e2 = mkExprRes "mkSquare" $ yices_square (unExpr e1) (unExpr e2)

mkPower :: Expr -> Word32 -> IO Expr
mkPower e n = mkExprRes "mkPower" $ yices_power (unExpr e) n

mkArithEq :: Expr -> Expr -> IO Expr
mkArithEq e1 e2 =
  mkExprRes "mkArithEq" $ yices_arith_eq_atom (unExpr e1) (unExpr e2)

mkArithNEq :: Expr -> Expr -> IO Expr
mkArithNEq e1 e2 =
  mkExprRes "mkArithNEq" $ yices_arith_neq_atom (unExpr e1) (unExpr e2)

mkArithGTE :: Expr -> Expr -> IO Expr
mkArithGTE e1 e2 =
  mkExprRes "mkArithGTE" $ yices_arith_geq_atom (unExpr e1) (unExpr e2)

mkArithLTE :: Expr -> Expr -> IO Expr
mkArithLTE e1 e2 =
  mkExprRes "mkArithLTE" $ yices_arith_leq_atom (unExpr e1) (unExpr e2)

mkArithGT :: Expr -> Expr -> IO Expr
mkArithGT e1 e2 =
  mkExprRes "mkArithGT" $ yices_arith_gt_atom (unExpr e1) (unExpr e2)

mkArithLT :: Expr -> Expr -> IO Expr
mkArithLT e1 e2 =
  mkExprRes "mkArithLT" $ yices_arith_lt_atom (unExpr e1) (unExpr e2)

mkArithEq0 :: Expr -> IO Expr
mkArithEq0 e = mkExprRes "mkArithEq0" $ yices_arith_eq0_atom (unExpr e)

mkArithNEq0 :: Expr -> IO Expr
mkArithNEq0 e = mkExprRes "mkArithNEq0" $ yices_arith_neq0_atom (unExpr e)

mkArithGTE0 :: Expr -> IO Expr
mkArithGTE0 e = mkExprRes "mkArithGTE0" $ yices_arith_geq0_atom (unExpr e)

mkArithLTE0 :: Expr -> IO Expr
mkArithLTE0 e = mkExprRes "mkArithLTE0" $ yices_arith_leq0_atom (unExpr e)

mkArithGT0 :: Expr -> IO Expr
mkArithGT0 e = mkExprRes "mkArithGT0" $ yices_arith_gt0_atom (unExpr e)

mkArithLT0 :: Expr -> IO Expr
mkArithLT0 e = mkExprRes "mkArithLT0" $ yices_arith_lt0_atom (unExpr e)

------------------------------------------------------------------------
-- Bit vector term constructors

mkBVConstantFromWord32 :: Word32 -> Word32 -> IO Expr
mkBVConstantFromWord32 n v =
    mkExprRes "mkBVConstantFromWord32" $
    yices_bvconst_uint32 n v

mkBVConstantFromWord64 :: Word32 -> Word64 -> IO Expr
mkBVConstantFromWord64 n v =
    mkExprRes "mkBVConstantFromWord64" $
    yices_bvconst_uint64 n v

mkBVConstantFromInteger :: Integer -> Integer -> IO Expr
mkBVConstantFromInteger width _ | (width < 1) =
  internalError "Yices.mkBVConstantFromInteger: width must be positive"
mkBVConstantFromInteger width val | fitsInWord32 =
  mkBVConstantFromWord32 (fromInteger width) (fromInteger val)
  where fitsInWord32 = (fromInteger width) <= word32_size
mkBVConstantFromInteger width val | fitsInWord64 =
  mkBVConstantFromWord64 (fromInteger width) (fromInteger val)
  where fitsInWord64 = (fromInteger width) <= word64_size
mkBVConstantFromInteger width val =
  -- XXX is it more efficient to create a concat of Word64 values?
  makeVPtrWith width val $ \vptr ->
  mkExprRes "mkBVConstantFromInteger" $ yices_parse_bvbin (castPtr vptr)

makeVPtrWith :: Integer -> Integer -> (CString -> IO b) -> IO b
makeVPtrWith width val f =
  let -- We could use "showIntAtBase", but then we should check to
      -- make sure the width is correct.
      -- This should rarely be needed, so don't worry about efficiency.
      mkBit idx = if (testBit val idx) then '1' else '0'
      str = map mkBit $ reverse [0 .. fromInteger (width-1)]
  in  withCString str f

mkBVConstantZero :: Word32 -> IO Expr
mkBVConstantZero n =
  mkExprRes "mkBVConstantZero" $ yices_bvconst_zero n

mkBVConstantOne :: Word32 -> IO Expr
mkBVConstantOne n =
  mkExprRes "mkBVConstantOne" $ yices_bvconst_one n

mkBVConstantMinusOne :: Word32 -> IO Expr
mkBVConstantMinusOne n =
  mkExprRes "mkBVConstantMinusOne" $ yices_bvconst_minus_one n

mkBVAdd :: Expr -> Expr -> IO Expr
mkBVAdd e1 e2 = mkExprRes "mkBVAdd" $ yices_bvadd (unExpr e1) (unExpr e2)

mkBVSub :: Expr -> Expr -> IO Expr
mkBVSub e1 e2 = mkExprRes "mkBVSub" $ yices_bvsub (unExpr e1) (unExpr e2)

mkBVMul :: Expr -> Expr -> IO Expr
mkBVMul e1 e2 = mkExprRes "mkBVMul" $ yices_bvmul (unExpr e1) (unExpr e2)

mkBVMinus :: Expr -> IO Expr
mkBVMinus e = mkExprRes "mkBVMinus" $ yices_bvneg (unExpr e)

mkBVDiv :: Expr -> Expr -> IO Expr
mkBVDiv e1 e2 = mkExprRes "mkBVDiv" $ yices_bvdiv (unExpr e1) (unExpr e2)

mkBVRem :: Expr -> Expr -> IO Expr
mkBVRem e1 e2 = mkExprRes "mkBVRem" $ yices_bvrem (unExpr e1) (unExpr e2)

mkBVNot :: Expr -> IO Expr
mkBVNot e = mkExprRes "mkBVNot" $ yices_bvnot (unExpr e)

mkBVAnd :: Expr -> Expr -> IO Expr
mkBVAnd e1 e2 = mkExprRes "mkBVAnd" $ yices_bvand2 (unExpr e1) (unExpr e2)

mkBVOr :: Expr -> Expr -> IO Expr
mkBVOr e1 e2 = mkExprRes "mkBVOr" $ yices_bvor2 (unExpr e1) (unExpr e2)

mkBVXOr :: Expr -> Expr -> IO Expr
mkBVXOr e1 e2 = mkExprRes "mkBVXOr" $ yices_bvxor2 (unExpr e1) (unExpr e2)

mkBVNAnd :: Expr -> Expr -> IO Expr
mkBVNAnd e1 e2 = mkExprRes "mkBVNAnd" $ yices_bvnand (unExpr e1) (unExpr e2)

mkBVNOr :: Expr -> Expr -> IO Expr
mkBVNOr e1 e2 = mkExprRes "mkBVNOr" $ yices_bvnor (unExpr e1) (unExpr e2)

mkBVXNOr :: Expr -> Expr -> IO Expr
mkBVXNOr e1 e2 = mkExprRes "mkBVXNOr" $ yices_bvxnor (unExpr e1) (unExpr e2)

mkBVShiftLeft :: Expr -> Expr -> IO Expr
mkBVShiftLeft e1 e2 =
  mkExprRes "mkBVShiftLeft" $ yices_bvshl (unExpr e1) (unExpr e2)

mkBVShiftRightArith :: Expr -> Expr -> IO Expr
mkBVShiftRightArith e1 e2 =
  mkExprRes "mkBVShiftRightArith" $ yices_bvashr (unExpr e1) (unExpr e2)

mkBVShiftRightLogical :: Expr -> Expr -> IO Expr
mkBVShiftRightLogical e1 e2 =
  mkExprRes "mkBVShiftRightLogical" $ yices_bvlshr (unExpr e1) (unExpr e2)

mkBVExtract :: Expr -> Word32 -> Word32 -> IO Expr
mkBVExtract e begin end =
  mkExprRes "mkBVExtract" $
  yices_bvextract (unExpr e) begin end

mkBVConcat :: Expr -> Expr -> IO Expr
mkBVConcat e1 e2 = mkExprRes "mkBVConcat" $ yices_bvconcat2 (unExpr e1) (unExpr e2)

mkBVSignExtend :: Expr -> Word32 -> IO Expr
mkBVSignExtend e n =
  mkExprRes "mkBVSignExtend" $ yices_sign_extend (unExpr e) n

mkBVZeroExtend :: Expr -> Word32 -> IO Expr
mkBVZeroExtend e n =
  mkExprRes "mkBVZeroExtend" $ yices_zero_extend (unExpr e) n

mkBVReduceAnd :: Expr -> IO Expr
mkBVReduceAnd e = mkExprRes "mkBVReduceAnd" $ yices_redand (unExpr e)

mkBVReduceOr :: Expr -> IO Expr
mkBVReduceOr e = mkExprRes "mkBVReduceOr" $ yices_redor (unExpr e)

mkBVReduceComp :: Expr -> IO Expr
mkBVReduceComp e = mkExprRes "mkBVReduceComp" $ yices_redcomp (unExpr e)

mkBoolsToBitVector :: [Expr] -> IO Expr
mkBoolsToBitVector es =
  withArray (map unExpr es) $ \aptr ->
  mkExprRes "mkBoolsToBitVector" $ yices_bvarray (fromIntegral (length es)) aptr

mkBVBoolExtract :: Expr -> Word32 -> IO Expr
mkBVBoolExtract e n =
  mkExprRes "mkBVBoolExtract" $ yices_bitextract (unExpr e) n

mkBVEq :: Expr -> Expr -> IO Expr
mkBVEq e1 e2 = mkExprRes "mkBVEq" $ yices_bveq_atom (unExpr e1) (unExpr e2)

mkBVNEq :: Expr -> Expr -> IO Expr
mkBVNEq e1 e2 = mkExprRes "mkBVNEq" $ yices_bvneq_atom (unExpr e1) (unExpr e2)

mkBVGe :: Expr -> Expr -> IO Expr
mkBVGe e1 e2 = mkExprRes "mkBVGe" $ yices_bvge_atom (unExpr e1) (unExpr e2)

mkBVGt :: Expr -> Expr -> IO Expr
mkBVGt e1 e2 = mkExprRes "mkBVGt" $ yices_bvgt_atom (unExpr e1) (unExpr e2)

mkBVLe :: Expr -> Expr -> IO Expr
mkBVLe e1 e2 = mkExprRes "mkBVLe" $ yices_bvle_atom (unExpr e1) (unExpr e2)

mkBVLt :: Expr -> Expr -> IO Expr
mkBVLt e1 e2 = mkExprRes "mkBVLt" $ yices_bvlt_atom (unExpr e1) (unExpr e2)

mkBVSge :: Expr -> Expr -> IO Expr
mkBVSge e1 e2 = mkExprRes "mkBVSge" $ yices_bvsge_atom (unExpr e1) (unExpr e2)

mkBVSgt :: Expr -> Expr -> IO Expr
mkBVSgt e1 e2 = mkExprRes "mkBVSgt" $ yices_bvsgt_atom (unExpr e1) (unExpr e2)

mkBVSle :: Expr -> Expr -> IO Expr
mkBVSle e1 e2 = mkExprRes "mkBVSle" $ yices_bvsle_atom (unExpr e1) (unExpr e2)

mkBVSlt :: Expr -> Expr -> IO Expr
mkBVSlt e1 e2 = mkExprRes "mkBVSlt" $ yices_bvslt_atom (unExpr e1) (unExpr e2)

------------------------------------------------------------------------
-- Parsing

-- ...

------------------------------------------------------------------------
-- Substitutions

-- ...

------------------------------------------------------------------------
-- Names

-- ...

------------------------------------------------------------------------
-- Pretty printing

-- ...

------------------------------------------------------------------------
-- Checks on terms

getType :: Expr -> IO Type
getType e = mkTypeRes "getType" $ yices_type_of_term (unExpr e)

isBool :: Expr -> IO Bool
isBool e = do
  res <- yices_term_is_bool (unExpr e)
  case res of
    0 -> return False
    1 -> return True
    _ -> errorWithCode "Yices.isBool: unexpected result"

isBitVector :: Expr -> IO Bool
isBitVector e = do
  res <- yices_term_is_bitvector (unExpr e)
  case res of
    0 -> return False
    1 -> return True
    _ -> errorWithCode "Yices.isBitVector: unexpected result"

getBVSize :: Expr -> IO Word32
getBVSize e = do
  res <- yices_term_bitsize (unExpr e)
  if (res == 0)
    then errorWithCode "Yices.getBVSize: error result"
    else return res

------------------------------------------------------------------------
-- Contexts

mkContext :: IO Context
mkContext = do
  -- make sure that Yices is initialized
  doInit
  cfg <- yices_new_config
  -- XXX set cfg to BV only?
  ctx <- yices_new_context cfg
  let delFn = do --yices_free_context ctx
                 --yices_free_config cfg
                 return ()
  ctx_fp <- F.newForeignPtr ctx delFn
  n <- newMVar 0
  return $! Context { yContext = ctx_fp,
                      yConfig  = cfg,
                      yDepth   = n }

ctxStatus :: Context -> IO Status
ctxStatus c = do
  res <- withForeignPtr (yContext c) $ \cptr ->
         yices_check_context cptr nullPtr
  return $ case res of
              0 -> Idle
              1 -> Searching
              2 -> Unknown
              3 -> Satisfiable
              4 -> Unsatisfiable
              5 -> Interrupted
              6 -> Error
              _ -> internalError "Yices.ctxStatus: unexpected status"

ctxReset :: Context -> IO ()
ctxReset c = do
  withForeignPtr (yContext c) $ yices_reset_context
  modifyMVar_ (yDepth c) $ \_ -> return 0

ctxPush :: Context -> IO ()
ctxPush c = modifyMVar_ (yDepth c) $ \n ->
  if n < 0
    then internalError "Yices.ctxPush: corrupted context, stack depth < 0"
    else do checkInt32Res "ctxPush" $ withForeignPtr (yContext c) $ yices_push
            return (n+1)

ctxPop :: Context -> IO ()
ctxPop c = modifyMVar_ (yDepth c) $ \n ->
  if n < 1
     then internalError "Yices.ctxPop: corrupted context, stack depth < 1"
     else do checkInt32Res "ctxPop" $ withForeignPtr (yContext c) $ yices_pop
             return (n-1)

assert :: Context -> Expr -> IO ()
assert c e = do
  res <- withForeignPtr (yContext c) $ \cptr ->
         yices_assert_formula cptr (unExpr e)
  when (res /= 0) $ errorWithCode "Yices.assert"

assertMany :: Context -> [Expr] -> IO ()
assertMany c es = do
  res <- withArray (map unExpr es) $ \aptr ->
         withForeignPtr (yContext c) $ \cptr ->
         yices_assert_formulas cptr (fromIntegral (length es)) aptr
  when (res /= 0) $ errorWithCode "Yices.assert"

------------------------------------------------------------------------
-- Models

getModel :: Context -> IO Model
getModel ctx = do
  Model <$>
    (withForeignPtr (yContext ctx) $ \cptr -> yices_get_model cptr 1)

printModel :: Model -> IO ()
printModel mdl = do
  fh <- withCString "model.txt" $ \fname ->
          withCString "a" $ \mode ->
            fopen fname mode
  yices_print_model fh (unModel mdl)
  fclose fh

------------------------------------------------------------------------

checkInt32Res :: String -> IO Int32 -> IO ()
checkInt32Res str fn = do
  res <- fn
  case res of
    -1 -> errorWithCode ("Yices." ++ str ++ ": error result")
    _ -> return ()

checkPtrRes :: String -> IO Int32 -> IO Int32
checkPtrRes str fn = do
  res <- fn
  -- NULL_TERM and NULL_TYPE are -1, but any value < 0 is also an error
  if (res < 0)
     then errorWithCode ("Yices." ++ str)
     else return res

mkTypeRes :: String -> IO YType -> IO Type
mkTypeRes str fn = Type <$> checkPtrRes str fn

mkExprRes :: String -> IO YExpr -> IO Expr
mkExprRes str fn = Expr <$> checkPtrRes str fn

errorWithCode :: String -> IO a
errorWithCode str = do
  res <- yices_error_code
  internalError (str ++ ": " ++ show res)

------------------------------------------------------------------------

foreign import ccall "stdio.h"
  fopen :: CString -> CString -> IO (Ptr CFile)

foreign import ccall "stdio.h"
  fclose :: Ptr CFile -> IO ()

------------------------------------------------------------------------
