{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE CPP #-}

module STP (

    -- * Core STP types
    Context,
    Type,
    Expr,
    Result(..),

    -- Check that the dynamic library is compatible
    -- with this FFI (and not a stub)
    checkVersion,

    -- * Manipulating contexts
    mkContext,
    ctxPush,
    ctxPop,
    deleteExpr, deleteExprs,

    -- * Debug
    setPrintVarDecls,
    setPrintAsserts,
    setPrintQuery,
    setClearDecls,
    printExpr,
    setFlag,

    -- * Making assertions
    assert,

    -- * Queries
    query,
    queryWithTimeout,
    isBool,

    -- * STP Types
    mkBoolType,
    mkBitVectorType,

    -- * STP Expressions

    -- ** Type conversion
    mkBoolToBitVector,

    -- ** Variables
    mkVar,

    -- ** Constants
    mkTrue, mkFalse,
    mkBVConstantFromInteger,

    -- ** Logical operators
    mkEq,
    mkNot,
    mkAnd, mkAndMany,
    mkOr, mkOrMany,
    mkXor,
    mkImplies,
    mkIff,
    mkIte,

    -- ** Bit-vector arithmetic
    mkBVAdd, mkBVAddMany,
    mkBVSub, mkBVMul, mkBVDiv, mkBVMod,
    mkBVSignedDiv, mkBVSignedMod,
    mkBVMinus,

    -- ** Bit-vector comparisons
    mkBVLt, mkBVLe,
    mkBVGt, mkBVGe,

    mkBVSlt, mkBVSle,
    mkBVSgt, mkBVSge,

    -- ** Bitwise operations
    mkBVAnd, mkBVOr, mkBVXor,
    mkBVNot,

    -- ** Bit-vector shifting and signs
    mkBVSignExtend,
    mkBVShiftLeft, mkBVShiftRight,
    mkBVShiftLeftExpr, mkBVShiftRightExpr,  mkBVSignedShiftRightExpr,


    -- ** Bit-vector strings
    mkBVConcat,
    mkBVExtract, mkBVBoolExtract

    ) where

import STPFFI

import Foreign
import Foreign.C.String
import Foreign.C.Types
import qualified Foreign.Concurrent as F

--import Control.Concurrent.MVar.Strict
import MVarStrict

import ErrorUtil(internalError)
import System.Posix.Env(getEnvDefault)
--import Util(traceM)


cullong_size :: Int
cullong_size = finiteBitSize (0 :: CULLong)

------------------------------------------------------------------------
-- Types

-- | An STP /context/
--
-- A context is an environment of assertions.
--
-- /Notes:/
--
-- * The resource is automatically managed by the Haskell garbage
-- collector, and the structure is automatically deleted once it is out
-- of scope (no need to call 'vc_Destroy'.)
--
-- * Improving on the C API, we maintain a stack depth, to prevent errors
-- relating to uneven numbers of 'push' and 'pop' operations. 'pop' on a
-- zero depth stack leaves the stack at zero.
--
data Context = Context { sContext :: ForeignPtr SContext
                       , sDepth   :: !(MVar Integer)
                       }
    deriving Eq

-- | STP types
--
newtype Type = Type { unType :: Ptr SType }
    deriving (Eq, Ord, Show, Storable)

-- | STP /expressions/
--
newtype Expr = Expr { unExpr :: Ptr SExpr }
    deriving (Eq, Ord, Show, Storable)

-- The return type for queries
data Result
    = Invalid
    | Valid
    | Error
    | Timeout
    deriving (Eq, Ord, Enum, Bounded, Read, Show)

toResult :: CInt -> Result
toResult n
    | n == 0 = Invalid
    | n == 1 = Valid
    | n == 2 = Error
    | n == 3 = Timeout
    | otherwise = internalError("STP.toResult: " ++ show n)

-- Name of environment variable contain flags
flagEnvironment :: String
flagEnvironment = "BSC_STP_FLAGS"

------------------------------------------------------------------------

checkVersion :: IO Bool
checkVersion = do
  -- The API doesn't provide version info
  -- so all we can do is check for a stub
  ptr <- vc_createValidityChecker
  return (ptr /= nullPtr)

------------------------------------------------------------------------
-- Context manipulation

-- | Create a new logical context.
-- When the context goes out of scope, it will be automatically deleted.
--
mkContext :: IO Context
mkContext = do
    ptr <- vc_createValidityChecker
    --traceM("==> vc created: " ++ show ptr)
    make_division_total ptr
    fp  <- F.newForeignPtr ptr (do --traceM("==> vc destryoy: " ++ show ptr)
                                   --vc_Destroy ptr
                                   --traceM("==> destroyed")
                                   return ()
                               )
    n   <- newMVar 0
    envFlags <- getEnvDefault flagEnvironment ""
    mapM_ (setFlag ptr) envFlags
    return $! Context fp n

-- | Create a backtracking point in the given logical context.
--
-- The logical context can be viewed as a stack of contexts. The scope
-- level is the number of elements on this stack. The stack of contexts
-- is simulated using trail (undo) stacks.
--
ctxPush :: Context -> IO ()
ctxPush c = modifyMVar_ (sDepth c) $ \n ->
    if n < 0
        then error "STP.ctxPush: Corrupted Context. Stack depth < 0"
        else do
            withForeignPtr (sContext c) $ vc_push
            return (n+1)

-- | Backtrack.
--
-- Restores the context from the top of the stack, and pops it off the
-- stack. Any changes to the logical context (by 'vc_assertFormula' or
-- other functions) between the matching 'push' and 'pop' operators are
-- flushed, and the context is completely restored to what it was right
-- before the 'push'.
--
ctxPop :: Context -> IO ()
ctxPop c = modifyMVar_ (sDepth c) $ \n -> case () of
    _ | n <  0    -> error "STP.mkPop: Corrupted context. Stack depth < 0"
      | n == 0    -> return n
      | otherwise -> do
            withForeignPtr (sContext c) $ vc_pop
            return (n-1)

------------------------------------------------------------------------
-- Debug

setPrintVarDecls :: Context -> IO ()
setPrintVarDecls c = withForeignPtr (sContext c) vc_printVarDecls

setPrintAsserts :: Context -> IO ()
setPrintAsserts c = withForeignPtr (sContext c) vc_printAsserts

setPrintQuery :: Context -> IO ()
setPrintQuery c = withForeignPtr (sContext c) vc_printQuery

setClearDecls :: Context -> IO ()
setClearDecls c = withForeignPtr (sContext c) vc_clearDecls

printExpr :: Context -> Expr -> IO ()
printExpr c e = do
    withForeignPtr (sContext c) $ \cptr -> vc_printExpr cptr (unExpr e)
    putChar '\n'

------------------------------------------------------------------------
-- Assertions

-- | Assert a constraint in the logical context.
--
assert :: Context -> Expr -> IO ()
assert c e = withForeignPtr (sContext c) $ \cptr ->
    vc_assertFormula cptr (unExpr e)

------------------------------------------------------------------------
-- Queries

-- | Check if an expression is satisfiable given the logical context.
--
-- * @Invalid@ means the expression is unsatisfiable in the context.
--
-- * @Valid@  means the expression is satisfiable in the context.
--
-- * @Error@ means that an error was encountered.
--
-- * @Timeout@ means it was not possible to decide in the given time.
--
query :: Context -> Expr -> IO Result
query c e = toResult <$>
    withForeignPtr (sContext c) (\cptr -> vc_query cptr (unExpr e))

queryWithTimeout :: Context -> Expr -> Int -> IO Result
queryWithTimeout c e msecs = toResult <$>
    withForeignPtr (sContext c)
        (\cptr -> vc_query_with_timeout cptr (unExpr e) (fromIntegral msecs))

-- | Determine whether an expression is True or False ?
--
-- Note that this takes no Context!  What is this function?!
--
isBool :: Expr -> IO (Maybe Bool)
isBool e = do
    res <- vc_isBool (unExpr e)
    case res of
      1  -> return $ Just True
      0  -> return $ Just False
      -1 -> return $ Nothing
      _  -> internalError ("STP.isBool: " ++ show res)

------------------------------------------------------------------------
-- Types

-- | Return the for booleans.
--
mkBoolType :: Context -> IO Type
mkBoolType c =
    withForeignPtr (sContext c) $ \cptr ->
        Type <$> vc_boolType cptr

-- | Returns a bitvector type of @n@ size.
--
-- Size must be greater than @0@.
--
mkBitVectorType :: Context -> Int -> IO Type
mkBitVectorType _ n | (n < 1) =
    internalError ("STP.mkBitVectorType: " ++ show n)
mkBitVectorType c n =
    withForeignPtr (sContext c) $ \cptr ->
        Type <$> vc_bvType cptr (fromIntegral n)

------------------------------------------------------------------------
-- Type conversion

mkBoolToBitVector :: Context -> Expr -> IO Expr
mkBoolToBitVector c e =
    withForeignPtr (sContext c) $ \cptr ->
        Expr <$> vc_boolToBVExpr cptr (unExpr e)

------------------------------------------------------------------------
-- Variables

mkVar :: Context -> String -> Type -> IO Expr
mkVar c str t =
    withCString str $ \cstr ->
    withForeignPtr (sContext c) $ \cptr ->
        Expr <$> vc_varExpr cptr cstr (unType t)

------------------------------------------------------------------------
-- Constants

-- | Return an expression representing 'True'.
--
mkTrue :: Context -> IO Expr
mkTrue c = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_trueExpr cptr

-- | Return an expression representing 'False'.
--
mkFalse :: Context -> IO Expr
mkFalse c = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_falseExpr cptr

-- | Create a bit vector constant of size bits and of the given value.
--
-- @size@ must be positive
--
mkBVConstantFromInteger :: Context -> Integer -> Integer -> IO Expr
mkBVConstantFromInteger _ width _ | (width < 1) =
    internalError ("STP.mkBVConstantFromInteger: " ++ show width)
mkBVConstantFromInteger c width val | fitsInCULLong =
    withForeignPtr (sContext c) $ \cptr ->
        Expr <$> vc_bvConstExprFromLL cptr (fromInteger width) (fromInteger val)
  where fitsInCULLong = (fromInteger width) <= cullong_size
mkBVConstantFromInteger c width val =
    -- XXX is it more efficient to create a concat of Word64 values?
    withForeignPtr (sContext c) $ \cptr ->
    makeVPtrWith width val $ \vptr ->
        Expr <$> vc_bvConstExprFromStr cptr (castPtr vptr)

makeVPtrWith :: Integer -> Integer -> (CString -> IO b) -> IO b
makeVPtrWith width val f =
  let -- We could use "showIntAtBase", but then we should check to
      -- make sure the width is correct.
      -- This should rarely be needed, so don't worry about efficiency.
      mkBit idx = if (testBit val idx) then '1' else '0'
      str = map mkBit $ reverse [0 .. fromInteger (width-1)]
  in  withCString str f

------------------------------------------------------------------------
-- Logical operations

-- | Return an expression representing:
--
-- > a1 == a2
--
mkEq :: Context -> Expr -> Expr -> IO Expr
mkEq c e1 e2 = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_eqExpr cptr (unExpr e1) (unExpr e2)

-- |    Return an expression representing:
--
-- > not a
--
mkNot :: Context -> Expr -> IO Expr
mkNot c e = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_notExpr cptr (unExpr e)

-- | Return an expression representing the binary /AND/ of the given arguments.
--
mkAnd :: Context -> Expr -> Expr -> IO Expr
mkAnd c e1 e2 = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_andExpr cptr (unExpr e1) (unExpr e2)

-- | Return an expression representing the /n/-ary /AND/ of the given arguments.
--
-- > and [a1, ..]
--
-- Reference: <http://yices.csl.sri.com/capi.shtml#ga52>
--
mkAndMany :: Context -> [Expr] -> IO Expr
mkAndMany _ [] = error "STP.mkAndMany: empty list of expressions"
mkAndMany c es =
    withArray es $ \aptr ->
    withForeignPtr (sContext c) $ \cptr ->
        Expr <$> vc_andExprN cptr (castPtr aptr) (fromIntegral (length es))

-- | Return an expression representing the binary /OR/ of the given arguments.
--
mkOr :: Context -> Expr -> Expr -> IO Expr
mkOr c e1 e2 = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_orExpr cptr (unExpr e1) (unExpr e2)

-- | Return an expression representing the /n/-ary /OR/ of the given arguments.
--
-- > or [a1, ..]
--
mkOrMany :: Context -> [Expr] -> IO Expr
mkOrMany _ [] = error "STP.mkOrMany: empty list of expressions"
mkOrMany c es =
    withArray es $ \aptr ->
    withForeignPtr (sContext c) $ \cptr ->
        Expr <$> vc_orExprN cptr (castPtr aptr) (fromIntegral (length es))

-- | Return an expression representing the binary /XOR/ of the given arguments.
--
mkXor :: Context -> Expr -> Expr -> IO Expr
mkXor c e1 e2 = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_xorExpr cptr (unExpr e1) (unExpr e2)

-- | Return an expression representing:
--
-- > e1 implies e2
--
mkImplies :: Context -> Expr -> Expr -> IO Expr
mkImplies c e1 e2 = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_impliesExpr cptr (unExpr e1) (unExpr e2)

-- | Return an expression representing:
--
-- > e1 if-and-only-if e2
--
mkIff :: Context -> Expr -> Expr -> IO Expr
mkIff c e1 e2 = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_iffExpr cptr (unExpr e1) (unExpr e2)

-- | Return an expression representing:
--
-- > if b then e1 else e2
--
mkIte :: Context -> Expr -> Expr -> Expr -> IO Expr
mkIte c b e1 e2 = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_iteExpr cptr (unExpr b) (unExpr e1) (unExpr e2)

------------------------------------------------------------------------
-- Bit-vector arithmetic

-- | Bitvector addition.
--
-- @a1@ and @a2@ must be bitvector expressions of same size.
--
mkBVAdd :: Context -> Int -> Expr -> Expr -> IO Expr
mkBVAdd c n e1 e2 =
    withForeignPtr (sContext c) $ \cptr ->
        Expr <$> vc_bvPlusExpr cptr (fromIntegral n) (unExpr e1) (unExpr e2)

-- | Bitvector addition of a list of expressions
--
-- The expression list must be non-empty.
--
mkBVAddMany :: Context -> Int -> [Expr] -> IO Expr
mkBVAddMany c n es =
    withArray es $ \esptr ->
    withForeignPtr (sContext c) $ \cptr ->
        Expr <$> vc_bvPlusExprN cptr (fromIntegral n)
                     (castPtr esptr) (fromIntegral (length es))

-- | Bitvector subtraction.
--
-- @a1@ and @a2@ must be bitvector expressions of same size.
--
mkBVSub :: Context -> Int -> Expr -> Expr -> IO Expr
mkBVSub c n e1 e2 =
    withForeignPtr (sContext c) $ \cptr ->
        Expr <$> vc_bvMinusExpr cptr (fromIntegral n) (unExpr e1) (unExpr e2)

-- | Bitvector multiplication.
--
-- @a1@ and @a2@ must be bitvector expressions of same size.
-- (The result is truncated to that size?)
--
mkBVMul :: Context -> Int -> Expr -> Expr -> IO Expr
mkBVMul c n e1 e2 =
    withForeignPtr (sContext c) $ \cptr ->
        Expr <$> vc_bvMultExpr cptr (fromIntegral n) (unExpr e1) (unExpr e2)

-- | Bitvector division
--
-- @a1@ and @a2@ must be bitvector expressions of same size.
--
mkBVDiv :: Context -> Int -> Expr -> Expr -> IO Expr
mkBVDiv c n e1 e2 =
    withForeignPtr (sContext c) $ \cptr ->
        Expr <$> vc_bvDivExpr cptr (fromIntegral n) (unExpr e1) (unExpr e2)

-- | Bitvector mod
--
-- @a1@ and @a2@ must be bitvector expressions of same size.
--
mkBVMod :: Context -> Int -> Expr -> Expr -> IO Expr
mkBVMod c n e1 e2 =
    withForeignPtr (sContext c) $ \cptr ->
        Expr <$> vc_bvModExpr cptr (fromIntegral n) (unExpr e1) (unExpr e2)

-- | Bitvector division (signed)
--
-- @a1@ and @a2@ must be bitvector expressions of same size.
--
mkBVSignedDiv :: Context -> Int -> Expr -> Expr -> IO Expr
mkBVSignedDiv c n e1 e2 =
    withForeignPtr (sContext c) $ \cptr ->
        Expr <$> vc_sbvDivExpr cptr (fromIntegral n) (unExpr e1) (unExpr e2)

-- | Bitvector mod (signed)
--
-- @a1@ and @a2@ must be bitvector expressions of same size.
--
mkBVSignedMod :: Context -> Int -> Expr -> Expr -> IO Expr
mkBVSignedMod c n e1 e2 =
    withForeignPtr (sContext c) $ \cptr ->
        Expr <$> vc_sbvModExpr cptr (fromIntegral n) (unExpr e1) (unExpr e2)

-- | Bitvector uniary minus.
--
-- @a1@ must be bitvector expression. The result is @(- a1)@.
--
mkBVMinus :: Context -> Expr -> IO Expr
mkBVMinus c e = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_bvUMinusExpr cptr (unExpr e)

------------------------------------------------------------------------
-- Bit-vector comparisons

-- | Unsigned bitvector comparison:
--
-- > a1 < a2
--
-- /a1/ and /a2/ must be bitvector expressions of same size.
--
mkBVLt :: Context -> Expr -> Expr -> IO Expr
mkBVLt c e1 e2 = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_bvLtExpr cptr (unExpr e1) (unExpr e2)

-- | Unsigned bitvector comparison:
--
-- > a1 <= a2
--
-- /a1/ and /a2/ must be bitvector expressions of same size.
--
mkBVLe :: Context -> Expr -> Expr -> IO Expr
mkBVLe c e1 e2 = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_bvLeExpr cptr (unExpr e1) (unExpr e2)

-- | Unsigned bitvector comparison:
--
-- > a1 > a2
--
-- /a1/ and /a2/ must be bitvector expressions of same size.
--
mkBVGt :: Context -> Expr -> Expr -> IO Expr
mkBVGt c e1 e2 = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_bvGtExpr cptr (unExpr e1) (unExpr e2)

-- | Unsigned bitvector comparison:
--
-- > a1 >= a2
--
-- /a1/ and /a2/ must be bitvector expressions of same size.
--
mkBVGe :: Context -> Expr -> Expr -> IO Expr
mkBVGe c e1 e2 = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_bvGeExpr cptr (unExpr e1) (unExpr e2)

-- | Signed bitvector comparison:
--
-- > a1 < a2
--
-- /a1/ and /a2/ must be bitvector expressions of same size.
--
mkBVSlt :: Context -> Expr -> Expr -> IO Expr
mkBVSlt c e1 e2 = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_sbvLtExpr cptr (unExpr e1) (unExpr e2)

-- | Signed bitvector comparison:
--
-- > a1 <= a2
--
-- /a1/ and /a2/ must be bitvector expressions of same size.
--
mkBVSle :: Context -> Expr -> Expr -> IO Expr
mkBVSle c e1 e2 = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_sbvLeExpr cptr (unExpr e1) (unExpr e2)

-- | Signed bitvector comparison:
--
-- > a1 > a2
--
-- /a1/ and /a2/ must be bitvector expressions of same size.
--
mkBVSgt :: Context -> Expr -> Expr -> IO Expr
mkBVSgt c e1 e2 = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_sbvGtExpr cptr (unExpr e1) (unExpr e2)

-- | Signed bitvector comparison:
--
-- > a1 >= a2
--
-- /a1/ and /a2/ must be bitvector expressions of same size.
--
mkBVSge :: Context -> Expr -> Expr -> IO Expr
mkBVSge c e1 e2 = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_sbvGeExpr cptr (unExpr e1) (unExpr e2)

------------------------------------------------------------------------
-- Bit-wise operations

-- | Bitwise @and@.
--
-- /a1/ and /a2/ must be bitvector expressions of same size.
--
mkBVAnd :: Context -> Expr -> Expr -> IO Expr
mkBVAnd c e1 e2 = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_bvAndExpr cptr (unExpr e1) (unExpr e2)

-- | Bitwise @or@.
--
-- /a1/ and /a2/ must be bitvector expressions of same size.
--
mkBVOr :: Context -> Expr -> Expr -> IO Expr
mkBVOr c e1 e2 = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_bvOrExpr cptr (unExpr e1) (unExpr e2)

-- | Bitwise @xor@.
--
-- /a1/ and /a2/ must be bitvector expressions of same size.
--
mkBVXor :: Context -> Expr -> Expr -> IO Expr
mkBVXor c e1 e2 = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_bvXorExpr cptr (unExpr e1) (unExpr e2)

-- | Bitwise negation.
--
mkBVNot :: Context -> Expr -> IO Expr
mkBVNot c e = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_bvNotExpr cptr (unExpr e)

------------------------------------------------------------------------
-- Bit-vector shifting and signs

-- | Sign extension.
--
-- Append /n/ times the most-significant bit of to the left of /a/.
--
mkBVSignExtend :: Context -> Expr -> Int -> IO Expr
mkBVSignExtend c e n = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_bvSignExtend cptr (unExpr e) (fromIntegral n)

-- | Left shift by n bits, padding with zeros.
--
mkBVShiftLeft :: Context -> Expr -> Int -> IO Expr
mkBVShiftLeft c e n = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_bvLeftShiftExpr cptr (fromIntegral n) (unExpr e)


-- | Right shift by n bits, padding with zeros.
--
mkBVShiftRight :: Context -> Expr -> Int -> IO Expr
mkBVShiftRight c e n = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_bvRightShiftExpr cptr (fromIntegral n) (unExpr e)

-- | Dynamic shift operations
mkBVShiftLeftExpr :: Context -> Int -> Expr -> Expr -> IO Expr
mkBVShiftLeftExpr c n e1 e2 = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_bvLeftShiftExprExpr cptr (fromIntegral n) (unExpr e1) (unExpr e2)

mkBVShiftRightExpr :: Context -> Int -> Expr -> Expr -> IO Expr
mkBVShiftRightExpr c n e1 e2 = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_bvRightShiftExprExpr cptr (fromIntegral n) (unExpr e1) (unExpr e2)

mkBVSignedShiftRightExpr :: Context -> Int -> Expr -> Expr -> IO Expr
mkBVSignedShiftRightExpr c n e1 e2 = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_bvSignedRightShiftExprExpr cptr (fromIntegral n) (unExpr e1) (unExpr e2)

------------------------------------------------------------------------
-- Bit vector strings

-- | Bitvector concatenation.
--
-- @a1@ and @a2@ must be two bitvector expressions.
-- @a1@ is the left part of the result and @a2@ the right part.
--
-- Assuming /a1/ and /a2/ have /n1/ and /n2/ bits, respectively, then the
-- result is a bitvector concat of size /n1 + n2/. Bit 0 of concat is bit 0 of
-- /a2/ and bit n2 of concat is bit 0 of /a1/.
--
mkBVConcat :: Context -> Expr -> Expr -> IO Expr
mkBVConcat c e1 e2 = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_bvConcatExpr cptr (unExpr e1) (unExpr e2)

-- | Bitvector extraction.
--
-- The first @Int@ argument is the initial index, the second is the end index.
-- /Note/: this is reversed wrt. the C API.
--
-- /a/ must a bitvector expression of size /n/ with @begin < end < n@.
-- The result is the subvector slice @a[begin .. end]@.
--
mkBVExtract :: Context -> Int -> Int -> Expr -> IO Expr
mkBVExtract c begin end e = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_bvExtract cptr (unExpr e)
                 (fromIntegral end) (fromIntegral begin)

-- | Bitvector extraction to Boolean result
--
-- > x[bit_no:bit_no] == 1
--
mkBVBoolExtract :: Context -> Int -> Expr -> IO Expr
mkBVBoolExtract c idx e = withForeignPtr (sContext c) $ \cptr ->
    Expr <$> vc_bvBoolExtract_One cptr (unExpr e) (fromIntegral idx)

------------------------------------------------------------------------

deleteExpr :: Expr -> IO ()
deleteExpr = vc_DeleteExpr . unExpr

deleteExprs :: [Expr] -> IO ()
deleteExprs = mapM_ deleteExpr


setFlag :: Ptr SContext -> Char -> IO ()
setFlag c f = vc_setFlag c (castCharToCChar f)
