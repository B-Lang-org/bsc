{-# LANGUAGE ForeignFunctionInterface   #-}
{-# LANGUAGE EmptyDataDecls             #-}
-- LANGUAGE GeneralizedNewtypeDeriving

module STPFFI (

    -- * C types
    SContext,
    SType,
    SExpr,

    -- * Context manipulation
    vc_createValidityChecker,
    vc_Destroy,
    vc_DeleteExpr,
    vc_DeleteExprFun,

    vc_push,
    vc_pop,

    -- * Debug
    vc_printVarDecls,
    vc_printAsserts,
    vc_printQuery,
    vc_clearDecls,
    vc_printExpr,
    --vc_exprString,
    --vc_typeString,
    vc_setFlag,

    -- * Assertions
    vc_assertFormula,

    -- * Solving
    vc_query,
    vc_query_with_timeout,
    vc_isBool,

    -- * Types
    vc_boolType,
    vc_bvType,

    -- * Expressions

    -- ** Type conversion
    vc_boolToBVExpr,

    -- ** Variables
    vc_varExpr,

    -- ** Constants
    vc_trueExpr,
    vc_falseExpr,
    vc_bvConstExprFromDecStr,
    vc_bvConstExprFromStr,
    --vc_bvConstExprFromInt,
    vc_bvConstExprFromLL,

    -- ** Logical operators
    vc_eqExpr,
    vc_notExpr,
    vc_andExpr,
    vc_andExprN,
    vc_orExpr,
    vc_orExprN,
    vc_xorExpr,
    vc_impliesExpr,
    vc_iffExpr,
    vc_iteExpr,

    -- ** Bit vector arithmetic
    vc_bvPlusExpr,
    vc_bvPlusExprN,
    vc_bvMinusExpr,
    vc_bvMultExpr,
    vc_bvDivExpr,
    vc_bvModExpr,
    vc_sbvDivExpr,
    vc_sbvModExpr,

    vc_bvUMinusExpr,

    -- ** Comparisons
    vc_bvLtExpr,
    vc_bvLeExpr,
    vc_bvGtExpr,
    vc_bvGeExpr,

    vc_sbvLtExpr,
    vc_sbvLeExpr,
    vc_sbvGtExpr,
    vc_sbvGeExpr,

    -- ** Bitwise operations
    vc_bvAndExpr,
    vc_bvOrExpr,
    vc_bvXorExpr,
    vc_bvNotExpr,

    -- ** Shifting and signs
    vc_bvSignExtend,
    vc_bvLeftShiftExpr,
    vc_bvRightShiftExpr,

    vc_bvLeftShiftExprExpr,
    vc_bvRightShiftExprExpr,
    vc_bvSignedRightShiftExprExpr,

    -- ** Bit vector /string/ operations
    vc_bvConcatExpr,
    vc_bvExtract,
    vc_bvBoolExtract_Zero,
    vc_bvBoolExtract_One,

    make_division_total,

    ) where

import Foreign
import Foreign.C.Types
import Foreign.C.String

------------------------------------------------------------------------
-- Types

-- | Abstract type representing an STP context.
--
data SContext

-- | Abstract type representing an STP expression.
--
data SExpr

-- | Abstract type representing an STP type.
--
data SType

------------------------------------------------------------------------
-- Function bindings

-- Contexts

foreign import ccall unsafe "stp_c_interface.h"
    vc_createValidityChecker  :: IO (Ptr SContext)

foreign import ccall unsafe "stp_c_interface.h"
    vc_Destroy :: Ptr SContext -> IO ()

foreign import ccall unsafe "stp_c_interface.h"
    vc_DeleteExpr :: Ptr SExpr -> IO ()

-- Function pointer
foreign import ccall unsafe "stp_c_interface.h &vc_DeleteExpr"
    vc_DeleteExprFun :: FunPtr (Ptr SExpr -> IO ())

foreign import ccall unsafe "stp_c_interface.h"
    vc_push :: Ptr SContext -> IO ()

foreign import ccall unsafe "stp_c_interface.h"
    vc_pop :: Ptr SContext -> IO ()

-- Debug

foreign import ccall unsafe "stp_c_interface.h"
    vc_printVarDecls :: Ptr SContext -> IO ()

foreign import ccall unsafe "stp_c_interface.h"
    vc_printAsserts :: Ptr SContext -> IO ()

foreign import ccall unsafe "stp_c_interface.h"
    vc_printQuery :: Ptr SContext -> IO ()

foreign import ccall unsafe "stp_c_interface.h"
    vc_clearDecls :: Ptr SContext -> IO ()

foreign import ccall unsafe "stp_c_interface.h"
    vc_printExpr :: Ptr SContext -> Ptr SExpr -> IO ()

-- Assertions

foreign import ccall unsafe "stp_c_interface.h"
    vc_assertFormula :: Ptr SContext -> Ptr SExpr -> IO ()

-- Solving

foreign import ccall unsafe "stp_c_interface.h"
    vc_query :: Ptr SContext -> Ptr SExpr -> IO CInt

foreign import ccall unsafe "stp_c_interface.h"
    vc_query_with_timeout :: Ptr SContext -> Ptr SExpr -> CInt -> IO CInt

foreign import ccall unsafe "stp_c_interface.h"
    vc_isBool :: Ptr SExpr -> IO CInt

-- Types

foreign import ccall unsafe "stp_c_interface.h"
    vc_boolType :: Ptr SContext -> IO (Ptr SType)

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvType :: Ptr SContext -> CInt -> IO (Ptr SType)

-- Type conversion

foreign import ccall unsafe "stp_c_interface.h"
    vc_boolToBVExpr :: Ptr SContext -> Ptr SExpr -> IO (Ptr SExpr)

-- Variables

foreign import ccall unsafe "stp_c_interface.h"
    vc_varExpr :: Ptr SContext -> CString -> Ptr SType -> IO (Ptr SExpr)

-- Constants

foreign import ccall unsafe "stp_c_interface.h"
    vc_trueExpr :: Ptr SContext -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_falseExpr :: Ptr SContext -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvConstExprFromDecStr :: Ptr SContext -> CString -> Ptr SType -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvConstExprFromStr :: Ptr SContext -> CString -> IO (Ptr SExpr)

{-
-- This merely casts the value to CULLong, so might as well always call
-- vc_bvConstExprFromLL instead. 
foreign import ccall unsafe "stp_c_interface.h"
    vc_bvConstExprFromInt :: Ptr SContext -> CInt -> CUInt -> IO (Ptr SExpr)
-}

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvConstExprFromLL :: Ptr SContext -> CInt -> CULLong -> IO (Ptr SExpr)

-- Logical operations

foreign import ccall unsafe "stp_c_interface.h"
    vc_eqExpr :: Ptr SContext -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_notExpr :: Ptr SContext -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_andExpr :: Ptr SContext -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_andExprN :: Ptr SContext -> Ptr (Ptr SExpr) -> CInt -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_orExpr :: Ptr SContext -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_orExprN :: Ptr SContext -> Ptr (Ptr SExpr) -> CInt -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_xorExpr :: Ptr SContext -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_impliesExpr :: Ptr SContext -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_iffExpr :: Ptr SContext -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_iteExpr :: Ptr SContext -> Ptr SExpr -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

-- Bit vector arithmetic

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvPlusExpr :: Ptr SContext -> CInt -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvPlusExprN :: Ptr SContext -> CInt -> Ptr (Ptr SExpr) -> CInt -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvMinusExpr :: Ptr SContext -> CInt -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvMultExpr :: Ptr SContext -> CInt -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvDivExpr :: Ptr SContext -> CInt -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvModExpr :: Ptr SContext -> CInt -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_sbvDivExpr :: Ptr SContext -> CInt -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_sbvModExpr :: Ptr SContext -> CInt -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvUMinusExpr :: Ptr SContext -> Ptr SExpr -> IO (Ptr SExpr)

-- Comparisons

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvLtExpr :: Ptr SContext -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvLeExpr :: Ptr SContext -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvGtExpr :: Ptr SContext -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvGeExpr :: Ptr SContext -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_sbvLtExpr :: Ptr SContext -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_sbvLeExpr :: Ptr SContext -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_sbvGtExpr :: Ptr SContext -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_sbvGeExpr :: Ptr SContext -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

-- Bitwise Operations

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvAndExpr :: Ptr SContext -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvOrExpr :: Ptr SContext -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvXorExpr :: Ptr SContext -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvNotExpr :: Ptr SContext -> Ptr SExpr -> IO (Ptr SExpr)

-- Shifting and signs

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvSignExtend :: Ptr SContext -> Ptr SExpr -> CInt -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvLeftShiftExpr :: Ptr SContext -> CInt -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvRightShiftExpr :: Ptr SContext -> CInt -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvLeftShiftExprExpr :: Ptr SContext -> CInt -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvRightShiftExprExpr :: Ptr SContext -> CInt -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvSignedRightShiftExprExpr :: Ptr SContext -> CInt -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)


-- Bit vector /string/ operations

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvConcatExpr :: Ptr SContext -> Ptr SExpr -> Ptr SExpr -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvExtract :: Ptr SContext -> Ptr SExpr -> CInt -> CInt -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvBoolExtract_Zero :: Ptr SContext -> Ptr SExpr -> CInt -> IO (Ptr SExpr)

foreign import ccall unsafe "stp_c_interface.h"
    vc_bvBoolExtract_One :: Ptr SContext -> Ptr SExpr -> CInt -> IO (Ptr SExpr)

-- configure and misc features
foreign import ccall unsafe "stp_c_interface.h"
  make_division_total :: Ptr SContext -> IO ()

foreign import ccall unsafe "stp_c_interface.h"
  vc_setFlag :: Ptr SContext -> CChar -> IO ()
