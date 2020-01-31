{-# LANGUAGE ForeignFunctionInterface   #-}
{-# LANGUAGE EmptyDataDecls             #-}

module YicesFFI (

    -- * C types
    YExpr,
    YType,
    YContext,
    YStatus,
    YModel,
    YContextConfig,
    YParams,

    YErrorCode,
    -- YErrorReport,

    -- * Version numbers
    yices_version,
    yices_build_arch,
    yices_build_mode,
    yices_build_date,

    -- yices_has_mcsat,
    -- yices_is_thread_safe,

    -- * Global initialization and cleanup
    yices_init,
    yices_exit,
    yices_reset,

    -- yices_free_string,

    -- * Out-of-memory callback
    -- yices_set_out_ot_mem_callback,

    -- * Error reporting
    yices_error_code,
    -- yices_error_report,
    -- yices_clear_error,
    -- yices_print_error,
    -- yices_print_error_fd,
    -- yices_error_string,

    -- * Vectors of terms and types
    -- yices_init_term_vector,
    -- yices_init_type_vector,
    -- yices_delete_term_vector,
    -- yices_delete_type_vector,
    -- yices_reset_term_vector,
    -- yices_reset_type_vector,

    -- * Type constructors
    yices_bool_type,
    yices_bv_type,
    yices_int_type,
    -- yices_real_type,
    -- yices_new_scalar_type,
    -- yices_new_uninterpreted_type,
    -- yices_tuple_type,
    -- yices_tuple_type1,
    -- yices_tuple_type2,
    -- yices_tuple_type3,
    -- yices_function_type,
    -- yices_function_type1,
    -- yices_function_type2,
    -- yices_function_type3,

    -- * Type exploration
    -- yices_type_is_bool,
    -- yices_type_is_int,
    -- yices_type_is_real,
    -- yices_type_is_arithmetic,
    -- yices_type_is_bitvector,
    -- yices_type_is_tuple,
    -- yices_type_is_function,
    -- yices_type_is_scalar,
    -- yices_type_is_uninterpreted,
    -- yices_test_subtype,
    -- yices_compatible_types,
    -- yices_bvtype_size,
    -- yices_scalar_type_card,
    -- yices_type_num_children,
    -- yices_type_child,
    -- yices_type_children,

    -- * Term constructors
    yices_true,
    yices_false,

    yices_constant,
    yices_new_uninterpreted_term,
    yices_new_variable,
    -- yices_application,
    -- yices_application1,
    -- yices_application2,
    -- yices_application3,

    yices_ite,
    yices_eq,
    yices_neq,
    yices_not,

    yices_or,
    yices_and,
    yices_xor,

    yices_or2,
    yices_and2,
    yices_xor2,

    -- yices_or3,
    -- yices_and3,
    -- yices_xor3,

    yices_iff,
    yices_implies,

    -- yices_tuple,
    -- yices_pair,
    -- yices_triple,
    -- yices_select,
    -- yices_tuple_update

    -- yices_update,
    -- yices_update1,
    -- yices_update2,
    -- yices_update3,

    yices_distinct,

    yices_forall,
    yices_exists,

    -- yices_lambda,

    -- * Arithmetic term constructors
    yices_zero,
    yices_int32,
    yices_int64,
    -- yices_rational32,
    -- yices_rational64,
    -- yices_mpz,
    -- yices_mpq,
    -- yices_parse_rational,
    -- yices_parse_float,

    yices_add,
    yices_sub,
    yices_neg,
    yices_mul,
    yices_square,
    yices_power,

    -- yices_abs,
    -- yices_floor,
    -- yices_ceil,

    -- yices_poly_int32,
    -- yices_poly_int64,
    -- yices_poly_rational32,
    -- yices_poly_rational64
    -- yices_poly_mpz,
    -- yices_poly_mpq,

    yices_arith_eq_atom,
    yices_arith_neq_atom,
    yices_arith_geq_atom,
    yices_arith_leq_atom,
    yices_arith_gt_atom,
    yices_arith_lt_atom,

    yices_arith_eq0_atom,
    yices_arith_neq0_atom,
    yices_arith_geq0_atom,
    yices_arith_leq0_atom,
    yices_arith_gt0_atom,
    yices_arith_lt0_atom,

    -- * Bit vector term constructors
    yices_bvconst_uint32,
    yices_bvconst_uint64,
    -- yices_bvconst_int32,
    -- yices_bvconst_int64,
    -- yices_bvconst_mpz,

    yices_bvconst_zero,
    yices_bvconst_one,
    yices_bvconst_minus_one,

    -- yices_bvconst_from_array,
    yices_parse_bvbin,
    yices_parse_bvhex,

    yices_bvadd,
    yices_bvsub,
    yices_bvneg,
    yices_bvmul,
    -- yices_bvsquare,
    -- yices_bvpower,
    yices_bvdiv,
    yices_bvrem,
    -- yices_bvsdiv,
    -- yices_bvsrem,
    -- yices_bvsmod,

    yices_bvnot,
    yices_bvnand,
    yices_bvnor,
    yices_bvxnor,

    yices_bvshl,
    yices_bvlshr,
    yices_bvashr,

    -- yices_bvand,
    -- yices_bvor,
    -- yices_bvxor,

    yices_bvand2,
    yices_bvor2,
    yices_bvxor2,

    -- yices_bvand3,
    -- yices_bvor3,
    -- yices_bvxor3,

    -- yices_bvsum,
    -- yices_bvproduct,

    -- yices_shift_left0,
    -- yices_shift_left1,
    -- yices_shift_right0,
    -- yices_shift_right1,
    -- yices_ashift_right,
    -- yices_rotate_left,
    -- yices_rotate_right,

    yices_bvextract,
    yices_bvconcat2,
    -- yices_bvconcat,
    -- yices_bvrepeat,
    yices_sign_extend,
    yices_zero_extend,

    yices_redand,
    yices_redor,
    yices_redcomp,

    yices_bvarray,  -- convert Bools to an array
    yices_bitextract,  -- get a Bool from an array

    yices_bveq_atom,
    yices_bvneq_atom,

    yices_bvge_atom,
    yices_bvgt_atom,
    yices_bvle_atom,
    yices_bvlt_atom,

    yices_bvsge_atom,
    yices_bvsgt_atom,
    yices_bvsle_atom,
    yices_bvslt_atom,

    {-
    -- * Parsing
    yices_parse_type,
    yices_parse_term,

    -- * Substitutions
    yices_subst_term,
    yices_subst_term_array,

    -- * Names
    yices_set_type_name,
    yices_set_term_name,
    yices_remove_type_name,
    yices_remove_term_name,
    yices_get_type_by_name,
    yices_get_term_by_name,
    yices_clear_type_name,
    yices_clear_term_name,
    yices_get_type_name,
    yices_get_term_name,
    -}

    -- * Checks on terms
    yices_type_of_term,
    yices_term_is_bool,
    yices_term_is_bitvector,
    -- yices_term_is_int,
    -- yices_term_is_real,
    -- yices_term_is_arithmetic,
    -- yices_term_is_tuple,
    -- yices_term_is_function,
    -- yices_term_is_scalar,
    yices_term_bitsize,
    -- yices_term_is_ground,
    -- yices_term_is_atomic,
    -- yices_term_is_composite,
    -- yices_term_is_projection,
    -- yices_term_is_sum,
    -- yices_term_is_bvsum,
    -- yices_term_is_product,
    -- yices_term_constructor,
    -- yices_term_num_children,
    -- yices_term_child,
    -- yices_proj_index,
    -- yices_proj_arg,
    -- yices_bool_const_value,
    -- yices_bv_const_value,
    -- yices_scalar_const_value,
    -- yices_rational_const_value,
    -- yices_sum_component,
    -- yices_bvsum_component,
    -- yices_product_component,

    -- * Garbage collection
    -- yices_num_terms,
    -- yices_num_types,
    -- yices_incref_term,
    -- yices_decref_term,
    -- yices_incref_type,
    -- yices_decref_type,
    -- yices_num_posref_terms,
    -- yices_num_posref_types,
    -- yices_garbage_collect,

    -- * Context configuration
    yices_new_config,
    yices_free_config,
    yices_set_config,
    yices_default_config_for_logic,

    -- * Contexts
    yices_new_context,
    yices_free_context,
    yices_context_status,
    yices_reset_context,
    yices_push,
    yices_pop,
    -- yices_context_enable_option,
    -- yices_context_disable_option,

    yices_assert_formula,
    yices_assert_formulas,
    yices_check_context,
    -- yices_check_context_with_assumptions,
    -- yices_assert_blocking_clause,
    -- yices_stop_search,

    -- * Search parameters
    yices_new_param_record,
    -- yices_default_params_for_context,
    yices_set_param,
    yices_free_param_record,

    -- * Unsat core
    -- yices_get_unsat_core

    -- * Models
    yices_get_model,
    yices_free_model,
    -- yices_model_from_map,
    -- yices_model_collect_defined_terms,

    -- * Values in a model
    yices_get_bool_value,
    -- yices_get_int32_value,
    -- yices_get_int64_value,
    -- yices_get_rational32_value,
    -- yices_get_rational64_value,
    -- yices_get_double_value,
    -- yices_get_mpz_value,
    -- yices_get_mpq_value,
    -- yices_get_algebraic_number_value,
    yices_get_bv_value,
    -- yices_get_scalar_value,

    -- * Generic form: Value descriptors and nodes
    -- ...

    -- * Check the value of boolean formulas
    -- ...

    -- * Conversion of values to constant terms
    -- ...

    -- * Implicants
    -- ...

    -- * Model generalization
    -- ...

    -- * Pretty printing
    yices_pp_type,
    yices_pp_term,
    -- yices_pp_term_array,
    yices_print_model
    -- yices_pp_model

    -- yices_pp_type_fd,
    -- yices_pp_term_fd,
    -- yices_pp_term_array_fd,
    -- yices_print_model_fd,
    -- yices_pp_model_fd

    -- yices_type_to_string,
    -- yices_term_to_string,
    -- yices_model_to_string

    ) where

import Foreign
import Foreign.C.Types
import Foreign.C.String

------------------------------------------------------------------------
-- C Types

-- Abstract type representing a Yices term (term_t)
-- XXX actually, since we need to check for NULL_TERM as a return value,
-- XXX we expose that it's int32
type YExpr = CInt

-- Abstract type representing a Yices type (type_t)
-- XXX actually, since we need to check for NULL_TYPE as a return value,
-- XXX we expose that it's int32
type YType = CInt

-- Abstract type representing a Yices context (context_t)
data YContext

-- Low level type for context status code (smt_status_t)
type YStatus = CInt

-- Abstract type representing a Yices model (model_t)
data YModel

-- Abstract type representing a Yices context configuration (ctx_config_t)
data YContextConfig

-- Abstract type representing a Yices search parameters (param_t)
data YParams

-- Type for Yices error codes
type YErrorCode = CUInt

------------------------------------------------------------------------
-- Version numbers

-- versions are (const char *),  not a C function call
foreign import ccall "yices.h &yices_version"
    yices_version ::  Ptr CString

foreign import ccall unsafe "yices.h &yices_build_arch"
    yices_build_arch :: Ptr CString

foreign import ccall unsafe "yices.h &yices_build_mode"
    yices_build_mode :: Ptr CString

foreign import ccall unsafe "yices.h &yices_build_date"
    yices_build_date :: Ptr CString

------------------------------------------------------------------------
-- Global initialization and cleanup

foreign import ccall unsafe "yices.h"
    yices_init :: IO ()

foreign import ccall unsafe "yices.h"
    yices_exit :: IO ()

foreign import ccall unsafe "yices.h"
    yices_reset :: IO ()

-- ...

------------------------------------------------------------------------
-- Error reporting

foreign import ccall unsafe "yices.h"
    yices_error_code :: IO YErrorCode

-- ...

------------------------------------------------------------------------
-- Type constructors

foreign import ccall unsafe "yices.h"
    yices_bool_type :: IO YType

foreign import ccall unsafe "yices.h"
    yices_bv_type :: CUInt -> IO YType

foreign import ccall unsafe "yices.h"
    yices_int_type :: IO YType

-- ...

------------------------------------------------------------------------
-- Term constructors

foreign import ccall unsafe "yices.h"
    yices_true :: IO YExpr

foreign import ccall unsafe "yices.h"
    yices_false :: IO YExpr

foreign import ccall unsafe "yices.h"
    yices_constant :: YType -> CInt -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_new_uninterpreted_term :: YType -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_new_variable :: YType -> IO YExpr

-- ...

foreign import ccall unsafe "yices.h"
    yices_ite :: YExpr -> YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_eq :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_neq :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_not :: YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_or :: CUInt -> Ptr YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_and :: CUInt -> Ptr YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_xor :: CUInt -> Ptr YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_or2 :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_and2 :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_xor2 :: YExpr -> YExpr -> IO YExpr

-- ...

foreign import ccall unsafe "yices.h"
    yices_iff :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_implies :: YExpr -> YExpr -> IO YExpr

-- ...

foreign import ccall unsafe "yices.h"
    yices_distinct :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_forall :: CUInt -> Ptr YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_exists :: CUInt -> Ptr YExpr -> YExpr -> IO YExpr

-- ...

------------------------------------------------------------------------
-- Arithmetic term constructors

foreign import ccall unsafe "yices.h"
    yices_zero :: IO YExpr

foreign import ccall unsafe "yices.h"
    yices_int32 :: CInt -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_int64 :: CLLong -> IO YExpr

-- ...

foreign import ccall unsafe "yices.h"
    yices_add :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_sub :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_neg :: YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_mul :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_square :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_power :: YExpr -> CUInt -> IO YExpr

-- ...

foreign import ccall unsafe "yices.h"
    yices_arith_eq_atom :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_arith_neq_atom :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_arith_geq_atom :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_arith_leq_atom :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_arith_gt_atom :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_arith_lt_atom :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_arith_eq0_atom :: YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_arith_neq0_atom :: YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_arith_geq0_atom :: YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_arith_leq0_atom :: YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_arith_gt0_atom :: YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_arith_lt0_atom :: YExpr -> IO YExpr

------------------------------------------------------------------------
-- Bit vector term constructors

foreign import ccall unsafe "yices.h"
    yices_bvconst_uint32 :: CUInt -> CUInt -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvconst_uint64 :: CUInt -> CULLong -> IO YExpr

-- ...

foreign import ccall unsafe "yices.h"
    yices_bvconst_zero :: CUInt -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvconst_one :: CUInt -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvconst_minus_one :: CUInt -> IO YExpr

-- ...

foreign import ccall unsafe "yices.h"
    yices_parse_bvbin :: CString -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_parse_bvhex :: CString -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvadd :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvsub :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvneg :: YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvmul :: YExpr -> YExpr -> IO YExpr

-- ...

foreign import ccall unsafe "yices.h"
    yices_bvdiv :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvrem :: YExpr -> YExpr -> IO YExpr

-- ...

foreign import ccall unsafe "yices.h"
    yices_bvnot :: YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvnand :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvnor :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvxnor :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvshl :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvlshr :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvashr :: YExpr -> YExpr -> IO YExpr

-- ...

foreign import ccall unsafe "yices.h"
    yices_bvand2 :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvor2 :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvxor2 :: YExpr -> YExpr -> IO YExpr

-- ...

foreign import ccall unsafe "yices.h"
    yices_bvextract :: YExpr -> CUInt -> CUInt -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvconcat2 :: YExpr -> YExpr -> IO YExpr

-- ...

foreign import ccall unsafe "yices.h"
    yices_sign_extend :: YExpr -> CUInt -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_zero_extend :: YExpr -> CUInt -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_redand :: YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_redor :: YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_redcomp :: YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvarray :: CUInt -> Ptr YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bitextract :: YExpr -> CUInt -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bveq_atom :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvneq_atom :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvge_atom :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvgt_atom :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvle_atom :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvlt_atom :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvsge_atom :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvsgt_atom :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvsle_atom :: YExpr -> YExpr -> IO YExpr

foreign import ccall unsafe "yices.h"
    yices_bvslt_atom :: YExpr -> YExpr -> IO YExpr

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
-- Checks on terms

foreign import ccall unsafe "yices.h"
    yices_type_of_term :: YExpr -> IO YType

foreign import ccall unsafe "yices.h"
    yices_term_is_bool :: YExpr -> IO CInt

foreign import ccall unsafe "yices.h"
    yices_term_is_bitvector :: YExpr -> IO CInt

-- ...

foreign import ccall unsafe "yices.h"
    yices_term_bitsize :: YExpr -> IO CUInt

-- ...

------------------------------------------------------------------------
-- Garbage collection

-- ...

------------------------------------------------------------------------
-- Context configuration

foreign import ccall unsafe "yices.h"
    yices_new_config :: IO (Ptr YContextConfig)

foreign import ccall unsafe "yices.h"
    yices_free_config :: Ptr YContextConfig -> IO ()

foreign import ccall unsafe "yices.h"
    yices_set_config :: Ptr YContextConfig -> CString -> CString -> IO CInt

foreign import ccall unsafe "yices.h"
    yices_default_config_for_logic :: Ptr YContextConfig -> CString -> IO CInt

------------------------------------------------------------------------
-- Contexts

foreign import ccall unsafe "yices.h"
    yices_new_context  :: Ptr YContextConfig -> IO (Ptr YContext)

foreign import ccall unsafe "yices.h"
    yices_free_context :: Ptr YContext -> IO ()

foreign import ccall unsafe "yices.h"
    yices_context_status :: Ptr YContext -> IO YStatus

foreign import ccall unsafe "yices.h"
    yices_reset_context :: Ptr YContext -> IO ()

foreign import ccall unsafe "yices.h"
    yices_push :: Ptr YContext -> IO CInt

foreign import ccall unsafe "yices.h"
    yices_pop :: Ptr YContext -> IO CInt

-- ...

foreign import ccall unsafe "yices.h"
    yices_assert_formula :: Ptr YContext -> YExpr -> IO CInt

foreign import ccall unsafe "yices.h"
    yices_assert_formulas :: Ptr YContext -> CUInt -> Ptr YExpr -> IO CInt

foreign import ccall unsafe "yices.h"
    yices_check_context :: Ptr YContext -> Ptr YParams -> IO YStatus

------------------------------------------------------------------------
-- Search parameters

foreign import ccall unsafe "yices.h"
    yices_new_param_record :: IO (Ptr YParams)

-- ...

foreign import ccall unsafe "yices.h"
    yices_set_param :: Ptr YParams -> CString -> CString -> IO CInt

foreign import ccall unsafe "yices.h"
    yices_free_param_record :: Ptr YParams -> IO ()

------------------------------------------------------------------------
-- Unsat core

-- ...

------------------------------------------------------------------------
-- Models

foreign import ccall unsafe "yices.h"
    yices_get_model :: Ptr YContext -> CInt -> IO (Ptr YModel)

foreign import ccall unsafe "yices.h"
    yices_free_model :: Ptr YModel -> IO ()

-- ...

------------------------------------------------------------------------
-- Values in a model

foreign import ccall unsafe "yices.h"
    yices_get_bool_value :: Ptr YModel -> YExpr -> Ptr CInt -> IO CInt

-- ...

foreign import ccall unsafe "yices.h"
    yices_get_bv_value :: Ptr YModel -> YExpr -> Ptr CInt -> IO CInt

-- ...

------------------------------------------------------------------------
-- Generic form: Value descriptors and nodes

-- ...

------------------------------------------------------------------------
-- Check the value of boolean formulas

-- ...

------------------------------------------------------------------------
-- Conversion of values to constant terms

-- ...

------------------------------------------------------------------------
-- Implicants

-- ...

------------------------------------------------------------------------
-- Model generalization

-- ...

------------------------------------------------------------------------
-- Pretty printing

foreign import ccall unsafe "yices.h"
    yices_pp_type :: Ptr CFile -> YType -> CUInt -> CUInt -> CUInt -> IO CInt

foreign import ccall unsafe "yices.h"
    yices_pp_term :: Ptr CFile -> YExpr -> CUInt -> CUInt -> CUInt -> IO CInt

-- ...

foreign import ccall unsafe "yices.h"
    yices_print_model :: Ptr CFile -> Ptr YModel -> IO ()

-- ...

------------------------------------------------------------------------

