#include "yices.h"

const char *yices_version = "stub";

const char *yices_build_arch = "";
const char *yices_build_mode = "";
const char *yices_build_date = "";

void yices_init(void) { }

void yices_exit(void) { }

void yices_reset(void) { }

error_code_t yices_error_code(void) { return NO_ERROR; }

error_report_t *yices_error_report(void) { return 0; }

void yices_clear_error(void) { }

int32_t yices_print_error(FILE *f) { return 0; }

type_t yices_bool_type(void) { return 0; }
type_t yices_int_type(void) { return 0; }
type_t yices_real_type(void) { return 0; }

type_t yices_bv_type(uint32_t size) { return 0; }

type_t yices_new_scalar_type(uint32_t card) { return 0; }

type_t yices_new_uninterpreted_type(void) { return 0; }

type_t yices_tuple_type(uint32_t n, const type_t tau[]) { return 0; }

type_t yices_function_type(uint32_t n, const type_t dom[], type_t range) { return 0; }

term_t yices_true(void) { return 0; }
term_t yices_false(void) { return 0; }

term_t yices_constant(type_t tau, int32_t index) { return 0; }

term_t yices_new_uninterpreted_term(type_t tau) { return 0; }

term_t yices_new_variable(type_t tau) { return 0; }

term_t yices_application(term_t fun, uint32_t n, const term_t arg[]) { return 0; }

term_t yices_ite(term_t cond, term_t then_term, term_t else_term) { return 0; }

term_t yices_eq(term_t left, term_t right) { return 0; }
term_t yices_neq(term_t left, term_t right) { return 0; }

term_t yices_not(term_t arg) { return 0; }

term_t yices_or(uint32_t n, term_t arg[]) { return 0; }
term_t yices_and(uint32_t n, term_t arg[]) { return 0; }
term_t yices_xor(uint32_t n, term_t arg[]) { return 0; }

term_t yices_or2(term_t t1, term_t t2) { return 0; }
term_t yices_and2(term_t t1, term_t t2) { return 0; }
term_t yices_xor2(term_t t1, term_t t2) { return 0; }

term_t yices_or3(term_t t1, term_t t2, term_t t3) { return 0; }
term_t yices_and3(term_t t1, term_t t2, term_t t3) { return 0; }
term_t yices_xor3(term_t t1, term_t t2, term_t t3) { return 0; }

term_t yices_iff(term_t left, term_t right) { return 0; }
term_t yices_implies(term_t left, term_t right) { return 0; }

term_t yices_tuple(uint32_t n, const term_t arg[]) { return 0; }

term_t yices_select(uint32_t index, term_t tuple) { return 0; }

term_t yices_tuple_update(term_t tuple, uint32_t index, term_t new_v) { return 0; }

term_t yices_update(term_t fun, uint32_t n, const term_t arg[], term_t new_v) { return 0; }

term_t yices_distinct(uint32_t n, term_t arg[]) { return 0; }

term_t yices_forall(uint32_t n, term_t var[], term_t body) { return 0; }
term_t yices_exists(uint32_t n, term_t var[], term_t body) { return 0; }

term_t yices_zero(void) { return 0; }

term_t yices_int32(int32_t val) { return 0; }
term_t yices_int64(int64_t val) { return 0; }

term_t yices_rational32(int32_t num, uint32_t den) { return 0; }
term_t yices_rational64(int64_t num, uint64_t den) { return 0; }

#ifdef __GMP_H__
term_t yices_mpz(mpz_t z) { return 0; }
term_t yices_mpq(mpq_t q) { return 0; }
#endif

term_t yices_parse_rational(const char *s) { return 0; }

term_t yices_parse_float(const char *s) { return 0; }

term_t yices_add(term_t t1, term_t t2) { return 0; }
term_t yices_sub(term_t t1, term_t t2) { return 0; }
term_t yices_neg(term_t t1) { return 0; }
term_t yices_mul(term_t t1, term_t t2) { return 0; }
term_t yices_square(term_t t1) { return 0; }
term_t yices_power(term_t t1, uint32_t d) { return 0; }

term_t yices_poly_int32(uint32_t n, const int32_t a[], const term_t t[]) { return 0; }
term_t yices_poly_int64(uint32_t n, const int64_t a[], const term_t t[]) { return 0; }

term_t yices_poly_rational32(uint32_t n, const int32_t num[], const uint32_t den[], const term_t t[]) { return 0; }
term_t yices_poly_rational64(uint32_t n, const int64_t num[], const uint64_t den[], const term_t t[]) { return 0; }

#ifdef __GMP_H__
term_t yices_poly_mpz(uint32_t n, mpz_t z[], term_t t[]) { return 0; }
term_t yices_poly_mpq(uint32_t n, mpq_t q[], term_t t[]) { return 0; }
#endif

term_t yices_arith_eq_atom(term_t t1, term_t t2) { return 0; }
term_t yices_arith_neq_atom(term_t t1, term_t t2) { return 0; }
term_t yices_arith_geq_atom(term_t t1, term_t t2) { return 0; }
term_t yices_arith_leq_atom(term_t t1, term_t t2) { return 0; }
term_t yices_arith_gt_atom(term_t t1, term_t t2)  { return 0; }
term_t yices_arith_lt_atom(term_t t1, term_t t2)  { return 0; }

term_t yices_arith_eq0_atom(term_t t) { return 0; }
term_t yices_arith_neq0_atom(term_t t) { return 0; }
term_t yices_arith_geq0_atom(term_t t) { return 0; }
term_t yices_arith_leq0_atom(term_t t) { return 0; }
term_t yices_arith_gt0_atom(term_t t) { return 0; }
term_t yices_arith_lt0_atom(term_t t) { return 0; }

term_t yices_bvconst_uint32(uint32_t n, uint32_t x) { return 0; }
term_t yices_bvconst_uint64(uint32_t n, uint64_t x) { return 0; }

#ifdef __GMP_H__
term_t yices_bvconst_mpz(uint32_t n, mpz_t x) { return 0; }
#endif

term_t yices_bvconst_zero(uint32_t n) { return 0; }
term_t yices_bvconst_one(uint32_t n) { return 0; }
term_t yices_bvconst_minus_one(uint32_t n) { return 0; }

term_t yices_bvconst_from_array(uint32_t n, const int32_t a[]) { return 0; }

term_t yices_parse_bvbin(const char *s) { return 0; }

term_t yices_parse_bvhex(const char *s) { return 0; }

term_t yices_bvadd(term_t t1, term_t t2) { return 0; }
term_t yices_bvsub(term_t t1, term_t t2) { return 0; }
term_t yices_bvneg(term_t t1) { return 0; }
term_t yices_bvmul(term_t t1, term_t t2) { return 0; }
term_t yices_bvsquare(term_t t1) { return 0; }
term_t yices_bvpower(term_t t1, uint32_t d) { return 0; }

term_t yices_bvdiv(term_t t1, term_t t2) { return 0; }
term_t yices_bvrem(term_t t1, term_t t2) { return 0; }
term_t yices_bvsdiv(term_t t1, term_t t2) { return 0; }
term_t yices_bvsrem(term_t t1, term_t t2) { return 0; }
term_t yices_bvsmod(term_t t1, term_t t2) { return 0; }

term_t yices_bvnot(term_t t1) { return 0; }
term_t yices_bvand2(term_t t1, term_t t2) { return 0; }
term_t yices_bvor2(term_t t1, term_t t2) { return 0; }
term_t yices_bvxor2(term_t t1, term_t t2) { return 0; }
term_t yices_bvnand(term_t t1, term_t t2) { return 0; }
term_t yices_bvnor(term_t t1, term_t t2) { return 0; }
term_t yices_bvxnor(term_t t1, term_t t2) { return 0; }

term_t yices_bvshl(term_t t1, term_t t2) { return 0; }
term_t yices_bvlshr(term_t t1, term_t t2) { return 0; }
term_t yices_bvashr(term_t t1, term_t t2) { return 0; }

term_t yices_shift_left0(term_t t, uint32_t n) { return 0; }
term_t yices_shift_left1(term_t t, uint32_t n) { return 0; }
term_t yices_shift_right0(term_t t, uint32_t n) { return 0; }
term_t yices_shift_right1(term_t t, uint32_t n) { return 0; }
term_t yices_ashift_right(term_t t, uint32_t n) { return 0; }
term_t yices_rotate_left(term_t t, uint32_t n) { return 0; }
term_t yices_rotate_right(term_t t, uint32_t n) { return 0; }

term_t yices_bvextract(term_t t, uint32_t i, uint32_t j) { return 0; }

term_t yices_bvconcat2(term_t t1, term_t t2) { return 0; }

term_t yices_bvrepeat(term_t t, uint32_t n) { return 0; }

term_t yices_sign_extend(term_t t, uint32_t n) { return 0; }

term_t yices_zero_extend(term_t t, uint32_t n) { return 0; }

term_t yices_redand(term_t t) { return 0; }
term_t yices_redor(term_t t) { return 0; }

term_t yices_redcomp(term_t t1, term_t t2) { return 0; }

term_t yices_bvarray(uint32_t n, const term_t arg[]) { return 0; }

term_t yices_bitextract(term_t t, uint32_t i) { return 0; }

term_t yices_bveq_atom(term_t t1, term_t t2) { return 0; }
term_t yices_bvneq_atom(term_t t1, term_t t2) { return 0; }

term_t yices_bvge_atom(term_t t1, term_t t2) { return 0; }
term_t yices_bvgt_atom(term_t t1, term_t t2) { return 0; }
term_t yices_bvle_atom(term_t t1, term_t t2) { return 0; }
term_t yices_bvlt_atom(term_t t1, term_t t2) { return 0; }

term_t yices_bvsge_atom(term_t t1, term_t t2) { return 0; }
term_t yices_bvsgt_atom(term_t t1, term_t t2) { return 0; }
term_t yices_bvsle_atom(term_t t1, term_t t2) { return 0; }
term_t yices_bvslt_atom(term_t t1, term_t t2) { return 0; }

type_t yices_parse_type(const char *s) { return 0; }
term_t yices_parse_term(const char *s) { return 0; }

term_t yices_subst_term(uint32_t n, const term_t var[], const term_t map[], term_t t) { return 0; }

int32_t yices_subst_term_array(uint32_t n, const term_t var[], const term_t map[], uint32_t m, term_t t[]) { return 0; }

int32_t yices_set_type_name(type_t tau, const char *name) { return 0; }
int32_t yices_set_term_name(term_t t, const char *name) { return 0; }

void yices_remove_type_name(const char *name) { }
void yices_remove_term_name(const char *name) { }

type_t yices_get_type_by_name(const char *name) { return 0; }
term_t yices_get_term_by_name(const char *name) { return 0; }

int32_t yices_clear_type_name(type_t tau) { return 0; }
int32_t yices_clear_term_name(term_t t) { return 0; }

int32_t yices_pp_type(FILE *f, type_t tau, uint32_t width, uint32_t height, uint32_t offset) { return 0; }
int32_t yices_pp_term(FILE *f, type_t t, uint32_t width, uint32_t height, uint32_t offset) { return 0; }

type_t yices_type_of_term(term_t t) { return 0; }

int32_t yices_term_is_bool(term_t t) { return 0; }
int32_t yices_term_is_int(term_t t) { return 0; }
int32_t yices_term_is_real(term_t t) { return 0; }
int32_t yices_term_is_arithmetic(term_t t) { return 0; }
int32_t yices_term_is_bitvector(term_t t) { return 0; }
int32_t yices_term_is_tuple(term_t t) { return 0; }
int32_t yices_term_is_function(term_t t) { return 0; }
int32_t yices_term_is_scalar(term_t t) { return 0; }

uint32_t yices_term_bitsize(term_t t) { return 0; }

ctx_config_t *yices_new_config(void) { return 0; }

void yices_free_config(ctx_config_t *config) { }

int32_t yices_set_config(ctx_config_t *config, const char *name, const char *value) { return 0; }

int32_t yices_default_config_for_logic(ctx_config_t *config, const char *logic) { return 0; }

context_t *yices_new_context(const ctx_config_t *config) { return 0; }

void yices_free_context(context_t *ctx) { }

smt_status_t yices_context_status(context_t *ctx) { return STATUS_IDLE; }

void yices_reset_context(context_t *ctx) { }

int32_t yices_push(context_t *ctx) { return 0; }

int32_t yices_pop(context_t *ctx) { return 0; }

int32_t yices_context_enable_option(context_t *ctx, const char *option) { return 0; }
int32_t yices_context_disable_option(context_t *ctx, const char *option) { return 0; }

int32_t yices_assert_formula(context_t *ctx, term_t t) { return 0; }

int32_t yices_assert_formulas(context_t *ctx, uint32_t n, const term_t t[]) { return 0; }

smt_status_t yices_check_context(context_t *ctx, const param_t *params) { return STATUS_IDLE; }

int32_t yices_assert_blocking_clause(context_t *ctx) { return 0; }

void yices_stop_search(context_t *ctx) { }

param_t *yices_new_param_record(void) { return 0; }

int32_t yices_set_param(param_t *p, const char *pname, const char *value) { return 0; }

void yices_free_param_record(param_t *param) { }

model_t *yices_get_model(context_t *ctx, int32_t keep_subst) { return 0; }

void yices_free_model(model_t *mdl) { }

void yices_print_model(FILE *f, model_t *mdl) { }

int32_t yices_get_bool_value(model_t *mdl, term_t t, int32_t *val) { return 0; }

int32_t yices_get_int32_value(model_t *mdl, term_t t, int32_t *val) { return 0; }
int32_t yices_get_int64_value(model_t *mdl, term_t t, int64_t *val) { return 0; }
int32_t yices_get_rational32_value(model_t *mdl, term_t t, int32_t *num, uint32_t *den) { return 0; }
int32_t yices_get_rational64_value(model_t *mdl, term_t t, int64_t *num, uint64_t *den) { return 0; }
int32_t yices_get_double_value(model_t *mdl, term_t t, double *val) { return 0; }

#ifdef __GMP_H__
int32_t yices_get_mpz_value(model_t *mdl, term_t t, mpz_t val) { return 0; }
int32_t yices_get_mpq_value(model_t *mdl, term_t t, mpq_t val) { return 0; }
#endif

int32_t yices_get_bv_value(model_t *mdl, term_t t, int32_t val[]) { return 0; }

int32_t yices_get_scalar_value(model_t *mdl, term_t t, int32_t *val) { return 0; }

