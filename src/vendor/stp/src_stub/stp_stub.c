#include "stp_c_interface.h"

void vc_setFlags(VC vc, char c, int num_absrefine) {
}

void vc_setFlag(VC vc, char c) {
}

void vc_setInterfaceFlags(VC vc, enum ifaceflag_t f, int param_value) {
}

void make_division_total(VC vc) {
}

VC vc_createValidityChecker(void) {
  return 0;
}

Type vc_boolType(VC vc) {
  return 0;
}

Type vc_arrayType(VC vc, Type typeIndex, Type typeData) {
  return 0;
}

Expr vc_varExpr(VC vc, const char * name, Type type) {
  return 0;
}

Expr vc_varExpr1(VC vc, const char* name,
                 int indexwidth, int valuewidth) {
  return 0;
}

Type vc_getType(VC vc, Expr e) {
  return 0;
}

int vc_getBVLength(VC vc, Expr e) {
  return 0;
}

Expr vc_eqExpr(VC vc, Expr child0, Expr child1) {
  return 0;
}

Expr vc_trueExpr(VC vc) {
  return 0;
}

Expr vc_falseExpr(VC vc) {
  return 0;
}

Expr vc_notExpr(VC vc, Expr child) {
  return 0;
}

Expr vc_andExpr(VC vc, Expr left, Expr right) {
  return 0;
}

Expr vc_andExprN(VC vc, Expr* children, int numOfChildNodes) {
  return 0;
}

Expr vc_orExpr(VC vc, Expr left, Expr right) {
  return 0;
}

Expr vc_xorExpr(VC vc, Expr left, Expr right) {
  return 0;
}

Expr vc_orExprN(VC vc, Expr* children, int numOfChildNodes) {
  return 0;
}

Expr vc_impliesExpr(VC vc, Expr hyp, Expr conc) {
  return 0;
}

Expr vc_iffExpr(VC vc, Expr left, Expr right) {
  return 0;
}

Expr vc_iteExpr(VC vc, Expr conditional, Expr ifthenpart, Expr elsepart) {
  return 0;
}

Expr vc_boolToBVExpr(VC vc, Expr form) {
  return 0;
}

Expr vc_paramBoolExpr(VC vc, Expr var, Expr param) {
  return 0;
}

Expr vc_readExpr(VC vc, Expr array, Expr index) {
  return 0;
}

Expr vc_writeExpr(VC vc, Expr array, Expr index, Expr newValue) {
  return 0;
}

Expr vc_parseExpr(VC vc, const char* s) {
  return 0;
}

void vc_printExpr(VC vc, Expr e) {
}

void vc_printExprCCode(VC vc, Expr e) {
}

char * vc_printSMTLIB(VC vc, Expr e) {
  return 0;
}

void vc_printExprFile(VC vc, Expr e, int fd) {
}

void vc_printExprToBuffer(VC vc, Expr e, char **buf, unsigned long * len) {
}

void vc_printCounterExample(VC vc) {
}

void vc_printVarDecls(VC vc) {
}

void vc_clearDecls(VC vc) {
}

void vc_printAsserts(VC vc, int simplify_print) {
}

void vc_printQueryStateToBuffer(VC vc, Expr e,
				char **buf, unsigned long *len, int simplify_print) {
}

void vc_printCounterExampleToBuffer(VC vc, char **buf,unsigned long *len) {
}

void vc_printQuery(VC vc) {
}

void vc_assertFormula(VC vc, Expr e) {
}

Expr vc_simplify(VC vc, Expr e) {
  return 0;
}

int vc_query_with_timeout(VC vc, Expr e, int timeout_ms) {
  return 0;
}

int vc_query(VC vc, Expr e) {
  return 0;
}

Expr vc_getCounterExample(VC vc, Expr e) {
  return 0;
}

void vc_getCounterExampleArray(VC vc, Expr e, Expr **indices, Expr **values, int *size) {
}
    
int vc_counterexample_size(VC vc) {
  return 0;
}

void vc_push(VC vc) {
}

void vc_pop(VC vc) {
}

int getBVInt(Expr e) {
  return 0;
}

unsigned int getBVUnsigned(Expr e) {
  return 0;
}

unsigned long long int getBVUnsignedLongLong(Expr e) {
  return 0;
}

Type vc_bvType(VC vc, int no_bits) {
  return 0;
}

Type vc_bv32Type(VC vc) {
  return 0;
}

Expr vc_bvConstExprFromDecStr(VC vc, int width, const char* decimalInput ) {
  return 0;
}

Expr vc_bvConstExprFromStr(VC vc, const char* binary_repr) {
  return 0;
}

Expr vc_bvConstExprFromInt(VC vc, int n_bits, unsigned int value) {
  return 0;
}

Expr vc_bvConstExprFromLL(VC vc, int n_bits, unsigned long long value) {
  return 0;
}

Expr vc_bv32ConstExprFromInt(VC vc, unsigned int value) {
  return 0;
}

Expr vc_bvConcatExpr(VC vc, Expr left, Expr right) {
  return 0;
}

Expr vc_bvPlusExpr(VC vc, int n_bits, Expr left, Expr right) {
  return 0;
}

Expr vc_bvPlusExprN(VC vc, int n_bits, Expr* children, int numOfChildNodes) {
  return 0;
}

Expr vc_bv32PlusExpr(VC vc, Expr left, Expr right) {
  return 0;
}

Expr vc_bvMinusExpr(VC vc, int n_bits, Expr left, Expr right) {
  return 0;
}

Expr vc_bv32MinusExpr(VC vc, Expr left, Expr right) {
  return 0;
}

Expr vc_bvMultExpr(VC vc, int n_bits, Expr left, Expr right) {
  return 0;
}

Expr vc_bv32MultExpr(VC vc, Expr left, Expr right) {
  return 0;
}

Expr vc_bvDivExpr(VC vc, int n_bits, Expr left, Expr right) {
  return 0;
}

Expr vc_bvModExpr(VC vc, int n_bits, Expr left, Expr right) {
  return 0;
}

Expr vc_sbvDivExpr(VC vc, int n_bits, Expr left, Expr right) {
  return 0;
}

Expr vc_sbvModExpr(VC vc, int n_bits, Expr left, Expr right) {
  return 0;
}

Expr vc_sbvRemExpr(VC vc, int n_bits, Expr left, Expr right) {
  return 0;
}

Expr vc_bvLtExpr(VC vc, Expr left, Expr right) {
  return 0;
}

Expr vc_bvLeExpr(VC vc, Expr left, Expr right) {
  return 0;
}

Expr vc_bvGtExpr(VC vc, Expr left, Expr right) {
  return 0;
}

Expr vc_bvGeExpr(VC vc, Expr left, Expr right) {
  return 0;
}

Expr vc_sbvLtExpr(VC vc, Expr left, Expr right) {
  return 0;
}

Expr vc_sbvLeExpr(VC vc, Expr left, Expr right) {
  return 0;
}

Expr vc_sbvGtExpr(VC vc, Expr left, Expr right) {
  return 0;
}

Expr vc_sbvGeExpr(VC vc, Expr left, Expr right) {
  return 0;
}

Expr vc_bvUMinusExpr(VC vc, Expr child) {
  return 0;
}

Expr vc_bvAndExpr(VC vc, Expr left, Expr right) {
  return 0;
}

Expr vc_bvOrExpr(VC vc, Expr left, Expr right) {
  return 0;
}

Expr vc_bvXorExpr(VC vc, Expr left, Expr right) {
  return 0;
}

Expr vc_bvNotExpr(VC vc, Expr child) {
  return 0;
}

Expr vc_bvLeftShiftExprExpr(VC vc, int n_bits, Expr left, Expr right) {
    return 0;
}

Expr vc_bvRightShiftExprExpr(VC vc, int n_bits,  Expr left, Expr right) {
    return 0;
}

Expr vc_bvSignedRightShiftExprExpr(VC vc, int n_bits, Expr left, Expr right) {
    return 0;
}

Expr vc_bvLeftShiftExpr(VC vc, int sh_amt, Expr child) {
  return 0;
}

Expr vc_bvRightShiftExpr(VC vc, int sh_amt, Expr child) {
  return 0;
}

Expr vc_bv32LeftShiftExpr(VC vc, int sh_amt, Expr child) {
  return 0;
}

Expr vc_bv32RightShiftExpr(VC vc, int sh_amt, Expr child) {
  return 0;
}

Expr vc_bvVar32LeftShiftExpr(VC vc, Expr sh_amt, Expr child) {
  return 0;
}

Expr vc_bvVar32RightShiftExpr(VC vc, Expr sh_amt, Expr child) {
  return 0;
}

Expr vc_bvVar32DivByPowOfTwoExpr(VC vc, Expr child, Expr rhs) {
  return 0;
}

Expr vc_bvExtract(VC vc, Expr child, int high_bit_no, int low_bit_no) {
  return 0;
}

Expr vc_bvBoolExtract(VC vc, Expr x, int bit_no) {
  return 0;
}

Expr vc_bvBoolExtract_Zero(VC vc, Expr x, int bit_no) {
  return 0;
}

Expr vc_bvBoolExtract_One(VC vc, Expr x, int bit_no) {
  return 0;
}

Expr vc_bvSignExtend(VC vc, Expr child, int nbits) {
  return 0;
}

Expr vc_bvCreateMemoryArray(VC vc, const char * arrayName) {
  return 0;
}

Expr vc_bvReadMemoryArray(VC vc,
			  Expr array, Expr byteIndex, int numOfBytes) {
  return 0;
}

Expr vc_bvWriteToMemoryArray(VC vc,
			     Expr array, Expr  byteIndex,
			     Expr element, int numOfBytes) {
  return 0;
}

char* exprString(Expr e) {
  return 0;
}

char* typeString(Type t) {
  return 0;
}

Expr getChild(Expr e, int i) {
  return 0;
}

int vc_isBool(Expr e) {
  return 0;
}

void vc_registerErrorHandler(void (*error_hdlr)(const char* err_msg)) {
}

int vc_getHashQueryStateToBuffer(VC vc, Expr query) {
  return 0;
}

void vc_Destroy(VC vc) {
}

void vc_DeleteExpr(Expr e) {
}

WholeCounterExample vc_getWholeCounterExample(VC vc) {
  return 0;
}

Expr vc_getTermFromCounterExample(VC vc, Expr e, WholeCounterExample c) {
  return 0;
}

void vc_deleteWholeCounterExample(WholeCounterExample cc) {
}

int getDegree (Expr e) {
  return 0;
}

int getBVLength(Expr e) {
  return 0;
}

enum type_t getType (Expr e) {
  return 0;
}

int getVWidth (Expr e) {
  return 0;
}

int getIWidth (Expr e) {
  return 0;
}

void vc_printCounterExampleFile(VC vc, int fd) {
}

const char* exprName(Expr e) {
  return 0;
}

int getExprID (Expr ex) {
  return 0;
}

int vc_parseMemExpr(VC vc, const char* s, Expr* oquery, Expr* oasserts ) {
  return 0;
}

