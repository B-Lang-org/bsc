/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
// -*- c++ -*-
#include "c_interface.h"

#include <stdlib.h>
#include <assert.h>
#include "fdstream.h"
#include "../printer/printers.h"
#include "../cpp_interface/cpp_interface.h"
#include "../extlib-abc/cnf_short.h"

//These typedefs lower the effort of using the keyboard to type (too
//many overloaded meanings of the word type)
typedef BEEV::ASTNode                    node;
typedef BEEV::ASTNode*                   nodestar;
typedef BEEV::STPMgr*                   bmstar;
typedef BEEV::STP*                       stpstar;
typedef BEEV::Simplifier*                simpstar;
typedef BEEV::BVSolver*                  bvsolverstar;
typedef BEEV::AbsRefine_CounterExample * ctrexamplestar;
typedef BEEV::ASTVec                     nodelist;
typedef BEEV::CompleteCounterExample*    CompleteCEStar;
BEEV::ASTVec *decls = NULL;
SimplifyingNodeFactory *simpNF = NULL;
//vector<BEEV::ASTNode *> created_exprs;

// persist holds a copy of ASTNodes so that the reference count of
// objects we have pointers to doesn't hit zero.
vector<BEEV::ASTNode*> persist;
bool cinterface_exprdelete_on_flag = true;

// GLOBAL FUNCTION: parser
extern int cvcparse(void*);
extern int smtparse(void*);

void vc_setFlags(VC vc, char c, int param_value) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  process_argument(c, b);
}

void vc_setFlag(VC vc, char c) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  process_argument(c, b);
}

void vc_setInterfaceFlags(VC vc, enum ifaceflag_t f, int param_value) {
    bmstar b = (bmstar)(((stpstar)vc)->bm);
    switch (f) {
  case EXPRDELETE:
    cinterface_exprdelete_on_flag = param_value != 0;
    break;
  case MS:
      b->UserFlags.solver_to_use = BEEV::UserDefinedFlags::MINISAT_SOLVER;
      break;
  case SMS:
      b->UserFlags.solver_to_use = BEEV::UserDefinedFlags::SIMPLIFYING_MINISAT_SOLVER;
      break;
  case CMS2:
      b->UserFlags.solver_to_use = BEEV::UserDefinedFlags::CRYPTOMINISAT_SOLVER;
      break;
  case MSP:
      b->UserFlags.solver_to_use = BEEV::UserDefinedFlags::MINISAT_PROPAGATORS;
      break;
  default:
    BEEV::FatalError("C_interface: vc_setInterfaceFlags: Unrecognized flag\n");
    break;
  }
}

void make_division_total(VC vc)
{
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  b->UserFlags.division_by_zero_returns_one_flag = true;
}

//Create a validity Checker. This is the global STPMgr
VC vc_createValidityChecker(void) {
  CONSTANTBV::ErrCode c = CONSTANTBV::BitVector_Boot();
  if(0 != c) {
    cout << CONSTANTBV::BitVector_Error(c) << endl;
    return 0;
  }

  BEEV::STPMgr * bm       = new BEEV::STPMgr();
  BEEV::Simplifier * simp  = new BEEV::Simplifier(bm);
  BEEV::BVSolver* bvsolver = new BEEV::BVSolver(bm, simp);
  BEEV::ToSAT * tosat      = new BEEV::ToSAT(bm);
  BEEV::ArrayTransformer * arrayTransformer = 
    new BEEV::ArrayTransformer(bm, simp);
  BEEV::AbsRefine_CounterExample * Ctr_Example = 
    new BEEV::AbsRefine_CounterExample(bm, 
                                       simp, 
                                       arrayTransformer
                                       );

  BEEV::ParserBM = bm;
  stpstar stp =
    new BEEV::STP(bm, simp, 
                  bvsolver, arrayTransformer, 
                  tosat, Ctr_Example);
  
  simpNF = new SimplifyingNodeFactory(*(bm->hashingNodeFactory), *bm);
  bm->defaultNodeFactory = simpNF;

  BEEV::GlobalSTP = stp;
  decls = new BEEV::ASTVec();
  //created_exprs.clear();
  vc_setFlags(stp,'d');
  return (VC)stp;
}

// Expr I/O
void vc_printExpr(VC vc, Expr e) {
  //do not print in lisp mode
  //bmstar b = (bmstar)vc;
  BEEV::ASTNode q = (*(nodestar)e);
  //   b->Begin_RemoveWrites = true;
  //   BEEV::ASTNode q = b->SimplifyFormula_TopLevel(*((nodestar)e),false);
  //   b->Begin_RemoveWrites = false;
  q.PL_Print(cout);
}

char * vc_printSMTLIB(VC vc, Expr e)
{
  stringstream ss;
  printer::SMTLIB1_PrintBack(ss,*((nodestar)e));
  string s = ss.str();
  char *copy = strdup(s.c_str());
  return copy;

}

// prints Expr 'e' to stdout as C code
void vc_printExprCCode(VC vc, Expr e) {
  BEEV::ASTNode q = (*(nodestar)e);
  bmstar b = (bmstar)(((stpstar)vc)->bm);

  // print variable declarations
  BEEV::ASTVec declsFromParser = (nodelist)b->ListOfDeclaredVars;

  for(BEEV::ASTVec::iterator it=declsFromParser.begin(),
        itend=declsFromParser.end(); it!=itend;it++) {
    if(BEEV::BITVECTOR_TYPE == it->GetType()) {
      const char* name = it->GetName();
      unsigned int bitWidth = it->GetValueWidth();
      assert(bitWidth % 8 == 0);
      unsigned int byteWidth = bitWidth / 8;
      cout << "unsigned char " 
           << name 
           << "[" << byteWidth << "];" << endl;
    }
    else {
      // vc_printExprCCode: unsupported decl. type
      assert(0);
    }
  }

  cout << endl;

  // print constraints and assert
  printer::C_Print(cout,q);
}


void vc_printExprFile(VC vc, Expr e, int fd) {
  fdostream os(fd);
  ((nodestar)e)->PL_Print(os);
  //os.flush();
}

static void vc_printVarDeclsToStream(VC vc, ostream &os) {
  for(BEEV::ASTVec::iterator i = decls->begin(),
        iend=decls->end();i!=iend;i++) {
    node a = *i;
    switch(a.GetType()) {
    case BEEV::BITVECTOR_TYPE:
      a.PL_Print(os);
      os << " : BITVECTOR(" 
         << a.GetValueWidth() 
         << ");" << endl;
      break;
    case BEEV::ARRAY_TYPE:
      a.PL_Print(os);
      os << " : ARRAY " 
         << "BITVECTOR(" 
         << a.GetIndexWidth() 
         << ") OF ";
      os << "BITVECTOR(" 
         << a.GetValueWidth() 
         << ");" 
         << endl;
      break;
    case BEEV::BOOLEAN_TYPE:
      a.PL_Print(os);
      os << " : BOOLEAN;" << endl;
      break;
    default:
      BEEV::FatalError("vc_printDeclsToStream: Unsupported type",a);
      break;
    }
  }
}

void vc_printVarDecls(VC vc) {
  vc_printVarDeclsToStream(vc, cout);
}

void vc_clearDecls(VC vc) {
  decls->clear();
}

static void vc_printAssertsToStream(VC vc, ostream &os, int simplify_print) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  BEEV::ASTVec v = b->GetAsserts();
  BEEV::Simplifier * simp = new BEEV::Simplifier(b);
  for(BEEV::ASTVec::iterator i=v.begin(),iend=v.end();i!=iend;i++) {
    //b->Begin_RemoveWrites = true;
    BEEV::ASTNode q = 
      (simplify_print == 1) ? 
      simp->SimplifyFormula_TopLevel(*i,false) : *i;
    q = 
      (simplify_print == 1) ? 
      simp->SimplifyFormula_TopLevel(q,false) : q;
    //b->Begin_RemoveWrites = false;
    os << "ASSERT( ";
    q.PL_Print(os);
    os << ");" << endl;
  }
}

void vc_printAsserts(VC vc, int simplify_print) {
  vc_printAssertsToStream(vc, cout, simplify_print);
}

void vc_printQueryStateToBuffer(VC vc, Expr e, 
                                char **buf, 
                                unsigned long *len, int simplify_print){
  assert(vc);
  assert(e);
  assert(buf);
  assert(len);
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  BEEV::Simplifier * simp = new BEEV::Simplifier(b);

  // formate the state of the query
  stringstream os;
  vc_printVarDeclsToStream(vc, os);
  os << "%----------------------------------------------------" << endl;
  vc_printAssertsToStream(vc, os, simplify_print);
  os << "%----------------------------------------------------" << endl;
  os << "QUERY( ";
  //b->Begin_RemoveWrites = true;
  BEEV::ASTNode q = 
    (simplify_print == 1) ? 
    simp->SimplifyFormula_TopLevel(*((nodestar)e),false) : 
    *(nodestar)e;
  //b->Begin_RemoveWrites = false;
  q.PL_Print(os);
  os << " );" << endl;

  // convert to a c buffer
  string s = os.str();
  const char *cstr = s.c_str();
  unsigned long size = s.size() + 1; // number of chars + terminating null
  *buf = (char *)malloc(size);
  if (!(*buf)) {
    fprintf(stderr, "malloc(%lu) failed.", size);
    assert(*buf);
  }
  *len = size;
  memcpy(*buf, cstr, size);
}

void vc_printCounterExampleToBuffer(VC vc, char **buf, unsigned long *len) {
  assert(vc);
  assert(buf);
  assert(len);
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  ctrexamplestar ce = (ctrexamplestar)(((stpstar)vc)->Ctr_Example);  

  // formate the state of the query
  std::ostringstream os;
  bool currentPrint = b->UserFlags.print_counterexample_flag;
  b->UserFlags.print_counterexample_flag = true;
  os << "COUNTEREXAMPLE BEGIN: \n";
  ce->PrintCounterExample(true,os);
  os << "COUNTEREXAMPLE END: \n";
  b->UserFlags.print_counterexample_flag = currentPrint;

  // convert to a c buffer
  string s = os.str();
  const char *cstr = s.c_str();
  unsigned long size = s.size() + 1; // number of chars + terminating null
  *buf = (char *)malloc(size);
  if (!(*buf)) {
    fprintf(stderr, "malloc(%lu) failed.", size);
    assert(*buf);
  }
  *len = size;
  memcpy(*buf, cstr, size);
}

void vc_printExprToBuffer(VC vc, Expr e, char **buf, unsigned long * len) {
  stringstream os;
  //bmstar b = (bmstar)(((stpstar)vc)->bm);
  BEEV::ASTNode q = *((nodestar)e);
  // b->Begin_RemoveWrites = true;
  //   BEEV::ASTNode q = b->SimplifyFormula_TopLevel(*((nodestar)e),false);
  //   b->Begin_RemoveWrites = false;
  q.PL_Print(os);
  //((nodestar)e)->PL_Print(os);
  string s = os.str();
  const char * cstr = s.c_str();
  unsigned long size = s.size() + 1; // number of chars + terminating null
  *buf = (char *)malloc(size);
  *len = size;
  memcpy(*buf, cstr, size);
}

void vc_printQuery(VC vc){
  ostream& os = std::cout;
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  os << "QUERY(";
  //b->Begin_RemoveWrites = true;
  //BEEV::ASTNode q = b->SimplifyFormula_TopLevel(b->GetQuery(),false);
  BEEV::ASTNode q = b->GetQuery();
  //b->Begin_RemoveWrites = false;
  q.PL_Print(os);
  // b->GetQuery().PL_Print(os);
  os << ");" << endl;
}

nodestar persistNode(node n)
{
  nodestar np = new node(n);
  if (cinterface_exprdelete_on_flag)
    persist.push_back(np);
  return np;
}


/////////////////////////////////////////////////////////////////////////////
// Array-related methods                                                   //
/////////////////////////////////////////////////////////////////////////////
//! Create an array type
Type vc_arrayType(VC vc, Type typeIndex, Type typeData) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar ti = (nodestar)typeIndex;
  nodestar td = (nodestar)typeData;

  if(!(ti->GetKind() == BEEV::BITVECTOR 
       && (*ti)[0].GetKind() == BEEV::BVCONST))
    {
      BEEV::FatalError("Tyring to build array whose"\
                       "indextype i is not a BITVECTOR, where i = ",*ti);
    }
  if(!(td->GetKind()  == BEEV::BITVECTOR
       && (*td)[0].GetKind() == BEEV::BVCONST)) 
    {
      BEEV::FatalError("Trying to build an array whose"\
                       "valuetype v is not a BITVECTOR. where a = ",*td);
    }
  node output = b->CreateNode(BEEV::ARRAY,(*ti)[0],(*td)[0]);

  return persistNode(output);
}

//! Create an expression for the value of array at the given index
Expr vc_readExpr(VC vc, Expr array, Expr index) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar a = (nodestar)array;
  nodestar i = (nodestar)index;

  assert(BVTypeCheck(*a));
  assert(BVTypeCheck(*i));
  node o = b->CreateTerm(BEEV::READ,a->GetValueWidth(),*a,*i);
  assert(BVTypeCheck(o));

  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

// //! Array update; equivalent to "array WITH [index] := newValue"
Expr vc_writeExpr(VC vc, Expr array, Expr index, Expr newValue) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar a = (nodestar)array;
  nodestar i = (nodestar)index;
  nodestar n = (nodestar)newValue;

  assert(BVTypeCheck(*a));
  assert(BVTypeCheck(*i));
  assert(BVTypeCheck(*n));
  node o = b->CreateTerm(BEEV::WRITE,a->GetValueWidth(),*a,*i,*n);
  o.SetIndexWidth(a->GetIndexWidth());
  assert(BVTypeCheck(o));

  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

/////////////////////////////////////////////////////////////////////////////
// Context-related methods                                                 //
/////////////////////////////////////////////////////////////////////////////
//! Assert a new formula in the current context.
/*! The formula must have Boolean type. */
void vc_assertFormula(VC vc, Expr e) {
  nodestar a = (nodestar)e;
  bmstar b = (bmstar)(((stpstar)vc)->bm);

  if(!BEEV::is_Form_kind(a->GetKind()))
    BEEV::FatalError("Trying to assert a NON formula: ",*a);

  assert(BVTypeCheck(*a));
  b->AddAssert(*a);
}

void soft_time_out(int ignored)
{
  BEEV::ParserBM->soft_timeout_expired = true;
}

//! Check validity of e in the current context. e must be a FORMULA
//
//if returned 0 then input is INVALID.
//
//if returned 1 then input is VALID
//
//if returned 2 then ERROR
//
//! Check validity of e in the current context.
/*! If the result is true, then the resulting context is the same as
 * the starting context.  If the result is false, then the resulting
 * context is a context in which e is false.  e must have Boolean
 * type. */
int vc_query(VC vc, Expr e)
{
  return vc_query_with_timeout(vc,e,-1);
}

int vc_query_with_timeout(VC vc, Expr e, int timeout_ms) {
  nodestar a = (nodestar)e;
  stpstar stp = ((stpstar)vc);
  bmstar b = (bmstar)(stp->bm);

  assert(!BEEV::ParserBM->soft_timeout_expired);
  if (timeout_ms != -1)
    {
      itimerval timeout;
      signal(SIGVTALRM, soft_time_out);
      timeout.it_interval.tv_usec = 0;
      timeout.it_interval.tv_sec  = 0;
      timeout.it_value.tv_usec    = 1000 * (timeout_ms % 1000);
      timeout.it_value.tv_sec     = timeout_ms / 1000;
      setitimer(ITIMER_VIRTUAL, &timeout, NULL);
    }

  if(!BEEV::is_Form_kind(a->GetKind())) 
    {     
      BEEV::FatalError("CInterface: Trying to QUERY a NON formula: ",*a);
    }
  //a->LispPrint(cout, 0);
  //printf("##################################################\n");
  assert(BVTypeCheck(*a));
  b->AddQuery(*a);

  const BEEV::ASTVec v = b->GetAsserts();
  node o;
  int output;
  if(!v.empty()) 
    {
      if(v.size()==1) 
        {
          output = stp->TopLevelSTP(v[0],*a);
        }
      else 
        {
          output = stp->TopLevelSTP(b->CreateNode(BEEV::AND,v),*a);
        }
    }
  else 
    {
      output = stp->TopLevelSTP(b->CreateNode(BEEV::TRUE),*a);
    }

  if (timeout_ms !=-1)
    {
      // Reset the timer.
      setitimer(ITIMER_VIRTUAL, NULL, NULL);
      BEEV::ParserBM->soft_timeout_expired = false;
    }

  return output;
} //end of vc_query

// int vc_absRefineQuery(VC vc, Expr e) {
//   nodestar a = (nodestar)e;
//   bmstar b   = (bmstar)(((stpstar)vc)->bm);

//   if(!BEEV::is_Form_kind(a->GetKind()))
//     BEEV::FatalError("CInterface: Trying to QUERY a NON formula: ",*a);

//   //a->LispPrint(cout, 0);
//   //printf("##################################################\n");
//   BVTypeCheck(*a);
//   b->AddQuery(*a);

//   const BEEV::ASTVec v = b->GetAsserts();
//   node o;
//   if(!v.empty()) {
//     if(v.size()==1)
//       return b->TopLevelSTP(v[0],*a);
//     else
//       return b->TopLevelSTP(b->CreateNode(BEEV::AND,v),*a);
//   }
//   else
//     return b->TopLevelSTP(b->CreateNode(BEEV::TRUE),*a);
// }

void vc_push(VC vc) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  ((stpstar)vc)->ClearAllTables();
  b->Push();
}

void vc_pop(VC vc) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  b->Pop();
}

void vc_printCounterExample(VC vc) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  ctrexamplestar ce = (ctrexamplestar)(((stpstar)vc)->Ctr_Example);

  bool currentPrint = b->UserFlags.print_counterexample_flag;
    b->UserFlags.print_counterexample_flag = true;
  cout << "COUNTEREXAMPLE BEGIN: \n";
  ce->PrintCounterExample(true);
  cout << "COUNTEREXAMPLE END: \n";
  b->UserFlags.print_counterexample_flag = currentPrint;
}

// //! Return the counterexample after a failed query.
// /*! This method should only be called after a query which returns
//  * false.  It will try to return the simplest possible set of
//  * assertions which are sufficient to make the queried expression
//  * false.  The caller is responsible for freeing the array when
//  * finished with it.
//  */

Expr vc_getCounterExample(VC vc, Expr e) {
  nodestar a = (nodestar)e;
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  ctrexamplestar ce = (ctrexamplestar)(((stpstar)vc)->Ctr_Example);  

  bool t = false;
  if(ce->CounterExampleSize())
    t = true;
  nodestar output = new node(ce->GetCounterExample(t, *a));
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

void vc_getCounterExampleArray(VC vc, Expr e, Expr **indices, Expr **values, int *size) {
  nodestar a = (nodestar)e;
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  ctrexamplestar ce = (ctrexamplestar)(((stpstar)vc)->Ctr_Example);  

  bool t = false;
  if(ce->CounterExampleSize())
    t = true;

  std::vector<std::pair<ASTNode, ASTNode> > entries = ce->GetCounterExampleArray(t, *a);
  *size = entries.size();
  if (*size != 0) {
    *indices = (Expr *) malloc(*size * sizeof(Expr*));
    *values = (Expr *) malloc(*size * sizeof(Expr*));
    for (int i = 0; i < *size; ++i) {
      (*indices)[i] = new node(entries[i].first);
      (*values)[i] = new node(entries[i].second);
    }
  }
}

int vc_counterexample_size(VC vc) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  ctrexamplestar ce = (ctrexamplestar)(((stpstar)vc)->Ctr_Example);  

  return ce->CounterExampleSize();
}

WholeCounterExample vc_getWholeCounterExample(VC vc) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  ctrexamplestar ce = (ctrexamplestar)(((stpstar)vc)->Ctr_Example);  

  CompleteCEStar c =
    new BEEV::CompleteCounterExample(ce->GetCompleteCounterExample(),
                                     b);
  return c;
}

Expr vc_getTermFromCounterExample(VC vc, Expr e, WholeCounterExample cc) {
  //bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar n = (nodestar)e;
  CompleteCEStar c = (CompleteCEStar)cc;

  nodestar output = new node(c->GetCounterExample(*n));
  return output;
}

void vc_deleteWholeCounterExample(WholeCounterExample cc) {
  CompleteCEStar c = (CompleteCEStar)cc;

  delete c;
}

int vc_getBVLength(VC vc, Expr ex) {
  nodestar e = (nodestar)ex;

  if(BEEV::BITVECTOR_TYPE != e->GetType()) 
    {
      BEEV::FatalError("c_interface: vc_GetBVLength: "          \
                       "Input expression must be a bit-vector");
    }
  return e->GetValueWidth();
} // end of vc_getBVLength

/////////////////////////////////////////////////////////////////////////////
// Expr Creation methods                                                   //
/////////////////////////////////////////////////////////////////////////////
//! Create a variable with a given name and type
/*! The type cannot be a function type. */
Expr vc_varExpr1(VC vc, const char* name,
                 int indexwidth, int valuewidth) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);

  node o = b->CreateSymbol(name,indexwidth,valuewidth);

  nodestar output = new node(o);
  ////if(cinterface_exprdelete_on) created_exprs.push_back(output);
  assert(BVTypeCheck(*output));

  //store the decls in a vector for printing purposes
  decls->push_back(o);
  return output;
}

Expr vc_varExpr(VC vc, const char * name, Type type) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar a = (nodestar)type;

  unsigned indexWidth;
  unsigned valueWidth;

  switch(a->GetKind()) {
  case BEEV::BITVECTOR:
    indexWidth = 0;
    valueWidth = (*a)[0].GetUnsignedConst();
    break;
  case BEEV::ARRAY:
    indexWidth = (*a)[0].GetUnsignedConst();
    valueWidth = (*a)[1].GetUnsignedConst();
    break;
  case BEEV::BOOLEAN:
    indexWidth = 0;
    valueWidth = 0;
    break;
  default:
    BEEV::FatalError("CInterface: vc_varExpr: Unsupported type",*a);
    break;

  }
  node o = b->CreateSymbol(name,indexWidth,valueWidth);

  nodestar output = new node(o);
  ////if(cinterface_exprdelete_on) created_exprs.push_back(output);
  assert(BVTypeCheck(*output));

  //store the decls in a vector for printing purposes
  decls->push_back(o);
  return output;
}

//! Create an equality expression.  The two children must have the
//same type.
Expr vc_eqExpr(VC vc, Expr ccc0, Expr ccc1) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);

  nodestar a = (nodestar)ccc0;
  nodestar aa = (nodestar)ccc1;
  assert(BVTypeCheck(*a));
  assert(BVTypeCheck(*aa));
  node o = b->CreateNode(BEEV::EQ,*a,*aa);

  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_boolType(VC vc) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);

  node o = b->CreateNode(BEEV::BOOLEAN);
  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

/////////////////////////////////////////////////////////////////////////////
// BOOLEAN EXPR Creation methods                                           //
/////////////////////////////////////////////////////////////////////////////
// The following functions create Boolean expressions.  The children
// provided as arguments must be of type Boolean.
Expr vc_trueExpr(VC vc) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  node c = b->CreateNode(BEEV::TRUE);

  nodestar d = new node(c);
  //if(cinterface_exprdelete_on) created_exprs.push_back(d);
  return d;
}

Expr vc_falseExpr(VC vc) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  node c = b->CreateNode(BEEV::FALSE);

  nodestar d = new node(c);
  //if(cinterface_exprdelete_on) created_exprs.push_back(d);
  return d;
}

Expr vc_notExpr(VC vc, Expr ccc) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar a = (nodestar)ccc;

  node o = b->CreateNode(BEEV::NOT,*a);
  assert(BVTypeCheck(o));

  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_andExpr(VC vc, Expr left, Expr right) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar l = (nodestar)left;
  nodestar r = (nodestar)right;

  node o = b->CreateNode(BEEV::AND,*l,*r);
  assert(BVTypeCheck(o));

  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_orExpr(VC vc, Expr left, Expr right) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar l = (nodestar)left;
  nodestar r = (nodestar)right;

  node o = b->CreateNode(BEEV::OR,*l,*r);
  assert(BVTypeCheck(o));
  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_xorExpr(VC vc, Expr left, Expr right) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar l = (nodestar)left;
  nodestar r = (nodestar)right;

  node o = b->CreateNode(BEEV::XOR,*l,*r);
  assert(BVTypeCheck(o));
  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}


Expr vc_andExprN(VC vc, Expr* cc, int n) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar * c = (nodestar *)cc;
  nodelist d;

  for(int i =0; i < n; i++)
    d.push_back(*c[i]);

  node o = b->CreateNode(BEEV::AND,d);
  assert(BVTypeCheck(o));

  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}


Expr vc_orExprN(VC vc, Expr* cc, int n) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar * c = (nodestar *)cc;
  nodelist d;

  for(int i =0; i < n; i++)
    d.push_back(*c[i]);

  node o = b->CreateNode(BEEV::OR,d);
  assert(BVTypeCheck(o));

  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_bvPlusExprN(VC vc, int n_bits, Expr* cc, int n) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar * c = (nodestar *)cc;
  nodelist d;

  for(int i =0; i < n; i++)
    d.push_back(*c[i]);

  node o = b->CreateTerm(BEEV::BVPLUS, n_bits, d);
  assert(BVTypeCheck(o));

  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}


Expr vc_iteExpr(VC vc, Expr cond, Expr thenpart, Expr elsepart){
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar c = (nodestar)cond;
  nodestar t = (nodestar)thenpart;
  nodestar e = (nodestar)elsepart;

  assert(BVTypeCheck(*c));
  assert(BVTypeCheck(*t));
  assert(BVTypeCheck(*e));
  node o;
  //if the user asks for a formula then produce a formula, else
  //prodcue a term
  if(BEEV::BOOLEAN_TYPE == t->GetType())
    o = b->CreateNode(BEEV::ITE,*c,*t,*e);
  else {
    o = b->CreateTerm(BEEV::ITE,t->GetValueWidth(),*c,*t,*e);
    o.SetIndexWidth(t->GetIndexWidth());
  }
  assert(BVTypeCheck(o));
  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_impliesExpr(VC vc, Expr antecedent, Expr consequent){
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar c = (nodestar)antecedent;
  nodestar t = (nodestar)consequent;

  assert(BVTypeCheck(*c));
  assert(BVTypeCheck(*t));
  node o;

  o = b->CreateNode(BEEV::IMPLIES,*c,*t);
  assert(BVTypeCheck(o));
  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_iffExpr(VC vc, Expr e0, Expr e1){
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar c = (nodestar)e0;
  nodestar t = (nodestar)e1;

  assert(BVTypeCheck(*c));
  assert(BVTypeCheck(*t));
  node o;

  o = b->CreateNode(BEEV::IFF,*c,*t);
  assert(BVTypeCheck(o));
  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_boolToBVExpr(VC vc, Expr form) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar c = (nodestar)form;

  assert(BVTypeCheck(*c));
  if(!is_Form_kind(c->GetKind()))
    {
      BEEV::FatalError("CInterface: vc_BoolToBVExpr: "\
                       "You have input a NON formula:",*c);
    }

  node o;
  node one = b->CreateOneConst(1);
  node zero = b->CreateZeroConst(1);
  o = b->CreateTerm(BEEV::ITE,1,*c,one,zero);

  assert(BVTypeCheck(o));
  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_paramBoolExpr(VC vc, Expr boolvar, Expr parameter){
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar c = (nodestar)boolvar;
  nodestar t = (nodestar)parameter;

  assert(BVTypeCheck(*c));
  assert(BVTypeCheck(*t));
  node o;

  o = b->CreateNode(BEEV::PARAMBOOL,*c,*t);
  //BVTypeCheck(o);
  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}


/////////////////////////////////////////////////////////////////////////////
// BITVECTOR EXPR Creation methods                                         //
/////////////////////////////////////////////////////////////////////////////
Type vc_bvType(VC vc, int num_bits) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);

  if(!(0 < num_bits))
    {
      BEEV::FatalError("CInterface: number of bits in a bvtype"\
                       " must be a positive integer:",
                       b->CreateNode(BEEV::UNDEFINED));
    }

  node e = b->CreateBVConst(32, num_bits);
  node output = (b->CreateNode(BEEV::BITVECTOR,e));
  return persistNode(output);
}

Type vc_bv32Type(VC vc) {
  return vc_bvType(vc,32);
}

Expr vc_bvConstExprFromDecStr(VC vc, 
                              int width, 
                              const char* decimalInput ) 
{
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  string str(decimalInput);
  node n = b->CreateBVConst(str, 10, width);
  assert(BVTypeCheck(n));
  nodestar output = new node(n);
  return output;
}


Expr vc_bvConstExprFromStr(VC vc, const char* binary_repr) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);

  node n = b->CreateBVConst(binary_repr,2);
  assert(BVTypeCheck(n));
  nodestar output = new node(n);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_bvConstExprFromInt(VC vc,
                           int n_bits,
                           unsigned int value) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);

  unsigned long long int v = (unsigned long long int)value;
  unsigned long long int max_n_bits = 0xFFFFFFFFFFFFFFFFULL >> 64-n_bits;
  //printf("%ull", max_n_bits);
  if(v > max_n_bits) {
    printf("CInterface: vc_bvConstExprFromInt: "\
           "Cannot construct a constant %llu >= %llu,\n", v, max_n_bits);
    BEEV::FatalError("FatalError");
  }
  node n = b->CreateBVConst(n_bits, v);
  assert(BVTypeCheck(n));
  return persistNode(n);
}

Expr vc_bvConstExprFromLL(VC vc,
                          int n_bits,
                          unsigned long long value) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);

  node n = b->CreateBVConst(n_bits, value);
  assert(BVTypeCheck(n));
  nodestar output = new node(n);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_bvConcatExpr(VC vc, Expr left, Expr right) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar l = (nodestar)left;
  nodestar r = (nodestar)right;

  assert(BVTypeCheck(*l));
  assert(BVTypeCheck(*r));
  node o =
    b->CreateTerm(BEEV::BVCONCAT,
                  l->GetValueWidth()+ r->GetValueWidth(),*l,*r);
  assert(BVTypeCheck(o));
  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr createBinaryTerm(VC vc, int n_bits, Kind k, Expr left, Expr right){
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar l = (nodestar)left;
  nodestar r = (nodestar)right;

  assert(BVTypeCheck(*l));
  assert(BVTypeCheck(*r));
  node o = b->CreateTerm(k,n_bits, *l, *r);
  assert(BVTypeCheck(o));
  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}


Expr vc_bvPlusExpr(VC vc, int n_bits, Expr left, Expr right){
    return createBinaryTerm(vc, n_bits, BEEV::BVPLUS, left, right);
}

Expr vc_bv32PlusExpr(VC vc, Expr left, Expr right) {
  return vc_bvPlusExpr(vc, 32, left, right);
}

Expr vc_bvMinusExpr(VC vc, int n_bits, Expr left, Expr right) {
    return createBinaryTerm(vc, n_bits, BEEV::BVSUB, left, right);
}

Expr vc_bv32MinusExpr(VC vc, Expr left, Expr right) {
  return vc_bvMinusExpr(vc, 32, left, right);
}

Expr vc_bvMultExpr(VC vc, int n_bits, Expr left, Expr right) {
    return createBinaryTerm(vc, n_bits, BEEV::BVMULT, left, right);
}

Expr vc_bvDivExpr(VC vc, int n_bits, Expr left, Expr right) {
    return createBinaryTerm(vc, n_bits, BEEV::BVDIV, left, right);
}

Expr vc_bvModExpr(VC vc, int n_bits, Expr left, Expr right) {
    return createBinaryTerm(vc, n_bits, BEEV::BVMOD, left, right);
}

Expr vc_sbvDivExpr(VC vc, int n_bits, Expr left, Expr right) {
    return createBinaryTerm(vc, n_bits, BEEV::SBVDIV, left, right);
}

Expr vc_sbvModExpr(VC vc, int n_bits, Expr left, Expr right) {
    return createBinaryTerm(vc, n_bits, BEEV::SBVREM, left, right);
}

Expr vc_sbvRemExpr(VC vc, int n_bits, Expr left, Expr right) {
    return createBinaryTerm(vc, n_bits, BEEV::SBVMOD, left, right);
}


Expr vc_bv32MultExpr(VC vc, Expr left, Expr right) {
  return vc_bvMultExpr(vc, 32, left, right);
}

Expr createBinaryNode(VC vc, Kind k, Expr left, Expr right)
{
    bmstar b = (bmstar)(((stpstar)vc)->bm);
    nodestar l = (nodestar)left;
    nodestar r = (nodestar)right;
    assert(BVTypeCheck(*l));
    assert(BVTypeCheck(*r));
    node o = b->CreateNode(k, *l, *r);
    assert(BVTypeCheck(o));
    nodestar output = new node(o);
    //if(cinterface_exprdelete_on)
    //  created_exprs.push_back(output);
    return output;
}

// unsigned comparators
Expr vc_bvLtExpr(VC vc, Expr left, Expr right) {
    return createBinaryNode(vc,BEEV::BVLT,left,right);
}
Expr vc_bvLeExpr(VC vc, Expr left, Expr right) {
  return createBinaryNode(vc,BEEV::BVLE,left,right);
}
Expr vc_bvGtExpr(VC vc, Expr left, Expr right) {
    return createBinaryNode(vc,BEEV::BVGT,left,right);
}
Expr vc_bvGeExpr(VC vc, Expr left, Expr right) {
    return createBinaryNode(vc,BEEV::BVGE,left,right);
}
// signed comparators
Expr vc_sbvLtExpr(VC vc, Expr left, Expr right) {
    return createBinaryNode(vc,BEEV::BVSLT,left,right);
}
Expr vc_sbvLeExpr(VC vc, Expr left, Expr right) {
    return createBinaryNode(vc,BEEV::BVSLE,left,right);
}
Expr vc_sbvGtExpr(VC vc, Expr left, Expr right) {
    return createBinaryNode(vc,BEEV::BVSGT,left,right);
}
Expr vc_sbvGeExpr(VC vc, Expr left, Expr right) {
    return createBinaryNode(vc,BEEV::BVSGE,left,right);
}

Expr vc_bvLeftShiftExprExpr(VC vc, int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits,BEEV::BVLEFTSHIFT,left,right);
}

Expr vc_bvRightShiftExprExpr(VC vc, int n_bits,Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits,BEEV::BVRIGHTSHIFT,left,right);
}

Expr vc_bvSignedRightShiftExprExpr(VC vc,int n_bits, Expr left, Expr right)
{
  return createBinaryTerm(vc, n_bits,BEEV::BVSRSHIFT,left,right);
}


Expr vc_bvUMinusExpr(VC vc, Expr ccc) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar a = (nodestar)ccc;
  assert(BVTypeCheck(*a));

  node o = b->CreateTerm(BEEV::BVUMINUS, a->GetValueWidth(), *a);
  assert(BVTypeCheck(o));
  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

// Expr createBinaryTerm(VC vc, int n_bits, Kind k, Expr left, Expr right){

// bitwise operations: these are terms not formulas
Expr vc_bvAndExpr(VC vc, Expr left, Expr right) {
    return createBinaryTerm(vc, (*((nodestar)left)).GetValueWidth(), BEEV::BVAND,  left,  right);
}

Expr vc_bvOrExpr(VC vc, Expr left, Expr right) {
    return createBinaryTerm(vc, (*((nodestar)left)).GetValueWidth(), BEEV::BVOR,  left,  right);
}

Expr vc_bvXorExpr(VC vc, Expr left, Expr right) {
    return createBinaryTerm(vc, (*((nodestar)left)).GetValueWidth(), BEEV::BVXOR,  left,  right);
}

Expr vc_bvNotExpr(VC vc, Expr ccc) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar a = (nodestar)ccc;

  assert(BVTypeCheck(*a));
  node o = b->CreateTerm(BEEV::BVNEG, a->GetValueWidth(), *a);
  assert(BVTypeCheck(o));
  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_bvLeftShiftExpr(VC vc, int sh_amt, Expr ccc) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar a = (nodestar)ccc;
  assert(BVTypeCheck(*a));

  //convert leftshift to bvconcat
  if(0 != sh_amt) {
    node len = b->CreateBVConst(sh_amt, 0);
    node o = 
      b->CreateTerm(BEEV::BVCONCAT, 
                    a->GetValueWidth() + sh_amt, *a, len);
    assert(BVTypeCheck(o));
    nodestar output = new node(o);
    //if(cinterface_exprdelete_on) created_exprs.push_back(output);
    return output;
  }
  else
    return a;
}

Expr vc_bvRightShiftExpr(VC vc, int sh_amt, Expr ccc) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar a = (nodestar)ccc;
  assert(BVTypeCheck(*a));

  unsigned int w = a->GetValueWidth();
  //the amount by which you are rightshifting
  //is less-than/equal-to the length of input
  //bitvector
  if(0 < (unsigned)sh_amt && (unsigned)sh_amt < w) {
    node len = b->CreateBVConst(sh_amt, 0);
    node hi = b->CreateBVConst(32,w-1);
    node low = b->CreateBVConst(32,sh_amt);
    node extract = b->CreateTerm(BEEV::BVEXTRACT,w-sh_amt,*a,hi,low);

    node n = b->CreateTerm(BEEV::BVCONCAT, w,len, extract);
    BVTypeCheck(n);
    nodestar output = new node(n);
    //if(cinterface_exprdelete_on) created_exprs.push_back(output);
    return output;
  }
  else if ((unsigned) sh_amt==w)
    {
      nodestar output = new node(b->CreateBVConst(w, 0));
      return output;
    }
  else if(sh_amt == 0)
    return a;
  else {
    if(0== w)
      {
        BEEV::FatalError("CInterface: vc_bvRightShiftExpr: "\
                         "cannot have a bitvector of length 0:",*a);
      }
    nodestar output = new node(b->CreateBVConst(w,0));
    //if(cinterface_exprdelete_on) created_exprs.push_back(output);
    return output;
  }
}

/* Same as vc_bvLeftShift only that the answer in 32 bits long */
Expr vc_bv32LeftShiftExpr(VC vc, int sh_amt, Expr child) {
  return vc_bvExtract(vc, vc_bvLeftShiftExpr(vc, sh_amt, child), 31, 0);
}

/* Same as vc_bvRightShift only that the answer in 32 bits long */
Expr vc_bv32RightShiftExpr(VC vc, int sh_amt, Expr child) {
  return vc_bvExtract(vc, vc_bvRightShiftExpr(vc, sh_amt, child), 31, 0);
}

Expr vc_bvVar32LeftShiftExpr(VC vc, Expr sh_amt, Expr child) {
  Expr ifpart;
  Expr thenpart;
  Expr elsepart = vc_trueExpr(vc);
  Expr ite = vc_trueExpr(vc);
  int child_width = vc_getBVLength(vc, child);
  int shift_width = vc_getBVLength(vc, sh_amt);

  assert(child_width>0);

  for(int count=32; count >= 0; count--)
    {
      if(count != 32) 
        {
          ifpart = vc_eqExpr(vc, sh_amt,
                             vc_bvConstExprFromInt(vc, shift_width, count));
          thenpart = vc_bvExtract(vc,
                                  vc_bvLeftShiftExpr(vc, count, child),
                                  child_width-1, 0);
                
          ite = vc_iteExpr(vc,ifpart,thenpart,elsepart);
          elsepart = ite;
        }
      else
        {
          elsepart = vc_bvConstExprFromInt(vc,child_width, 0);
        }
    }
  return ite;
}

Expr vc_bvVar32DivByPowOfTwoExpr(VC vc, Expr child, Expr rhs) {
  Expr ifpart;
  Expr thenpart;
  Expr elsepart = vc_trueExpr(vc);
  Expr ite = vc_trueExpr(vc);

  for(int count=32; count >= 0; count--)
    {
      if(count != 32) 
        {
          ifpart = vc_eqExpr(vc, rhs,
                             vc_bvConstExprFromInt(vc, 32, 1 << count));
          thenpart = vc_bvRightShiftExpr(vc, count, child);
          ite = vc_iteExpr(vc,ifpart,thenpart,elsepart);
          elsepart = ite;
        } 
      else 
        {
          elsepart = vc_bvConstExprFromInt(vc,32, 0);
        }
    }
  return ite;
}

Expr vc_bvVar32RightShiftExpr(VC vc, Expr sh_amt, Expr child) {
  Expr ifpart;
  Expr thenpart;
  Expr elsepart = vc_trueExpr(vc);
  Expr ite = vc_trueExpr(vc);

  int child_width = vc_getBVLength(vc, child);
  int shift_width = vc_getBVLength(vc, sh_amt);

  assert(child_width>0);

  for(int count=32; count >= 0; count--)
    {
      if(count != 32) 
        {
          ifpart = vc_eqExpr(vc, sh_amt,
                             vc_bvConstExprFromInt(vc, shift_width, count));
          thenpart = vc_bvRightShiftExpr(vc, count, child);
          ite = vc_iteExpr(vc,ifpart,thenpart,elsepart);
          elsepart = ite;
        } 
      else 
        {
          elsepart = vc_bvConstExprFromInt(vc,child_width, 0);
        }
    }
  return ite;
}

Expr vc_bvExtract(VC vc, Expr ccc, int hi_num, int low_num) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar a = (nodestar)ccc;
  BVTypeCheck(*a);

  node hi = b->CreateBVConst(32,hi_num);
  node low = b->CreateBVConst(32,low_num);
  node o = b->CreateTerm(BEEV::BVEXTRACT,hi_num-low_num+1,*a,hi,low);
  BVTypeCheck(o);
  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_bvBoolExtract(VC vc, Expr ccc, int bit_num) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar a = (nodestar)ccc;
  BVTypeCheck(*a);

  node bit = b->CreateBVConst(32,bit_num);
  //node o = b->CreateNode(BEEV::BVGETBIT,*a,bit);
  node zero = b->CreateBVConst(1,0);
  node oo = b->CreateTerm(BEEV::BVEXTRACT,1,*a,bit,bit);
  node o = b->CreateNode(BEEV::EQ,oo,zero);
  BVTypeCheck(o);
  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_bvBoolExtract_Zero(VC vc, Expr ccc, int bit_num) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar a = (nodestar)ccc;
  BVTypeCheck(*a);

  node bit = b->CreateBVConst(32,bit_num);
  //node o = b->CreateNode(BEEV::BVGETBIT,*a,bit);
  node zero = b->CreateBVConst(1,0);
  node oo = b->CreateTerm(BEEV::BVEXTRACT,1,*a,bit,bit);
  node o = b->CreateNode(BEEV::EQ,oo,zero);
  BVTypeCheck(o);
  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_bvBoolExtract_One(VC vc, Expr ccc, int bit_num) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar a = (nodestar)ccc;
  BVTypeCheck(*a);

  node bit = b->CreateBVConst(32,bit_num);
  //node o = b->CreateNode(BEEV::BVGETBIT,*a,bit);
  node one = b->CreateBVConst(1,1);
  node oo = b->CreateTerm(BEEV::BVEXTRACT,1,*a,bit,bit);
  node o = b->CreateNode(BEEV::EQ,oo,one);
  BVTypeCheck(o);
  nodestar output = new node(o);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

Expr vc_bvSignExtend(VC vc, Expr ccc, int nbits) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar a = (nodestar)ccc;

  //width of the expr which is being sign extended. nbits is the
  //resulting length of the signextended expr
  BVTypeCheck(*a);

  unsigned exprlen = a->GetValueWidth();
  unsigned outputlen = nbits;
  node n;
  if(exprlen >= outputlen) {
    //extract
    node hi = b->CreateBVConst(32,outputlen-1);
    node low = b->CreateBVConst(32,0);
    n = b->CreateTerm(BEEV::BVEXTRACT,nbits,*a,hi,low);
    BVTypeCheck(n);
  }
  else {
    //sign extend
    BEEV::ASTNode width = b->CreateBVConst(32,nbits);
    n = b->CreateTerm(BEEV::BVSX,nbits,*a, width);
  }

  BVTypeCheck(n);
  nodestar output = new node(n);
  //if(cinterface_exprdelete_on) created_exprs.push_back(output);
  return output;
}

//! Return an int from a constant bitvector expression
int getBVInt(Expr e) {
  //bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar a = (nodestar)e;

  if(BEEV::BVCONST != a->GetKind())
    {
      BEEV::FatalError("CInterface: getBVInt: Attempting to "\
                       "extract int value from a NON-constant BITVECTOR: ",
                       *a);
    }
  return (int)a->GetUnsignedConst();
}

//! Return an unsigned int from a constant bitvector expression
unsigned int getBVUnsigned(Expr e) {
  //bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar a = (nodestar)e;

  if(BEEV::BVCONST != a->GetKind())
    {
      BEEV::FatalError("getBVUnsigned: Attempting to extract int "\
                       "value from a NON-constant BITVECTOR: ",
                       *a);
    }
  return (unsigned int)a->GetUnsignedConst();
}

//! Return an unsigned long long int from a constant bitvector expression
unsigned long long int getBVUnsignedLongLong(Expr e) {
  //bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar a = (nodestar)e;

  if(BEEV::BVCONST != a->GetKind())
    BEEV::FatalError("getBVUnsigned: Attempting to extract int value"\
                     "from a NON-constant BITVECTOR: ",*a);
  unsigned* bv = a->GetBVConst();

  char * str_bv  = (char *)CONSTANTBV::BitVector_to_Bin(bv);
  unsigned long long int tmp = strtoull(str_bv,NULL,2);
  CONSTANTBV::BitVector_Dispose((unsigned char *)str_bv);
  return tmp;
}


Expr vc_simplify(VC vc, Expr e) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar a = (nodestar)e;
  simpstar simp = (simpstar)(((stpstar)vc)->simp);

  if(BEEV::BOOLEAN_TYPE == a->GetType()) 
    {
      nodestar round1 = 
        new node(simp->SimplifyFormula_TopLevel(*a,false));
      //b->Begin_RemoveWrites = true;
      nodestar output = 
        new node(simp->SimplifyFormula_TopLevel(*round1,false));
      //if(cinterface_exprdelete_on) created_exprs.push_back(output);
      //b->Begin_RemoveWrites = false;
      delete round1;
      return output;
    }
  else 
    {
      nodestar round1 = new node(simp->SimplifyTerm(*a));
      //b->Begin_RemoveWrites = true;
      nodestar output = new node(simp->SimplifyTerm(*round1));
      //if(cinterface_exprdelete_on) created_exprs.push_back(output);
      //b->Begin_RemoveWrites = false;
      delete round1;
      return output;
    }
}

/* C pointer support: C interface to support C memory arrays in CVCL */
Expr vc_bvCreateMemoryArray(VC vc, const char * arrayName) {
  Type bv8  = vc_bvType(vc,8);
  Type bv32 = vc_bvType(vc,32);

  Type malloced_mem0 = vc_arrayType(vc,bv32,bv8);
  return vc_varExpr(vc, arrayName, malloced_mem0);
}

Expr vc_bvReadMemoryArray(VC vc,
                          Expr array,
                          Expr byteIndex, int numOfBytes) {
  if(!(numOfBytes > 0))
    BEEV::FatalError("numOfBytes must be greater than 0");

  if(numOfBytes == 1)
    return vc_readExpr(vc,array,byteIndex);
  else 
    {
      int count = 1;
      Expr a = vc_readExpr(vc,array,byteIndex);
      while(--numOfBytes > 0) 
        {
          Expr b = vc_readExpr(vc,array,
                               /*vc_simplify(vc, */
                               vc_bvPlusExpr(vc, 32,
                                             byteIndex,
                                             vc_bvConstExprFromInt(vc,32,
                                                                   count)));
          a = vc_bvConcatExpr(vc,b,a);
          count++;
        }
      return a;
    }
}

Expr vc_bvWriteToMemoryArray(VC vc,
                             Expr array, Expr byteIndex,
                             Expr element, int numOfBytes) {
  if(!(numOfBytes > 0))
    BEEV::FatalError("numOfBytes must be greater than 0");

  int newBitsPerElem = numOfBytes*8;
  if(numOfBytes == 1)
    return vc_writeExpr(vc, array, byteIndex, element);
  else {
    int count = 1;
    int hi = newBitsPerElem - 1;
    int low = newBitsPerElem - 8;
    int low_elem = 0;
    int hi_elem = low_elem + 7;
    Expr c = vc_bvExtract(vc, element, hi_elem, low_elem);
    Expr newarray = vc_writeExpr(vc, array, byteIndex, c);
    while(--numOfBytes > 0) {
      hi = low-1;
      low = low-8;
            
      low_elem = low_elem + 8;
      hi_elem = low_elem + 7;
            
      c = vc_bvExtract(vc, element, hi_elem, low_elem);
      newarray =
        vc_writeExpr(vc, newarray,
                     vc_bvPlusExpr(vc, 32, 
                                   byteIndex, 
                                   vc_bvConstExprFromInt(vc,32,count)),
                     c);
      count++;
    }
    return newarray;
  }
}

Expr vc_bv32ConstExprFromInt(VC vc, unsigned int value){
  return vc_bvConstExprFromInt(vc, 32, value);
}


#if 0
static char *val_to_binary_str(unsigned nbits, unsigned long long val) {
  char s[65];

  assert(nbits < sizeof s);
  strcpy(s, "");
  while(nbits-- > 0) {
    if((val >> nbits) & 1)
      strcat(s, "1");
    else
      strcat(s, "0");
  }
  return strdup(s);
}
#endif

Expr vc_parseExpr(VC vc, const char* infile) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  extern FILE *cvcin, *smtin;
  const char * prog = "stp";

  cvcin = fopen(infile,"r");
  if(cvcin == NULL) {
    fprintf(stderr,"%s: Error: cannot open %s\n",prog,infile);
    BEEV::FatalError("");
  }

  //BEEV::GlobalSTP = (stpstar)vc;
  CONSTANTBV::ErrCode c = CONSTANTBV::BitVector_Boot();
  if(0 != c) {
    cout << CONSTANTBV::BitVector_Error(c) << endl;
    return 0;
  }

  BEEV::Cpp_interface pi(*b, b->defaultNodeFactory);
  BEEV::parserInterface = &pi;


  BEEV::ASTVec * AssertsQuery = new BEEV::ASTVec;
  if (b->UserFlags.smtlib1_parser_flag) 
    {
      smtin = cvcin;
      cvcin = NULL;
      smtparse((void*)AssertsQuery);
    } 
  else
    {
      cvcparse((void*)AssertsQuery);
    }

  BEEV::ASTNode asserts = (*(BEEV::ASTVec*)AssertsQuery)[0];
  BEEV::ASTNode query   = (*(BEEV::ASTVec*)AssertsQuery)[1];


  node oo = b->CreateNode(BEEV::NOT,query);
  node o = b->CreateNode(BEEV::AND,asserts,oo);
  nodestar output = new node(o);
  delete AssertsQuery;
  return output;
} //end of vc_parseExpr()

char* exprString(Expr e){
  stringstream ss;
  ((nodestar)e)->PL_Print(ss,0);
  string s = ss.str();
  char *copy = strdup(s.c_str());
  return copy;
}

char* typeString(Type t){
  stringstream ss;
  ((nodestar)t)->PL_Print(ss,0);

  string s = ss.str();
  char *copy = strdup(s.c_str());
  return copy;
}

Expr getChild(Expr e, int i){
  nodestar a = (nodestar)e;

  BEEV::ASTVec c = a->GetChildren();
  if(0 <=  i && (unsigned)i < c.size()) 
    {
      BEEV::ASTNode o = c[i];
      nodestar output = new node(o);
      //if(cinterface_exprdelete_on) created_exprs.push_back(output);
      return output;
    }
  else
    {
      BEEV::FatalError("getChild: Error accessing childNode "   \
                       "in expression: ",*a);
    }
  return a;
}

void vc_registerErrorHandler(void (*error_hdlr)(const char* err_msg)) {
  BEEV::vc_error_hdlr = error_hdlr;
}


int vc_getHashQueryStateToBuffer(VC vc, Expr query) {
  assert(vc);
  assert(query);
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  nodestar qry = (nodestar)query;
  BEEV::ASTVec v = b->GetAsserts();
  BEEV::ASTNode out = b->CreateNode(BEEV::AND,b->CreateNode(BEEV::NOT,*qry),v);
  return out.Hash();
}

Type vc_getType(VC vc, Expr ex) {
  nodestar e = (nodestar)ex;
  
  switch(e->GetType()) {
  case BEEV::BOOLEAN_TYPE:
    return vc_boolType(vc);
    break;
  case BEEV::BITVECTOR_TYPE:
    return vc_bvType(vc,e->GetValueWidth());
    break;
  case BEEV::ARRAY_TYPE: {
    Type typeindex = vc_bvType(vc,e->GetIndexWidth());
    Type typedata = vc_bvType(vc,e->GetValueWidth());
    return vc_arrayType(vc,typeindex,typedata);
    break;
  }
  default:
    BEEV::FatalError("c_interface: vc_GetType: "\
                     "expression with bad typing: "\
                     "please check your expression construction");
    return vc_boolType(vc);
    break;
  }
}// end of vc_gettype()

//!if e is TRUE then return 1; if e is FALSE then return 0; otherwise
//return -1
int vc_isBool(Expr e) {
  nodestar input = (nodestar)e;
  if(BEEV::TRUE == input->GetKind()) {
    return 1;
  }

  if(BEEV::FALSE == input->GetKind()) {
    return 0;
  }

  return -1;
}

void vc_Destroy(VC vc) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  // for(std::vector<BEEV::ASTNode *>::iterator it=created_exprs.begin(),
  //    itend=created_exprs.end();it!=itend;it++) {
  //     BEEV::ASTNode * aaa = *it;
  //     delete aaa;
  //   }

  if (cinterface_exprdelete_on_flag) {
    for (vector<nodestar>::iterator it = persist.begin(); it!= persist.end();it++)
      delete *it;
    persist.clear();
  }

  Cnf_ClearMemory();

  delete decls;
  delete (stpstar)vc;
  BEEV::GlobalSTP = NULL;
  delete  BEEV::ParserBM;
  BEEV::ParserBM = NULL;
  delete simpNF;
}

void vc_DeleteExpr(Expr e) {
  nodestar input = (nodestar)e;
  //bmstar b = (bmstar)(((stpstar)vc)->bm);
  delete input;
}

exprkind_t getExprKind(Expr e) {
  nodestar input = (nodestar)e;
  return (exprkind_t)(input->GetKind());
}

int getDegree (Expr e) {
  nodestar input = (nodestar)e;
  return input->Degree();
}

int getBVLength(Expr ex) {
  nodestar e = (nodestar)ex;
  
  if(BEEV::BITVECTOR_TYPE != e->GetType()) 
    {
      BEEV::FatalError("c_interface: vc_GetBVLength: "\
                       "Input expression must be a bit-vector");
    }
  
  return e->GetValueWidth();
}

type_t getType (Expr ex) {
  nodestar e = (nodestar)ex;  
  return (type_t)(e->GetType());
}

int getVWidth (Expr ex) {
  nodestar e = (nodestar)ex;
  return e->GetValueWidth();
}

int getIWidth (Expr ex) {
  nodestar e = (nodestar)ex;
  return e->GetIndexWidth();
}

void vc_printCounterExampleFile(VC vc, int fd) {
  fdostream os(fd);
  bmstar b = (bmstar)(((stpstar)vc)->bm);
  ctrexamplestar ce = (ctrexamplestar)(((stpstar)vc)->Ctr_Example);  
  
  bool currentPrint = b->UserFlags.print_counterexample_flag;
  b->UserFlags.print_counterexample_flag = true;
  os << "COUNTEREXAMPLE BEGIN: \n";
  ce->PrintCounterExample(true, os);
  os << "COUNTEREXAMPLE END: \n";
  b->UserFlags.print_counterexample_flag = currentPrint;
}

const char* exprName(Expr e){
  return ((nodestar)e)->GetName();
}

int getExprID (Expr ex) {
  BEEV::ASTNode q = (*(nodestar)ex);  
  return q.GetNodeNum();
}

//////////////////////////////////////////////////////////////////////////
// extended version


#if 0
/#ifndef YY_TYPEDEF_YY_BUFFER_STATE
struct yy_buffer_state;
#define YY_TYPEDEF_YY_BUFFER_STATE
typedef struct yy_buffer_state *YY_BUFFER_STATE;


extern YY_BUFFER_STATE cvc_scan_string (const char *yy_str  );
extern void cvc_delete_buffer (YY_BUFFER_STATE  b );
extern YY_BUFFER_STATE smt_scan_string (const char *yy_str  );
extern void smt_delete_buffer (YY_BUFFER_STATE  b );
extern void cvc_switch_to_buffer (YY_BUFFER_STATE new_buffer  );
extern void smt_switch_to_buffer (YY_BUFFER_STATE new_buffer  );
#endif

int smt_scan_string(const char *yy_str);

int vc_parseMemExpr(VC vc, const char* s, Expr* oquery, Expr* oasserts ) {
  bmstar b = (bmstar)(((stpstar)vc)->bm);

#if 0
 BEEV::GlobalSTP = (stpstar)vc;
  CONSTANTBV::ErrCode c = CONSTANTBV::BitVector_Boot();
  if(0 != c) {
    cout << CONSTANTBV::BitVector_Error(c) << endl;
    return 0;
  }
#endif
  
  BEEV::Cpp_interface pi(*b, b->defaultNodeFactory);
  BEEV::parserInterface = &pi;

  BEEV::ASTVec AssertsQuery;
  if (b->UserFlags.smtlib1_parser_flag) 
    {
      //YY_BUFFER_STATE bstat = smt_scan_string(s);
      //smt_switch_to_buffer(bstat);
      smt_scan_string(s);
      smtparse((void*)&AssertsQuery);
      //smt_delete_buffer(bstat);
    } 
  else
    {
      //YY_BUFFER_STATE bstat = cvc_scan_string(s);
      //cvc_switch_to_buffer(bstat);
      smt_scan_string(s);
      cvcparse((void*)&AssertsQuery);
      //cvc_delete_buffer(bstat);
    }

  if ( oquery ) {
    *(nodestar*) oquery = new node(AssertsQuery[1]);
  }
  if ( oasserts ) {
    *(nodestar*) oasserts = new node(AssertsQuery[0]);
  }
  return 1;
} //end of vc_parseMemExpr()

