%{
  /********************************************************************
   * AUTHORS: Vijay Ganesh, Trevor Hansen
   *
   * BEGIN DATE: July, 2006
   *
   * This file is modified version of the CVCL's smtlib.y file. Please
   * see CVCL license below
   ********************************************************************/
  
  /********************************************************************
   *
   * \file smtlib.y
   * 
   * Author: Sergey Berezin, Clark Barrett
   * 
   * Created: Apr 30 2005
   *
   * <hr>
   * Copyright (C) 2004 by the Board of Trustees of Leland Stanford
   * Junior University and by New York University. 
   *
   * License to use, copy, modify, sell and/or distribute this software
   * and its documentation for any purpose is hereby granted without
   * royalty, subject to the terms and conditions defined in the \ref
   * LICENSE file provided with this distribution.  In particular:
   *
   * - The above copyright notice and this permission notice must appear
   * in all copies of the software and related documentation.
   *
   * - THE SOFTWARE IS PROVIDED "AS-IS", WITHOUT ANY WARRANTIES,
   * EXPRESSED OR IMPLIED.  USE IT AT YOUR OWN RISK.
   * 
   * <hr>
   ********************************************************************/
  // -*- c++ -*-

#include "../cpp_interface/cpp_interface.h"

  using namespace std; 
  using namespace BEEV;

  // Suppress the bogus warning suppression in bison (it generates
  // compile error)
#undef __GNUC_MINOR__
  
  extern char* smttext;
  extern int smtlineno;
  extern int smtlex(void);

  int yyerror(const char *s) {
    cout << "syntax error: line " << smtlineno << "\n" << s << endl;
    cout << "  token: " << smttext << endl;
    FatalError("");
    return 1;
  }
  int yyerror(void* AssertsQuery, const char* s) { return yyerror(s); }

  ASTNode query;
#define YYLTYPE_IS_TRIVIAL 1
#define YYMAXDEPTH 104857600
#define YYERROR_VERBOSE 1
#define YY_EXIT_FAILURE -1
  %}

%parse-param {void* AssertsQuery}

%union {  
  // FIXME: Why is this not an UNSIGNED int?
  int uintval;                  /* for numerals in types. */

  // for BV32 BVCONST 
  unsigned long long ullval;

  struct {
    //stores the indexwidth and valuewidth
    //indexwidth is 0 iff type is bitvector. positive iff type is
    //array, and stores the width of the indexing bitvector
    unsigned int indexwidth;
    //width of the bitvector type
    unsigned int valuewidth;
  } indexvaluewidth;

  //ASTNode,ASTVec
  BEEV::ASTNode *node;
  BEEV::ASTVec *vec;
  std::string *str;
};

%start cmd

%type <indexvaluewidth> sort_symb sort_symbs
%type <node> status
%type <vec> bench_attributes an_formulas an_terms

%type <node> benchmark bench_attribute
%type <node> an_term an_nonbvconst_term an_formula 

%type <node> var fvar 
%type <str> user_value logic_name bench_name

%token <uintval> NUMERAL_TOK
%token <str> BVCONST_TOK
%token <node> BITCONST_TOK
%token <node> FORMID_TOK TERMID_TOK 
%token <str> STRING_TOK
%token <str> USER_VAL_TOK
%token SOURCE_TOK
%token CATEGORY_TOK
%token DIFFICULTY_TOK
%token BITVEC_TOK
%token ARRAY_TOK
%token SELECT_TOK
%token STORE_TOK
%token TRUE_TOK
%token FALSE_TOK
%token NOT_TOK
%token IMPLIES_TOK
%token ITE_TOK
%token AND_TOK
%token OR_TOK
%token XOR_TOK
%token IFF_TOK
%token EXISTS_TOK
%token FORALL_TOK
%token LET_TOK
%token FLET_TOK
%token NOTES_TOK
%token CVC_COMMAND_TOK
%token SORTS_TOK
%token FUNS_TOK
%token PREDS_TOK
%token EXTENSIONS_TOK
%token DEFINITION_TOK
%token AXIOMS_TOK
%token LOGIC_TOK
%token COLON_TOK
%token LBRACKET_TOK
%token RBRACKET_TOK
%token LPAREN_TOK
%token RPAREN_TOK
%token SAT_TOK
%token UNSAT_TOK
%token UNKNOWN_TOK
%token ASSUMPTION_TOK
%token FORMULA_TOK
%token STATUS_TOK
%token BENCHMARK_TOK
%token EXTRASORTS_TOK
%token EXTRAFUNS_TOK
%token EXTRAPREDS_TOK
%token LANGUAGE_TOK
%token DOLLAR_TOK
%token QUESTION_TOK
%token DISTINCT_TOK
%token SEMICOLON_TOK
%token EOF_TOK
%token EQ_TOK
 /*BV SPECIFIC TOKENS*/
%token NAND_TOK
%token NOR_TOK
%token NEQ_TOK
%token ASSIGN_TOK
%token BV_TOK
%token BOOLEAN_TOK
%token BVLEFTSHIFT_1_TOK
%token BVRIGHTSHIFT_1_TOK
%token BVARITHRIGHTSHIFT_TOK
%token BVPLUS_TOK
%token BVSUB_TOK
%token BVNOT_TOK //bvneg in CVCL
%token BVMULT_TOK
%token BVDIV_TOK
%token SBVDIV_TOK
%token BVMOD_TOK
%token SBVREM_TOK
%token SBVMOD_TOK
%token BVNEG_TOK //bvuminus in CVCL
%token BVAND_TOK
%token BVOR_TOK
%token BVXOR_TOK
%token BVNAND_TOK
%token BVNOR_TOK
%token BVXNOR_TOK
%token BVCONCAT_TOK
%token BVLT_TOK
%token BVGT_TOK
%token BVLE_TOK
%token BVGE_TOK
%token BVSLT_TOK
%token BVSGT_TOK
%token BVSLE_TOK
%token BVSGE_TOK
%token BVSX_TOK 
%token BVZX_TOK
%token BVROTATE_RIGHT_TOK
%token BVROTATE_LEFT_TOK
%token BVREPEAT_TOK 
%token BVCOMP_TOK

%token BOOLEXTRACT_TOK
%token BOOL_TO_BV_TOK
%token BVEXTRACT_TOK

%left LBRACKET_TOK RBRACKET_TOK

%%

cmd:
benchmark
{
  ASTNode assumptions;
  if($1 == NULL) 
    {
      assumptions = parserInterface->CreateNode(TRUE);
    } 
  else 
    {
      assumptions = *$1;
    }
      
  if(query.IsNull()) 
    {
      query = parserInterface->CreateNode(FALSE);
    }

  ((ASTVec*)AssertsQuery)->push_back(assumptions);
  ((ASTVec*)AssertsQuery)->push_back(query);
  delete $1;
  parserInterface->letMgr.cleanupParserSymbolTable();
  query = ASTNode();
  YYACCEPT;
}
;

benchmark:
LPAREN_TOK BENCHMARK_TOK bench_name bench_attributes RPAREN_TOK
{
  if($4 != NULL){
    if($4->size() > 1) 
      $$ = new ASTNode(parserInterface->CreateNode(AND,*$4));
    else if($4->size() ==1)
      $$ = new ASTNode((*$4)[0]);
     else
      $$ = new ASTNode(parserInterface->CreateNode(TRUE));     
    delete $4;
  }
  else {
    $$ = NULL;
  }
  delete $3; //discard the benchmarkname.
}
/*   | EOF_TOK */
/*     { */
/*     } */
;

bench_name:
STRING_TOK
{
}
;

bench_attributes:
bench_attribute
{
  $$ = new ASTVec;
  if ($1 != NULL) {
    $$->push_back(*$1);
    parserInterface->AddAssert(*$1);
    delete $1;
  }
}
| bench_attributes bench_attribute
{
  if ($1 != NULL && $2 != NULL) {
    $1->push_back(*$2);
    parserInterface->AddAssert(*$2);
    $$ = $1;
    delete $2;
  }
}
;

bench_attribute:
COLON_TOK ASSUMPTION_TOK an_formula
{
  //assumptions are like asserts
  $$ = $3;
}
| COLON_TOK FORMULA_TOK an_formula
{
  // Previously this would call AddQuery() on the negation.
  // But if multiple formula were (eroneously) present
  // it discarded all but the last formula. Allowing multiple 
  // formula and taking the conjunction of them along with all
  // the assumptions is what the other solvers do.  

  //assumptions are like asserts
  $$ = $3;
}
| COLON_TOK STATUS_TOK status
{
  $$ = NULL;
}
| COLON_TOK LOGIC_TOK logic_name
{
  if (!(0 == strcmp($3->c_str(),"QF_UFBV")  ||
        0 == strcmp($3->c_str(),"QF_BV") ||
        //0 == strcmp($3->c_str(),"QF_UF") ||
        0 == strcmp($3->c_str(),"QF_AUFBV"))) {
    yyerror("Wrong input logic:");
  }
  delete $3;
  $$ = NULL;
}
| COLON_TOK EXTRAFUNS_TOK LPAREN_TOK var_decls RPAREN_TOK
{
  $$ = NULL;
}
| COLON_TOK EXTRAPREDS_TOK LPAREN_TOK var_decls RPAREN_TOK
{
  $$ = NULL;
}
| annotation 
{
  $$ = NULL;
}
;

logic_name:
STRING_TOK LBRACKET_TOK NUMERAL_TOK RBRACKET_TOK
{
  $$ = $1;
}
| STRING_TOK
{
  $$ = $1;
}
;

status:
SAT_TOK { 
  input_status = TO_BE_SATISFIABLE; 
  $$ = NULL; 
}
| UNSAT_TOK { 
  input_status = TO_BE_UNSATISFIABLE; 
  $$ = NULL; 
  }
| UNKNOWN_TOK 
{ 
  input_status = TO_BE_UNKNOWN; 
  $$ = NULL; 
}
;


/* annotations: */
/*     annotation */
/*     { */
/*     } */
/*   | annotations annotation */
/*     { */
/*     } */
/*   ; */
  
annotation:
attribute 
{
}
| attribute user_value 
{
}
;

user_value:
USER_VAL_TOK
{
  //cerr << "Printing user_value: " << *$1 << endl;
  delete $1;
}
;

attribute:
COLON_TOK SOURCE_TOK
{
}
| COLON_TOK CATEGORY_TOK
{
}
| COLON_TOK DIFFICULTY_TOK 
;

sort_symbs:
sort_symb 
{
  //a single sort symbol here means either a BitVec or a Boolean
  $$.indexwidth = $1.indexwidth;
  $$.valuewidth = $1.valuewidth;
}
| sort_symb sort_symb
{
  //two sort symbols mean f: type --> type
  $$.indexwidth = $1.valuewidth;
  $$.valuewidth = $2.valuewidth;
}
;

// There are some gulwani benchmarks that create multiple variables in the same header.
// Maybe you shouldn'.t..
var_decls:
var_decl
{}
|
var_decls var_decl
{}
;



var_decl:
LPAREN_TOK STRING_TOK sort_symbs RPAREN_TOK
{
  ASTNode s = BEEV::parserInterface->LookupOrCreateSymbol($2->c_str());
  //Sort_symbs has the indexwidth/valuewidth. Set those fields in
  //var
  s.SetIndexWidth($3.indexwidth);
  s.SetValueWidth($3.valuewidth);
  parserInterface->letMgr._parser_symbol_table.insert(s);
  delete $2;
}
| LPAREN_TOK STRING_TOK RPAREN_TOK
{
  ASTNode s = BEEV::parserInterface->LookupOrCreateSymbol($2->c_str());
  s.SetIndexWidth(0);
  s.SetValueWidth(0);
  parserInterface->letMgr._parser_symbol_table.insert(s);
  //Sort_symbs has the indexwidth/valuewidth. Set those fields in
  //var
  delete $2;
}
;

an_formulas:
an_formula
{
  $$ = new ASTVec;
  if ($1 != NULL) {
    $$->push_back(*$1);
    delete $1;
  }
}
|
an_formulas an_formula
{
  if ($1 != NULL && $2 != NULL) {
    $1->push_back(*$2);
    $$ = $1;
    delete $2;
  }
}
;

an_formula:   
TRUE_TOK
{
  $$ = new ASTNode(parserInterface->CreateNode(TRUE)); 
  assert(0 == $$->GetIndexWidth()); 
  assert(0 == $$->GetValueWidth());
}
| FALSE_TOK
{
  $$ = new ASTNode(parserInterface->CreateNode(FALSE)); 
  assert(0 == $$->GetIndexWidth()); 
  assert(0 == $$->GetValueWidth());
}
| fvar
{
  $$ = $1;
}
| LPAREN_TOK EQ_TOK an_term an_term RPAREN_TOK
{
  ASTNode * n = new ASTNode(parserInterface->CreateNode(EQ,*$3, *$4));
  $$ = n;
  delete $3;
  delete $4;      
}
| LPAREN_TOK DISTINCT_TOK an_terms RPAREN_TOK
{
  using namespace BEEV;

  ASTVec terms = *$3;
  ASTVec forms;

  for(ASTVec::const_iterator it=terms.begin(),itend=terms.end();
      it!=itend; it++) {
    for(ASTVec::const_iterator it2=it+1; it2!=itend; it2++) {
      ASTNode n = (parserInterface->nf->CreateNode(NOT, parserInterface->CreateNode(EQ, *it, *it2)));

          
      forms.push_back(n); 
    }
  }

  if(forms.size() == 0) 
    FatalError("empty distinct");
 
  $$ = (forms.size() == 1) ?
    new ASTNode(forms[0]) :
    new ASTNode(parserInterface->CreateNode(AND, forms));

  delete $3;
}

| LPAREN_TOK BVSLT_TOK an_term an_term RPAREN_TOK
  //| LPAREN_TOK BVSLT_TOK an_term an_term annotations RPAREN_TOK
{
  ASTNode * n = parserInterface->newNode(BVSLT, *$3, *$4);
  $$ = n;
  delete $3;
  delete $4;      
}
| LPAREN_TOK BVSLE_TOK an_term an_term RPAREN_TOK
  //| LPAREN_TOK BVSLE_TOK an_term an_term annotations RPAREN_TOK
{
  ASTNode * n = parserInterface->newNode(BVSLE, *$3, *$4);
  $$ = n;
  delete $3;
  delete $4;      
}
| LPAREN_TOK BVSGT_TOK an_term an_term RPAREN_TOK
  //| LPAREN_TOK BVSGT_TOK an_term an_term annotations RPAREN_TOK
{
  ASTNode * n = parserInterface->newNode(BVSGT, *$3, *$4);
  $$ = n;
  delete $3;
  delete $4;      
}
| LPAREN_TOK BVSGE_TOK an_term an_term RPAREN_TOK
  //| LPAREN_TOK BVSGE_TOK an_term an_term annotations RPAREN_TOK
{
  ASTNode * n = parserInterface->newNode(BVSGE, *$3, *$4);
  $$ = n;
  delete $3;
  delete $4;      
}
| LPAREN_TOK BVLT_TOK an_term an_term RPAREN_TOK
  //| LPAREN_TOK BVLT_TOK an_term an_term annotations RPAREN_TOK
{
  ASTNode * n = parserInterface->newNode(BVLT, *$3, *$4);
  $$ = n;
  delete $3;
  delete $4;      
}
| LPAREN_TOK BVLE_TOK an_term an_term RPAREN_TOK
  //| LPAREN_TOK BVLE_TOK an_term an_term annotations RPAREN_TOK
{
  ASTNode * n = parserInterface->newNode(BVLE, *$3, *$4);
  $$ = n;
  delete $3;
  delete $4;      
}
| LPAREN_TOK BVGT_TOK an_term an_term RPAREN_TOK
  //| LPAREN_TOK BVGT_TOK an_term an_term annotations RPAREN_TOK
{
  ASTNode * n = parserInterface->newNode(BVGT, *$3, *$4);
  $$ = n;
  delete $3;
  delete $4;      
}
| LPAREN_TOK BVGE_TOK an_term an_term RPAREN_TOK
  //| LPAREN_TOK BVGE_TOK an_term an_term annotations RPAREN_TOK
{
  ASTNode * n = parserInterface->newNode(BVGE, *$3, *$4);
  $$ = n;
  delete $3;
  delete $4;      
}
| LPAREN_TOK an_formula RPAREN_TOK
{
  $$ = $2;
}
| LPAREN_TOK NOT_TOK an_formula RPAREN_TOK
{
  $$ = new ASTNode(parserInterface->nf->CreateNode(NOT, *$3));
  delete $3;
}
| LPAREN_TOK IMPLIES_TOK an_formula an_formula RPAREN_TOK
{
  $$ = parserInterface->newNode(IMPLIES, *$3, *$4);
  delete $3;
  delete $4;
}
| LPAREN_TOK ITE_TOK an_formula an_formula an_formula RPAREN_TOK
{
  $$ = new ASTNode(parserInterface->nf->CreateNode(ITE, *$3, *$4, *$5));
  delete $3;
  delete $4;
  delete $5;
}
| LPAREN_TOK AND_TOK an_formulas RPAREN_TOK
{
  $$ = new ASTNode(parserInterface->CreateNode(AND, *$3));
  delete $3;
}
| LPAREN_TOK OR_TOK an_formulas RPAREN_TOK
{
  $$ = new ASTNode(parserInterface->CreateNode(OR, *$3));
  delete $3;
}
| LPAREN_TOK XOR_TOK an_formula an_formula RPAREN_TOK
{
  $$ = parserInterface->newNode(XOR, *$3, *$4);
  delete $3;
  delete $4;
}
| LPAREN_TOK IFF_TOK an_formula an_formula RPAREN_TOK
{
  $$ = parserInterface->newNode(IFF, *$3, *$4);
  delete $3;
  delete $4;
}
| letexpr_mgmt an_formula RPAREN_TOK
  //| letexpr_mgmt an_formula annotations RPAREN_TOK
{
  $$ = $2;
  //Cleanup the LetIDToExprMap
  parserInterface->letMgr.CleanupLetIDMap();                      
}
;

letexpr_mgmt: 
LPAREN_TOK LET_TOK LPAREN_TOK QUESTION_TOK STRING_TOK an_term RPAREN_TOK
{
  //populate the hashtable from LET-var -->
  //LET-exprs and then process them:
  //
  //1. ensure that LET variables do not clash
  //1. with declared variables.
  //
  //2. Ensure that LET variables are not
  //2. defined more than once
  parserInterface->letMgr.LetExprMgr(*$5,*$6);
  
  delete $5;
  delete $6;      
}
| LPAREN_TOK FLET_TOK LPAREN_TOK DOLLAR_TOK STRING_TOK an_formula RPAREN_TOK 
{
  //Do LET-expr management
  parserInterface->letMgr.LetExprMgr(*$5,*$6);
  delete $5;
  delete $6;     
}

an_terms: 
an_term
{
  $$ = new ASTVec;
  if ($1 != NULL) {
    $$->push_back(*$1);
    delete $1;
  }
}
|
an_terms an_term
{
  if ($1 != NULL && $2 != NULL) {
    $1->push_back(*$2);
    $$ = $1;
    delete $2;
  }
}
;

an_term:
BVCONST_TOK
{
  $$ = new ASTNode(parserInterface->CreateBVConst(*$1, 10, 32));
  delete $1;
}
| BVCONST_TOK LBRACKET_TOK NUMERAL_TOK RBRACKET_TOK
{
  $$ = new ASTNode(parserInterface->CreateBVConst(*$1,10,$3));
  delete $1;
}
| an_nonbvconst_term
{
$$ = $1;
}
;

an_nonbvconst_term: 
BITCONST_TOK { $$ = $1; }
| var
{
  $$ = new ASTNode((*$1));
  delete $1;
}
| LPAREN_TOK an_term RPAREN_TOK
{
  $$ = $2;
}
| SELECT_TOK an_term an_term
{
  //ARRAY READ
  // valuewidth is same as array, indexwidth is 0.
  ASTNode array = *$2;
  ASTNode index = *$3;
  unsigned int width = array.GetValueWidth();
  ASTNode * n = 
    new ASTNode(parserInterface->nf->CreateTerm(READ, width, array, index));
  $$ = n;
  delete $2;
  delete $3;
}
| STORE_TOK an_term an_term an_term
{
  //ARRAY WRITE
  unsigned int width = $4->GetValueWidth();
  ASTNode array = *$2;
  ASTNode index = *$3;
  ASTNode writeval = *$4;
  ASTNode write_term = parserInterface->nf->CreateArrayTerm(WRITE,$2->GetIndexWidth(),width,array,index,writeval);
  ASTNode * n = new ASTNode(write_term);
  $$ = n;
  delete $2;
  delete $3;
  delete $4;
}
| BVEXTRACT_TOK LBRACKET_TOK NUMERAL_TOK COLON_TOK NUMERAL_TOK RBRACKET_TOK an_term
{
  int width = $3 - $5 + 1;
  if (width < 0)
    yyerror("Negative width in extract");
      
  if((unsigned)$3 >= $7->GetValueWidth())
    yyerror("Parsing: Wrong width in BVEXTRACT\n");                      
      
  ASTNode hi  =  parserInterface->CreateBVConst(32, $3);
  ASTNode low =  parserInterface->CreateBVConst(32, $5);
  ASTNode output = parserInterface->nf->CreateTerm(BVEXTRACT, width, *$7,hi,low);
  ASTNode * n = new ASTNode(output);
  $$ = n;
  delete $7;
}
|  ITE_TOK an_formula an_term an_term 
{
  const unsigned int width = $3->GetValueWidth();
  $$ = new ASTNode(parserInterface->nf->CreateArrayTerm(ITE,$4->GetIndexWidth(), width,*$2, *$3, *$4));      
  delete $2;
  delete $3;
  delete $4;
}
|  BVCONCAT_TOK an_term an_term 
{
  const unsigned int width = $2->GetValueWidth() + $3->GetValueWidth();
  ASTNode * n = new ASTNode(parserInterface->nf->CreateTerm(BVCONCAT, width, *$2, *$3));
  $$ = n;
  delete $2;
  delete $3;
}
|  BVNOT_TOK an_term
{
  //this is the BVNEG (term) in the CVCL language
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = new ASTNode(parserInterface->nf->CreateTerm(BVNEG, width, *$2));
  $$ = n;
  delete $2;
}
|  BVNEG_TOK an_term
{
  //this is the BVUMINUS term in CVCL langauge
  unsigned width = $2->GetValueWidth();
  ASTNode * n =  new ASTNode(parserInterface->nf->CreateTerm(BVUMINUS,width,*$2));
  $$ = n;
  delete $2;
}
|  BVAND_TOK an_term an_term 
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(BVAND, width, *$2, *$3);
  $$ = n;
  delete $2;
  delete $3;
}
|  BVOR_TOK an_term an_term 
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(BVOR, width, *$2, *$3); 
  $$ = n;
  delete $2;
  delete $3;
}
|  BVXOR_TOK an_term an_term 
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n =parserInterface->newNode(BVXOR, width, *$2, *$3);
  $$ = n;
  delete $2;
  delete $3;
}
  | BVXNOR_TOK an_term an_term
  {
//   (bvxnor s t) abbreviates (bvor (bvand s t) (bvand (bvnot s) (bvnot t)))

	
      unsigned int width = $2->GetValueWidth();
      ASTNode * n = new ASTNode(
      parserInterface->nf->CreateTerm( BVOR, width,
     parserInterface->nf->CreateTerm(BVAND, width, *$2, *$3),
     parserInterface->nf->CreateTerm(BVAND, width,
	     parserInterface->nf->CreateTerm(BVNEG, width, *$2),
     	 parserInterface->nf->CreateTerm(BVNEG, width, *$3)
     )));

      $$ = n;
      delete $2;
      delete $3;
  
  }
  |  BVCOMP_TOK an_term an_term
  {
	

  	ASTNode * n = new ASTNode(parserInterface->nf->CreateTerm(ITE, 1, 
  	parserInterface->nf->CreateNode(EQ, *$2, *$3),
  	parserInterface->CreateOneConst(1),
  	parserInterface->CreateZeroConst(1)));
  	
      $$ = n;
      delete $2;
      delete $3;
  }
  
    
|  BVSUB_TOK an_term an_term 
{
  const unsigned int width = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(BVSUB, width, *$2, *$3);
  $$ = n;
  delete $2;
  delete $3;
}
|  BVPLUS_TOK an_terms 
{
  const unsigned int width = (*$2)[0].GetValueWidth();
  ASTNode * n = new ASTNode(parserInterface->nf->CreateTerm(BVPLUS, width, *$2));
  $$ = n;
  delete $2;

}
|  BVMULT_TOK an_terms 
{
  const unsigned int width = (*$2)[0].GetValueWidth();
  ASTNode * n = new ASTNode(parserInterface->nf->CreateTerm(BVMULT, width, *$2));
  $$ = n;
  delete $2;
}

|      BVDIV_TOK an_term an_term  
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(BVDIV, width, *$2, *$3);
  $$ = n;

  delete $2;
  delete $3;
}
|      BVMOD_TOK an_term an_term
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(BVMOD, width, *$2, *$3);
  $$ = n;

  delete $2;
  delete $3;
}
|      SBVDIV_TOK an_term an_term
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(SBVDIV, width, *$2, *$3);
  $$ = n;

  delete $2;
  delete $3;
}
|      SBVREM_TOK an_term an_term
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(SBVREM, width, *$2, *$3);
  $$ = n;
  delete $2;
  delete $3;
}        
|      SBVMOD_TOK an_term an_term
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(SBVMOD, width, *$2, *$3);
  $$ = n;
  delete $2;
  delete $3;
}        
|  BVNAND_TOK an_term an_term 
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = new ASTNode(parserInterface->nf->CreateTerm(BVNEG, width, parserInterface->nf->CreateTerm(BVAND, width, *$2, *$3)));
  $$ = n;
  delete $2;
  delete $3;
}
|  BVNOR_TOK an_term an_term 
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = new ASTNode(parserInterface->nf->CreateTerm(BVNEG, width, parserInterface->nf->CreateTerm(BVOR, width, *$2, *$3))); 
  $$ = n;
  delete $2;
  delete $3;
}
|  BVLEFTSHIFT_1_TOK an_term an_term 
{
  // shifting left by who know how much?
  unsigned int w = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(BVLEFTSHIFT,w,*$2,*$3);
  $$ = n;
  delete $2;
  delete $3;
}
| BVRIGHTSHIFT_1_TOK an_term an_term 
{
  // shifting right by who know how much?
  unsigned int w = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(BVRIGHTSHIFT,w,*$2,*$3);
  $$ = n;
  delete $2;
  delete $3;
}
|  BVARITHRIGHTSHIFT_TOK an_term an_term
{
  // shifting arithmetic right by who know how much?
  unsigned int w = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(BVSRSHIFT,w,*$2,*$3);
  $$ = n;
  delete $2;
  delete $3;
}
|  BVROTATE_LEFT_TOK LBRACKET_TOK NUMERAL_TOK RBRACKET_TOK an_term 
{
      
  ASTNode *n;
  unsigned width = $5->GetValueWidth();
  unsigned rotate = $3;
  if (0 == rotate)
    {
      n = $5;
    }
  else if (rotate < width)
    {
      ASTNode high = parserInterface->CreateBVConst(32,width-1);
      ASTNode zero = parserInterface->CreateBVConst(32,0);
      ASTNode cut = parserInterface->CreateBVConst(32,width-rotate);
      ASTNode cutMinusOne = parserInterface->CreateBVConst(32,width-rotate-1);

      ASTNode top =  parserInterface->nf->CreateTerm(BVEXTRACT,rotate,*$5,high, cut);
      ASTNode bottom =  parserInterface->nf->CreateTerm(BVEXTRACT,width-rotate,*$5,cutMinusOne,zero);
      n =  new ASTNode(parserInterface->nf->CreateTerm(BVCONCAT,width,bottom,top));
      delete $5;
    }
  else
    {
      n = NULL; // remove gcc warning.
      yyerror("Rotate must be strictly less than the width.");
    }
      
  $$ = n;
      
}
|  BVROTATE_RIGHT_TOK LBRACKET_TOK NUMERAL_TOK RBRACKET_TOK an_term 
{
      
  ASTNode *n;
  unsigned width = $5->GetValueWidth();
  unsigned rotate = $3;
  if (0 == rotate)
    {
      n = $5;
    }
  else if (rotate < width)
    {
      ASTNode high = parserInterface->CreateBVConst(32,width-1);
      ASTNode zero = parserInterface->CreateBVConst(32,0);
      ASTNode cut = parserInterface->CreateBVConst(32,rotate); 
      ASTNode cutMinusOne = parserInterface->CreateBVConst(32,rotate-1);

      ASTNode bottom =  parserInterface->nf->CreateTerm(BVEXTRACT,rotate,*$5,cutMinusOne, zero);
      ASTNode top =  parserInterface->nf->CreateTerm(BVEXTRACT,width-rotate,*$5,high,cut);
      n =  new ASTNode(parserInterface->nf->CreateTerm(BVCONCAT,width,bottom,top));
      delete $5;
    }
  else
    {
      n = NULL; // remove gcc warning.
      yyerror("Rotate must be strictly less than the width.");
    }
      
  $$ = n;
      
}
   |  BVREPEAT_TOK LBRACKET_TOK NUMERAL_TOK RBRACKET_TOK an_term 
    {
	  unsigned count = $3;
	  if (count < 1)
	  	FatalError("One or more repeats please");

	  unsigned w = $5->GetValueWidth();  
      ASTNode n =  *$5;
      
      for (unsigned i =1; i < count; i++)
      {
      	  n = parserInterface->nf->CreateTerm(BVCONCAT,w*(i+1),n,*$5);
      }
       delete $5;
      $$ = new ASTNode(n);
    }
|  BVSX_TOK LBRACKET_TOK NUMERAL_TOK RBRACKET_TOK an_term 
{
  unsigned w = $5->GetValueWidth() + $3;
  ASTNode width = parserInterface->CreateBVConst(32,w);
  ASTNode *n =  new ASTNode(parserInterface->nf->CreateTerm(BVSX,w,*$5,width));
  $$ = n;
  delete $5;
}
| BVZX_TOK LBRACKET_TOK NUMERAL_TOK RBRACKET_TOK an_term 
{
  if (0 != $3)
    {
      unsigned w = $5->GetValueWidth() + $3;
      ASTNode leading_zeroes = parserInterface->CreateZeroConst($3);
      ASTNode *n =  new ASTNode(parserInterface->nf->CreateTerm(BVCONCAT,w,leading_zeroes,*$5));
      $$ = n;
      delete $5;
    }
  else
    $$ = $5;

}
;
  
sort_symb:
BITVEC_TOK LBRACKET_TOK NUMERAL_TOK RBRACKET_TOK
{
  // Just return BV width.  If sort is BOOL, width is 0.
  // Otherwise, BITVEC[w] returns w. 
  //
  //((indexwidth is 0) && (valuewidth>0)) iff type is BV
  $$.indexwidth = 0;
  unsigned int length = $3;
  if(length > 0) {
    $$.valuewidth = length;
  }
  else {
    FatalError("Fatal Error: parsing: BITVECTORS must be of positive length: \n");
  }
}
| ARRAY_TOK LBRACKET_TOK NUMERAL_TOK COLON_TOK NUMERAL_TOK RBRACKET_TOK
{
  unsigned int index_len = $3;
  unsigned int value_len = $5;
  if(index_len > 0) {
    $$.indexwidth = $3;
  }
  else {
    FatalError("Fatal Error: parsing: BITVECTORS must be of positive length: \n");
  }

  if(value_len > 0) {
    $$.valuewidth = $5;
  }
  else {
    FatalError("Fatal Error: parsing: BITVECTORS must be of positive length: \n");
  }
}
;

var:
FORMID_TOK 
{
  $$ = new ASTNode((*$1)); 
  delete $1;      
}
| TERMID_TOK
{
  $$ = new ASTNode((*$1));
  delete $1;
}
| QUESTION_TOK TERMID_TOK
{
  $$ = $2;
}
;

fvar:
DOLLAR_TOK FORMID_TOK
{
  $$ = $2; 
}
| FORMID_TOK
{
  $$ = new ASTNode((*$1)); 
  delete $1;      
}   
;
%%
