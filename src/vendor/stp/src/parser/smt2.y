%{
  /********************************************************************
   * AUTHORS:  Trevor Hansen
   *
   * BEGIN DATE: May, 2010
   *
   * This file is modified version of the STP's smtlib.y file. Please
   * see CVCL license below
   ********************************************************************/

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
  
  extern char* smt2text;
  extern int smt2lineno;
  extern int smt2lex(void);

  int yyerror(const char *s) {
    cout << "syntax error: line " << smt2lineno << "\n" << s << endl;
    cout << "  token: " << smt2text << endl;
    FatalError("");
    return 1;
  }

   
#define YYLTYPE_IS_TRIVIAL 1
#define YYMAXDEPTH 104857600
#define YYERROR_VERBOSE 1
#define YY_EXIT_FAILURE -1

  %}

%union {  
  unsigned uintval;                  /* for numerals in types. */
  //ASTNode,ASTVec
  BEEV::ASTNode *node;
  BEEV::ASTVec *vec;
  std::string *str;
};

%start cmd

%type <node> status
%type <vec> an_formulas an_terms

%type <node> an_term  an_formula 

%token <uintval> NUMERAL_TOK
%token <str> BVCONST_DECIMAL_TOK
%token <str> BVCONST_BINARY_TOK
%token <str> BVCONST_HEXIDECIMAL_TOK

 /* We have this so we can parse :smt-lib-version 2.0 */
%token  DECIMAL_TOK

%token <node> FORMID_TOK TERMID_TOK 
%token <str> STRING_TOK


 /* set-info tokens */
%token SOURCE_TOK
%token CATEGORY_TOK
%token DIFFICULTY_TOK
%token VERSION_TOK
%token STATUS_TOK
%token PRINT_TOK

 /* ASCII Symbols */
 /* Semicolons (comments) are ignored by the lexer */
%token UNDERSCORE_TOK
%token LPAREN_TOK
%token RPAREN_TOK

 
 /*BV SPECIFIC TOKENS*/
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
%token BVEXTRACT_TOK
%token BVZX_TOK
%token BVROTATE_RIGHT_TOK
%token BVROTATE_LEFT_TOK
%token BVREPEAT_TOK 
%token BVCOMP_TOK

 /* Types for QF_BV and QF_AUFBV. */
%token BITVEC_TOK
%token ARRAY_TOK
%token BOOL_TOK

/* CORE THEORY pg. 29 of the SMT-LIB2 standard 30-March-2010. */
%token TRUE_TOK; 
%token FALSE_TOK;  
%token NOT_TOK;  
%token AND_TOK;  
%token OR_TOK;  
%token XOR_TOK;  
%token ITE_TOK; 
%token EQ_TOK;
%token IMPLIES_TOK; 

 /* CORE THEORY. But not on pg 29. */
%token DISTINCT_TOK; 
%token LET_TOK; 

// COMMANDS
%token EXIT_TOK
%token CHECK_SAT_TOK
%token LOGIC_TOK
%token NOTES_TOK
%token OPTION_TOK
%token DECLARE_FUNCTION_TOK
%token FORMULA_TOK
%token PUSH_TOK
%token POP_TOK

 /* Functions for QF_AUFBV. */
%token SELECT_TOK;
%token STORE_TOK; 

%token END 0 "end of file"

%%
cmd: commands END
{
       parserInterface->cleanUp();
       YYACCEPT;
}
;


commands: commands cmdi  
| cmdi
{}
;

cmdi:
	LPAREN_TOK EXIT_TOK RPAREN_TOK
	{
       parserInterface->cleanUp();
       YYACCEPT;
	}
|	LPAREN_TOK CHECK_SAT_TOK RPAREN_TOK
	{
		parserInterface->checkSat(parserInterface->getAssertVector());
	}
|
	LPAREN_TOK LOGIC_TOK STRING_TOK RPAREN_TOK
	{
	  if (!(0 == strcmp($3->c_str(),"QF_BV") ||
	        0 == strcmp($3->c_str(),"QF_ABV") ||
	        0 == strcmp($3->c_str(),"QF_AUFBV"))) {
	    yyerror("Wrong input logic:");
	  }
	  parserInterface->success();
	  delete $3;
	}
|	LPAREN_TOK NOTES_TOK attribute STRING_TOK RPAREN_TOK
	{
	delete $4;
	}
|	LPAREN_TOK OPTION_TOK attribute RPAREN_TOK
	{
	}
|	LPAREN_TOK NOTES_TOK attribute DECIMAL_TOK RPAREN_TOK
	{}
|	LPAREN_TOK NOTES_TOK attribute RPAREN_TOK
	{}
|	LPAREN_TOK PUSH_TOK NUMERAL_TOK RPAREN_TOK
	{
		for (int i=0; i < $3;i++)
		{
			parserInterface->push();
		}
		parserInterface->success();
	}
|	LPAREN_TOK POP_TOK NUMERAL_TOK RPAREN_TOK
	{
		for (int i=0; i < $3;i++)
			parserInterface->pop();
		parserInterface->success();
	}
|   LPAREN_TOK DECLARE_FUNCTION_TOK var_decl RPAREN_TOK
    {
    parserInterface->success();
    }
|   LPAREN_TOK FORMULA_TOK an_formula RPAREN_TOK
	{
	parserInterface->AddAssert(*$3);
	parserInterface->deleteNode($3);
	parserInterface->success();
	}
;

status:
STRING_TOK { 
 
 std::transform($1->begin(), $1->end(), $1->begin(), ::tolower);
  
  if (0 == strcmp($1->c_str(), "sat"))
  	input_status = TO_BE_SATISFIABLE;
  else if (0 == strcmp($1->c_str(), "unsat"))
    input_status = TO_BE_UNSATISFIABLE;
  else if (0 == strcmp($1->c_str(), "unknown"))
  	input_status = TO_BE_UNKNOWN; 
  else 
  	yyerror($1->c_str());
  delete $1;
  $$ = NULL; 
}
;

attribute:
SOURCE_TOK
{}
| CATEGORY_TOK
{}
| DIFFICULTY_TOK
{}
| VERSION_TOK
{}
| STATUS_TOK status
{} 
| PRINT_TOK TRUE_TOK
{
	parserInterface->setPrintSuccess(true);
	parserInterface->success();
}
| PRINT_TOK FALSE_TOK
{
	parserInterface->setPrintSuccess(false);
}

;

var_decl:
STRING_TOK LPAREN_TOK RPAREN_TOK LPAREN_TOK UNDERSCORE_TOK BITVEC_TOK NUMERAL_TOK RPAREN_TOK
{
  ASTNode s = BEEV::parserInterface->LookupOrCreateSymbol($1->c_str()); 
  parserInterface->addSymbol(s);
  //Sort_symbs has the indexwidth/valuewidth. Set those fields in
  //var
  s.SetIndexWidth(0);
  s.SetValueWidth($7);
  delete $1;
}
| STRING_TOK LPAREN_TOK RPAREN_TOK BOOL_TOK
{
  ASTNode s = BEEV::parserInterface->LookupOrCreateSymbol($1->c_str());
  s.SetIndexWidth(0);
  s.SetValueWidth(0);
  parserInterface->addSymbol(s);
  delete $1;
}
| STRING_TOK LPAREN_TOK RPAREN_TOK LPAREN_TOK ARRAY_TOK LPAREN_TOK UNDERSCORE_TOK BITVEC_TOK NUMERAL_TOK RPAREN_TOK LPAREN_TOK UNDERSCORE_TOK BITVEC_TOK NUMERAL_TOK RPAREN_TOK RPAREN_TOK
{
  ASTNode s = BEEV::parserInterface->LookupOrCreateSymbol($1->c_str());
  parserInterface->addSymbol(s);
  unsigned int index_len = $9;
  unsigned int value_len = $14;
  if(index_len > 0) {
    s.SetIndexWidth($9);
  }
  else {
    FatalError("Fatal Error: parsing: BITVECTORS must be of positive length: \n");
  }

  if(value_len > 0) {
    s.SetValueWidth($14);
  }
  else {
    FatalError("Fatal Error: parsing: BITVECTORS must be of positive length: \n");
  }
  delete $1;
}
;

an_formulas:
an_formula
{
  $$ = new ASTVec;
  if ($1 != NULL) {
    $$->push_back(*$1);
    parserInterface->deleteNode($1);
  }
}
|
an_formulas an_formula
{
  if ($1 != NULL && $2 != NULL) {
    $1->push_back(*$2);
    $$ = $1;
    parserInterface->deleteNode($2);
  }
}
;

an_formula:   
TRUE_TOK
{
  $$ = parserInterface->newNode(parserInterface->CreateNode(TRUE)); 
  assert(0 == $$->GetIndexWidth()); 
  assert(0 == $$->GetValueWidth());
}
| FALSE_TOK
{
  $$ = parserInterface->newNode(parserInterface->CreateNode(FALSE)); 
  assert(0 == $$->GetIndexWidth()); 
  assert(0 == $$->GetValueWidth());
}
| FORMID_TOK
{
  $$ = parserInterface->newNode(*$1); 
  parserInterface->deleteNode($1);      
}
| LPAREN_TOK EQ_TOK an_term an_term RPAREN_TOK
{
  ASTNode * n = parserInterface->newNode(EQ,*$3, *$4);
  $$ = n;
  parserInterface->deleteNode($3);
  parserInterface->deleteNode($4);      
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
    parserInterface->newNode(forms[0]) :
    parserInterface->newNode(parserInterface->CreateNode(AND, forms));

  delete $3;
}
| LPAREN_TOK DISTINCT_TOK an_formulas RPAREN_TOK
{
  using namespace BEEV;

  ASTVec terms = *$3;
  ASTVec forms;

  for(ASTVec::const_iterator it=terms.begin(),itend=terms.end();
      it!=itend; it++) {
    for(ASTVec::const_iterator it2=it+1; it2!=itend; it2++) {
      ASTNode n = (parserInterface->nf->CreateNode(NOT, parserInterface->CreateNode(IFF, *it, *it2)));
      forms.push_back(n); 
    }
  }

  if(forms.size() == 0) 
    FatalError("empty distinct");
 
  $$ = (forms.size() == 1) ?
    parserInterface->newNode(forms[0]) :
    parserInterface->newNode(parserInterface->CreateNode(AND, forms));

  delete $3;
}
| LPAREN_TOK BVSLT_TOK an_term an_term RPAREN_TOK
{
  ASTNode * n = parserInterface->newNode(BVSLT, *$3, *$4);
  $$ = n;
  parserInterface->deleteNode($3);
  parserInterface->deleteNode($4);      
}
| LPAREN_TOK BVSLE_TOK an_term an_term RPAREN_TOK
{
  ASTNode * n = parserInterface->newNode(BVSLE, *$3, *$4);
  $$ = n;
  parserInterface->deleteNode( $3);
  parserInterface->deleteNode( $4);      
}
| LPAREN_TOK BVSGT_TOK an_term an_term RPAREN_TOK
{
  ASTNode * n = parserInterface->newNode(BVSGT, *$3, *$4);
  $$ = n;
  parserInterface->deleteNode( $3);
  parserInterface->deleteNode( $4);      
}
| LPAREN_TOK BVSGE_TOK an_term an_term RPAREN_TOK
{
  ASTNode * n = parserInterface->newNode(BVSGE, *$3, *$4);
  $$ = n;
  parserInterface->deleteNode( $3);
  parserInterface->deleteNode( $4);      
}
| LPAREN_TOK BVLT_TOK an_term an_term RPAREN_TOK
{
  ASTNode * n = parserInterface->newNode(BVLT, *$3, *$4);
  $$ = n;
  parserInterface->deleteNode( $3);
  parserInterface->deleteNode( $4);      
}
| LPAREN_TOK BVLE_TOK an_term an_term RPAREN_TOK
{
  ASTNode * n = parserInterface->newNode(BVLE, *$3, *$4);
  $$ = n;
  parserInterface->deleteNode( $3);
  parserInterface->deleteNode( $4);      
}
| LPAREN_TOK BVGT_TOK an_term an_term RPAREN_TOK
{
  ASTNode * n = parserInterface->newNode(BVGT, *$3, *$4);
  $$ = n;
  parserInterface->deleteNode( $3);
  parserInterface->deleteNode( $4);      
}
| LPAREN_TOK BVGE_TOK an_term an_term RPAREN_TOK
{
  ASTNode * n = parserInterface->newNode(BVGE, *$3, *$4);
  $$ = n;
  parserInterface->deleteNode( $3);
  parserInterface->deleteNode( $4);      
}
| LPAREN_TOK an_formula RPAREN_TOK
{
  $$ = $2;
}
| LPAREN_TOK NOT_TOK an_formula RPAREN_TOK
{
  $$ = parserInterface->newNode(parserInterface->nf->CreateNode(NOT, *$3));
    parserInterface->deleteNode( $3);
}
| LPAREN_TOK IMPLIES_TOK an_formula an_formula RPAREN_TOK
{
  $$ = parserInterface->newNode(IMPLIES, *$3, *$4);
  parserInterface->deleteNode( $3);
  parserInterface->deleteNode( $4);      
}
| LPAREN_TOK ITE_TOK an_formula an_formula an_formula RPAREN_TOK
{
  $$ = parserInterface->newNode(parserInterface->nf->CreateNode(ITE, *$3, *$4, *$5));
  parserInterface->deleteNode( $3);
  parserInterface->deleteNode( $4);      
  parserInterface->deleteNode( $5);
}
| LPAREN_TOK AND_TOK an_formulas RPAREN_TOK
{
  $$ = parserInterface->newNode(parserInterface->CreateNode(AND, *$3));
  delete $3;
}
| LPAREN_TOK OR_TOK an_formulas RPAREN_TOK
{
  $$ = parserInterface->newNode(parserInterface->CreateNode(OR, *$3));
  delete $3;
}
| LPAREN_TOK XOR_TOK an_formula an_formula RPAREN_TOK
{
  $$ = parserInterface->newNode(XOR, *$3, *$4);
  parserInterface->deleteNode( $3);
  parserInterface->deleteNode( $4);
}
| LPAREN_TOK EQ_TOK an_formula an_formula RPAREN_TOK
{
  $$ = parserInterface->newNode(IFF, *$3, *$4);
  parserInterface->deleteNode( $3);
  parserInterface->deleteNode( $4);
}
| LPAREN_TOK LET_TOK LPAREN_TOK lets RPAREN_TOK an_formula RPAREN_TOK
{
  $$ = $6;
  //Cleanup the LetIDToExprMap
  parserInterface->letMgr.CleanupLetIDMap();                      
}
;

lets: let lets 
| let
{};

let: LPAREN_TOK STRING_TOK an_formula RPAREN_TOK
{
  //populate the hashtable from LET-var -->
  //LET-exprs and then process them:
  //
  //1. ensure that LET variables do not clash
  //1. with declared variables.
  //
  //2. Ensure that LET variables are not
  //2. defined more than once
  parserInterface->letMgr.LetExprMgr(*$2,*$3);
  delete $2;
  parserInterface->deleteNode( $3);
}
| LPAREN_TOK STRING_TOK an_term RPAREN_TOK
{
  //populate the hashtable from LET-var -->
  //LET-exprs and then process them:
  //
  //1. ensure that LET variables do not clash
  //1. with declared variables.
  //
  //2. Ensure that LET variables are not
  //2. defined more than once
  parserInterface->letMgr.LetExprMgr(*$2,*$3);
  delete $2;
  parserInterface->deleteNode( $3);

}
;
 
an_terms: 
an_term
{
  $$ = new ASTVec;
  if ($1 != NULL) {
    $$->push_back(*$1);
    parserInterface->deleteNode( $1);
  
  }
}
|
an_terms an_term
{
  if ($1 != NULL && $2 != NULL) {
    $1->push_back(*$2);
    $$ = $1;
    parserInterface->deleteNode( $2);
  }
}
;

an_term: 
TERMID_TOK
{
  $$ = parserInterface->newNode((*$1));
  parserInterface->deleteNode( $1);
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
    parserInterface->newNode(parserInterface->nf->CreateTerm(READ, width, array, index));
  $$ = n;
  parserInterface->deleteNode( $2);
  parserInterface->deleteNode( $3);
}
| STORE_TOK an_term an_term an_term
{
  //ARRAY WRITE
  unsigned int width = $4->GetValueWidth();
  ASTNode array = *$2;
  ASTNode index = *$3;
  ASTNode writeval = *$4;
  ASTNode write_term = parserInterface->nf->CreateArrayTerm(WRITE,$2->GetIndexWidth(),width,array,index,writeval);
  ASTNode * n = parserInterface->newNode(write_term);
  $$ = n;
  parserInterface->deleteNode( $2);
  parserInterface->deleteNode( $3);
  parserInterface->deleteNode( $4);
}
| LPAREN_TOK UNDERSCORE_TOK BVEXTRACT_TOK  NUMERAL_TOK  NUMERAL_TOK RPAREN_TOK an_term
{
  int width = $4 - $5 + 1;
  if (width < 0)
    yyerror("Negative width in extract");
      
  if((unsigned)$4 >= $7->GetValueWidth())
    yyerror("Parsing: Wrong width in BVEXTRACT\n");                      
      
  ASTNode hi  =  parserInterface->CreateBVConst(32, $4);
  ASTNode low =  parserInterface->CreateBVConst(32, $5);
  ASTNode output = parserInterface->nf->CreateTerm(BVEXTRACT, width, *$7,hi,low);
  ASTNode * n = parserInterface->newNode(output);
  $$ = n;
    parserInterface->deleteNode( $7);
}
| LPAREN_TOK UNDERSCORE_TOK BVZX_TOK  NUMERAL_TOK  RPAREN_TOK an_term 
{
  if (0 != $4)
    {
      unsigned w = $6->GetValueWidth() + $4;
      ASTNode leading_zeroes = parserInterface->CreateZeroConst($4);
      ASTNode *n =  parserInterface->newNode(parserInterface->nf->CreateTerm(BVCONCAT,w,leading_zeroes,*$6));
      $$ = n;
      parserInterface->deleteNode( $6);
    }
  else
    $$ = $6;
}
|  LPAREN_TOK UNDERSCORE_TOK BVSX_TOK  NUMERAL_TOK  RPAREN_TOK an_term 
{
  unsigned w = $6->GetValueWidth() + $4;
  ASTNode width = parserInterface->CreateBVConst(32,w);
  ASTNode *n =  parserInterface->newNode(parserInterface->nf->CreateTerm(BVSX,w,*$6,width));
  $$ = n;
  parserInterface->deleteNode( $6);
}

|  ITE_TOK an_formula an_term an_term 
{
  const unsigned int width = $3->GetValueWidth();
  $$ = parserInterface->newNode(parserInterface->nf->CreateArrayTerm(ITE,$4->GetIndexWidth(), width,*$2, *$3, *$4));      
  parserInterface->deleteNode( $2);
  parserInterface->deleteNode( $3);
  parserInterface->deleteNode( $4);
}
|  BVCONCAT_TOK an_term an_term 
{
  const unsigned int width = $2->GetValueWidth() + $3->GetValueWidth();
  ASTNode * n = parserInterface->newNode(parserInterface->nf->CreateTerm(BVCONCAT, width, *$2, *$3));
  $$ = n;
  parserInterface->deleteNode( $2);
  parserInterface->deleteNode( $3);
}
|  BVNOT_TOK an_term
{
  //this is the BVNEG (term) in the CVCL language
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(parserInterface->nf->CreateTerm(BVNEG, width, *$2));
  $$ = n;
  parserInterface->deleteNode( $2);
}
|  BVNEG_TOK an_term
{
  //this is the BVUMINUS term in CVCL langauge
  unsigned width = $2->GetValueWidth();
  ASTNode * n =  parserInterface->newNode(parserInterface->nf->CreateTerm(BVUMINUS,width,*$2));
  $$ = n;
    parserInterface->deleteNode( $2);
}
|  BVAND_TOK an_term an_term 
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(BVAND, width, *$2, *$3);
  $$ = n;
    parserInterface->deleteNode( $2);
    parserInterface->deleteNode( $3);
}
|  BVOR_TOK an_term an_term 
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(BVOR, width, *$2, *$3); 
  $$ = n;
    parserInterface->deleteNode( $2);
    parserInterface->deleteNode( $3);
}
|  BVXOR_TOK an_term an_term 
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(BVXOR, width, *$2, *$3);
  $$ = n;
    parserInterface->deleteNode( $2);
    parserInterface->deleteNode( $3);
}
| BVXNOR_TOK an_term an_term
{
//   (bvxnor s t) abbreviates (bvor (bvand s t) (bvand (bvnot s) (bvnot t)))
      unsigned int width = $2->GetValueWidth();
      ASTNode * n = parserInterface->newNode(
      parserInterface->nf->CreateTerm( BVOR, width,
     parserInterface->nf->CreateTerm(BVAND, width, *$2, *$3),
     parserInterface->nf->CreateTerm(BVAND, width,
	     parserInterface->nf->CreateTerm(BVNEG, width, *$2),
     	 parserInterface->nf->CreateTerm(BVNEG, width, *$3)
     )));

      $$ = n;
    parserInterface->deleteNode( $2);
    parserInterface->deleteNode( $3);
}
|  BVCOMP_TOK an_term an_term
{
  	ASTNode * n = parserInterface->newNode(parserInterface->nf->CreateTerm(ITE, 1, 
  	parserInterface->nf->CreateNode(EQ, *$2, *$3),
  	parserInterface->CreateOneConst(1),
  	parserInterface->CreateZeroConst(1)));
  	
      $$ = n;
    parserInterface->deleteNode( $2);
    parserInterface->deleteNode( $3);
}
|  BVSUB_TOK an_term an_term 
{
  const unsigned int width = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(BVSUB, width, *$2, *$3);
  $$ = n;
    parserInterface->deleteNode( $2);
    parserInterface->deleteNode( $3);
}
|  BVPLUS_TOK an_term an_term 
{
  const unsigned int width = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(BVPLUS, width, *$2, *$3);
  $$ = n;
    parserInterface->deleteNode( $2);
    parserInterface->deleteNode( $3);

}
|  BVMULT_TOK an_term an_term 
{
  const unsigned int width = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(parserInterface->nf->CreateTerm(BVMULT, width, *$2, *$3));
  $$ = n;
    parserInterface->deleteNode( $2);
    parserInterface->deleteNode( $3);
}
|      BVDIV_TOK an_term an_term  
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(BVDIV, width, *$2, *$3);
  $$ = n;

    parserInterface->deleteNode( $2);
    parserInterface->deleteNode( $3);
}
|      BVMOD_TOK an_term an_term
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(BVMOD, width, *$2, *$3);
  $$ = n;

    parserInterface->deleteNode( $2);
    parserInterface->deleteNode( $3);
}
|      SBVDIV_TOK an_term an_term
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(SBVDIV, width, *$2, *$3);
  $$ = n;

    parserInterface->deleteNode( $2);
    parserInterface->deleteNode( $3);
}
|      SBVREM_TOK an_term an_term
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(SBVREM, width, *$2, *$3);
  $$ = n;
    parserInterface->deleteNode( $2);
    parserInterface->deleteNode( $3);
}        
|      SBVMOD_TOK an_term an_term
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(SBVMOD, width, *$2, *$3);
  $$ = n;
    parserInterface->deleteNode( $2);
    parserInterface->deleteNode( $3);
}        
|  BVNAND_TOK an_term an_term 
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(parserInterface->nf->CreateTerm(BVNEG, width, parserInterface->nf->CreateTerm(BVAND, width, *$2, *$3)));
  $$ = n;
    parserInterface->deleteNode( $2);
    parserInterface->deleteNode( $3);
}
|  BVNOR_TOK an_term an_term 
{
  unsigned int width = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(parserInterface->nf->CreateTerm(BVNEG, width, parserInterface->nf->CreateTerm(BVOR, width, *$2, *$3))); 
  $$ = n;
    parserInterface->deleteNode( $2);
    parserInterface->deleteNode( $3);
}
|  BVLEFTSHIFT_1_TOK an_term an_term 
{
  // shifting left by who know how much?
  unsigned int w = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(BVLEFTSHIFT,w,*$2,*$3);
  $$ = n;
    parserInterface->deleteNode( $2);
    parserInterface->deleteNode( $3);
}
| BVRIGHTSHIFT_1_TOK an_term an_term 
{
  // shifting right by who know how much?
  unsigned int w = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(BVRIGHTSHIFT,w,*$2,*$3);
  $$ = n;
    parserInterface->deleteNode( $2);
    parserInterface->deleteNode( $3);
}
|  BVARITHRIGHTSHIFT_TOK an_term an_term
{
  // shifting arithmetic right by who know how much?
  unsigned int w = $2->GetValueWidth();
  ASTNode * n = parserInterface->newNode(BVSRSHIFT,w,*$2,*$3);
  $$ = n;
    parserInterface->deleteNode( $2);
    parserInterface->deleteNode( $3);
}
| LPAREN_TOK UNDERSCORE_TOK BVROTATE_LEFT_TOK  NUMERAL_TOK  RPAREN_TOK an_term
{
  ASTNode *n;
  unsigned width = $6->GetValueWidth();
  unsigned rotate = $4 % width;
  if (0 == rotate)
    {
      n = $6;
    }
  else 
    {
      ASTNode high = parserInterface->CreateBVConst(32,width-1);
      ASTNode zero = parserInterface->CreateBVConst(32,0);
      ASTNode cut = parserInterface->CreateBVConst(32,width-rotate);
      ASTNode cutMinusOne = parserInterface->CreateBVConst(32,width-rotate-1);

      ASTNode top =  parserInterface->nf->CreateTerm(BVEXTRACT,rotate,*$6,high, cut);
      ASTNode bottom =  parserInterface->nf->CreateTerm(BVEXTRACT,width-rotate,*$6,cutMinusOne,zero);
      n =  parserInterface->newNode(parserInterface->nf->CreateTerm(BVCONCAT,width,bottom,top));
          parserInterface->deleteNode( $6);


    }
      
  $$ = n;
}
| LPAREN_TOK UNDERSCORE_TOK BVROTATE_RIGHT_TOK  NUMERAL_TOK  RPAREN_TOK an_term 
{
  ASTNode *n;
  unsigned width = $6->GetValueWidth();
  unsigned rotate = $4 % width;
  if (0 == rotate)
    {
      n = $6;
    }
  else 
    {
      ASTNode high = parserInterface->CreateBVConst(32,width-1);
      ASTNode zero = parserInterface->CreateBVConst(32,0);
      ASTNode cut = parserInterface->CreateBVConst(32,rotate); 
      ASTNode cutMinusOne = parserInterface->CreateBVConst(32,rotate-1);

      ASTNode bottom =  parserInterface->nf->CreateTerm(BVEXTRACT,rotate,*$6,cutMinusOne, zero);
      ASTNode top =  parserInterface->nf->CreateTerm(BVEXTRACT,width-rotate,*$6,high,cut);
      n =  parserInterface->newNode(parserInterface->nf->CreateTerm(BVCONCAT,width,bottom,top));
      parserInterface->deleteNode( $6);
    }
      
  $$ = n;
}
| LPAREN_TOK UNDERSCORE_TOK BVREPEAT_TOK  NUMERAL_TOK RPAREN_TOK an_term
{
	  unsigned count = $4;
	  if (count < 1)
	  	FatalError("One or more repeats please");

	  unsigned w = $6->GetValueWidth();  
      ASTNode n =  *$6;
      
      for (unsigned i =1; i < count; i++)
      {
      	  n = parserInterface->nf->CreateTerm(BVCONCAT,w*(i+1),n,*$6);
      }
      $$ = parserInterface->newNode(n);
      parserInterface->deleteNode( $6);
}
| UNDERSCORE_TOK BVCONST_DECIMAL_TOK NUMERAL_TOK
{
	$$ = parserInterface->newNode(parserInterface->CreateBVConst(*$2, 10, $3));
    $$->SetValueWidth($3);
    delete $2;
}
| BVCONST_HEXIDECIMAL_TOK
{
	unsigned width = $1->length()*4;
	$$ = parserInterface->newNode(parserInterface->CreateBVConst(*$1, 16, width));
    $$->SetValueWidth(width);
    delete $1;
}
| BVCONST_BINARY_TOK
{
	unsigned width = $1->length();
	$$ = parserInterface->newNode(parserInterface->CreateBVConst(*$1, 2, width));
    $$->SetValueWidth(width);
    delete $1;
}
;

%%
