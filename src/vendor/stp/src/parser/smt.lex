%{
  /********************************************************************
   * AUTHORS: Vijay Ganesh, David L. Dill, Trevor Hansen
   *
   * BEGIN DATE: July, 2006
   *
   * This file is modified version of the CVCL's smtlib.lex file. Please
   * see CVCL license below
   ********************************************************************/
   
  /********************************************************************
   * \file smtlib.lex
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
#include <iostream>
#include "parser.h"
#include "parsesmt.hpp"
#include "../cpp_interface/cpp_interface.h"

  using namespace std;
  using namespace BEEV;
  
  extern char *smttext;
  extern int smterror (const char *msg);

  // File-static (local to this file) variables and functions
  static std::string _string_lit;  
  static char escapeChar(char c) {
    switch(c) {
    case 'n': return '\n';
    case 't': return '\t';
    default: return c;
    }
  }      
%}

%option noyywrap
%option nounput
%option noreject
%option noyymore
%option yylineno

%x	COMMENT
%x	STRING_LITERAL
%x      USER_VALUE

LETTER	([a-zA-Z])
DIGIT	([0-9])
OPCHAR	(['\.\_]) 
ANYTHING  ({LETTER}|{DIGIT}|{OPCHAR})

%%
[ \n\t\r\f]	{ /* sk'ip whitespace */ }
{DIGIT}+	{ smtlval.uintval = strtoul(smttext, NULL, 10); return NUMERAL_TOK; }


	 bv{DIGIT}+	{ smtlval.str = new std::string(smttext+2); return BVCONST_TOK; }

bit{DIGIT}+     {
  		   char c = smttext[3];
		   if (c == '1') {
		     smtlval.node = new BEEV::ASTNode(parserInterface->CreateOneConst(1));
		   }
		   else {
		     smtlval.node = new BEEV::ASTNode(parserInterface->CreateZeroConst(1));
		   }
		   return BITCONST_TOK;
		};


";"		{ BEGIN COMMENT; }
<COMMENT>"\n"	{ BEGIN INITIAL; /* return to normal mode */}
<COMMENT>.	{ /* stay in comment mode */ }

<INITIAL>"\""		{ BEGIN STRING_LITERAL;
                          _string_lit.erase(_string_lit.begin(),
                                            _string_lit.end()); }
<STRING_LITERAL>"\\".	{ /* escape characters (like \n or \") */
                          _string_lit.insert(_string_lit.end(),
                                             escapeChar(smttext[1])); }
<STRING_LITERAL>"\""	{ BEGIN INITIAL; /* return to normal mode */
			  smtlval.str = new std::string(_string_lit);
                          return STRING_TOK; }
<STRING_LITERAL>.	{ _string_lit.insert(_string_lit.end(),*smttext); }


<INITIAL>"{"		{ BEGIN USER_VALUE;
                          _string_lit.erase(_string_lit.begin(),
                                            _string_lit.end()); }
<USER_VALUE>"\\"[{}] { /* escape characters */
                          _string_lit.insert(_string_lit.end(),smttext[1]); }

<USER_VALUE>"}"	        { BEGIN INITIAL; /* return to normal mode */
			  smtlval.str = new std::string(_string_lit);
                          return USER_VAL_TOK; }
<USER_VALUE>"\n"        { _string_lit.insert(_string_lit.end(),'\n');}
<USER_VALUE>.	        { _string_lit.insert(_string_lit.end(),*smttext); }

"BitVec"        { return BITVEC_TOK;}
"Array"         { return ARRAY_TOK;}
"true"          { return TRUE_TOK; }
"false"         { return FALSE_TOK; }
"not"           { return NOT_TOK; }
"implies"       { return IMPLIES_TOK; }
"ite"           { return ITE_TOK;}
"if_then_else"  { return ITE_TOK;} // This is in the SMTLIB benchmarks.
"and"           { return AND_TOK; }
"or"            { return OR_TOK; }
"xor"           { return XOR_TOK; }
"iff"           { return IFF_TOK; }
"let"           { return LET_TOK; }
"flet"          { return FLET_TOK; }
"notes"         { return NOTES_TOK; }
"sorts"         { return SORTS_TOK; }
"funs"          { return FUNS_TOK; }
"preds"         { return PREDS_TOK; }
"extensions"    { return EXTENSIONS_TOK; }
"definition"    { return DEFINITION_TOK; }
"axioms"        { return AXIOMS_TOK; }
"logic"         { return LOGIC_TOK; }
"sat"           { return SAT_TOK; }
"unsat"         { return UNSAT_TOK; }
"unknown"       { return UNKNOWN_TOK; }
"assumption"    { return ASSUMPTION_TOK; }
"formula"       { return FORMULA_TOK; }
"status"        { return STATUS_TOK; }
"difficulty"    { return DIFFICULTY_TOK; }
"benchmark"     { return BENCHMARK_TOK; }
"source"        { return SOURCE_TOK;}
"category"      { return CATEGORY_TOK;} 
"extrasorts"    { return EXTRASORTS_TOK; }
"extrafuns"     { return EXTRAFUNS_TOK; }
"extrapreds"    { return EXTRAPREDS_TOK; }
"language"      { return LANGUAGE_TOK; }
"distinct"      { return DISTINCT_TOK; }
"select"        { return SELECT_TOK; }
"store"         { return STORE_TOK; }
":"             { return COLON_TOK; }
"\["            { return LBRACKET_TOK; }
"\]"            { return RBRACKET_TOK; }
"("             { return LPAREN_TOK; }
")"             { return RPAREN_TOK; }
"$"             { return DOLLAR_TOK; }
"?"             { return QUESTION_TOK; }
"="             {return EQ_TOK;}

"nand"		{ return NAND_TOK;}
"nor"		{ return NOR_TOK;}
"bvshl"         { return BVLEFTSHIFT_1_TOK;}
"bvlshr"        { return BVRIGHTSHIFT_1_TOK;}
"bvashr"        { return BVARITHRIGHTSHIFT_TOK;}
"bvadd"         { return BVPLUS_TOK;}
"bvsub"         { return BVSUB_TOK;}
"bvnot"         { return BVNOT_TOK;}
"bvmul"         { return BVMULT_TOK;}
"bvudiv"         { return BVDIV_TOK;}
"bvsdiv"        { return SBVDIV_TOK;}
"bvurem"        { return BVMOD_TOK;} 
"bvsrem"        { return SBVREM_TOK;}
"bvsmod"        { return SBVMOD_TOK;}
"bvneg"         { return BVNEG_TOK;}
"bvand"         { return BVAND_TOK;}
"bvor"          { return BVOR_TOK;}
"bvxor"         { return BVXOR_TOK;}
"bvnand"        { return BVNAND_TOK;}
"bvnor"         { return BVNOR_TOK;}
"bvxnor"        { return BVXNOR_TOK;}
"concat"        { return BVCONCAT_TOK;}
"extract"       { return BVEXTRACT_TOK;}
"bvlt"          { return BVLT_TOK;}
"bvgt"          { return BVGT_TOK;}
"bvleq"         { return BVLE_TOK;}
"bvgeq"         { return BVGE_TOK;}
"bvult"         { return BVLT_TOK;}
"bvugt"         { return BVGT_TOK;}
"bvuleq"        { return BVLE_TOK;}
"bvugeq"        { return BVGE_TOK;}
"bvule"         { return BVLE_TOK;}
"bvuge"         { return BVGE_TOK;}

"bvslt"         { return BVSLT_TOK;}
"bvsgt"         { return BVSGT_TOK;}
"bvsleq"        { return BVSLE_TOK;}
"bvsgeq"        { return BVSGE_TOK;}
"bvsle"         { return BVSLE_TOK;}
"bvsge"         { return BVSGE_TOK;}

"bvcomp"         { return BVCOMP_TOK;}


"zero_extend"   { return BVZX_TOK;}
"sign_extend"   { return BVSX_TOK;} 
"repeat"        { return BVREPEAT_TOK;} 

"rotate_left"   { return BVROTATE_LEFT_TOK;}
"rotate_right"   { return BVROTATE_RIGHT_TOK;} 

"boolextract"   { return BOOLEXTRACT_TOK;}
"boolbv"        { return BOOL_TO_BV_TOK;}

(({LETTER})|(_)({ANYTHING}))({ANYTHING})*	{
  string str(smttext);
   bool found = false;
   ASTNode nptr;
   
  if (BEEV::parserInterface->isSymbolAlreadyDeclared(str)) // it's a symbol.
    {
    	nptr= BEEV::parserInterface->LookupOrCreateSymbol(str);
    	found = true;
    }
    else if (BEEV::parserInterface->letMgr.isLetDeclared(str)) // a let.
    {
    	nptr= BEEV::parserInterface->letMgr.resolveLet(str);
    	found = true;
    }

	if (found)
	{
	  smtlval.node = BEEV::parserInterface->newNode(nptr);
	  if ((smtlval.node)->GetType() == BEEV::BOOLEAN_TYPE)
	    return FORMID_TOK;
	  else 
	    return TERMID_TOK;
	   }
	   
    // It hasn't been found. So it's not already declared.
    // it has not been seen before.
	smtlval.str = new std::string(str);
	return STRING_TOK;
}
. { smterror("Illegal input character."); }
%%
