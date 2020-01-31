%{
  /********************************************************************
   * AUTHORS:  Trevor Hansen
   *
   * BEGIN DATE: May, 2010
   *
   * This file is modified version of the STP's smtlib.lex file. Please
   * see CVCL license below
   ********************************************************************/

  /********************************************************************
   * AUTHORS: Trevor Hansen, Vijay Ganesh, David L. Dill
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
  // -*- c++ -*-L
#include "parser.h"
#include "parsesmt2.hpp"
#include "../cpp_interface/cpp_interface.h"

  extern char *smt2text;
  extern int smt2error (const char *msg);

  // File-static (local to this file) variables and functions
  static std::string _string_lit;  
  static char escapeChar(char c) {
    switch(c) {
    case 'n': return '\n';
    case 't': return '\t';
    default: return c;
    }
  }    
   
  static int lookup(const char* s)
  {
    string str(s);
  
    // The SMTLIB2 specifications sez that the outter bars aren't part of the
    // name. This means that we can create an empty string symbol name.
    if (s[0] == '|' && s[str.size()-1] == '|')
    	str = str.substr(1,str.length()-2);
    
    BEEV::ASTNode nptr;
    bool found = false;
    
    if (BEEV::parserInterface->isSymbolAlreadyDeclared(str)) // it's a symbol.
    {
    	nptr= BEEV::parserInterface->LookupOrCreateSymbol(str);
    	found = true;
    }
    else if (BEEV::parserInterface->letMgr.isLetDeclared(str)) // a let.
    {
    	nptr = BEEV::parserInterface->letMgr.resolveLet(str);
    	found = true;
    }

	if (found)
	{
	  // Check valuesize to see if it's a prop var.  I don't like doing
	  // type determination in the lexer, but it's easier than rewriting
	  // the whole grammar to eliminate the term/formula distinction.  
	  smt2lval.node = BEEV::parserInterface->newNode(nptr);
	  if ((smt2lval.node)->GetType() == BEEV::BOOLEAN_TYPE)
	    return FORMID_TOK;
	  else 
	    return TERMID_TOK;
	   }
	else
	{
		// it has not been seen before.
		smt2lval.str = new std::string(str);
		return STRING_TOK;
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
%x  SYMBOL

LETTER	([a-zA-Z])
DIGIT	([0-9])
OPCHAR	([~!@$%^&*\_\-+=<>\.?/]) 

ANYTHING  ({LETTER}|{DIGIT}|{OPCHAR})

%%
[ \n\t\r\f]	{ /* sk'ip whitespace */ }

 /* We limit numerals to maxint, in the specification they are arbitary precision.*/
{DIGIT}+	{ smt2lval.uintval = strtoul(smt2text, NULL, 10); return NUMERAL_TOK; }

bv{DIGIT}+	{ smt2lval.str = new std::string(smt2text+2); return BVCONST_DECIMAL_TOK; }
#b{DIGIT}+  { smt2lval.str = new std::string(smt2text+2); return BVCONST_BINARY_TOK; }
#x({DIGIT}|[a-fA-F])+  { smt2lval.str = new std::string(smt2text+2); return BVCONST_HEXIDECIMAL_TOK; }

{DIGIT}+"."{DIGIT}+ { return DECIMAL_TOK;}

";"		{ BEGIN COMMENT; }
<COMMENT>"\n"	{ BEGIN INITIAL; /* return to normal mode */}
<COMMENT>.	{ /* stay in comment mode */ }

<INITIAL>"\""		{ BEGIN STRING_LITERAL;
                          _string_lit.erase(_string_lit.begin(),
                                            _string_lit.end()); }
<STRING_LITERAL>"\\".	{ /* escape characters (like \n or \") */
                          _string_lit.insert(_string_lit.end(),
                                             escapeChar(smt2text[1])); }
<STRING_LITERAL>"\""	{ BEGIN INITIAL; 
			  smt2lval.str = new std::string(_string_lit);
                          return STRING_TOK; }
<STRING_LITERAL>.	{ _string_lit.insert(_string_lit.end(),*smt2text); }                           
<STRING_LITERAL>"\n"	{ _string_lit.insert(_string_lit.end(),*smt2text); }

 /* Valid character are: ~ ! @ # $ % ^ & * _ - + = | \ : ; " < > . ? / ( )     */
"("             { return LPAREN_TOK; }
")"             { return RPAREN_TOK; }
"_"             { return UNDERSCORE_TOK; }

 /* Set info types */
 /* This is a very restricted set of the possible keywords */
":source"        { return SOURCE_TOK;}
":category"      { return CATEGORY_TOK;} 
":difficulty"    { return DIFFICULTY_TOK; }
":smt-lib-version"  { return VERSION_TOK; }
":status"        { return STATUS_TOK; }
":print-success"        { return PRINT_TOK; }


 /* COMMANDS */
"set-logic"         { return LOGIC_TOK; }  
"set-info"  		{ return NOTES_TOK;  }
"set-option"  		{ return OPTION_TOK;  }
"declare-fun"		{ return DECLARE_FUNCTION_TOK; }
"push"				{ return PUSH_TOK;}
"pop"				{ return POP_TOK;}
 
 /*
	"declare-sort" 
	"define-sort"  
*/ 
"assert" 			{ return FORMULA_TOK; }
"check-sat"			{ return CHECK_SAT_TOK; }
 /*
	"get-assertions" 
	"get-proof" 
	"get-unsat-core" 
	"get-value"   
	"get-assignment" 
	"get-option" 
	"get-info" 
*/
"exit" {return EXIT_TOK;}

 /* Types for QF_BV and QF_AUFBV. */
"BitVec"        { return BITVEC_TOK;}
"Array"         { return ARRAY_TOK;}
"Bool"          { return BOOL_TOK;}


 /* CORE THEORY pg. 29 of the SMT-LIB2 standard 30-March-2010. */
"true"          { return TRUE_TOK; } 
"false"         { return FALSE_TOK; } 
"not"           { return NOT_TOK; } 
"and"           { return AND_TOK; } 
"or"            { return OR_TOK; } 
"xor"           { return XOR_TOK;}  
"ite"           { return ITE_TOK;} // PARAMETRIC 
"="             { return EQ_TOK;} 
"=>"       		{ return IMPLIES_TOK; } 

 /* CORE THEORY. But not on pg 29. */
"distinct"      { return DISTINCT_TOK; }  // variadic
"let"           { return LET_TOK; }

 /* Functions for QF_BV and QF_AUFBV.  */
"bvshl"         { return BVLEFTSHIFT_1_TOK;} 
"bvlshr"        { return BVRIGHTSHIFT_1_TOK;} 
"bvashr"        { return BVARITHRIGHTSHIFT_TOK;} 
"bvadd"         { return BVPLUS_TOK;} 
"bvsub"         { return BVSUB_TOK;} 
"bvnot"         { return BVNOT_TOK;} 
"bvmul"         { return BVMULT_TOK;} 
"bvudiv"        { return BVDIV_TOK;} 
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
"bvult"         { return BVLT_TOK;} 
"bvugt"         { return BVGT_TOK;} 
"bvule"         { return BVLE_TOK;} 
"bvuge"         { return BVGE_TOK;} 
"bvslt"         { return BVSLT_TOK;} 
"bvsgt"         { return BVSGT_TOK;} 
"bvsle"         { return BVSLE_TOK;} 
"bvsge"         { return BVSGE_TOK;} 
"bvcomp"        { return BVCOMP_TOK;} 
"zero_extend"   { return BVZX_TOK;} 
"sign_extend"   { return BVSX_TOK;}  
"repeat"        { return BVREPEAT_TOK;}  
"rotate_left"   { return BVROTATE_LEFT_TOK;} 
"rotate_right"  { return BVROTATE_RIGHT_TOK;}  

 /* Functions for QF_AUFBV. */
"select"        { return SELECT_TOK; }
"store"         { return STORE_TOK; }

({LETTER}|{OPCHAR})({ANYTHING})*	{return lookup(smt2text);}
\|([^\|]|\n)*\| {return lookup(smt2text);}

. { smt2error("Illegal input character."); }
%%
