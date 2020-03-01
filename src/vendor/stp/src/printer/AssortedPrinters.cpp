/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
// -*- c++ -*-

#include "printers.h"
#include "AssortedPrinters.h"

// to get the PRIu64 macro from inttypes, this needs to be defined.
#ifndef __STDC_FORMAT_MACROS
  #define __STDC_FORMAT_MACROS
#endif
#include <inttypes.h>
//#undef __STDC_FORMAT_MACROS

namespace BEEV
{
  /******************************************************************
   * Assorted print routines collected in one place. The code here is
   * different from the one in printers directory. It is possible that
   * there is some duplication.
   *
   * FIXME: Get rid of any redundant code
   ******************************************************************/  

  ostream &ASTNode::LispPrint(ostream &os, int indentation) const
  {
    return printer::Lisp_Print(os, *this, indentation);
  }

  ostream &ASTNode::LispPrint_indent(ostream &os, int indentation) const
  {
    return printer::Lisp_Print_indent(os, *this, indentation);
  }

  ostream& ASTNode::PL_Print(ostream &os,  int indentation) const
  {
    return printer::PL_Print(os, *this, indentation);
  }

  //This is the IO manipulator.  It builds an object of class
  //"LispPrinter" that has a special overloaded "<<" operator.
  inline LispPrinter lisp(const ASTNode &node, int indentation = 0)
  {
    LispPrinter lp(node, indentation);
    return lp;
  } //end of LispPrinter_lisp

  //iomanipulator. builds an object of class "LisPrinter" that has a
  //special overloaded "<<" operator.
  inline LispVecPrinter lisp(const ASTVec &vec, int indentation = 0)
  {
    LispVecPrinter lvp(vec, indentation);
    return lvp;
  } //end of LispVecPrinter_lisp()

  // FIXME: Made non-ref in the hope that it would work better.
  void lp(ASTNode node)
  {
    cout << lisp(node) << endl;
  }

  void lpvec(const ASTVec &vec)
  {
    (vec[0].GetSTPMgr())->AlreadyPrintedSet.clear();
    LispPrintVec(cout, vec, 0);
    cout << endl;
  }

  //  //Variable Order Printer: A global function which converts a MINISAT
  //   //var into a ASTNODE var. It then prints this var along with
  //   //variable order dcisions taken by MINISAT.
  //   void Convert_MINISATVar_To_ASTNode_Print(int minisat_var, 
  //                                       int decision_level, int polarity)
  //   {
  //     BEEV::ASTNode vv = BEEV::GlobalSTPMgr->_SATVar_to_AST[minisat_var];
  //     cout << spaces(decision_level);
  //     if (polarity)
  //       {
  //         cout << "!";
  //       }
  //     printer::PL_Print(cout,vv, 0);
  //     cout << endl;
  //   } //end of Convert_MINISATVar_To_ASTNode_Print()

  void STPMgr::printVarDeclsToStream(ostream &os, ASTNodeSet& ListOfDeclaredVars) {
    for(ASTNodeSet::iterator
          i = ListOfDeclaredVars.begin(),iend=ListOfDeclaredVars.end();
        i!=iend;i++) 
      {
        BEEV::ASTNode a = *i;
        switch(a.GetType()) {
        case BEEV::BITVECTOR_TYPE:
          a.PL_Print(os);
          os << " : BITVECTOR(" << a.GetValueWidth() << ");" << endl;
          break;
        case BEEV::ARRAY_TYPE:
          a.PL_Print(os);
          os << " : ARRAY " << "BITVECTOR(" << a.GetIndexWidth() << ") OF ";
          os << "BITVECTOR(" << a.GetValueWidth() << ");" << endl;
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
  } //printVarDeclsToStream

  void STPMgr::printAssertsToStream(ostream &os, int simplify_print) {
    ASTVec v = GetAsserts();
    for(ASTVec::iterator i=v.begin(),iend=v.end();i!=iend;i++) {
      //Begin_RemoveWrites = true; ASTNode q = (simplify_print == 1) ?
      //SimplifyFormula_TopLevel(*i,false) : *i; q = (simplify_print
      //== 1) ? SimplifyFormula_TopLevel(q,false) : q;
      ASTNode q = *i;
      //Begin_RemoveWrites = false;
      os << "ASSERT( ";
      q.PL_Print(os);
      os << ");" << endl;
    }
  }

  void print_STPInput_Back(const ASTNode& query) {

	  // Determine the symbols in the query and asserts.
	  ASTNodeSet visited;
	  ASTNodeSet symbols;
	  buildListOfSymbols(query,  visited, symbols);
      ASTVec v = (BEEV::GlobalSTP->bm)->GetAsserts();
      for(ASTVec::iterator i=v.begin(),iend=v.end();i!=iend;i++)
    	buildListOfSymbols(*i,  visited, symbols);

	(BEEV::GlobalSTP->bm)->printVarDeclsToStream(cout, symbols);
    (BEEV::GlobalSTP->bm)->printAssertsToStream(cout,0);
    cout << "QUERY(";
    query.PL_Print(cout);
    cout << ");\n";
  } //end of print_STPInput_Back()
};//end of namespace BEEV
