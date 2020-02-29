/********************************************************************
 * AUTHORS: Trevor Hansen, Vijay Ganesh
 *
 * BEGIN DATE: July, 2009
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
// -*- c++ -*-

#include "printers.h"
#include <cassert>
#include <cctype>
#include "SMTLIBPrinter.h"

// Outputs in the SMTLIB1 format. If you want something that can be parsed by other tools call
// SMTLIB_PrintBack(). SMTLIB_Print() prints just an expression.
// Wierdly is seems that only terms, not formulas can be LETized.

// NB: This code doesn't include the substitution map. So if you've already simplified
// the graph, then solving what this prints out wont necessarily give you a model.


namespace printer
{
  using std::string;
  using namespace BEEV;

  void SMTLIB1_Print1(ostream& os, const BEEV::ASTNode n, int indentation,	bool letize);
  void printSMTLIB1VarDeclsToStream(ASTNodeSet& symbols, ostream& os);

  void SMTLIB1_PrintBack(ostream &os, const ASTNode& n)
{
    os << "(" << endl;
    os << "benchmark blah" << endl;
	if (containsArrayOps(n))
	    os << ":logic QF_AUFBV" << endl;
	else
		os << ":logic QF_BV" << endl;

	if (input_status == TO_BE_SATISFIABLE) {
		os << ":status sat" << endl;
	}
	else if (input_status == TO_BE_UNSATISFIABLE) {
		os << ":status unsat" << endl;
	}
	else
		os << ":status unknown" << endl;

	ASTNodeSet visited, symbols;
	buildListOfSymbols(n, visited, symbols);
	printSMTLIB1VarDeclsToStream(symbols, os);
	os << ":formula ";
    SMTLIB_Print(os, n, 0, &SMTLIB1_Print1,true);
    os << ")" << endl;
  }

void printSMTLIB1VarDeclsToStream(ASTNodeSet& symbols, ostream& os)
{
	for (ASTNodeSet::const_iterator i = symbols.begin(), iend = symbols.end(); i
			!= iend; i++)
	{
      const BEEV::ASTNode& a = *i;

      // Should be a symbol.
      assert(a.GetKind()== SYMBOL);

		switch (a.GetType())
		{
      case BEEV::BITVECTOR_TYPE:

        os << ":extrafuns (( ";
        a.nodeprint(os);
        os << " BitVec[" << a.GetValueWidth() << "]";
        os << " ))" << endl;
        break;
      case BEEV::ARRAY_TYPE:
        os << ":extrafuns (( ";
        a.nodeprint(os);
        os << " Array[" << a.GetIndexWidth();
        os << ":" << a.GetValueWidth() << "] ))" << endl;
        break;
      case BEEV::BOOLEAN_TYPE:
        os << ":extrapreds (( ";
        a.nodeprint(os);
        os << "))" << endl;
        break;
      default:
        BEEV::FatalError("printVarDeclsToStream: Unsupported type",a);
        break;
      }
    }
  } //printVarDeclsToStream

  void outputBitVec(const ASTNode n, ostream& os)
  {
	const Kind k = n.GetKind();
    const ASTVec &c = n.GetChildren();
    ASTNode op;

    if (BITVECTOR == k)
      {
        op = c[0];
      }
    else if (BVCONST == k)
      {
        op = n;
      }
    else
      FatalError("nsadfsdaf");

    // CONSTANTBV::BitVector_to_Dec returns a signed representation by default.
    // Prepend with zero to convert to unsigned.

    os << "bv";
	CBV unsign = CONSTANTBV::BitVector_Concat(
			n.GetSTPMgr()->CreateZeroConst(1).GetBVConst(), op.GetBVConst());
    unsigned char * str = CONSTANTBV::BitVector_to_Dec(unsign);
    CONSTANTBV::BitVector_Destroy(unsign);
    os << str << "[" << op.GetValueWidth() << "]";
    CONSTANTBV::BitVector_Dispose(str);
  }

  void SMTLIB1_Print1(ostream& os, const ASTNode n, int indentation, bool letize)
  {
    //os << spaces(indentation);
    //os << endl << spaces(indentation);
    if (!n.IsDefined())
      {
    	FatalError("<undefined>");
        return;
      }

    //if this node is present in the letvar Map, then print the letvar
    //this is to print letvars for shared subterms inside the printing
    //of "(LET v0 = term1, v1=term1@term2,...
	if ((NodeLetVarMap1.find(n) != NodeLetVarMap1.end()) && !letize)
      {
		SMTLIB1_Print1(os, (NodeLetVarMap1[n]), indentation, letize);
        return;
      }

    //this is to print letvars for shared subterms inside the actual
    //term to be printed
	if ((NodeLetVarMap.find(n) != NodeLetVarMap.end()) && letize)
      {
		SMTLIB1_Print1(os, (NodeLetVarMap[n]), indentation, letize);
        return;
      }

    //otherwise print it normally
	const Kind kind = n.GetKind();
    const ASTVec &c = n.GetChildren();
    switch (kind)
      {
      case BITVECTOR:
      case BVCONST:
        outputBitVec(n, os);
        break;
      case SYMBOL:
        n.nodeprint(os);
        break;
      case FALSE:
        os << "false";
        break;
      case NAND: // No NAND, NOR in smtlib format.
      case NOR:
    	  assert(c.size() ==2);
    	  os << "(" << "not ";
    	  if (NAND == kind )
    		  os << "(" << "and ";
    	  else
    		  os << "(" << "or ";
    	  SMTLIB1_Print1(os, c[0], 0, letize);
    	  os << " " ;
    	  SMTLIB1_Print1(os, c[1], 0, letize);
    	  os << "))";
    	  break;
      case TRUE:
        os << "true";
        break;
      case BVSX:
      case BVZX:
        {
          unsigned int amount = c[1].GetUnsignedConst();
          if (BVZX == kind)
            os << "(zero_extend[";
          else
            os << "(sign_extend[";

		os << (amount - c[0].GetValueWidth()) << "]";
          SMTLIB1_Print1(os, c[0], indentation, letize);
          os << ")";
        }
        break;
      case BVEXTRACT:
        {
          unsigned int upper = c[1].GetUnsignedConst();
          unsigned int lower = c[2].GetUnsignedConst();
          assert(upper >= lower);
          os << "(extract[" << upper << ":" << lower << "] ";
          SMTLIB1_Print1(os, c[0], indentation, letize);
          os << ")";
        }
        break;
  	default:
  	{
  	    if ((kind == AND  || kind == OR|| kind == XOR) && n.Degree() == 1)
  	    {
  	    	FatalError("Wrong number of arguments to operation (must be >1).", n);
  	    }

  		// SMT-LIB only allows these functions to have two parameters.
  	    if ((kind == AND  || kind == OR|| kind == XOR || BVPLUS == kind || kind == BVOR || kind == BVAND)  && n.Degree() > 2)
  		{
  			string close = "";

  			for (int i =0; i < c.size()-1; i++)
  			{
  				os << "(" << functionToSMTLIBName(kind,true);
  				os << " ";
  				SMTLIB1_Print1(os, c[i], 0, letize);
  				os << " ";
  				close += ")";
  			}
  			SMTLIB1_Print1(os, c[c.size()-1], 0, letize);
  			os << close;
  		}
  		else
  		{
  			os << "(" << functionToSMTLIBName(kind,true);

  			ASTVec::const_iterator iend = c.end();
  			for (ASTVec::const_iterator i = c.begin(); i != iend; i++)
  			{
  				os << " ";
  				SMTLIB1_Print1(os, *i, 0, letize);
  			}

  			os << ")";
  		}
  	}
      }
  }
}
