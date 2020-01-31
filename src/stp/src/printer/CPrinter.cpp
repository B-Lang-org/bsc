// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include <cassert>
#include "printers.h"
namespace printer
{

  using std::string;
  using namespace BEEV;

  // printer for C code (copied from PL_Print())
  // TODO: this does not fully implement printing of all of the STP
  // language - FatalError calls inserted for unimplemented
  // functionality, e.g.,:
  //   FatalError("C_Print1: printing not implemented for this kind: ",*this);

  // helper function for printing C code (copied from PL_Print1())
  void C_Print1(ostream& os, const ASTNode n, int indentation, bool letize)
  {

    unsigned int upper, lower, num_bytes;
    Kind LHSkind, RHSkind;

    //os << spaces(indentation);
    //os << endl << spaces(indentation);
    if (!n.IsDefined())
      {
        os << "<undefined>";
        return;
      }

    //if this node is present in the letvar Map, then print the letvar
    STPMgr *bm = n.GetSTPMgr();

    //this is to print letvars for shared subterms inside the printing
    //of "(LET v0 = term1, v1=term1@term2,...
    if ((bm->NodeLetVarMap1.find(n) != bm->NodeLetVarMap1.end()) && !letize)
      {
        C_Print1(os, (bm->NodeLetVarMap1[n]), indentation, letize);
        return;
      }

    //this is to print letvars for shared subterms inside the actual
    //term to be printed
    if ((bm->NodeLetVarMap.find(n) != bm->NodeLetVarMap.end()) && letize)
      {
        C_Print1(os, (bm->NodeLetVarMap[n]), indentation, letize);
        return;
      }

    //otherwise print it normally
    Kind kind = n.GetKind();
    const ASTVec &c = n.GetChildren();
    switch (kind)
      {
      case BVGETBIT:
        FatalError("C_Print1: printing not implemented for this kind: ", n);
        C_Print1(os, c[0], indentation, letize);
        os << "{";
        C_Print1(os, c[1], indentation, letize);
        os << "}";
        break;
      case BITVECTOR:
        FatalError("C_Print1: printing not implemented for this kind: ", n);
        os << "BITVECTOR(";
        unsigned char * str;
        str = CONSTANTBV::BitVector_to_Hex(c[0].GetBVConst());
        os << str << ")";
        CONSTANTBV::BitVector_Dispose(str);
        break;
      case BOOLEAN:
        FatalError("C_Print1: printing not implemented for this kind: ", n);
        os << "BOOLEAN";
        break;
      case FALSE:
        os << "0";
        break;
      case TRUE:
        os << "1";
        break;
      case BVCONST:
      case SYMBOL:
        // print in C friendly format:
        n.nodeprint(os, true);
        break;
      case READ:
        C_Print1(os, c[0], indentation, letize);
        os << "[";
        C_Print1(os, c[1], indentation, letize);
        os << "]";
        break;
      case WRITE:
        os << "(";
        C_Print1(os, c[0], indentation, letize);
        os << " WITH [";
        C_Print1(os, c[1], indentation, letize);
        os << "] := ";
        C_Print1(os, c[2], indentation, letize);
        os << ")";
        os << endl;
        break;
      case BVUMINUS:
        os << kind << "( ";
        C_Print1(os, c[0], indentation, letize);
        os << ")";
        break;
      case NOT:
        os << "!(";
        C_Print1(os, c[0], indentation, letize);
        os << ") " << endl;
        break;
      case BVNEG:
        os << " ~(";
        C_Print1(os, c[0], indentation, letize);
        os << ")";
        break;
      case BVCONCAT:
        // stopgap for un-implemented features
        FatalError("C_Print1: printing not implemented for this kind: ", n);
        os << "(";
        C_Print1(os, c[0], indentation, letize);
        os << " @ ";
        C_Print1(os, c[1], indentation, letize);
        os << ")" << endl;
        break;
      case BVOR:
        os << "(";
        C_Print1(os, c[0], indentation, letize);
        os << " | ";
        C_Print1(os, c[1], indentation, letize);
        os << ")";
        break;
      case BVAND:
        os << "(";
        C_Print1(os, c[0], indentation, letize);
        os << " & ";
        C_Print1(os, c[1], indentation, letize);
        os << ")";
        break;
      case BVEXTRACT:

        // we only accept indices that are byte-aligned
        // (e.g., [15:8], [23:16])
        // and round down to byte indices rather than bit indices
        upper = c[1].GetUnsignedConst();
        lower = c[2].GetUnsignedConst();
        assert(upper > lower);
        assert(lower % 8 == 0);
        assert((upper + 1) % 8 == 0);
        num_bytes = (upper - lower + 1) / 8;
        assert (num_bytes > 0);

        // for multi-byte extraction, use the ADDRESS
        if (num_bytes > 1)
          {
            os << "&";
            C_Print1(os, c[0], indentation, letize);
            os << "[" << lower / 8 << "]";
          }
        // for single-byte extraction, use the VALUE
        else
          {
            C_Print1(os, c[0], indentation, letize);
            os << "[" << lower / 8 << "]";
          }

        break;
      case BVLEFTSHIFT:
        // stopgap for un-implemented features
        FatalError("C_Print1: printing not implemented for this kind: ", n);
        os << "(";
        C_Print1(os, c[0], indentation, letize);
        os << " << ";
        os << c[1].GetUnsignedConst();
        os << ")";
        break;
      case BVRIGHTSHIFT:
        // stopgap for un-implemented features
        FatalError("C_Print1: printing not implemented for this kind: ", n);
        os << "(";
        C_Print1(os, c[0], indentation, letize);
        os << " >> ";
        os << c[1].GetUnsignedConst();
        os << ")";
        break;
      case BVMULT:
      case BVSUB:
      case BVPLUS:
      case SBVDIV:
      case SBVREM:
      case BVDIV:
      case BVMOD:
        os << kind << "(";
        os << n.GetValueWidth();
        for (ASTVec::const_iterator
               it = c.begin(), itend = c.end(); it != itend; it++)
          {
            os << ", " << endl;
            C_Print1(os, *it, indentation, letize);
          }
        os << ")" << endl;
        break;
      case ITE:
        os << "if (";
        C_Print1(os, c[0], indentation, letize);
        os << ")" << endl;
        os << "{";
        C_Print1(os, c[1], indentation, letize);
        os << endl << "} else {";
        C_Print1(os, c[2], indentation, letize);
        os << endl << "}";
        break;
      case BVLT:
        // convert to UNSIGNED before doing comparison!
        os << "((unsigned char)";
        C_Print1(os, c[0], indentation, letize);
        os << " < ";
        os << "(unsigned char)";
        C_Print1(os, c[1], indentation, letize);
        os << ")";
        break;
      case BVLE:
        // convert to UNSIGNED before doing comparison!
        os << "((unsigned char)";
        C_Print1(os, c[0], indentation, letize);
        os << " <= ";
        os << "(unsigned char)";
        C_Print1(os, c[1], indentation, letize);
        os << ")";
        break;
      case BVGT:
        // convert to UNSIGNED before doing comparison!
        os << "((unsigned char)";
        C_Print1(os, c[0], indentation, letize);
        os << " > ";
        os << "(unsigned char)";
        C_Print1(os, c[1], indentation, letize);
        os << ")";
        break;
      case BVGE:
        // convert to UNSIGNED before doing comparison!
        os << "((unsigned char)";
        C_Print1(os, c[0], indentation, letize);
        os << " >= ";
        os << "(unsigned char)";
        C_Print1(os, c[1], indentation, letize);
        os << ")";
        break;
      case BVXOR:
      case BVNAND:
      case BVNOR:
      case BVXNOR:
        // stopgap for un-implemented features
        FatalError("C_Print1: printing not implemented for this kind: ", n);
        break;
      case BVSLT:
        // convert to SIGNED before doing comparison!
        os << "((signed char)";
        C_Print1(os, c[0], indentation, letize);
        os << " < ";
        os << "(signed char)";
        C_Print1(os, c[1], indentation, letize);
        os << ")";
        break;
      case BVSLE:
        // convert to SIGNED before doing comparison!
        os << "((signed char)";
        C_Print1(os, c[0], indentation, letize);
        os << " <= ";
        os << "(signed char)";
        C_Print1(os, c[1], indentation, letize);
        os << ")";
        break;
      case BVSGT:
        // convert to SIGNED before doing comparison!
        os << "((signed char)";
        C_Print1(os, c[0], indentation, letize);
        os << " > ";
        os << "(signed char)";
        C_Print1(os, c[1], indentation, letize);
        os << ")";
        break;
      case BVSGE:
        // convert to SIGNED before doing comparison!
        os << "((signed char)";
        C_Print1(os, c[0], indentation, letize);
        os << " >= ";
        os << "(signed char)";
        C_Print1(os, c[1], indentation, letize);
        os << ")";
        break;
      case EQ:
        // tricky tricky ... if it's a single-byte comparison,
        // simply do ==, but if it's multi-byte, must do memcmp
        LHSkind = c[0].GetKind();
        RHSkind = c[1].GetKind();

        num_bytes = 0;

        // try to figure out whether it's a single-byte or multi-byte
        // comparison
        if (LHSkind == BVEXTRACT)
          {
            upper = c[0].GetChildren()[1].GetUnsignedConst();
            lower = c[0].GetChildren()[2].GetUnsignedConst();
            num_bytes = (upper - lower + 1) / 8;
          }
        else if (RHSkind == BVEXTRACT)
          {
            upper = c[1].GetChildren()[1].GetUnsignedConst();
            lower = c[1].GetChildren()[2].GetUnsignedConst();
            num_bytes = (upper - lower + 1) / 8;
          }

        if (num_bytes > 1)
          {
            os << "(memcmp(";
            C_Print1(os, c[0], indentation, letize);
            os << ", ";
            C_Print1(os, c[1], indentation, letize);
            os << ", ";
            os << num_bytes;
            os << ") == 0)";
          }
        else if (num_bytes == 1)
          {
            os << "(";
            C_Print1(os, c[0], indentation, letize);
            os << " == ";
            C_Print1(os, c[1], indentation, letize);
            os << ")";
          }
        else
          {
            FatalError("C_Print1: ugh problem in implementing ==");
          }

        break;
      case AND:
      case OR:
      case NAND:
      case NOR:
      case XOR:
        {
          os << "(";
          C_Print1(os, c[0], indentation, letize);
          ASTVec::const_iterator it = c.begin();
          ASTVec::const_iterator itend = c.end();

          it++;
          for (; it != itend; it++)
            {
              switch (kind)
                {
                case AND:
                  os << " && ";
                  break;
                case OR:
                  os << " || ";
                  break;
                case NAND:
                  FatalError("unsupported boolean type in C_Print1");
                  break;
                case NOR:
                  FatalError("unsupported boolean type in C_Print1");
                  break;
                case XOR:
                  FatalError("unsupported boolean type in C_Print1");
                  break;
                default:
                  FatalError("unsupported boolean type in C_Print1");
                }
              C_Print1(os, *it, indentation, letize);
            }
          os << ")";
          break;
        }
      case IFF:
        // stopgap for un-implemented features
        FatalError("C_Print1: printing not implemented for this kind: ", n);
        os << "(";
        os << "(";
        C_Print1(os, c[0], indentation, letize);
        os << ")";
        os << " <=> ";
        os << "(";
        C_Print1(os, c[1], indentation, letize);
        os << ")";
        os << ")";
        os << endl;
        break;
      case IMPLIES:
        // stopgap for un-implemented features
        FatalError("C_Print1: printing not implemented for this kind: ", n);
        os << "(";
        os << "(";
        C_Print1(os, c[0], indentation, letize);
        os << ")";
        os << " => ";
        os << "(";
        C_Print1(os, c[1], indentation, letize);
        os << ")";
        os << ")";
        os << endl;
        break;
      case BVSX:
        // stopgap for un-implemented features
        FatalError("C_Print1: printing not implemented for this kind: ", n);

        os << kind << "(";
        C_Print1(os, c[0], indentation, letize);
        os << ",";
        os << n.GetValueWidth();
        os << ")" << endl;
        break;
      default:
        //remember to use LispPrinter here. Otherwise this function will
        //go into an infinite loop. Recall that "<<" is overloaded to
        //the lisp printer. FatalError uses lispprinter
        FatalError("C_Print1: printing not implemented for this kind: ", n);
        break;
      }
  } //end of C_Print1()


  //two pass algorithm:
  //
  //1. In the first pass, letize this Node, N: i.e. if a node
  //1. appears more than once in N, then record this fact.
  //
  //2. In the second pass print a "global let" and then print N
  //2. as follows: Every occurence of a node occuring more than
  //2. once is replaced with the corresponding let variable.
  ostream& C_Print(ostream &os, const ASTNode n, int indentation)
  {
    // Clear the PrintMap
    STPMgr* bm = n.GetSTPMgr();
    bm->PLPrintNodeSet.clear();
    bm->NodeLetVarMap.clear();
    bm->NodeLetVarVec.clear();
    bm->NodeLetVarMap1.clear();

    //pass 1: letize the node
    n.LetizeNode();

    unsigned int lower, upper, num_bytes = 0;

    //pass 2:
    //
    //2. print all the let variables and their counterpart expressions
    //2. as follows (LET var1 = expr1, var2 = expr2, ...
    //
    //3. Then print the Node itself, replacing every occurence of
    //3. expr1 with var1, expr2 with var2, ...
    //os << "(";
    if (0 < bm->NodeLetVarMap.size())
      {
        //ASTNodeMap::iterator it=bm->NodeLetVarMap.begin();
        //ASTNodeMap::iterator itend=bm->NodeLetVarMap.end();
        std::vector<pair<ASTNode, ASTNode> >::iterator it = 
          bm->NodeLetVarVec.begin();
        std::vector<pair<ASTNode, ASTNode> >::iterator itend = 
          bm->NodeLetVarVec.end();

        // start a new block to create new static scope
        os << "{" << endl;

        for (; it != itend; it++)
          {

            // see if it's a BVEXTRACT, and if so, whether it's multi-byte
            if (it->second.GetKind() == BVEXTRACT)
              {
                upper = it->second.GetChildren()[1].GetUnsignedConst();
                lower = it->second.GetChildren()[2].GetUnsignedConst();
                num_bytes = (upper - lower + 1) / 8;
                assert(num_bytes > 0);
              }

            //print the let var first
            if (num_bytes > 1)
              {
                // for multi-byte assignment, use 'memcpy' and array notation
                os << "unsigned char ";
                C_Print1(os, it->first, indentation, false);
                os << "[" << num_bytes << "]; ";
                os << "memcpy(";
                C_Print1(os, it->first, indentation, false);
                os << ", ";
                //print the expr
                C_Print1(os, it->second, indentation, false);
                os << ", " << num_bytes << ");";
              }
            else
              {
                // for single-byte assignment, use '='
                os << "unsigned char ";
                C_Print1(os, it->first, indentation, false);
                os << " = ";
                //print the expr
                C_Print1(os, it->second, indentation, false);
                os << ";" << endl;
              }

            //update the second map for proper printing of LET
            bm->NodeLetVarMap1[it->second] = it->first;
          }

        os << endl << "stp_assert ";
        C_Print1(os, n, indentation, true);

        os << ";" << endl << "}";
      }
    else
      {
        os << "stp_assert ";
        C_Print1(os, n, indentation, false);
        os << ";";
      }
    //os << " )";
    //os << " ";

    return os;
  } //end of C_Print()
}
