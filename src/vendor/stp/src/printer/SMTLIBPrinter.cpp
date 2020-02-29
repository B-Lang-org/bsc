#include "printers.h"
#include "SMTLIBPrinter.h"

// Functions used by both the version1 and version2 STMLIB printers.

namespace printer
{
using namespace BEEV;

static string tolower(const char * name)
{
  string s(name);
  for (size_t i = 0; i < s.size(); ++i)
	s[i] = ::tolower(s[i]);
  return s;
}


	//Map from ASTNodes to LetVars
	BEEV::ASTNodeMap NodeLetVarMap;

	//This is a vector which stores the Node to LetVars pairs. It
	//allows for sorted printing, as opposed to NodeLetVarMap
	std::vector<pair<ASTNode, ASTNode> > NodeLetVarVec;

	//a partial Map from ASTNodes to LetVars. Needed in order to
	//correctly print shared subterms inside the LET itself
	BEEV::ASTNodeMap NodeLetVarMap1;

	  // copied from Presentation Langauge printer.
	  ostream& SMTLIB_Print(ostream &os, const ASTNode n, const int indentation, void (*SMTLIB1_Print1)(ostream&, const ASTNode , int , bool ), bool smtlib1)
	  {
	    // Clear the maps
		NodeLetVarMap.clear();
		NodeLetVarVec.clear();
		NodeLetVarMap1.clear();

	    //pass 1: letize the node
		{
			ASTNodeSet PLPrintNodeSet;
			LetizeNode(n, PLPrintNodeSet, smtlib1);
		}

	    //pass 2:
	    //
	    //2. print all the let variables and their counterpart expressions
	    //2. as follows (LET var1 = expr1, var2 = expr2, ...
	    //
	    //3. Then print the Node itself, replacing every occurence of
	    //3. expr1 with var1, expr2 with var2, ...
	    //os << "(";
		if (0 < NodeLetVarMap.size())
	      {
			std::vector<pair<ASTNode, ASTNode> >::iterator it =
					NodeLetVarVec.begin();
			const std::vector<pair<ASTNode, ASTNode> >::iterator itend =
					NodeLetVarVec.end();

			os << "(let (";
			if (!smtlib1)
				os << "(";
	        //print the let var first
	        SMTLIB1_Print1(os, it->first, indentation, false);
			os << " ";
	        //print the expr
	        SMTLIB1_Print1(os, it->second, indentation, false);
			os << " )";
			if (!smtlib1)
				os << ")";


	        //update the second map for proper printing of LET
			NodeLetVarMap1[it->second] = it->first;

			string closing = "";
	        for (it++; it != itend; it++)
	          {
				os << " " << endl;
				os << "(let (";
				if (!smtlib1)
						os << "(";
	            //print the let var first
	            SMTLIB1_Print1(os, it->first, indentation, false);
				os << " ";
	            //print the expr
	            SMTLIB1_Print1(os, it->second, indentation, false);
				os << ")";
				if (!smtlib1)
						os << ")";

	            //update the second map for proper printing of LET
				NodeLetVarMap1[it->second] = it->first;
				closing += ")";
	          }
                  os << endl;
                  SMTLIB1_Print1(os, n, indentation, true);
                  os << closing;
                  os << " )  ";
	      }
	    else
	      SMTLIB1_Print1(os, n, indentation, false);

	    os << endl;
	    return os;
	  }

	void LetizeNode(const ASTNode& n, ASTNodeSet& PLPrintNodeSet, bool smtlib1)
	{
		const Kind kind = n.GetKind();

		if (kind == SYMBOL || kind == BVCONST || kind == FALSE || kind == TRUE)
			return;

		const ASTVec &c = n.GetChildren();
		for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it != itend; it++)
		{
			const ASTNode& ccc = *it;

			const Kind k = ccc.GetKind();
			if (k == SYMBOL || k == BVCONST || k == FALSE || k == TRUE)
				continue;

			if (PLPrintNodeSet.find(ccc) == PLPrintNodeSet.end())
			{
				//If branch: if *it is not in NodeSet then,
				//
				//1. add it to NodeSet
				//
				//2. Letize its childNodes
				PLPrintNodeSet.insert(ccc);
				LetizeNode(ccc, PLPrintNodeSet, smtlib1);
			}
			else
			{
				//0. Else branch: Node has been seen before
				//
				//1. Check if the node has a corresponding letvar in the
				//1. NodeLetVarMap.
				//
				//2. if no, then create a new var and add it to the
				//2. NodeLetVarMap
				if ((!smtlib1 || ccc.GetType() == BITVECTOR_TYPE) && NodeLetVarMap.find(ccc)
						== NodeLetVarMap.end())
				{
					//Create a new symbol. Get some name. if it conflicts with a
					//declared name, too bad.
					int sz = NodeLetVarMap.size();
					ostringstream oss;
					oss << "?let_k_" << sz;

					ASTNode CurrentSymbol = n.GetSTPMgr()->CreateSymbol(
							oss.str().c_str(),n.GetIndexWidth(), n.GetValueWidth());
					/* If for some reason the variable being created here is
					 * already declared by the user then the printed output will
					 * not be a legal input to the system. too bad. I refuse to
					 * check for this.  [Vijay is the author of this comment.]
					 */

					NodeLetVarMap[ccc] = CurrentSymbol;
					std::pair<ASTNode, ASTNode>
							node_letvar_pair(CurrentSymbol, ccc);
					NodeLetVarVec.push_back(node_letvar_pair);
				}
			}
		}
	} //end of LetizeNode()

  string functionToSMTLIBName(const Kind k, bool smtlib1)
  {
    switch (k)
      {
    case IFF:
    	if (smtlib1)
			return "iff";
    	else
    		return "=";
    case IMPLIES:
    	if (smtlib1)
    		return "implies";
    	 else
    	    return "=>";
      case AND:
      case BVAND:
      case BVNAND:
      case BVNOR:
      case BVOR:
      case BVSGE:
      case BVSGT:
      case BVSLE:
      case BVSLT:
      case BVSUB:
      case BVXOR:
      case ITE:
      case NAND:
      case NOR:
      case NOT:
      case OR:
      case XOR:
	{
        return tolower(_kind_names[k]);
	}

      case BVCONCAT:
        return "concat";
      case BVDIV:
        return "bvudiv";
      case BVGT:
        return "bvugt";
      case BVGE:
        return "bvuge";
      case BVLE:
        return "bvule";
      case BVLEFTSHIFT:
        return "bvshl";
      case BVLT:
        return "bvult";
      case BVMOD:
        return "bvurem";
      case BVMULT:
        return "bvmul";
      case BVNEG:
        return "bvnot"; // CONFUSSSSINNG. (1/2)
      case BVPLUS:
        return "bvadd";
      case BVRIGHTSHIFT:
        return "bvlshr"; // logical
      case BVSRSHIFT:
        return "bvashr"; // arithmetic.
      case BVUMINUS:
        return "bvneg"; // CONFUSSSSINNG. (2/2)
      case EQ:
        return "=";
      case READ:
        return "select";
      case WRITE:
        return "store";
      case SBVDIV:
        return "bvsdiv";
      case SBVREM:
        return "bvsrem";
      case SBVMOD:
        return "bvsmod";

      default:
        {
          cerr << "Unknown name when outputting:";
          FatalError(_kind_names[k]);
          return ""; // to quieten compiler/
        }
      }
  }
};
