/*
 * VariablesInExpression.h
 *
 */

#ifndef VARIABLESINEXPRESSION_H_
#define VARIABLESINEXPRESSION_H_

#include "../AST/AST.h"
#include "Symbols.h"
#include "../boost/noncopyable.hpp"

namespace BEEV
{

class VariablesInExpression : boost::noncopyable
{
private:

	void insert(const ASTNode& n, Symbols *s);

	typedef HASHMAP<
	  int,
	  Symbols*
	  > ASTNodeToNodes;
	  ASTNodeToNodes symbol_graph;


public:
	VariablesInExpression();
	virtual ~VariablesInExpression();


    // When solving, we're interested in whether variables appear multiple times.
    typedef HASHSET<Symbols*,SymbolPtrHasher> SymbolPtrSet;


	  Symbols* getSymbol(const ASTNode& n);

	    //this map is useful while traversing terms and uniquely
	    //identifying variables in the those terms. Prevents double
	    //counting.

	    typedef HASHMAP<
		  Symbols*,
		  ASTNodeSet*,
		  SymbolPtrHasher
		  > SymbolPtrToNode;
		SymbolPtrToNode TermsAlreadySeenMap;

    //this function return true if the var occurs in term, else the
    //function returns false
    bool VarSeenInTerm(const ASTNode& var, const ASTNode& term);
    ASTNodeSet * SetofVarsSeenInTerm(const ASTNode& term, bool& destruct);
    ASTNodeSet * SetofVarsSeenInTerm(Symbols* symbol, bool& destruct);
    void VarSeenInTerm(Symbols* term, SymbolPtrSet& visited, ASTNodeSet& found, vector<Symbols*>& av);

    void ClearAllTables()
    {
		set<Symbols*> deleted;
		for (ASTNodeToNodes::iterator it = symbol_graph.begin(); it
				!= symbol_graph.end(); it++) {
			if (deleted.find(it->second) == deleted.end()) {
				deleted.insert(it->second);
				delete it->second;
			}
		}

		for (SymbolPtrToNode::iterator it = TermsAlreadySeenMap.begin(); it
				!= TermsAlreadySeenMap.end(); it++)
			delete (it->second);

		symbol_graph.clear();
		TermsAlreadySeenMap.clear();
	}
};
};



#endif /* VARIABLESINEXPRESSION_H_ */
