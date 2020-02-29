/*
 * VariablesInExpression.cpp
 */

#include "VariablesInExpression.h"

namespace BEEV {

VariablesInExpression::VariablesInExpression() {
	// TODO Auto-generated constructor stub

}

VariablesInExpression::~VariablesInExpression() {
	ClearAllTables();
}

void VariablesInExpression::insert(const ASTNode& n, Symbols *s)
{
	assert (s!= NULL);
	symbol_graph.insert(make_pair(n.GetNodeNum(), s));
}

// This builds a reduced version of a graph, where there
// is only a new node if the number of non-array SYMBOLS
// in the descendents changes. For example (EXTRACT 0 1 n)
// will have the same "Symbols" node as n, because
// no new symbols are introduced.
Symbols* VariablesInExpression::getSymbol(const ASTNode& n) {
	if (symbol_graph.find(n.GetNodeNum()) != symbol_graph.end()) {
		return symbol_graph[n.GetNodeNum()];
	}

	Symbols* node;

	// Note we skip array variables. We never solve for them so
	// can ignore them.
	if (n.GetKind() == SYMBOL && n.GetIndexWidth() == 0) {
		node = new Symbols(n);
		insert(n, node);
		return node;
	}

	vector<Symbols*> children;
	for (int i = 0; i < n.Degree(); i++) {
		Symbols* v = getSymbol(n[i]);
		if (!v->empty())
			children.push_back(v);
	}

	if (children.size() == 1) {
		// If there is only a single child with a symbol. Then jump to it.
		node = children.back();
	} else
		node = new Symbols(children);

	insert(n, node);

	return node;
}

// Builds a set of the SYMBOLS that were found under the "term". The symbols are the union of "found" and
// all the sets : TermsAlreadySeen(av[0]) union ... TermsAlreadySeen(av[n])".
void VariablesInExpression::VarSeenInTerm(Symbols* term, SymbolPtrSet& visited,
		ASTNodeSet& found, vector<Symbols*>& av) {
	if (visited.find(term) != visited.end()) {
		return;
	}

	if (term->isLeaf()) {
		found.insert(term->found);
		return;
	}

	visited.insert(term);

	SymbolPtrToNode::const_iterator it;
	if ((it = TermsAlreadySeenMap.find(term)) != TermsAlreadySeenMap.end()) {
		// We've previously built the set of variables below this "symbols".
		// It's not added into "found" because its sometimes 70k variables
		// big, and if there are no other symbols discovered it's a terrible
		// waste to create a copy of the set. Instead we store (in effect)
		// a pointer to the set.
		av.push_back(term);
		return;
	}

	for (vector<Symbols*>::const_iterator it = term->children.begin(), itend =
			term->children.end(); it != itend; it++) {
		VarSeenInTerm(*it, visited, found, av);
	}

	return;
}//End of VarSeenInTerm

ASTNodeSet * VariablesInExpression::SetofVarsSeenInTerm(Symbols* symbol, bool& destruct)
{
	assert(symbol != NULL);

	SymbolPtrToNode::iterator it = TermsAlreadySeenMap.find(symbol);

	if ( it != TermsAlreadySeenMap.end())
		{
		destruct = false;
		return it->second;
		}

	SymbolPtrSet visited;

	ASTNodeSet *symbols = new ASTNodeSet();
	vector<Symbols*> av;
	VarSeenInTerm(symbol,visited,*symbols,av);

	for (int i =0; i < av.size();i++)
	{
		const ASTNodeSet& sym = *TermsAlreadySeenMap.find(av[i])->second;
		symbols->insert(sym.begin(), sym.end());
	}

	destruct = true;
	//TermsAlreadySeenMap.insert(make_pair(symbol,symbols));

	return symbols;
}

ASTNodeSet * VariablesInExpression::SetofVarsSeenInTerm(const ASTNode& term, bool& destruct)
{
	getSymbol(term);
	return SetofVarsSeenInTerm(symbol_graph[term.GetNodeNum()],  destruct);
}

bool VariablesInExpression::VarSeenInTerm(const ASTNode& var,
		const ASTNode& term) {
	// This only returns true if we are searching for variables that aren't arrays.
	assert(var.GetKind() == SYMBOL && var.GetIndexWidth() == 0);
	if (term.isConstant())
		return false;

	getSymbol(term);

	SymbolPtrSet visited;
	ASTNodeSet *symbols = new ASTNodeSet();
	vector<Symbols*> av;
	VarSeenInTerm(symbol_graph[term.GetNodeNum()], visited, *symbols, av);

	bool result = (symbols->count(var) != 0);

	//cerr << "visited:" << visited.size() << endl;
	//cerr << "av:" << av.size() << endl;
	//cerr << "Term is const" << term.isConstant() << endl;


	if (visited.size() > 250) // No use caching it, unless we've done some work.
	{
		sort(av.begin(), av.end());

		//cout << "===" << endl;
		for (int i = 0; i < av.size(); i++) {
			if (i!=0 && av[i] == av[i-1])
				continue;

			const ASTNodeSet& sym = *TermsAlreadySeenMap.find(av[i])->second;
			//cout << "set: " << i << " " << sym.size() << endl;
			symbols->insert(sym.begin(), sym.end());
		}
		TermsAlreadySeenMap.insert(make_pair(symbol_graph[term.GetNodeNum()], symbols));
		//cout << "finish" << symbols->size() << endl;
		//cout << "===" << endl;
		result = (symbols->count(var) != 0);
	} else {
		const int size = av.size();
		for (int i = 0; i < size; i++) {
			if (result)
				break;
			const ASTNodeSet& sym = *TermsAlreadySeenMap.find(av[i])->second;
			result |= (sym.find(var) != sym.end());
		}
		delete symbols;
	}
	return result;
}

};
