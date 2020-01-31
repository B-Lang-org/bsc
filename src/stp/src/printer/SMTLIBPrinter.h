#ifndef SMTLIBPRINTERS_H_
#define SMTLIBPRINTERS_H_

#include "printers.h"

namespace printer
{

	//Map from ASTNodes to LetVars
	extern BEEV::ASTNodeMap NodeLetVarMap;

	//This is a vector which stores the Node to LetVars pairs. It
	//allows for sorted printing, as opposed to NodeLetVarMap
	extern std::vector<pair<ASTNode, ASTNode> > NodeLetVarVec;

	//a partial Map from ASTNodes to LetVars. Needed in order to
	//correctly print shared subterms inside the LET itself
	extern BEEV::ASTNodeMap NodeLetVarMap1;

	string functionToSMTLIBName(const Kind k, bool smtlib1);

	void LetizeNode(const ASTNode& n, BEEV::ASTNodeSet& PLPrintNodeSet, bool smtlib1);

	ostream& SMTLIB_Print(ostream &os, const ASTNode n, const int indentation, void (*SMTLIB_Print1)(ostream&, const ASTNode , int , bool ), bool smtlib1);

	bool containsAnyArrayOps(const ASTNode& n);

	static string tolower(const char * name);
};
#endif
