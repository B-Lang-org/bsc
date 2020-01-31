/*
	A decorator pattern, which calls some base node factory, then type checks each of the results.
 */

#ifndef TYPECHECKER_H_
#define TYPECHECKER_H_

#include "NodeFactory.h"
#include "../../STPManager/STPManager.h"

namespace BEEV
{
class BeevMgr;
}
using BEEV::STPMgr;

class TypeChecker : public NodeFactory
{
NodeFactory& f;

public:
	TypeChecker(NodeFactory& f_, STPMgr& bm_) : f(f_), NodeFactory(bm)
	{}

	BEEV::ASTNode CreateTerm(BEEV::Kind kind, unsigned int width, const BEEV::ASTVec &children);
	BEEV::ASTNode CreateNode(BEEV::Kind kind, const BEEV::ASTVec& children);
	BEEV::ASTNode CreateArrayTerm(Kind kind, unsigned int index,unsigned int width, const BEEV::ASTVec &children);

	virtual string getName() {return "type checking";}
};

#endif /* TYPECHECKER_H_ */
