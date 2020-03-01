/* A node factory that:
 * 	    * Sorts children to increases sharing,
 *	    * Performs constant evaluation,
 *	    * performs simplify boolean simplifications,
 *	    * converts less thans to greater thans.
 *
 * NOTE: CreateNode doesn't necessary return a node with the same Kind as what it was called
 * with. For example: (AND TRUE FALSE) will return FALSE. Which isn't an AND node.
 *
 * The intention is to never create nodes that will later be simplified by single level
 * re-write rules. So we will never create the node (NOT(NOT x)). This is and example of
 * a multi-level rule that never increases the global number of nodes.
 *
 * These rules never increase the total number of nodes.  They are complimented by
 * multi-level re-write rules that consider the global reference count when simplifying.
 *
 */

#ifndef SIMPLIFYINGNODEFACTORY_H
#define SIMPLIFYINGNODEFACTORY_H

#include "NodeFactory.h"
#include "../../STPManager/STPManager.h"

using BEEV::ASTNode;
using BEEV::ASTVec;

class SimplifyingNodeFactory: public NodeFactory
{

private:
	NodeFactory& hashing;

	const ASTNode& ASTTrue;
	const ASTNode& ASTFalse;
	const ASTNode& ASTUndefined;

	ASTNode CreateSimpleFormITE(const ASTVec &children);
	ASTNode CreateSimpleXor(const ASTVec &children);
	ASTNode CreateSimpleAndOr(bool IsAnd, const ASTVec &children);
	ASTNode CreateSimpleAndOr(bool IsAnd, const ASTNode& form1,
			const ASTNode& form2);
	ASTNode CreateSimpleNot(const ASTNode& form);
	ASTNode CreateSimpleNot(const ASTVec& children);

	ASTNode CreateSimpleEQ(const ASTVec& children);

	SimplifyingNodeFactory(const SimplifyingNodeFactory& );
	SimplifyingNodeFactory& operator=(const SimplifyingNodeFactory&);

	ASTNode chaseRead(const ASTVec& children, unsigned int width );

	ASTNode plusRules(const ASTNode& n0, const ASTNode& n1);
public:

	virtual BEEV::ASTNode CreateNode(BEEV::Kind kind, const BEEV::ASTVec & children);
	virtual BEEV::ASTNode CreateTerm(BEEV::Kind kind, unsigned int width, const BEEV::ASTVec &children);

	virtual std::string getName() {return "simplifying";}

	SimplifyingNodeFactory(NodeFactory& raw_, BEEV::STPMgr& bm_)
	:hashing(raw_), NodeFactory(bm_), ASTTrue(bm_.ASTTrue), ASTFalse(bm_.ASTFalse), ASTUndefined(bm_.ASTUndefined)
	{
	}
	;
	~SimplifyingNodeFactory()
	{
	}

};

#endif
