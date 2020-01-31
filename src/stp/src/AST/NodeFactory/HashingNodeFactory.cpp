#include "HashingNodeFactory.h"
#include "../AST.h"
#include "../../STPManager/STP.h"

using BEEV::Kind;
using BEEV::ASTInterior;
using BEEV::ASTVec;
using BEEV::ASTNode;


HashingNodeFactory::~HashingNodeFactory()
{
}

// Get structurally hashed version of the node.
BEEV::ASTNode HashingNodeFactory::CreateNode(const Kind kind, const BEEV::ASTVec & back_children)
{
       // We can't create NOT(NOT (..)) nodes because of how the numbering scheme we use works.
       // So you can't trust the hashiing node factory even to return nodes of the same kind that
       // you ask for.
        if (kind == BEEV::NOT && back_children[0].GetKind() == BEEV::NOT)
        {
              return back_children[0][0];
        }

        ASTVec children(back_children);
	// The Bitvector solver seems to expect constants on the RHS, variables on the LHS.
	// We leave the order of equals children as we find them.
	if (BEEV::isCommutative(kind) && kind != BEEV::AND)
	{
		SortByArith(children);
	}

        ASTInterior *n_ptr = new ASTInterior(kind,children);
	ASTNode n(bm.LookupOrCreateInterior(n_ptr));
	return n;
}

// Create and return an ASTNode for a term
ASTNode HashingNodeFactory::CreateTerm(Kind kind, unsigned int width,const ASTVec &children)
{

	ASTNode n = CreateNode(kind, children);
	n.SetValueWidth(width);

	//by default we assume that the term is a Bitvector. If
	//necessary the indexwidth can be changed later
	n.SetIndexWidth(0);
	return n;
}


