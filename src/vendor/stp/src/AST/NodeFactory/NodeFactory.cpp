#include "../ASTKind.h"
#include "../AST.h"
#include "../../STPManager/STPManager.h"

NodeFactory::~NodeFactory()
{
}

BEEV::ASTNode NodeFactory::CreateTerm(BEEV::Kind kind, unsigned int width,
		const BEEV::ASTVec &children)
{
	return CreateTerm(kind, width, children);
}

ASTNode NodeFactory::CreateTerm(Kind kind, unsigned int width,
		const ASTNode& child0, const ASTVec &children)
{
	ASTVec child;
	child.reserve(children.size() + 1);
	child.push_back(child0);
	child.insert(child.end(), children.begin(), children.end());
	return CreateTerm(kind, width, child);
}

ASTNode NodeFactory::CreateTerm(Kind kind, unsigned int width,
		const ASTNode& child0, const ASTNode& child1, const ASTVec &children)
{
	ASTVec child;
	child.reserve(children.size() + 2);
	child.push_back(child0);
	child.push_back(child1);
	child.insert(child.end(), children.begin(), children.end());
	return CreateTerm(kind, width, child);
}

ASTNode NodeFactory::CreateTerm(Kind kind, unsigned int width,
		const ASTNode& child0, const ASTNode& child1, const ASTNode& child2,
		const ASTVec &children)
{
	ASTVec child;
	child.reserve(children.size() + 3);
	child.push_back(child0);
	child.push_back(child1);
	child.push_back(child2);
	child.insert(child.end(), children.begin(), children.end());
	return CreateTerm(kind, width, child);
}

ASTNode NodeFactory::CreateNode(Kind kind, const ASTNode& child0,
		const ASTVec & back_children)
{
	ASTVec front_children;
	front_children.reserve(1 + back_children.size());
	front_children.push_back(child0);
	front_children.insert(front_children.end(), back_children.begin(),
			back_children.end());
	return CreateNode(kind, front_children);
}

ASTNode NodeFactory::CreateNode(Kind kind, const ASTNode& child0,
		const ASTNode& child1, const ASTVec & back_children)
{
	ASTVec front_children;
	front_children.reserve(2 + back_children.size());
	front_children.push_back(child0);
	front_children.push_back(child1);
	front_children.insert(front_children.end(), back_children.begin(),
			back_children.end());
	return CreateNode(kind, front_children);
}

ASTNode NodeFactory::CreateNode(Kind kind, const ASTNode& child0,
		const ASTNode& child1, const ASTNode& child2,
		const ASTVec & back_children)
{
	ASTVec front_children;
	front_children.reserve(3 + back_children.size());
	front_children.push_back(child0);
	front_children.push_back(child1);
	front_children.push_back(child2);
	front_children.insert(front_children.end(), back_children.begin(),
			back_children.end());
	return CreateNode(kind, front_children);
}

ASTNode NodeFactory::CreateArrayTerm(Kind kind, unsigned int index, unsigned int width,
		const ASTNode& child0, const ASTNode& child1, const ASTNode& child2,
		const ASTVec &children)
{
	ASTVec child;
	child.reserve(children.size() + 3);
	child.push_back(child0);
	child.push_back(child1);
	child.push_back(child2);
	child.insert(child.end(), children.begin(), children.end());
	return CreateArrayTerm(kind, index, width, child);
}

BEEV::ASTNode NodeFactory::CreateArrayTerm(Kind kind, unsigned int index,
		unsigned int width, const BEEV::ASTVec &children)
{
	ASTNode result = CreateTerm(kind, width, children);
	result.SetIndexWidth(index);
	return result;
}

BEEV::ASTNode NodeFactory::getTrue() {return bm.ASTTrue;}
BEEV::ASTNode NodeFactory::getFalse(){return bm.ASTFalse;}


ASTNode NodeFactory::CreateSymbol(const char * const name, unsigned indexWidth, unsigned valueWidth)
{
  ASTNode n = bm.LookupOrCreateSymbol(name);
  n.SetIndexWidth(indexWidth);
  n.SetValueWidth(valueWidth);
  return n;
}

ASTNode NodeFactory::CreateConstant(BEEV::CBV  cbv, unsigned width)
{
  return bm.CreateBVConst(cbv,width);
}
