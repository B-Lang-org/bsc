// Abstract base class for all the node factories.
#ifndef NODEFACTORY_H
#define NODEFACTORY_H

#include <vector>
#include "../ASTKind.h"
#include "../../boost/noncopyable.hpp"

namespace BEEV
{
class ASTNode;
typedef std::vector<ASTNode> ASTVec;
extern ASTVec _empty_ASTVec;
class STPMgr;
typedef unsigned int * CBV;
}

using BEEV::ASTNode;
using BEEV::Kind;
using BEEV::ASTVec;
using BEEV::_empty_ASTVec;

class NodeFactory : boost::noncopyable
{
protected:
        BEEV::STPMgr& bm;

public:
        NodeFactory(BEEV::STPMgr& bm_) : bm(bm_){}

	virtual ~NodeFactory();

	virtual BEEV::ASTNode CreateTerm(Kind kind, unsigned int width,
				const BEEV::ASTVec &children) =0;

	virtual BEEV::ASTNode CreateArrayTerm(Kind kind, unsigned int index, unsigned int width,
				const BEEV::ASTVec &children);

	virtual BEEV::ASTNode CreateNode(Kind kind,
			const BEEV::ASTVec& children) =0;

	ASTNode CreateSymbol(const char * const name, unsigned indexWidth, unsigned valueWidth);

	ASTNode CreateTerm(Kind kind, unsigned int width, const ASTNode& child0,
			const ASTVec &children = _empty_ASTVec);
	ASTNode CreateTerm(Kind kind, unsigned int width, const ASTNode& child0,
			const ASTNode& child1, const ASTVec &children = _empty_ASTVec);
	ASTNode CreateTerm(Kind kind, unsigned int width, const ASTNode& child0,
			const ASTNode& child1, const ASTNode& child2,
			const ASTVec &children = _empty_ASTVec);

	ASTNode CreateNode(Kind kind, const ASTNode& child0,
			const ASTVec & back_children = _empty_ASTVec);
	ASTNode CreateNode(Kind kind, const ASTNode& child0, const ASTNode& child1,
			const ASTVec & back_children = _empty_ASTVec);
	ASTNode	CreateNode(Kind kind, const ASTNode& child0, const ASTNode& child1,
			const ASTNode& child2, const ASTVec & back_children =
			_empty_ASTVec);


	ASTNode CreateArrayTerm(Kind kind, unsigned int index, unsigned int width, const ASTNode& child0,
			const ASTNode& child1, const ASTNode& child2,
			const ASTVec &children = _empty_ASTVec);

	ASTNode getTrue();
	ASTNode getFalse();

	ASTNode CreateConstant(BEEV::CBV cbv, unsigned width);

	virtual std::string getName()=0;
};

#endif
