// A Node factory that only does structural hashing.
#ifndef HASHINGNODEFACTORY_H_
#define HASHINGNODEFACTORY_H_

#include "NodeFactory.h"
#include "../ASTKind.h"
namespace BEEV
{
	class STPMgr;
}

class HashingNodeFactory : public NodeFactory
{
public:
	HashingNodeFactory(BEEV::STPMgr& bm_)
	:NodeFactory(bm_)
	{
	}

	virtual ~HashingNodeFactory();
	BEEV::ASTNode CreateNode(const BEEV::Kind kind,	const BEEV::ASTVec & back_children);
	BEEV::ASTNode CreateTerm(BEEV::Kind kind, unsigned int width,const BEEV::ASTVec &children);

	virtual std::string getName() {return "hashing";}
};

#endif /* HASHINGNODEFACTORY_H_ */
