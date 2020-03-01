#include "TypeChecker.h"
#include "../AST.h"

BEEV::ASTNode TypeChecker::CreateTerm(BEEV::Kind kind, unsigned int width, const BEEV::ASTVec &children)
{
	BEEV::ASTNode r = f.CreateTerm(kind,width,children);
	BVTypeCheck(r);
	return r;
}

//virtual BEEV::ASTNode CreateNode(BEEV::Kind kind, const BEEV::ASTVec& children);
BEEV::ASTNode TypeChecker::CreateNode(BEEV::Kind kind, const BEEV::ASTVec& children)
{
	BEEV::ASTNode r = f.CreateNode(kind,children);
	BVTypeCheck(r);
	return r;
}

BEEV::ASTNode TypeChecker::CreateArrayTerm(Kind kind, unsigned int index,
		unsigned int width, const BEEV::ASTVec &children)
{
	ASTNode r = f.CreateTerm(kind, width, children);
	r.SetIndexWidth(index);
	BVTypeCheck(r);
	return r;
}

