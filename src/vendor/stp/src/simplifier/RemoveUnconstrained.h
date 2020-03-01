/*
 * RemoveUnconstrained.h
 *
 *  Unconstrained variable elination.
 */

#ifndef REMOVEUNCONSTRAINED_H_
#define REMOVEUNCONSTRAINED_H_
#include "../AST/AST.h"
#include "../STPManager/STPManager.h"
#include "constantBitP/Dependencies.h"
#include "simplifier.h"
#include "MutableASTNode.h"
#include "../boost/noncopyable.hpp"


namespace BEEV
{
  using simplifier::constantBitP::Dependencies;

  class RemoveUnconstrained :  boost::noncopyable
  {
    STPMgr& bm;

    ASTNode replaceParentWithFresh(MutableASTNode& mute, vector<MutableASTNode*>& variables);

    ASTNode
    topLevel_other(const ASTNode &n, Simplifier *simplifier);

    void
    splitExtractOnly(vector<MutableASTNode*> extracts);

    void
    replace(MutableASTNode* from, const ASTNode to);


    void
    replace(const ASTNode& from, const ASTNode to);

    NodeFactory* nf;

  public:

    RemoveUnconstrained(STPMgr& bm);

    ASTNode
    topLevel(const ASTNode &n, Simplifier *s);

  };

}
;

#endif /* REMOVEUNCONSTRAINED_H_ */
