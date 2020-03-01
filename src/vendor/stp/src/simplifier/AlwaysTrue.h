#ifndef ALWAYSTRUE_H_
#define ALWAYSTRUE_H_

//Applies the AlwaysTrueSet to the input node.

#include <map>
#include "../AST/AST.h"
#include "../STPManager/STPManager.h"
#include "../simplifier/simplifier.h"
#include "../boost/noncopyable.hpp"

namespace BEEV
{

class AlwaysTrue : boost::noncopyable
{
  Simplifier *simplifier;
  STPMgr* stp;
  NodeFactory *nf;

  enum State {AND_STATE, NOT_STATE, BOTTOM_STATE};

public:
  AlwaysTrue(Simplifier *simplifier_, STPMgr* stp_, NodeFactory *nf_)
  {
    simplifier = simplifier_;
    stp = stp_;
    nf = nf_;
  }

  ASTNode topLevel(ASTNode& n)
  {
    stp->GetRunTimes()->start(RunTimes::AlwaysTrue);
    ASTNodeMap fromTo;
    ASTNode result = visit(n,AND_STATE,fromTo);
    stp->GetRunTimes()->stop(RunTimes::AlwaysTrue);
    return result;
  }

  // Replace nodes that aren't conjoined to the top with TRUE/FALSE,
  // if that node is conjoined..
  // The "state" tracks whether we are still at nodes that are conjoined to the top,
  // only after we get out of the top part can we replace nodes that we know to be
  // true or false.
  ASTNode visit(const ASTNode&n, State state, ASTNodeMap& fromTo)
  {
    if (n.isConstant())
      return n;

    if (fromTo.find(n) != fromTo.end())
    {
        // It has been visited as BOTTOM_STATE once before.
        return fromTo.find(n)->second;
    }

    ASTVec newChildren;
    newChildren.reserve(n.Degree());
    State new_state;

    if (state == BOTTOM_STATE)
    {
        bool result;
        if (simplifier->CheckAlwaysTrueFormSet(n,result))
          {
            cerr << "+";
            if (result)
              return stp->ASTTrue;
            else
              return stp->ASTFalse;
          }
    }

    if (n.GetKind() == SYMBOL)
      return n;

    if (n.GetKind() != AND && state == AND_STATE )
      {
        if (n.GetKind() == NOT)
          new_state = NOT_STATE;
        else
          new_state = BOTTOM_STATE;
      }
    else if (state == NOT_STATE)
      new_state = BOTTOM_STATE;
    else
      new_state = state;

    for (int i=0; i < n.Degree(); i++)
      {
        newChildren.push_back(visit(n[i],new_state,fromTo));
      }

    ASTNode result = n;
    if (newChildren != n.GetChildren())
      {
        if (n.GetType() == BOOLEAN_TYPE)
          result =  nf->CreateNode(n.GetKind(), newChildren);
        else
          result = nf->CreateArrayTerm(n.GetKind(), n.GetIndexWidth(), n.GetValueWidth(), newChildren);
      }

    if (state == BOTTOM_STATE)
      {
          fromTo.insert(make_pair(n,result));
      }
    return result;
  }
};
};
#endif
