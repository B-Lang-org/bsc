#ifndef TOSATBASE_H
#define TOSATBASE_H

#include "../AST/AST.h"
#include "../STPManager/STPManager.h"
#include "../boost/noncopyable.hpp"

namespace BEEV
{
  class ToSATBase : boost::noncopyable
  {
  protected:
    ASTNode ASTTrue, ASTFalse, ASTUndefined;

    // Ptr to STPManager
    STPMgr * bm;

  public:

    typedef HASHMAP<
    ASTNode,
    vector<unsigned>,
    ASTNode::ASTNodeHasher,
    ASTNode::ASTNodeEqual> ASTNodeToSATVar;

    // Constructor
    ToSATBase(STPMgr * bm) :
      bm(bm)
    {
      ASTTrue      = bm->CreateNode(TRUE);
      ASTFalse     = bm->CreateNode(FALSE);
      ASTUndefined = bm->CreateNode(UNDEFINED);
    }

    virtual ~ToSATBase()
    {}

    //print the STP solver output
    void PrintOutput(SOLVER_RETURN_TYPE ret);

    // Bitblasts, CNF conversion and calls toSATandSolve()
    virtual bool CallSAT(SATSolver& SatSolver, const ASTNode& input, bool doesAbsRef) =0;

    virtual ASTNodeToSATVar& SATVar_to_SymbolIndexMap()= 0;

    virtual void ClearAllTables(void)  =0;
  };
}

#endif
