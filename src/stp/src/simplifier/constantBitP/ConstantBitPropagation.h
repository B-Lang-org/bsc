#ifndef CONSTANTBITPROPAGATION_H_
#define CONSTANTBITPROPAGATION_H_

#include "FixedBits.h"
#include "Dependencies.h"
#include "NodeToFixedBitsMap.h"
#include "WorkList.h"
#include "MultiplicationStats.h"

namespace BEEV
{
  class ASTNode;
  typedef unsigned int * CBV;
  class Simplifier;
}

namespace simplifier
{
  namespace constantBitP
  {

    enum Result
    {
      NO_CHANGE = 1, CHANGED, CONFLICT, NOT_IMPLEMENTED
    };

    class MultiplicationStatsMap;
    class WorkList;

    using BEEV::ASTNode;
    using BEEV::Simplifier;

    class ConstantBitPropagation
    {
      NodeFactory *nf;
      Simplifier *simplifier;

      Result status;
      WorkList *workList;
      Dependencies * dependents;

      bool topFixed;

      // A vector that's reused.
      vector< int > previousChildrenFixedCount;

      void
      printNodeWithFixings();

      FixedBits*
      getUpdatedFixedBits(const ASTNode& n);

      FixedBits*
      getCurrentFixedBits(const ASTNode& n);

      void
      scheduleDown(const ASTNode& n);

public:
      NodeToFixedBitsMap* fixedMap;
      MultiplicationStatsMap* msm;

      bool isUnsatisfiable()
      {
        return status == CONFLICT;
      }

      // propagates.
      ConstantBitPropagation(BEEV::Simplifier* _sm, NodeFactory* _nf, const ASTNode & top);

      ~ConstantBitPropagation()
      {
        clearTables();
      }
      ;

      // Returns the node after writing in simplifications from constant Bit propagation.
      BEEV::ASTNode
      topLevelBothWays(const ASTNode& top, bool setTopToTrue = true, bool conjoinToTop=true);


      void clearTables()
      {
        delete fixedMap;
        fixedMap = NULL;
        delete dependents;
        dependents = NULL;
        delete workList;
        workList = NULL;
        delete msm;
        msm = NULL;
      }

      bool
      checkAtFixedPoint(const ASTNode& n, BEEV::ASTNodeSet & visited);

      void
      propagate();

      void
      scheduleUp(const ASTNode& n);

      void
      scheduleNode(const ASTNode& n);

      void
      setNodeToTrue(const ASTNode& top);

      ASTNodeMap
      getAllFixed();

      void initWorkList(const ASTNode n)
      {
        workList->initWorkList(n);
      }

    };
  }
}

#endif /* CONSTANTBITPROPAGATION_H_ */
