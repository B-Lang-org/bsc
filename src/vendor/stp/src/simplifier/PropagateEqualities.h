#ifndef PROPAGATEEQUALITIES_H_
#define PROPAGATEEQUALITIES_H_

#include "../AST/AST.h"
#include "../STPManager/STPManager.h"
#include "../simplifier/simplifier.h"
#include "../boost/noncopyable.hpp"

//This finds conjuncts which are one of: (= SYMBOL BVCONST), (= BVCONST (READ SYMBOL BVCONST)),
// (IFF SYMBOL TRUE), (IFF SYMBOL FALSE), (IFF SYMBOL SYMBOL), (=SYMBOL SYMBOL)
// or (=SYMBOL BVCONST).
// It tries to remove the conjunct, storing it in the substitutionmap. It replaces it in the
// formula by true.

namespace BEEV
{
    class Simplifier;
    class ArrayTransformer;

    class PropagateEqualities :  boost::noncopyable
    {

        Simplifier *simp;
        NodeFactory *nf;
        STPMgr *bm;
        const ASTNode ASTTrue, ASTFalse;

        bool searchXOR(const ASTNode& lhs, const ASTNode& rhs);
        bool searchTerm(const ASTNode& lhs, const ASTNode& rhs);

        ASTNode
        propagate(const ASTNode& a, ArrayTransformer*at);
        HASHSET<int> alreadyVisited;

        const bool always_true;
    public:

        PropagateEqualities(Simplifier *simp_, NodeFactory *nf_, STPMgr *bm_) :
                ASTTrue(bm_->ASTTrue), ASTFalse(bm_->ASTFalse),
                always_true(bm_->UserFlags.isSet("always_true","1"))
        {
            simp = simp_;
            nf = nf_;
            bm = bm_;
        }

        ASTNode
        topLevel(const ASTNode& a, ArrayTransformer* at)
        {
          if (!bm->UserFlags.propagate_equalities)
              return a;

          bm->GetRunTimes()->start(RunTimes::PropagateEqualities);
          ASTNode result = propagate(a, at);
          bm->GetRunTimes()->stop(RunTimes::PropagateEqualities);
          return result;
        }

    };
}

#endif
