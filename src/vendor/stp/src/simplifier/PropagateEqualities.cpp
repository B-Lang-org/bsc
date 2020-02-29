#include <string>
#include "PropagateEqualities.h"
#include "simplifier.h"
#include "../AST/ArrayTransformer.h"

namespace BEEV
{

  /* The search functions look for variables that can be expressed in terms of variables.
   * The most obvious case it doesn't check for is NOT (OR (.. .. )).
   * I suspect this could take exponential time in the worst case, but on the benchmarks I've tested,
   * it finishes in reasonable time.
   * The obvious way to speed it up (if required), is to create the RHS lazily.
   */

  // The old XOR code used to use updateSolverMap instead of UpdateSubstitutionMap, I've no idea why.

  bool
  PropagateEqualities::searchXOR(const ASTNode& lhs, const ASTNode& rhs)
  {
    Kind k = lhs.GetKind();

    if (lhs == rhs)
      return true;

    if (k == SYMBOL)
          return simp->UpdateSubstitutionMap(lhs, rhs); // checks whether it's been solved for or loops.

    if (k == NOT)
      return searchXOR(lhs[0], nf->CreateNode(NOT, rhs));

    bool result = false;
    if (k == XOR)
      for (int i = 0; i < lhs.Degree(); i++)
        {
          ASTVec others;
          for (int j = 0; j < lhs.Degree(); j++)
            if (j != i)
              others.push_back(lhs[j]);

          others.push_back(rhs);
          assert (others.size() > 1);
          ASTNode new_rhs = nf->CreateNode(XOR, others);

          result =  searchXOR(lhs[i], new_rhs);
          if (result)
            return result;
        }

    if (k == EQ && lhs[0].GetValueWidth() ==1)
      {
        bool result =  searchTerm(lhs[0], nf->CreateTerm(ITE, 1,rhs, lhs[1], nf->CreateTerm(BVNEG, 1,lhs[1])));

        if (!result)
          result =  searchTerm(lhs[1], nf->CreateTerm(ITE, 1,rhs, lhs[0], nf->CreateTerm(BVNEG, 1,lhs[0])));
      }

    return result;
  }

  bool
  PropagateEqualities::searchTerm(const ASTNode& lhs, const ASTNode& rhs)
  {
    const int width = lhs.GetValueWidth();

    if (lhs == rhs)
      return true;


    if (lhs.GetKind() == SYMBOL)
        return simp->UpdateSubstitutionMap(lhs, rhs); // checks whether it's been solved for, or if the RHS contains the LHS.

    if (lhs.GetKind() == BVUMINUS)
      return searchTerm(lhs[0], nf->CreateTerm(BVUMINUS, width, rhs));

    if (lhs.GetKind() == BVNEG)
      return searchTerm(lhs[0], nf->CreateTerm(BVNEG, width, rhs));

    if (lhs.GetKind() == BVXOR || lhs.GetKind() == BVPLUS)
      for (int i = 0; i < lhs.Degree(); i++)
        {
          ASTVec others;
          for (int j = 0; j < lhs.Degree(); j++)
            if (j != i)
              others.push_back(lhs[j]);

          ASTNode new_rhs;
          if (lhs.GetKind() == BVXOR)
            {
              others.push_back(rhs);
              assert (others.size() > 1);
              new_rhs = nf->CreateTerm(lhs.GetKind(), width, others);
            }
          else if (lhs.GetKind() == BVPLUS)
            {
              if (others.size() >1)
                new_rhs = nf->CreateTerm(BVPLUS, width, others);
              else
                new_rhs = others[0];

              new_rhs = nf->CreateTerm(BVUMINUS,width,new_rhs);
              new_rhs = nf->CreateTerm(BVPLUS,width,new_rhs, rhs);
            }
          else
            FatalError("sdafasfsdf2q3234423");

          bool result =  searchTerm(lhs[i], new_rhs);
          if (result)
            return true;
        }

    if (lhs.Degree() == 2 && lhs.GetKind() == BVMULT && lhs[0].isConstant() && simp->BVConstIsOdd(lhs[0]))
      return searchTerm(lhs[1], nf->CreateTerm(BVMULT, width, simp->MultiplicativeInverse(lhs[0]), rhs));

    return false;
  }


    // This doesn't rewrite changes through properly so needs to have a substitution applied to its output.
    ASTNode
    PropagateEqualities::propagate(const ASTNode& a, ArrayTransformer*at)
    {
        ASTNode output;
        //if the variable has been solved for, then simply return it
        if (simp->CheckSubstitutionMap(a, output))
            return output;

        if (!alreadyVisited.insert(a.GetNodeNum()).second)
            {
                return a;
            }

        output = a;

        //traverse a and populate the SubstitutionMap
        const Kind k = a.GetKind();
        if (SYMBOL == k && BOOLEAN_TYPE == a.GetType())
            {
                bool updated = simp->UpdateSubstitutionMap(a, ASTTrue);
                output = updated ? ASTTrue : a;
            }
        else if (NOT == k )
            {
                bool updated = searchXOR(a[0], ASTFalse);
                output = updated ? ASTTrue : a;
            }
        else if (IFF == k || EQ == k)
            {
                const ASTVec& c = a.GetChildren();

                if (c[0] == c[1])
                    return ASTTrue;

                bool updated = simp->UpdateSubstitutionMap(c[0], c[1]);

                if (updated)
                    {
                        //fill the arrayname readindices vector if e0 is a
                        //READ(Arr,index) and index is a BVCONST
                        int to;
                        if ((to = TermOrder(c[0], c[1])) == 1 && c[0].GetKind() == READ)
                            at->FillUp_ArrReadIndex_Vec(c[0], c[1]);
                        else if (to == -1 && c[1].GetKind() == READ)
                            at->FillUp_ArrReadIndex_Vec(c[1], c[0]);
                    }


                if (!updated)
                  updated = searchTerm(c[0],c[1]);

                if (!updated)
                  updated = searchTerm(c[1],c[0]);

                output = updated ? ASTTrue : a;

            }
        else if (XOR == k)
            {
            bool updated = searchXOR(a, ASTTrue);
            output = updated ? ASTTrue : a;

            if (updated)
              return output;

            // The below block should be subsumed by the searchXOR function which generalises it.
            // So the below block should never do anything..
#ifndef NDEBUG
                if (a.Degree() != 2)
                    return output;

                int to = TermOrder(a[0], a[1]);
                if (0 == to)
                    {
                        if (a[0].GetKind() == NOT && a[0][0].GetKind() == EQ && a[0][0][0].GetValueWidth() == 1
                                && a[0][0][1].GetKind() == SYMBOL)
                            {
                                // (XOR (NOT(= (1 v)))  ... )
                                const ASTNode& symbol = a[0][0][1];
                                const ASTNode newN = nf->CreateTerm(ITE, 1, a[1], a[0][0][0],
                                        nf->CreateTerm(BVNEG, 1, a[0][0][0]));

                                if (simp->UpdateSolverMap(symbol, newN))
                                    {
                                    assert(false);
                                    output = ASTTrue;
                                    }
                            }
                        else if (a[1].GetKind() == NOT && a[1][0].GetKind() == EQ && a[1][0][0].GetValueWidth() == 1
                                && a[1][0][1].GetKind() == SYMBOL)
                            {
                                const ASTNode& symbol = a[1][0][1];
                                const ASTNode newN = nf->CreateTerm(ITE, 1, a[0], a[1][0][0],
                                        nf->CreateTerm(BVNEG, 1, a[1][0][0]));

                                if (simp->UpdateSolverMap(symbol, newN))
                                    {
                                    assert(false);
                                    output = ASTTrue;
                                    }
                            }
                        else if (a[0].GetKind() == EQ && a[0][0].GetValueWidth() == 1 && a[0][1].GetKind() == SYMBOL)
                            {
                                // XOR ((= 1 v) ... )

                                const ASTNode& symbol = a[0][1];
                                const ASTNode newN = nf->CreateTerm(ITE, 1, a[1], nf->CreateTerm(BVNEG, 1, a[0][0]),
                                        a[0][0]);

                                if (simp->UpdateSolverMap(symbol, newN))
                                    {
                                    assert(false);
                                    output = ASTTrue;
                                    }
                            }
                        else if (a[1].GetKind() == EQ && a[1][0].GetValueWidth() == 1 && a[1][1].GetKind() == SYMBOL)
                            {
                                const ASTNode& symbol = a[1][1];
                                const ASTNode newN = nf->CreateTerm(ITE, 1, a[0], nf->CreateTerm(BVNEG, 1, a[1][0]),
                                        a[1][0]);

                                if (simp->UpdateSolverMap(symbol, newN))
                                  {
                                    assert(false);
                                    output = ASTTrue;
                                  }
                            }
                        else
                            return output;
                    }
                else
                    {
                        ASTNode symbol, rhs;
                        if (to == 1)
                            {
                                symbol = a[0];
                                rhs = a[1];
                            }
                        else
                            {
                                symbol = a[1];
                                rhs = a[0];
                            }

                        assert(symbol.GetKind() == SYMBOL);

                        if (simp->UpdateSolverMap(symbol, nf->CreateNode(NOT, rhs)))
                            {
                            assert(false);
                            output = ASTTrue;
                            }
                    }
#endif

            }
        else if (AND == k)
            {
                const ASTVec& c = a.GetChildren();
                ASTVec o;
                o.reserve(c.size());

                for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it != itend; it++)
                    {
                        if (always_true)
                          simp->UpdateAlwaysTrueFormSet(*it);
                        ASTNode aaa = propagate(*it, at);

                        if (ASTTrue != aaa)
                            {
                                if (ASTFalse == aaa)
                                    return ASTFalse;
                                else
                                    o.push_back(aaa);
                            }
                    }
                if (o.size() == 0)
                    output = ASTTrue;
                else if (o.size() == 1)
                    output = o[0];
                else if (o != c)
                    output = nf->CreateNode(AND, o);
                else
                    output = a;
            }

        return output;
    } //end of CreateSubstitutionMap()

}
;
