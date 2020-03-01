/*
 * Identifies unconstrained variables and remove them from the input.
 * Robert Bruttomesso's & Robert Brummayer's dissertations describe this.
 * 
 * Nb. this isn't finished. It doesn't do reads / writes.
 * I don't think anything can be done for : bvsx, bvzx.
 */

#include "RemoveUnconstrained.h"
#include "MutableASTNode.h"

namespace BEEV
{
  using simplifier::constantBitP::Dependencies;

  RemoveUnconstrained::RemoveUnconstrained(STPMgr& _bm) :
    bm(_bm)
  {
    nf = _bm.defaultNodeFactory;
 }

  const bool debug_unconstrained = false;

  ASTNode
  RemoveUnconstrained::topLevel(const ASTNode &n, Simplifier *simplifier)
  {
    ASTNode result(n);

    bm.GetRunTimes()->start(RunTimes::RemoveUnconstrained);

    if(simplifier->hasUnappliedSubstitutions())
      result = simplifier->applySubstitutionMap(result);

    // In some rare cases, the simplifier might not have removed a term
    // that can be substituted away. e.g. read(A,0), if read(A,0) == 1,
    // in the substitution map.
    result = topLevel_other(result, simplifier);

    // It is idempotent if there are no big ANDS (we have a special hack), and,
    // if we don't introduced any new "disjoint extracts."

    #if 0
    ASTNode result2 = topLevel_other(result, simplifier);
    if (result2 != result)
      {
        cerr << n;
        cerr << result;
        cerr << result2;
        assert(result2 == result);
      }
    #endif
    bm.GetRunTimes()->stop(RunTimes::RemoveUnconstrained);
    return result;
  }

  bool allChildrenAreUnconstrained(vector <MutableASTNode*> children)
  {
      for (int i =0; i < children.size(); i++)
        if (!children[i]->isUnconstrained())
          return false;

      return true;
  }

  Simplifier *simplifier_convenient;

  ASTNode RemoveUnconstrained::replaceParentWithFresh(MutableASTNode& mute, vector<MutableASTNode*>& variables)
  {
      const ASTNode& parent = mute.n;
      ASTNode v = bm.CreateFreshVariable(0, parent.GetValueWidth(), "unconstrained");
      mute.replaceWithVar(v,variables);
      return v;
    }

  //  nb. This avoids the expensive checks that usually updating the substitution map
  // entails.
  void
  RemoveUnconstrained::replace(const ASTNode& from, const ASTNode to)
  {
    assert(from.GetKind() == SYMBOL);
    assert(from.GetValueWidth() == to.GetValueWidth());
    simplifier_convenient->UpdateSubstitutionMapFewChecks(from, to);
    return;
  }

  /* The most complicated handling is for EXTRACTS. If a variable has parents that
 * are all extracts and each of those extracts is disjoint (i.e. reads different bits)
 * Then each of the extracts are replaced by a fresh variable. This is the only case
 * where a variable with multiple distinct parents is replaced by a fresh variable.
 * + We perform this check upfront, so will miss any extra cases the the unconstrained
 *   variable elimination introduces.
 * + It's all or nothing. So even if there's an extract of [0:2] [1:2] and [3:5], we wont
 *   replace the [3:5] (even though it could be).
 */
  void
  RemoveUnconstrained::splitExtractOnly(vector<MutableASTNode*> extracts)
  {
    assert(extracts.size() >0);

    // Going to be rebuilt later anyway, so discard.
    vector<MutableASTNode*> variables;

    for (int i =0; i <extracts.size(); i++)
      {
        ASTNode& var = extracts[i]->n;
        assert(var.GetKind() == SYMBOL);
        const int size = var.GetValueWidth();
        std::vector<ASTNode> toVar(size);

        // Create a mutable copy that we can iterate over.
        vector <MutableASTNode*> mut;
        mut.insert(mut.end(), extracts[i]->parents.begin(), extracts[i]->parents.end());

        for (vector<MutableASTNode*>::iterator it = mut.begin(); it != mut.end(); it++)
          {
            ASTNode parent_node = (*it)->n;
            assert(((**it)).children[0] == extracts[i]);
            assert(!parent_node.IsNull());
            assert(parent_node.GetKind() == BVEXTRACT);

            int lb = parent_node[2].GetUnsignedConst();
            // Replace each parent with a fresh.
            toVar[lb] = replaceParentWithFresh(**it,variables);
          }

      ASTVec concatVec;
      int empty =0;
      for (int j=0; j < size;j++)
      {
          if (toVar[j].IsNull())
            {
              empty++;
              continue;
            }

          if (empty > 0)
            {
              concatVec.push_back(bm.CreateFreshVariable(0, empty, "extract_unc"));
              empty = 0;
            }

          concatVec.push_back(toVar[j]);
          //cout << toVar[j];
          assert(toVar[j].GetValueWidth() > 0);
          j+=toVar[j].GetValueWidth()-1;
        }

      if (empty> 0)
        {
          concatVec.push_back(bm.CreateFreshVariable(0, empty, "extract_unc"));
        }

    ASTNode concat = concatVec[0];
    for (int i=1; i < concatVec.size();i++)
      {
          assert(!concat.IsNull());
          concat = bm.CreateTerm(BVCONCAT, concat.GetValueWidth() + concatVec[i].GetValueWidth(),concatVec[i], concat);
      }

    replace(var,concat);
        }
  }

  ASTNode
  RemoveUnconstrained::topLevel_other(const ASTNode &n, Simplifier *simplifier)
  {
    if (n.GetKind() == SYMBOL)
      return n; // top level is an unconstrained symbol/.

    simplifier_convenient = simplifier;

    ASTNodeSet noCheck; // We don't want to check some expensive nodes over and over again.

    vector<MutableASTNode*> variable_array;

    MutableASTNode* topMutable = MutableASTNode::build(n);

    vector<MutableASTNode*> extracts;
    topMutable->getDisjointExtractVariables(extracts);
    if (extracts.size() > 0)
      {
          splitExtractOnly(extracts);
      }

    topMutable->getAllUnconstrainedVariables(variable_array);

    for (int i =0; i < variable_array.size() ; i++)
      {
        // Don't make this is a reference. If the vector gets resized, it will point to
        // memory that no longer contains the object.
        MutableASTNode& muteNode = *variable_array[i];

        const ASTNode var = muteNode.n;
        assert(var.GetKind() == SYMBOL);

        if (!muteNode.isUnconstrained())
          continue;

        MutableASTNode& muteParent = muteNode.getParent();

        if (noCheck.find(muteParent.n) != noCheck.end())
          {
            continue;
          }

        vector <MutableASTNode*> mutable_children = muteParent.children;

        //nb. The children might be dirty. i.e. not have substitutions written through them yet.
        ASTVec children;
        children.reserve(mutable_children.size());
        for (int j = 0; j <mutable_children.size(); j++ )
          children.push_back(mutable_children[j]->n);

        const size_t numberOfChildren = children.size();
        const Kind kind = muteNode.getParent().n.GetKind();
        unsigned width = muteNode.getParent().n.GetValueWidth();
        unsigned indexWidth = muteNode.getParent().n.GetIndexWidth();

        ASTNode other;
        MutableASTNode* muteOther;

          if(numberOfChildren == 2)
          {
            if (children[0] != var)
              {
                other = children[0];
                muteOther = mutable_children[0];
              }
            else
              {
                other = children[1];
                muteOther = mutable_children[1];
              }

            if (kind != AND && kind != OR && kind != BVOR && kind != BVAND)
              if (other == var)
                continue; // Most rules don't like duplicate variables.
          }
        else
          {
            if (kind != AND && kind != OR && kind != BVOR && kind != BVAND)
              {
                  int found = 0;

                  for (int i = 0; i < numberOfChildren; i++)
                    {
                      if (children[i] == var)
                        found++;
                   }

                    if (found != 1)
                      continue; // Most rules don't like duplicate variables.
              }
          }

          /*
          cout << i << " " << kind << " " << variable_array.size() <<  " " << mutable_children.size() << endl;
          cout << "children[0]" << children[0] << endl;
          cout << "children[1]" << children[1] << endl;
          cout << muteParent.n << endl;

           */

        switch (kind)
          {
        case BVCONCAT:
          assert(numberOfChildren == 2);
          if (mutable_children[0]->isUnconstrained() && (mutable_children[1]->isUnconstrained()))
            {
              ASTNode v =replaceParentWithFresh(muteParent, variable_array);

              ASTNode top_lhs = bm.CreateBVConst(32, width - 1);
              ASTNode bottom_lhs = bm.CreateBVConst(32, children[1].GetValueWidth());

              ASTNode top_rhs = bm.CreateBVConst(32, children[1].GetValueWidth()- 1);
              ASTNode bottom_rhs = bm.CreateBVConst(32, 0);

              ASTNode lhs = nf->CreateTerm(BVEXTRACT, children[0].GetValueWidth(), v,top_lhs, bottom_lhs);
              ASTNode rhs = nf->CreateTerm(BVEXTRACT, children[1].GetValueWidth(), v,top_rhs, bottom_rhs);

              replace(children[0],lhs);
              replace(children[1],rhs);
            }
          break;
        case NOT:
          {
            ASTNode v =replaceParentWithFresh(muteParent, variable_array);
            replace(children[0], nf->CreateNode(NOT, v));
          }
          break;

        case BVUMINUS:
        case BVNEG:
          {
            assert(numberOfChildren ==1);
            ASTNode v =replaceParentWithFresh(muteParent, variable_array);
            replace(var, nf->CreateTerm(kind, width,v));
          }
          break;

        case BVSGT:
        case BVSGE:
        case BVGT:
        case BVGE:
          {
            width = var.GetValueWidth();
            if (width ==1)
              continue; // Hard to get right, not used often.

            ASTNode biggestNumber, smallestNumber;

            if (kind == BVSGT || kind == BVSGE)
              {
                // 011111111 (most positive number.)
                CBV max = CONSTANTBV::BitVector_Create(width, false);
                CONSTANTBV::BitVector_Fill(max);
                CONSTANTBV::BitVector_Bit_Off(max, width - 1);
                biggestNumber = bm.CreateBVConst(max, width);

                // 1000000000 (most negative number.)
                max = CONSTANTBV::BitVector_Create(width, true);
                CONSTANTBV::BitVector_Bit_On(max, width - 1);
                smallestNumber = bm.CreateBVConst(max, width);
              }
            else if (kind == BVGT || kind == BVGE)
              {
                biggestNumber = bm.CreateMaxConst(width);
                smallestNumber =  bm.CreateZeroConst(width);
              }
            else
              FatalError("SDFA!@S");


            ASTNode c1,c2;
            if (kind == BVSGT || kind == BVGT)
              {
                c1= biggestNumber;
                c2 = smallestNumber;
              }
            else if (kind == BVSGE || kind == BVGE)
              {
                c1= smallestNumber;
                c2 = biggestNumber;
              }
            else
              FatalError("SDFA!@S");

            if (mutable_children[0]->isUnconstrained() && mutable_children[1]->isUnconstrained())
              {
                ASTNode v =replaceParentWithFresh(muteParent, variable_array);

                ASTNode lhs = nf->CreateTerm(ITE, width, v, bm.CreateOneConst(width), bm.CreateZeroConst(width));
                ASTNode rhs = nf->CreateTerm(ITE, width, v, bm.CreateZeroConst(width), bm.CreateOneConst(width));
                replace(children[0], lhs);
                replace(children[1], rhs);
              }
            else if (children[0] == var && children[1].isConstant())
              {
                if (children[1] == c1)
                  continue; // always false. Or always false.

                ASTNode v =replaceParentWithFresh(muteParent, variable_array);

                ASTNode rhs = nf->CreateTerm(ITE, width, v,biggestNumber, smallestNumber);
                replace(var, rhs);
              }
            else if (children[1] == var && children[0].isConstant())
              {
                if (children[0] == c2)
                  continue;  // always false. Or always false.

                ASTNode v =replaceParentWithFresh(muteParent, variable_array);

                ASTNode rhs = nf->CreateTerm(ITE, width, v, smallestNumber, biggestNumber);
                replace(var, rhs);
              }
            else // One side is a variable. The other is anything.
              {
            	 bool varOnLHS = (var == children[0]);

                // All the ASTNode vars need to map to their existing MutableASTNodes. So we collect all the variables
                vector<MutableASTNode*> vars;
                set<MutableASTNode*> visited;
                muteOther->getAllVariablesRecursively(vars, visited);
                visited.clear();

                map<ASTNode, MutableASTNode *> create;
                for (vector<MutableASTNode*>::iterator it = vars.begin(); it != vars.end();it++)
                  create.insert(make_pair((*it)->n, *it));
                vars.clear();

                ASTNode v= bm.CreateFreshVariable(0, 0, "STP_INTERNAL_comparison");

                ASTNode rhs;
                ASTNode n;
                if (varOnLHS)
                  {
                    rhs = nf->CreateTerm(ITE, width, v, biggestNumber, smallestNumber);

                    if (kind == BVSGE || kind == BVGE)
                      n= nf->CreateNode(OR, v, nf->CreateNode(EQ, mutable_children[1]->toASTNode(nf), c1));
                    else
                      n= nf->CreateNode(AND, v, nf->CreateNode(NOT,nf->CreateNode(EQ, mutable_children[1]->toASTNode(nf), c1)));
                  }
                else
                  {
                    rhs = nf->CreateTerm(ITE, width, v, smallestNumber, biggestNumber);

                    if (kind == BVSGE || kind == BVGE)
                      n= nf->CreateNode(OR, v, nf->CreateNode(EQ, mutable_children[0]->toASTNode(nf), c2));
                    else
                      n= nf->CreateNode(AND, v, nf->CreateNode(NOT,nf->CreateNode(EQ, mutable_children[0]->toASTNode(nf), c2)));
                  }
                replace(var, rhs);
                MutableASTNode *newN = MutableASTNode::build(n,create);
                muteParent.replaceWithAnotherNode(newN);
                //assert(muteParent.checkInvariant());
              }
          }
          break;


        case AND:
        case OR:
        case BVOR:
        case BVAND:
          {
            if (allChildrenAreUnconstrained(mutable_children))
              {
                ASTNodeSet already;
                ASTNode v =replaceParentWithFresh(muteParent, variable_array);
                for (int i =0; i < numberOfChildren;i++)
                  {
                    /* to avoid problems with:
                    734:(AND
                    732:unconstrained_4
                    716:unconstrained_2
                    732:unconstrained_4)
                    */
                    if (already.find(children[i]) == already.end())
                      {
                        replace(children[i], v);
                        already.insert(children[i]);
                      }
                  }
              }
            else
              {
                // Hack. ff.stp has a 325k node conjunction
                // So we check if all the children are unconstrained each time
                // we find a new unconstrained conjunct. This means that if
                // eventually all the nodes become unconstrained we will miss it
                // and not rewrite the AND to a fresh unconstrained variable.

                if (mutable_children.size() > 200)
                  noCheck.insert(muteParent.n);
              }
          }
          break;

        case XOR:
        case BVXOR:
              {
                ASTNode v =replaceParentWithFresh(muteParent, variable_array);

                ASTVec others;
                for (int i = 0; i < numberOfChildren; i++)
                {
                    if (children[i] !=var)
                        others.push_back(mutable_children[i]->toASTNode(nf));
                }
                assert(others.size() +1 == numberOfChildren);
                assert(others.size() >=1);

                if (kind == XOR)
              {
                ASTNode xorNode = nf->CreateNode(XOR, others);
                replace(var, nf->CreateNode(XOR, v, xorNode));
              }
            else
              {
                ASTNode xorNode ;
                if (others.size() > 1 )
                  xorNode = nf->CreateTerm(BVXOR, width, others);
                else
                  xorNode = others[0];

                replace(var, nf->CreateTerm(BVXOR, width, v, xorNode));
              }
              }
           break;

        case ITE:
              {
                if (indexWidth > 0)
                  continue; // don't do arrays.

                if (mutable_children[0]->isUnconstrained() && mutable_children[1]->isUnconstrained() && children[0] != children[1])
                  {
                    ASTNode v =replaceParentWithFresh(muteParent, variable_array);
                    replace(children[0], bm.ASTTrue);
                    replace(children[1], v);

                  }
                else if (mutable_children[0]->isUnconstrained() && mutable_children[2]->isUnconstrained() && children[0] != children[2])
                  {
                    ASTNode v =replaceParentWithFresh(muteParent, variable_array);
                    replace(children[0], bm.ASTFalse);
                    replace(children[2], v);
                  }
                else if (mutable_children[1]->isUnconstrained() && mutable_children[2]->isUnconstrained())
                  {
                    ASTNode v =replaceParentWithFresh(muteParent, variable_array);
                    replace(children[1], v);
                    if (children[1] != children[2])
                      replace(children[2], v);
                  }
              }
              break;
        case BVLEFTSHIFT:
        case BVRIGHTSHIFT:
        case BVSRSHIFT:
             {
                 assert(numberOfChildren == 2);
                 if (mutable_children[0]->isUnconstrained() && mutable_children[1]->isUnconstrained())
                  {
                     assert(children[0] != children[1]);
                     ASTNode v =replaceParentWithFresh(muteParent, variable_array);
                     replace(children[1], bm.CreateZeroConst(width));
                     replace(children[0], v);
                  }
              }
             break;

        case BVMOD:
             {
                 assert(numberOfChildren == 2);
                 if (mutable_children[0]->isUnconstrained() && mutable_children[1]->isUnconstrained() && bm.UserFlags.isSet("unconstrained-bvmod", "0") )
                  {
                     assert (children[0] != children[1]);
                     ASTNode v =replaceParentWithFresh(muteParent, variable_array);
                     replace(children[1], bm.CreateZeroConst(width));
                     replace(children[0], v);
                  }
              }
             break;


        case BVDIV:
             {
                 assert(numberOfChildren == 2);
                 if (mutable_children[0]->isUnconstrained() && mutable_children[1]->isUnconstrained())
                  {
                     assert (children[0] != children[1]);
                     ASTNode v =replaceParentWithFresh(muteParent, variable_array);
                     replace(children[1], bm.CreateOneConst(width));
                     replace(children[0], v);
                  }
              }
             break;
        case BVMULT:
              {
                 assert(numberOfChildren == 2);

                if (mutable_children[1]->isUnconstrained() && mutable_children[0]->isUnconstrained()) // both are unconstrained
                  {
                    ASTNode v =replaceParentWithFresh(muteParent, variable_array);
                    replace(children[0], bm.CreateOneConst(width));
                    replace(children[1], v);
                  }

                if (other.isConstant() && simplifier->BVConstIsOdd(other))
                  {
                    ASTNode v =replaceParentWithFresh(muteParent, variable_array);
                    ASTNode inverse = simplifier->MultiplicativeInverse(other);
                    ASTNode rhs = nf->CreateTerm(BVMULT, width, inverse, v);
                    replace(var, rhs);
                  }

                break;
        case IFF:
              {
                ASTNode v =replaceParentWithFresh(muteParent, variable_array);

                ASTNode rhs = nf->CreateNode(ITE, v, muteOther->toASTNode(nf), nf->CreateNode(NOT, muteOther->toASTNode(nf)));
                replace(var, rhs);
              }
          break;
        case EQ:
              {
                ASTNode v =replaceParentWithFresh(muteParent, variable_array);

                width = var.GetValueWidth();
                ASTNode rhs = nf->CreateTerm(ITE, width, v, muteOther->toASTNode(nf), nf->CreateTerm(BVPLUS, width, muteOther->toASTNode(nf),
                    bm.CreateOneConst(width)));

                replace(var, rhs);
              }
          break;
        case BVSUB:
          {
            assert(numberOfChildren == 2);

            ASTNode v =replaceParentWithFresh(muteParent, variable_array);

            ASTNode rhs;

            if (children[0] == var)
              rhs= nf->CreateTerm(BVPLUS, width, v, muteOther->toASTNode(nf));
            if (children[1] == var)
              rhs= nf->CreateTerm(BVSUB, width, muteOther->toASTNode(nf), v);

            replace(var, rhs);
          }
          break;

        case BVPLUS:
              {
                ASTVec other;
                for (int i = 0; i < children.size(); i++)
                  if (children[i] != var)
                    other.push_back(mutable_children[i]->toASTNode(nf));

                assert(other.size() == children.size()-1);
                assert(other.size() >=1);

                ASTNode v =replaceParentWithFresh(muteParent, variable_array);

                ASTNode rhs;
                if (other.size() > 1)
                  rhs = nf->CreateTerm(BVSUB, width, v, nf->CreateTerm(BVPLUS, width, other));
                else
                  rhs = nf->CreateTerm(BVSUB, width, v, other[0]);

                replace(var, rhs);
              }
           break;
        case BVEXTRACT:
              {
                ASTNode v =replaceParentWithFresh(muteParent, variable_array);

                const unsigned resultWidth = width;
                const unsigned operandWidth = var.GetValueWidth();
                assert(children[0] == var); // It can't be anywhere else.

                // Create Fresh variables to pad the LHS and RHS.
                const unsigned high = children[1].GetUnsignedConst();
                const unsigned low = children[2].GetUnsignedConst();
                assert(high >=low);

                const int rhsSize = low;
                const int lhsSize = operandWidth - high - 1;

                ASTNode current = v;
                int newWidth = v.GetValueWidth();

                if (lhsSize > 0)
                  {
                    ASTNode lhsFresh = bm.CreateFreshVariable(0, lhsSize, "lhs_padding");
                    current = nf->CreateTerm(BVCONCAT, newWidth + lhsSize, lhsFresh, current);
                    newWidth += lhsSize;
                  }

                if (rhsSize > 0)
                  {
                    ASTNode rhsFresh = bm.CreateFreshVariable(0, rhsSize, "rhs_padding");
                    current = nf->CreateTerm(BVCONCAT, newWidth + rhsSize, current, rhsFresh);
                    newWidth += rhsSize;
                  }

                assert(newWidth == operandWidth);
                replace(var, current);
              }
        break;
        default:
          {
            //cerr << "!!!!" << kind << endl;
          }

            //        cerr << var;
              //      cerr << parent;

              }
          }
      }

    ASTNode result = topMutable->toASTNode(nf);
    topMutable->cleanup();
    //cout << result;
    return result;
  }

}
;
