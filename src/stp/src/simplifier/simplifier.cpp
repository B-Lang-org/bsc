// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include <cassert>
#include <cmath>
#include "simplifier.h"
#include "AIGSimplifyPropositionalCore.h"

namespace BEEV
{

  // If enabled, simplifyTerm will simplify all the arguments to a function before attempting
  // the simplification of that function. Without this option the case will be selected for
  // each kind, and that case needs to simplify the arguments.

  // Longer term, this means that each function doesn't need to worry about calling simplify
// on it's arguments (I suspect some paths don't call simplify on their arguments). But it
// does mean that we can't short cut, for example, if the first argument to a BVOR is all trues,
// then all the other arguments have already been simplified, so won't be short-cutted.

  // is it ITE(p,bv0[1], bv1[1])  OR  ITE(p,bv0[0], bv1[0])
  bool
  isPropositionToTerm(const ASTNode& n)
  {
    if (n.GetType() != BITVECTOR_TYPE)
      return false;
    if (n.GetValueWidth() != 1)
      return false;
    if (n.GetKind() != ITE)
      return false;
    if (!n[1].isConstant())
      return false;
    if (!n[2].isConstant())
      return false;
    if (n[1] == n[0])
      return false;
    return true;
  }

  bool
  Simplifier::CheckMap(ASTNodeMap* VarConstMap, const ASTNode& key, ASTNode& output)
  {
    if (NULL == VarConstMap)
      {
        return false;
      }
    ASTNodeMap::iterator it;
    if ((it = VarConstMap->find(key)) != VarConstMap->end())
      {
        output = it->second;
        return true;
      }
    return false;
  }

  bool
  Simplifier::CheckSimplifyMap(const ASTNode& key, ASTNode& output, bool pushNeg, ASTNodeMap* VarConstMap)
  {
    if (NULL != VarConstMap)
      {
        return false;
      }

    if (!pushNeg && key.isSimplfied())
      {
        output = key;
        return true;
      }

    ASTNodeMap::iterator it, itend;
    it = pushNeg ? SimplifyNegMap->find(key) : SimplifyMap->find(key);
    itend = pushNeg ? SimplifyNegMap->end() : SimplifyMap->end();

    if (it != itend)
      {
        output = it->second;
        CountersAndStats("Successful_CheckSimplifyMap", _bm);
        return true;
      }

    if (pushNeg && (it = SimplifyMap->find(key)) != SimplifyMap->end())
      {
        output = (ASTFalse == it->second) ? ASTTrue :
                 (ASTTrue == it->second) ? ASTFalse : nf->CreateNode(NOT, it->second);
        CountersAndStats("2nd_Successful_CheckSimplifyMap", _bm);
        return true;
      }

    return false;
  }

  void
  Simplifier::UpdateSimplifyMap(const ASTNode& key, const ASTNode& value, bool pushNeg, ASTNodeMap* VarConstMap)
  {
    if (NULL != VarConstMap)
      {
        return;
      }assert(!value.IsNull());

    // Don't add leaves. Leaves are easy to recalculate, no need
    // to cache.
    if (0 == key.Degree())
      return;

    if (pushNeg)
      (*SimplifyNegMap)[key] = value;
    else
      (*SimplifyMap)[key] = value;

    if (!pushNeg && key == value)
      {
        key.hasBeenSimplfied();
      }
  }

  // Substitution Map methods....

  bool
  Simplifier::UpdateSolverMap(const ASTNode& key, const ASTNode& value)
  {
    return substitutionMap.UpdateSolverMap(key, value);
  }

  bool
  Simplifier::CheckSubstitutionMap(const ASTNode& key, ASTNode& output)
  {
    return substitutionMap.CheckSubstitutionMap(key, output);
  }

  ASTNode
  Simplifier::applySubstitutionMap(const ASTNode& n)
  {
    return substitutionMap.applySubstitutionMap(n);
  }

  ASTNode
  Simplifier::applySubstitutionMapUntilArrays(const ASTNode& n)
  {
    return substitutionMap.applySubstitutionMapUntilArrays(n);
  }

  bool
  Simplifier::CheckSubstitutionMap(const ASTNode& key)
  {
    return substitutionMap.CheckSubstitutionMap(key);
  }
  bool
  Simplifier::UpdateSubstitutionMapFewChecks(const ASTNode& e0, const ASTNode& e1)
  {
    return substitutionMap.UpdateSubstitutionMapFewChecks(e0, e1);
  }

  bool
  Simplifier::UpdateSubstitutionMap(const ASTNode& e0, const ASTNode& e1)
  {
    return substitutionMap.UpdateSubstitutionMap(e0, e1);
  }
  // --- Substitution Map methods....

  bool
  Simplifier::CheckMultInverseMap(const ASTNode& key, ASTNode& output)
  {
    ASTNodeMap::iterator it;
    if ((it = MultInverseMap.find(key)) != MultInverseMap.end())
      {
        output = it->second;
        return true;
      }
    return false;
  }

  void
  Simplifier::UpdateMultInverseMap(const ASTNode& key, const ASTNode& value)
  {
    MultInverseMap[key] = value;
  }

  // Check if key, or NOT(key) is found in the alwaysTrueSet.
  bool
  Simplifier::CheckAlwaysTrueFormSet(const ASTNode& key, bool& result)
  {
    HASHSET<int>::const_iterator it_end_2 = AlwaysTrueHashSet.end();
    HASHSET<int>::const_iterator it2 = AlwaysTrueHashSet.find(key.GetNodeNum());

    if (it2 != it_end_2)
      {
        result = true; // The key should be replaced by TRUE.
        return true;
      }

    int toSearch;
    if (key.GetKind() == NOT)
      toSearch = key.GetNodeNum() - 1;
    else
      toSearch = key.GetNodeNum() + 1;

    it2 = AlwaysTrueHashSet.find(toSearch);
    if (it2 != it_end_2)
      {
        result = false;
        return true;
      }

    return false;
  }

  void
  Simplifier::UpdateAlwaysTrueFormSet(const ASTNode& key)
  {
    // The always true/ always false relies on the top level constraint not being removed.
    // however with bb equivalence checking, AIGs can figure out that the outer constraint
    // is unncessary because it's enforced by the implicit constraint---removing it. That
    // leaves just one instance of the constraint, so it we replace it with true/false
    // the constraint is lost. This is subsumed by constant bit propagation, so I suspect
    // it's not a big loss.
    if (!_bm->UserFlags.isSet("bb-equiv","1"))
      AlwaysTrueHashSet.insert(key.GetNodeNum());
  }

  ASTNode
  Simplifier::SimplifyFormula_NoRemoveWrites(const ASTNode& b, bool pushNeg, ASTNodeMap* VarConstMap)
  {
    //_bm->Begin_RemoveWrites = false;
    ASTNode out = SimplifyFormula(b, pushNeg, VarConstMap);
    return out;
  }

  // I like simplify to have been run on all the nodes.
  void
  Simplifier::checkIfInSimplifyMap(const ASTNode& n, ASTNodeSet visited)
  {
    if (n.isConstant() || (n.GetKind() == SYMBOL))
      return;

    if (visited.find(n) != visited.end())
      return;

    if (SimplifyMap->find(n) == SimplifyMap->end())
      {
        cerr << "not found";
        cerr << n;
        assert(false);
      }

    for (int i = 0; i < n.Degree(); i++)
      {
        checkIfInSimplifyMap(n[i], visited);
      }

    visited.insert(n);
  }

  // The SimplifyMaps on entry to the topLevel functions may contain
  // useful entries.  E.g. The BVSolver calls SimplifyTerm()
  ASTNode
  Simplifier::SimplifyFormula_TopLevel(const ASTNode& b, bool pushNeg, ASTNodeMap* VarConstMap)
  {
    assert(_bm->UserFlags.optimize_flag);
    _bm->GetRunTimes()->start(RunTimes::SimplifyTopLevel);
    ASTNode out = SimplifyFormula(b, pushNeg, VarConstMap);
    ASTNodeSet visited;
    //checkIfInSimplifyMap(out,visited);
    ResetSimplifyMaps();
    _bm->GetRunTimes()->stop(RunTimes::SimplifyTopLevel);
    return out;
  }

  ASTNode
  Simplifier::SimplifyTerm_TopLevel(const ASTNode& b)
  {
    assert(_bm->UserFlags.optimize_flag);
    _bm->GetRunTimes()->start(RunTimes::SimplifyTopLevel);
    ASTNode out = SimplifyTerm(b);
    ResetSimplifyMaps();
    _bm->GetRunTimes()->stop(RunTimes::SimplifyTopLevel);
    return out;
  }

  ASTNode
  Simplifier::SimplifyFormula(const ASTNode& b, bool pushNeg, ASTNodeMap* VarConstMap)
  {
    assert(_bm->UserFlags.optimize_flag);
    assert(BOOLEAN_TYPE == b.GetType());

    if (b.isConstant())
      {
        if (!pushNeg)
          return b;
        else
          {
            if (ASTTrue == b)
              return ASTFalse;
            else
              return ASTTrue;
          }
      }

    ASTNode output;
    if (CheckSimplifyMap(b, output, pushNeg, VarConstMap))
      return output;

    Kind kind = b.GetKind();

    ASTNode a = b;
    ASTVec ca = a.GetChildren();
    if (!(IMPLIES == kind || ITE == kind || PARAMBOOL == kind || isAtomic(kind)))
      {
        SortByArith(ca);
        if (ca != a.GetChildren())
          a = nf->CreateNode(kind, ca);
      }

    kind = a.GetKind();

    if (false)
      {
        if (!a.isConstant() && kind != SYMBOL) // const and symbols need to be created specially.
          {
            assert(a.Degree() > 0);
            ASTVec v;
            v.reserve(a.Degree());
            for (unsigned i = 0; i < a.Degree(); i++)
              if (a[i].GetType() == BITVECTOR_TYPE)
                v.push_back(SimplifyTerm(a[i], VarConstMap));
              else if (a[i].GetType() == BOOLEAN_TYPE)
                v.push_back(SimplifyFormula(a[i], VarConstMap));
              else
                v.push_back(a[i]);

            // TODO: Should check if the children arrays are different and only
            // create then.
            ASTNode output = nf->CreateNode(kind, v);

            if (a != output)
              {
                UpdateSimplifyMap(a, output, false, VarConstMap);
                a = output;
              }
          }
      }

    a = PullUpITE(a);
    kind = a.GetKind(); // pullUpITE can change the Kind of the node.

    switch (kind)
      {
    case AND:
    case OR:
      output = SimplifyAndOrFormula(a, pushNeg, VarConstMap);
      break;
    case NOT:
      output = SimplifyNotFormula(a, pushNeg, VarConstMap);
      break;
    case XOR:
      output = SimplifyXorFormula(a, pushNeg, VarConstMap);
      break;
    case NAND:
      output = SimplifyNandFormula(a, pushNeg, VarConstMap);
      break;
    case NOR:
      output = SimplifyNorFormula(a, pushNeg, VarConstMap);
      break;
    case IFF:
      output = SimplifyIffFormula(a, pushNeg, VarConstMap);
      break;
    case IMPLIES:
      output = SimplifyImpliesFormula(a, pushNeg, VarConstMap);
      break;
    case ITE:
      output = SimplifyIteFormula(a, pushNeg, VarConstMap);
      break;
    default:
      //kind can be EQ,NEQ,BVLT,BVLE,... or a propositional variable
      output = SimplifyAtomicFormula(a, pushNeg, VarConstMap);
      break;
      }

    UpdateSimplifyMap(b, output, pushNeg, VarConstMap);
    UpdateSimplifyMap(a, output, pushNeg, VarConstMap);

    ASTNode input_with_not = pushNeg ? nf->CreateNode(NOT, a) : a;
    if (input_with_not != output)
      {
        return SimplifyFormula(output, false, VarConstMap);
      }
    return output;
  }

  ASTNode
  Simplifier::SimplifyForFormula(const ASTNode& a, bool pushNeg, ASTNodeMap* VarConstMap)
  {
    //FIXME: Code this up properly later. Mainly pushing the negation
    //down
    return a;
  }

  ASTNode
  Simplifier::SimplifyAtomicFormula(const ASTNode& a, bool pushNeg, ASTNodeMap* VarConstMap)
  {
    //     if (!optimize_flag)
    //       return a;

    ASTNode output;
    if (CheckSimplifyMap(a, output, pushNeg, VarConstMap))
      {
        return output;
      }

    ASTNode left, right;
    if (a.Degree() == 2)
      {
        //cerr << "Input to simplifyterm: left: " << a[0] << endl;
        left = SimplifyTerm(a[0], VarConstMap);
        //cerr << "Output of simplifyterm:left: " << left << endl;
        //cerr << "Input to simplifyterm: right: " << a[1] << endl;
        right = SimplifyTerm(a[1], VarConstMap);
        //cerr << "Output of simplifyterm:left: " << right << endl;
      }

    Kind kind = a.GetKind();
    switch (kind)
      {
    case TRUE:
      output = pushNeg ? ASTFalse : ASTTrue;
      break;
    case FALSE:
      output = pushNeg ? ASTTrue : ASTFalse;
      break;
    case SYMBOL:
      if (!CheckSubstitutionMap(a, output))
        {
          output = a;
        }
      output = pushNeg ? nf->CreateNode(NOT, output) : output;
      break;
    case PARAMBOOL:
      {
        ASTNode term = SimplifyTerm(a[1], VarConstMap);
        output = nf->CreateNode(PARAMBOOL, a[0], term);
        output = pushNeg ? nf->CreateNode(NOT, output) : output;
        break;
      }
    case BVGETBIT:
      {
        ASTNode term = SimplifyTerm(a[0], VarConstMap);
        ASTNode thebit = a[1];
        ASTNode zero = _bm->CreateZeroConst(1);
        ASTNode one = _bm->CreateOneConst(1);
        ASTNode getthebit = SimplifyTerm(nf->CreateTerm(BVEXTRACT, 1, term, thebit, thebit), VarConstMap);
        if (getthebit == zero)
          output = pushNeg ? ASTTrue : ASTFalse;
        else if (getthebit == one)
          output = pushNeg ? ASTFalse : ASTTrue;
        else
          {
            output = nf->CreateNode(BVGETBIT, term, thebit);
            output = pushNeg ? nf->CreateNode(NOT, output) : output;
          }
        break;
      }
    case EQ:
      {
        output = CreateSimplifiedEQ(left, right);
        output = LhsMinusRhs(output);
        output = ITEOpt_InEqs(output);
        if (output == ASTTrue)
          output = pushNeg ? ASTFalse : ASTTrue;
        else if (output == ASTFalse)
          output = pushNeg ? ASTTrue : ASTFalse;
        else
          output = pushNeg ? nf->CreateNode(NOT, output) : output;
        break;
      }
    case BVLT:
    case BVLE:
    case BVGT:
    case BVGE:
    case BVSLT:
    case BVSLE:
    case BVSGT:
    case BVSGE:
      {
        output = CreateSimplifiedINEQ(kind, left, right, pushNeg);
        break;
      }
    default:
      FatalError("SimplifyAtomicFormula: "
          "NO atomic formula of the kind: ", ASTUndefined, kind);
      break;
      }

    //memoize
    UpdateSimplifyMap(a, output, pushNeg, VarConstMap);
    return output;
  } //end of SimplifyAtomicFormula()

  // number of constant bits in the most significant places.
  int
  mostSignificantConstants(const ASTNode& n)
  {
    if (n.isConstant())
      return n.GetValueWidth();
    if (n.GetKind() == BVCONCAT)
      return mostSignificantConstants(n[0]);
    return 0;
  }

  int
  getConstantBit(const ASTNode& n, const int i)
  {
    if (n.GetKind() == BVCONST)
      {
        assert(n.GetValueWidth()-1-i >=0);
        return CONSTANTBV::BitVector_bit_test(n.GetBVConst(), n.GetValueWidth() - 1 - i) ? 1 : 0;
      }
    if (n.GetKind() == BVCONCAT)
      return getConstantBit(n[0], i);

    assert(false);
  }

  ASTNode
  replaceIteConst(const ASTNode&n, const ASTNode& newVal, NodeFactory *nf)
  {
    assert(!n.IsNull());
    assert(!newVal.IsNull());
    if (n.GetKind() == BVCONST)
      {
        return nf->CreateNode(EQ, newVal, n);
      }
    else if (n.GetKind() == ITE)
      {
        return nf->CreateNode(ITE, n[0], replaceIteConst(n[1], newVal, nf), replaceIteConst(n[2], newVal, nf));
      }
    FatalError("never here", n);
  }

  bool
  getPossibleValues(const ASTNode&n, ASTNodeSet& visited, vector<ASTNode>& found, int maxCount = 5)
  {
    if (maxCount <= 0)
      return false;

    ASTNodeSet::iterator it = visited.find(n);
    if (it != visited.end())
      return true;
    visited.insert(n);

    if (n.GetKind() == BVCONST)
      {
        found.push_back(n);
        return true;
      }

    if (n.GetKind() == ITE)
      {
        bool a = getPossibleValues(n[1], visited, found, maxCount - 1);
        if (!a)
          return a;

        bool b = getPossibleValues(n[2], visited, found, maxCount - 1);
        if (!b)
          return b;
        return true;
      }

    return false;
  }

  int
  numberOfLeadingZeroes(const ASTNode& n)
  {
    int c = mostSignificantConstants(n);
    if (c <= 0)
      return 0;

    for (int i = 0; i < c; i++)
      if (getConstantBit(n, i) != 0)
        return i;
    return c;
  }

  bool
  unsignedGreaterThan(const ASTNode& n1, const ASTNode& n2)
  {
    assert(n1.isConstant());
    assert(n2.isConstant());
    assert(n1.GetValueWidth() == n2.GetValueWidth());

    int comp = CONSTANTBV::BitVector_Lexicompare(n1.GetBVConst(), n2.GetBVConst());
    return comp == 1;
  }

  bool
  signedGreaterThan(const ASTNode& n1, const ASTNode& n2)
  {
    assert(n1.isConstant());
    assert(n2.isConstant());
    assert(n1.GetValueWidth() == n2.GetValueWidth());

    int comp = CONSTANTBV::BitVector_Compare(n1.GetBVConst(), n2.GetBVConst());
    return comp == 1;
  }

  ASTNode
  Simplifier::CreateSimplifiedINEQ(const Kind k_i, const ASTNode& left_i, const ASTNode& right_i, bool pushNeg)
  {

    // We reduce down to four possible inequalities.
    // NB. If the simplifying node factory is enabled, it will have done this already.
    bool swap = false;
    if (k_i == BVLT || k_i == BVLE || k_i == BVSLT || k_i == BVSLE)
      swap = true;

    const ASTNode& left = (swap) ? right_i : left_i;
    const ASTNode& right = (swap) ? left_i : right_i;

    Kind k = k_i;
    if (k == BVLT)
      k = BVGT;
    else if (k == BVLE)
      k = BVGE;
    else if (k == BVSLT)
      k = BVSGT;
    else if (k == BVSLE)
      k = BVSGE;

    assert(k == BVGT || k == BVGE || k== BVSGT || k == BVSGE);

    ASTNode output;
    if (BVCONST == left.GetKind() && BVCONST == right.GetKind())
      {
        output = BVConstEvaluator(nf->CreateNode(k, left, right));
        output = pushNeg ? (ASTFalse == output) ? ASTTrue : ASTFalse : output;
        return output;
      }

    if (k == BVLT || k == BVGT || k == BVSLT || k == BVSGT)
      {
        if (left == right)
          return pushNeg ? ASTTrue : ASTFalse;
      }

    if (k == BVLE || k == BVGE || k == BVSLE || k == BVSGE)
      {
        if (left == right)
          return pushNeg ? ASTFalse : ASTTrue;
      }

    const unsigned len = left.GetValueWidth();

    if (_bm->UserFlags.isSet("inequality-simplifications", "1"))
      {

        const int constStart = std::min(mostSignificantConstants(left), mostSignificantConstants(right));
        int comparator = 0;

        for (int i = 0; i < constStart; i++)
          {
            const int a = getConstantBit(left, i);
            const int b = getConstantBit(right, i);
            assert(a==1 || a==0);
            assert(b==1 || b==0);

            if (a < b)
              {
                comparator = -1;
                break;
              }
            else if (a > b)
              {
                comparator = +1;
                break;
              }
          }

        if (comparator != 0 && (k == BVGT || k == BVGE))
          {
            ASTNode status = (comparator == 1) ? ASTTrue : ASTFalse;
            return pushNeg ? nf->CreateNode(NOT, status) : status;
          }

        if (comparator != 0 && (k == BVSGT || k == BVSGE))
          {
            // one is bigger than the other.
            int sign_a = getConstantBit(left, 0);
            int sign_b = getConstantBit(right, 0);
            if (sign_a < sign_b)
              {
                comparator = 1; // a > b.
              }
            if (sign_a > sign_b)
              comparator = -1;

            ASTNode status = (comparator == 1) ? ASTTrue : ASTFalse;
            return pushNeg ? nf->CreateNode(NOT, status) : status;
          }

          {
            ASTNodeSet visited0, visited1;
            vector<ASTNode> l0, l1;

            // Sound overapproximation. Doesn't consider the equalities.
            if (getPossibleValues(left, visited0, l0) && getPossibleValues(right, visited1, l1))
              {
                  {
                    bool
                    (*comp)(const ASTNode&, const ASTNode&);
                    if (k == BVSGT || k == BVSGE)
                      comp = signedGreaterThan;
                    else
                      comp = unsignedGreaterThan;
                      {
                        ASTNode minLHS = *max_element(l0.begin(), l0.end(), comp);
                        ASTNode maxRHS = *min_element(l1.begin(), l1.end(), comp);

                        if (comp(minLHS, maxRHS))
                          return pushNeg ? ASTFalse : ASTTrue;
                      }
                      {
                        ASTNode maxLHS = *min_element(l0.begin(), l0.end(), comp);
                        ASTNode minRHS = *max_element(l1.begin(), l1.end(), comp);

                        if (comp(minRHS, maxLHS))
                          return pushNeg ? ASTTrue : ASTFalse;
                      }
                  }
              }
          }
      }

    const ASTNode unsigned_min = _bm->CreateZeroConst(len);
    const ASTNode one = _bm->CreateOneConst(len);
    const ASTNode unsigned_max = _bm->CreateMaxConst(len);

    switch (k)
      {
    case BVGT:
      if (left == unsigned_min)
        {
          output = pushNeg ? ASTTrue : ASTFalse;
        }
      else if (one == left)
        {
          output = CreateSimplifiedEQ(right, unsigned_min);
          output = pushNeg ? nf->CreateNode(NOT, output) : output;
        }
      else if (right == unsigned_max)
        {
          output = pushNeg ? ASTTrue : ASTFalse;
        }
      else
        {
          output = pushNeg ? nf->CreateNode(BVLE, left, right) : nf->CreateNode(BVLT, right, left);
        }
      break;
    case BVGE:
      if (right == unsigned_min)
        {
          output = pushNeg ? ASTFalse : ASTTrue;
        }
      else if (unsigned_max == left)
        {
          output = pushNeg ? ASTFalse : ASTTrue;
        }
      else if (unsigned_min == left)
        {
          output = CreateSimplifiedEQ(right, unsigned_min);
          output = pushNeg ? nf->CreateNode(NOT, output) : output;
        }
      else
        {
          output = pushNeg ? nf->CreateNode(BVLT, left, right) : nf->CreateNode(BVLE, right, left);
        }
      break;
    case BVSGE:
      {
        output = nf->CreateNode(k, left, right);
        output = pushNeg ? nf->CreateNode(NOT, output) : output;
      }

      break;
    case BVSGT:
      output = nf->CreateNode(k, left, right);
      output = pushNeg ? nf->CreateNode(NOT, output) : output;
      break;
    default:
      FatalError("Wrong Kind");
      break;
      }

    assert(!output.IsNull());
    return output;
  }

  // turns say (bvslt (ite a b c) (ite a d e)) INTO (ite a (bvslt b d)
  // (bvslt c e)) Expensive. But makes some other simplifications
  // possible.
  ASTNode
  Simplifier::PullUpITE(const ASTNode& in)
  {
    if (2 != in.GetChildren().size())
      return in;
    if (ITE != in[0].GetKind())
      return in;
    if (ITE != in[1].GetKind())
      return in;
    if (in[0][0] != in[1][0]) // if the conditional is not equal.
      return in;

    // Consider equals. It takes bitvectors and returns a boolean.
    // Consider add. It takes bitvectors and returns bitvectors.
    // Consider concat. The bitwidth of each side could vary.

    ASTNode l1;
    ASTNode l2;
    ASTNode result;

    if (in.GetType() == BOOLEAN_TYPE)
      {
        l1 = nf->CreateNode(in.GetKind(), in[0][1], in[1][1]);
        l2 = nf->CreateNode(in.GetKind(), in[0][2], in[1][2]);
        result = nf->CreateNode(ITE, in[0][0], l1, l2);
      }
    else
      {
        l1 = nf->CreateTerm(in.GetKind(), in.GetValueWidth(), in[0][1], in[1][1]);
        l2 = nf->CreateTerm(in.GetKind(), in.GetValueWidth(), in[0][2], in[1][2]);
        result = nf->CreateTerm(ITE, in.GetValueWidth(), in[0][0], l1, l2);
      }

    assert(result.GetType() == in.GetType());
    assert(result.GetValueWidth() == in.GetValueWidth());
    assert(result.GetIndexWidth() == in.GetIndexWidth());
    assert(BVTypeCheck(result));

    return result;
  }

  //takes care of some simple ITE Optimizations in the context of equations
  ASTNode
  Simplifier::ITEOpt_InEqs(const ASTNode& in, ASTNodeMap* VarConstMap)
  {
    CountersAndStats("ITEOpts_InEqs", _bm);

    if (!(EQ == in.GetKind()))
      {
        return in;
      }

    ASTNode output;
    if (CheckSimplifyMap(in, output, false))
      {
        return output;
      }

    const ASTNode& in1 = in[0];
    const ASTNode& in2 = in[1];
    const Kind k1 = in1.GetKind();
    const Kind k2 = in2.GetKind();
    if (in1 == in2)
      {
        //terms are syntactically the same
        output = ASTTrue;
      }
    else if (BVCONST == k1 && BVCONST == k2)
      {
        assert(in1!=in2);
        output = ASTFalse;
      }
    else if (ITE == k1 && BVCONST == in1[1].GetKind() && BVCONST == in1[2].GetKind() && BVCONST == k2)
      {
        //if one side is a BVCONST and the other side is an ITE over
        //BVCONST then we can do the following optimization:
        //
        // c = ITE(cond,c,d) <=> cond
        //
        // similarly ITE(cond,c,d) = c <=> cond
        //
        // c = ITE(cond,d,c) <=> NOT(cond)
        //
        //similarly ITE(cond,d,c) = d <=> NOT(cond)
        ASTNode cond = in1[0];
        if (in1[1] == in2 && (in2 != in1[2]))
          {
            //ITE(cond, c, d) = c <=> cond
            output = cond;
          }
        else if (in1[2] == in2 && (in2 != in1[1]))
          {
            cond = SimplifyFormula(cond, true, VarConstMap);
            output = cond;
          }
        else
          {
            //last resort is to nf->CreateNode
            output = nf->CreateNode(EQ, in1, in2);
          }
      }
    else if (ITE == k2 && BVCONST == in2[1].GetKind() && BVCONST == in2[2].GetKind() && BVCONST == k1)
      {
        ASTNode cond = in2[0];
        if (in2[1] == in1 && (in1 != in2[2]))
          {
            //ITE(cond, c, d) = c <=> cond
            output = cond;
          }
        else if (in2[2] == in1 && (in1 != in2[1]))
          {
            cond = SimplifyFormula(cond, true, VarConstMap);
            output = cond;
          }
        else
          {
            //last resort is to CreateNode
            output = nf->CreateNode(EQ, in1, in2);
          }
      }
    else
      {
        //last resort is to CreateNode
        output = nf->CreateNode(EQ, in1, in2);
      }

    UpdateSimplifyMap(in, output, false, VarConstMap);
    return output;
  } //End of ITEOpts_InEqs()

  //Tries to simplify the input to TRUE/FALSE. if it fails, then
  //return the constructed equality
  ASTNode
  Simplifier::CreateSimplifiedEQ(const ASTNode& in1, const ASTNode& in2)
  {
    CountersAndStats("CreateSimplifiedEQ", _bm);
    const Kind k1 = in1.GetKind();
    const Kind k2 = in2.GetKind();

    if (in1 == in2)
      //terms are syntactically the same
      return ASTTrue;

    //here the terms are definitely not syntactically equal but may be
    //semantically equal.
    if (BVCONST == k1 && BVCONST == k2)
      return ASTFalse;

    // Check if some of the leading constant bits are different. Fancier code would check
    // each bit, not just the leading bits.
    const int constStart = std::min(mostSignificantConstants(in1), mostSignificantConstants(in2));

    for (int i = 0; i < constStart; i++)
      {
        const int a = getConstantBit(in1, i);
        const int b = getConstantBit(in2, i);
        assert(a==1 || a==0);
        assert(b==1 || b==0);

        if (a != b)
          return ASTFalse;
      }

    // The above loop has determined that the leading bits are the same.
    if (constStart > 0)
      {
        int newWidth = in1.GetValueWidth() - constStart;
        ASTNode zero = _bm->CreateZeroConst(32);

        ASTNode lhs = nf->CreateTerm(BVEXTRACT, newWidth, in1, _bm->CreateBVConst(32, newWidth - 1), zero);
        ASTNode rhs = nf->CreateTerm(BVEXTRACT, newWidth, in2, _bm->CreateBVConst(32, newWidth - 1), zero);
        ASTNode r = nf->CreateNode(EQ, lhs, rhs);
        assert(BVTypeCheck(r));
        return r;
      }

    // If both the children are concats split them apart.
    // nb. This doesn't cover the case when the children are organised differently:
    // (concat (concat A B) C) == (concat A (concat B C))
    if (k1 == BVCONCAT && k2 == BVCONCAT && in1[0].GetValueWidth() == in2[0].GetValueWidth())
      {
        return nf->CreateNode(AND, nf->CreateNode(EQ, in1[0], in2[0]), nf->CreateNode(EQ, in1[1], in2[1]));
      }

    // If the rhs is a concat, and the lhs is a constant. Split.
    if (k1 == BVCONST && k2 == BVCONCAT)
      {
        int width = in1.GetValueWidth();
        int bottomW = in2[1].GetValueWidth();
        ASTNode zero = _bm->CreateZeroConst(32);

        // split the constant.
        ASTNode top = nf->CreateTerm(BVEXTRACT, width - bottomW, in1, _bm->CreateBVConst(32, width - 1),
            _bm->CreateBVConst(32, bottomW));
        ASTNode bottom = nf->CreateTerm(BVEXTRACT, bottomW, in1, _bm->CreateBVConst(32, bottomW - 1), zero);
        assert(BVTypeCheck(top));
        assert(BVTypeCheck(bottom));

        ASTNode r = nf->CreateNode(AND, nf->CreateNode(EQ, top, in2[0]), nf->CreateNode(EQ, bottom, in2[1]));

        return r;
      }

    if ((k1 == ITE || k1 == BVCONST) && (k2 == ITE || k2 == BVCONST) && _bm->UserFlags.isSet("ite-const","1"))
      {
        // If it can only evaluate to constants on the LHS and the RHS, and those constants are never equal,
        // then it must be false. e.g.   ite( f, 10 , 20 ) = ite (g, 30 ,12)
        ASTNodeSet visited0, visited1;
        vector<ASTNode> l0, l1;

        if (getPossibleValues(in1, visited0, l0) && getPossibleValues(in2, visited1, l1))
          {
            sort(l0.begin(), l0.end());
            sort(l1.begin(), l1.end());
            vector<ASTNode> result(l0.size() + l1.size());
            vector<ASTNode>::iterator it = set_intersection(l0.begin(), l0.end(), l1.begin(), l1.end(), result.begin());
            if (it == result.begin())
              return ASTFalse;

            if (it == result.begin() + 1)
              {
                // If there is just one value in common, then, set it to true whenever it equals that value.
                ASTNode lhs = replaceIteConst(in1, *result.begin(), nf);
                ASTNode rhs = replaceIteConst(in2, *result.begin(), nf);

                ASTNode result = nf->CreateNode(AND, lhs, rhs);
                return result;
              }
          }
      }

    //last resort is to CreateNode
    return nf->CreateNode(EQ, in1, in2);
  }

  // nb. this is sometimes used to build array terms.
  //accepts cond == t1, then part is t2, and else part is t3
  ASTNode
  Simplifier::CreateSimplifiedTermITE(const ASTNode& in0, const ASTNode& in1, const ASTNode& in2)
  {
    const ASTNode& t0 = in0;
    const ASTNode& t1 = in1;
    const ASTNode& t2 = in2;
    CountersAndStats("CreateSimplifiedITE", _bm);
    if (!_bm->UserFlags.optimize_flag)
      {
        if (t1.GetValueWidth() != t2.GetValueWidth())
          {
            cerr << "t2 is : = " << t2;
            FatalError("CreateSimplifiedTermITE: "
                "the lengths of the two branches don't match", t1);
          }
        if (t1.GetIndexWidth() != t2.GetIndexWidth())
          {
            cerr << "t2 is : = " << t2;
            FatalError("CreateSimplifiedTermITE: "
                "the lengths of the two branches don't match", t1);
          }
        return nf->CreateArrayTerm(ITE, t1.GetIndexWidth(), t1.GetValueWidth(), t0, t1, t2);
      }

    if (t0 == ASTTrue)
      return t1;
    if (t0 == ASTFalse)
      return t2;
    if (t1 == t2)
      return t1;

    bool result;
    if (CheckAlwaysTrueFormSet(t0, result))
      {
        if (result)
          return t1;
        else
          return t2;
      }

    return nf->CreateArrayTerm(ITE, t1.GetIndexWidth(), t1.GetValueWidth(), t0, t1, t2);
  }

  ASTNode
  Simplifier::CreateSimplifiedFormulaITE(const ASTNode& in0, const ASTNode& in1, const ASTNode& in2)
  {
    const ASTNode& t0 = in0;
    const ASTNode& t1 = in1;
    const ASTNode& t2 = in2;
    CountersAndStats("CreateSimplifiedFormulaITE", _bm);

    if (_bm->UserFlags.optimize_flag)
      {
        if (t0 == ASTTrue)
          return t1;
        if (t0 == ASTFalse)
          return t2;
        if (t1 == t2)
          return t1;

        bool result;
        if (CheckAlwaysTrueFormSet(t0, result))
          {
            if (result)
              return t1;
            else
              return t2;
          }

      }
    ASTNode result = nf->CreateNode(ITE, t0, t1, t2);
    assert(BVTypeCheck(result));
    return result;
  }

  ASTNode
  Simplifier::SimplifyAndOrFormula(const ASTNode& a, bool pushNeg, ASTNodeMap* VarConstMap)
  {
    ASTNode output;
    //cerr << "input:\n" << a << endl;

    if (CheckSimplifyMap(a, output, pushNeg, VarConstMap))
      return output;

    const Kind k = a.GetKind();
    ASTVec c = FlattenKind(k, a.GetChildren());
    SortByArith(c);

    const bool isAnd = (k == AND) ? true : false;

    const ASTNode annihilator = isAnd ? (pushNeg ? ASTTrue : ASTFalse) : (pushNeg ? ASTFalse : ASTTrue);

    const ASTNode identity = isAnd ? (pushNeg ? ASTFalse : ASTTrue) : (pushNeg ? ASTTrue : ASTFalse);

    ASTVec outvec;
    outvec.reserve(c.size());

    //do the work
    ASTVec::const_iterator next_it;
    for (ASTVec::const_iterator i = c.begin(), iend = c.end(); i != iend; i++)
      {
        next_it = i + 1;
        bool nextexists = (next_it < iend);

        const ASTNode aaa = SimplifyFormula(*i, pushNeg, VarConstMap);
        if (annihilator == aaa)
          {
            //memoize
            UpdateSimplifyMap(*i, annihilator, pushNeg, VarConstMap);
            UpdateSimplifyMap(a, annihilator, pushNeg, VarConstMap);
            //cerr << "annihilator1: output:\n" << annihilator << endl;
            return annihilator;
          }
        ASTNode bbb;
        if (nextexists)
          {
            bbb = SimplifyFormula(*next_it, pushNeg, VarConstMap);
          }
        if (nextexists && bbb == aaa)
          {
            //skip the duplicate aaa. *next_it will be included
          }
        else if (nextexists && ((bbb.GetKind() == NOT && bbb[0] == aaa)))
          {
            //memoize
            UpdateSimplifyMap(a, annihilator, pushNeg, VarConstMap);
            //cerr << "annihilator2: output:\n" << annihilator << endl;
            return annihilator;
          }
        else if (identity == aaa)
          {
            // //drop identites
          }
        else
          {
            outvec.push_back(aaa);
          }
      }

    switch (outvec.size())
      {
    case 0:
      {
        //only identities were dropped
        output = identity;
        break;
      }
    case 1:
      {
        output = outvec[0];
        break;
      }
    default:
      {
        output =
            (isAnd) ? (pushNeg ? nf->CreateNode(OR, outvec) : nf->CreateNode(AND, outvec)) :
                (pushNeg ? nf->CreateNode(AND, outvec) : nf->CreateNode(OR, outvec));
        break;
      }
      }

    //memoize
    UpdateSimplifyMap(a, output, pushNeg, VarConstMap);
    //cerr << "output:\n" << output << endl;
    return output;
  } //end of SimplifyAndOrFormula

  ASTNode
  Simplifier::SimplifyNotFormula(const ASTNode& a, bool pushNeg, ASTNodeMap* VarConstMap)
  {
    ASTNode output;
    if (CheckSimplifyMap(a, output, pushNeg, VarConstMap))
      return output;

    if (!(a.Degree() == 1 && NOT == a.GetKind()))
      FatalError("SimplifyNotFormula: input vector with more than 1 node", ASTUndefined);

    //if pushNeg is set then there is NOT on top
    unsigned int NotCount = pushNeg ? 1 : 0;
    ASTNode o = a;
    //count the number of NOTs in 'a'
    while (NOT == o.GetKind())
      {
        o = o[0];
        NotCount++;
      }

    //pushnegation if there are odd number of NOTs
    bool pn = (NotCount % 2 == 0) ? false : true;

    bool alwaysTrue;
    if (CheckAlwaysTrueFormSet(o, alwaysTrue))
      {
        if (alwaysTrue)
          return (pn ? ASTFalse : ASTTrue);

        // We don't do the false case because it is sometimes
        // called at the top level.
      }

    if (CheckSimplifyMap(o, output, pn))
      {
        return output;
      }

    if (ASTTrue == o)
      {
        output = pn ? ASTFalse : ASTTrue;
      }
    else if (ASTFalse == o)
      {
        output = pn ? ASTTrue : ASTFalse;
      }
    else
      {
        output = SimplifyFormula(o, pn, VarConstMap);
      }
    //memoize
    UpdateSimplifyMap(o, output, pn, VarConstMap);
    UpdateSimplifyMap(a, output, pushNeg, VarConstMap);
    return output;
  }

  ASTNode
  Simplifier::SimplifyXorFormula(const ASTNode& a, bool pushNeg, ASTNodeMap* VarConstMap)
  {
    ASTNode output;
    if (CheckSimplifyMap(a, output, pushNeg, VarConstMap))
      return output;

    assert(a.GetChildren().size() > 0);

    if (a.GetChildren().size() == 1)
      {
        output = a[0];
      }
    else if (a.GetChildren().size() == 2)
      {
        ASTNode a0 = SimplifyFormula(a[0], false, VarConstMap);
        ASTNode a1 = SimplifyFormula(a[1], false, VarConstMap);
        if (pushNeg)
          a0 = nf->CreateNode(NOT, a0);
        output = nf->CreateNode(XOR, a0, a1);

        if (a0 == a1)
          output = ASTFalse;
        else if ((a0 == ASTTrue && a1 == ASTFalse) || (a0 == ASTFalse && a1 == ASTTrue))
          output = ASTTrue;
      }
    else
      {
        ASTVec newC;
        for (int i = 0; i < a.GetChildren().size(); i++)
          {
            newC.push_back(SimplifyFormula(a[i], false, VarConstMap));
          }
        if (pushNeg)
          newC[0] = nf->CreateNode(NOT, newC[0]);

        output = nf->CreateNode(XOR, newC);
      }

    //memoize
    UpdateSimplifyMap(a, output, pushNeg, VarConstMap);
    return output;
  }

  ASTNode
  Simplifier::SimplifyNandFormula(const ASTNode& a, bool pushNeg, ASTNodeMap* VarConstMap)
  {
    ASTNode output, a0, a1;
    if (CheckSimplifyMap(a, output, pushNeg, VarConstMap))
      return output;

    //the two NOTs cancel out
    if (pushNeg)
      {
        a0 = SimplifyFormula(a[0], false, VarConstMap);
        a1 = SimplifyFormula(a[1], false, VarConstMap);
        output = nf->CreateNode(AND, a0, a1);
      }
    else
      {
        //push the NOT implicit in the NAND
        a0 = SimplifyFormula(a[0], true, VarConstMap);
        a1 = SimplifyFormula(a[1], true, VarConstMap);
        output = nf->CreateNode(OR, a0, a1);
      }

    //memoize
    UpdateSimplifyMap(a, output, pushNeg, VarConstMap);
    return output;
  }

  ASTNode
  Simplifier::SimplifyNorFormula(const ASTNode& a, bool pushNeg, ASTNodeMap* VarConstMap)
  {
    ASTNode output, a0, a1;
    if (CheckSimplifyMap(a, output, pushNeg, VarConstMap))
      return output;

    //the two NOTs cancel out
    if (pushNeg)
      {
        a0 = SimplifyFormula(a[0], false);
        a1 = SimplifyFormula(a[1], false, VarConstMap);
        output = nf->CreateNode(OR, a0, a1);
      }
    else
      {
        //push the NOT implicit in the NAND
        a0 = SimplifyFormula(a[0], true, VarConstMap);
        a1 = SimplifyFormula(a[1], true, VarConstMap);
        output = nf->CreateNode(AND, a0, a1);
      }

    //memoize
    UpdateSimplifyMap(a, output, pushNeg, VarConstMap);
    return output;
  }

  ASTNode
  Simplifier::SimplifyImpliesFormula(const ASTNode& a, bool pushNeg, ASTNodeMap* VarConstMap)
  {
    ASTNode output;
    if (CheckSimplifyMap(a, output, pushNeg, VarConstMap))
      return output;

    if (!(a.Degree() == 2 && IMPLIES == a.GetKind()))
      FatalError("SimplifyImpliesFormula: vector with wrong num of nodes", ASTUndefined);

    ASTNode c0, c1;
    if (pushNeg)
      {
        c0 = SimplifyFormula(a[0], false, VarConstMap);
        c1 = SimplifyFormula(a[1], true, VarConstMap);
        output = nf->CreateNode(AND, c0, c1);
      }
    else
      {
        c0 = SimplifyFormula(a[0], false, VarConstMap);
        c1 = SimplifyFormula(a[1], false, VarConstMap);
        bool atResult;
        if (ASTFalse == c0)
          {
            output = ASTTrue;
          }
        else if (ASTTrue == c0)
          {
            output = c1;
          }
        else if (c0 == c1)
          {
            output = ASTTrue;
          }
        else if (CheckAlwaysTrueFormSet(c0, atResult))
          {
            // c0 AND (~c0 OR c1) <==> c1
            //(~c0 AND (~c0 OR c1)) <==> TRUE
            //(c0 AND ~c0->c1) <==> TRUE
            //(~c1 AND c0->c1) <==> (~c1 AND ~c1->~c0) <==> ~c0
            //(c1 AND c0->~c1) <==> (c1 AND c1->~c0) <==> ~c0

            if (atResult)
              output = c1;
            else
              output = ASTTrue;
          }
        else if (CheckAlwaysTrueFormSet(c1, atResult))
          {
            if (atResult)
              output = ASTTrue;
            else
              output = nf->CreateNode(NOT, c0);
          }
        else
          {
            if (NOT == c0.GetKind())
              {
                output = nf->CreateNode(OR, c0[0], c1);
              }
            else
              {
                output = nf->CreateNode(OR, nf->CreateNode(NOT, c0), c1);
              }
          }
      }

    //memoize
    UpdateSimplifyMap(a, output, pushNeg, VarConstMap);
    return output;
  }

  ASTNode
  Simplifier::SimplifyIffFormula(const ASTNode& a, bool pushNeg, ASTNodeMap* VarConstMap)
  {
    ASTNode output;
    if (CheckSimplifyMap(a, output, pushNeg, VarConstMap))
      return output;

    if (!(a.Degree() == 2 && IFF == a.GetKind()))
      FatalError("SimplifyIffFormula: vector with wrong num of nodes", ASTUndefined);

    ASTNode c0 = a[0];
    ASTNode c1 = SimplifyFormula(a[1], false, VarConstMap);

    if (pushNeg)
      c0 = SimplifyFormula(c0, true, VarConstMap);
    else
      c0 = SimplifyFormula(c0, false, VarConstMap);

    bool alwaysResult;

    if (ASTTrue == c0)
      {
        output = c1;
      }
    else if (ASTFalse == c0)
      {
        output = SimplifyFormula(c1, true, VarConstMap);
      }
    else if (ASTTrue == c1)
      {
        output = c0;
      }
    else if (ASTFalse == c1)
      {
        output = SimplifyFormula(c0, true, VarConstMap);
      }
    else if (c0 == c1)
      {
        output = ASTTrue;
      }
    else if ((NOT == c0.GetKind() && c0[0] == c1) || (NOT == c1.GetKind() && c0 == c1[0]))
      {
        output = ASTFalse;
      }
    else if (CheckAlwaysTrueFormSet(c0, alwaysResult))
      {
        if (alwaysResult)
          output = c1;
        else
          output = nf->CreateNode(NOT, c1);
      }
    else if (CheckAlwaysTrueFormSet(c1, alwaysResult))
      {
        if (alwaysResult)
          output = c0;
        else
          output = nf->CreateNode(NOT, c0);
      }
    else
      {
        output = nf->CreateNode(XOR, nf->CreateNode(NOT, c0), c1);
      }

    //memoize
    UpdateSimplifyMap(a, output, pushNeg, VarConstMap);
    return output;
  }

  ASTNode
  Simplifier::SimplifyIteFormula(const ASTNode& b, bool pushNeg, ASTNodeMap* VarConstMap)
  {
    //    if (!optimize_flag)
    //       return b;

    ASTNode output;
    if (CheckSimplifyMap(b, output, pushNeg, VarConstMap))
      return output;

    if (!(b.Degree() == 3 && ITE == b.GetKind()))
      FatalError("SimplifyIteFormula: vector with wrong num of nodes", ASTUndefined);

    ASTNode a = b;
    ASTNode t0 = SimplifyFormula(a[0], false, VarConstMap);
    ASTNode t1, t2;
    if (pushNeg)
      {
        t1 = SimplifyFormula(a[1], true, VarConstMap);
        t2 = SimplifyFormula(a[2], true, VarConstMap);
      }
    else
      {
        t1 = SimplifyFormula(a[1], false, VarConstMap);
        t2 = SimplifyFormula(a[2], false, VarConstMap);
      }

    bool alwaysTrue;

    if (ASTTrue == t0)
      {
        output = t1;
      }
    else if (ASTFalse == t0)
      {
        output = t2;
      }
    else if (t1 == t2)
      {
        output = t1;
      }
    else if (ASTTrue == t1 && ASTFalse == t2)
      {
        output = t0;
      }
    else if (ASTFalse == t1 && ASTTrue == t2)
      {
        output = SimplifyFormula(t0, true, VarConstMap);
      }
    else if (ASTTrue == t1)
      {
        output = nf->CreateNode(OR, t0, t2);
      }
    else if (ASTFalse == t1)
      {
        output = nf->CreateNode(AND, nf->CreateNode(NOT, t0), t2);
      }
    else if (ASTTrue == t2)
      {
        output = nf->CreateNode(OR, nf->CreateNode(NOT, t0), t1);
      }
    else if (ASTFalse == t2)
      {
        output = nf->CreateNode(AND, t0, t1);
      }
    else if (CheckAlwaysTrueFormSet(t0, alwaysTrue))
      {
        if (alwaysTrue)
          output = t1;
        else
          output = t2;
      }
    else
      {
        output = nf->CreateNode(ITE, t0, t1, t2);
      }

    //memoize
    UpdateSimplifyMap(a, output, pushNeg, VarConstMap);
    return output;
  }

  ASTNode
  Simplifier::makeTower(const Kind k, const BEEV::ASTVec &children)
  {
    deque<ASTNode> names;

    for (unsigned i = 0; i < children.size(); i++)
      names.push_back(children[i]);

    while (names.size() > 2)
      {
        ASTNode a = names.front();
        names.pop_front();

        ASTNode b = names.front();
        names.pop_front();

        ASTNode n = nf->CreateTerm(k, a.GetValueWidth(), a, b);
        names.push_back(n);
      }

    // last two now.
    assert(names.size() == 2);

    ASTNode a = names.front();
    names.pop_front();

    ASTNode b = names.front();
    names.pop_front();

    return nf->CreateTerm(k, a.GetValueWidth(), a, b);
  }

  // If a node is not a leaf, it has only been simplified  if it
  // maps to itself in the simplifyMap.
  bool
  Simplifier::hasBeenSimplified(const ASTNode& n)
  {
    //n has been simplified if, it's a constant:
    if (n.isConstant())
      return true;

    if (n.isSimplfied())
      return true;

    //If it's a symbol that's not in the substitition Map.
    if (n.GetKind() == SYMBOL && CheckSubstitutionMap(n))
      return false;

    if (n.GetKind() == SYMBOL)
      return true;

    ASTNodeMap::const_iterator it;
    //If it's in the simplification map, it has been simplified.
    if ((it = SimplifyMap->find(n)) == SimplifyMap->end())
      return false;

    return (it->second == n);
  }

  // If both of the children are sign extended. Makes this node sign extended too.
  ASTNode
  Simplifier::pullUpBVSX(ASTNode output)
  {
    assert(output.GetChildren().size() ==2);
    assert(output[0].GetKind() == BVSX);
    assert(output[1].GetKind() == BVSX);
    const Kind k = output.GetKind();

    assert(BVMULT == k || SBVDIV == k || BVPLUS ==k);
    const int inputValueWidth = output.GetValueWidth();

    int lengthA = output.GetChildren()[0][0].GetValueWidth();
    int lengthB = output.GetChildren()[1][0].GetValueWidth();
    int maxLength;
    if (BVMULT == output.GetKind())
      maxLength = lengthA + lengthB;
    else if (BVPLUS == output.GetKind() || SBVDIV == output.GetKind())
      maxLength = std::max(lengthA, lengthB) + 1;
    else
      FatalError("Unexpected.");
    if (maxLength < output.GetValueWidth())
      {
        ASTNode newA = nf->CreateTerm(BVEXTRACT, maxLength, output.GetChildren()[0],
            _bm->CreateBVConst(32, maxLength - 1), _bm->CreateZeroConst(32));
        newA = SimplifyTerm(newA);
        ASTNode newB = nf->CreateTerm(BVEXTRACT, maxLength, output.GetChildren()[1],
            _bm->CreateBVConst(32, maxLength - 1), _bm->CreateZeroConst(32));
        newB = SimplifyTerm(newB);

        ASTNode mult = nf->CreateTerm(output.GetKind(), maxLength, newA, newB);
        output = nf->CreateTerm(BVSX, inputValueWidth, mult, _bm->CreateBVConst(32, inputValueWidth));
      }
    return output;
  }

  // If the shift is bigger than the bitwidth, replace by an extract.
  ASTNode
  Simplifier::convertArithmeticKnownShiftAmount(const Kind k, const ASTVec& children, STPMgr& bm, NodeFactory *nf)
  {
    const ASTNode a = children[0];
    const ASTNode b = children[1];
    const int width = children[0].GetValueWidth();
    ASTNode output;

    assert(b.isConstant());
    assert(k == BVSRSHIFT);

    if (CONSTANTBV::Set_Max(b.GetBVConst()) > 1 + log2(width))
      {
        ASTNode top = bm.CreateBVConst(32, width - 1);
        return nf->CreateTerm(BVSX, width, nf->CreateTerm(BVEXTRACT, 1, children[0], top, top),
            bm.CreateBVConst(32, width));
      }
    else
      {
        if (b.GetUnsignedConst() >= width)
          {
            ASTNode top = bm.CreateBVConst(32, width - 1);
            return nf->CreateTerm(BVSX, width, nf->CreateTerm(BVEXTRACT, 1, children[0], top, top),
                bm.CreateBVConst(32, width));
          }
      }

    return ASTNode();
  }

  // If the rhs of a left or right shift is known.
  ASTNode
  Simplifier::convertKnownShiftAmount(const Kind k, const ASTVec& children, STPMgr& bm, NodeFactory *nf)
  {
    const ASTNode a = children[0];
    const ASTNode b = children[1];
    const int width = children[0].GetValueWidth();
    ASTNode output;

    assert(b.isConstant());
    assert(k == BVLEFTSHIFT || BVRIGHTSHIFT ==k);

    if (CONSTANTBV::Set_Max(b.GetBVConst()) > 1 + log2(width))
      {
        // Intended to remove shifts by very large amounts
        // that don't fit into the unsigned.  at thhe start
        // of the "else" branch.
        output = bm.CreateZeroConst(width);
      }
    else
      {
        const unsigned int shift = b.GetUnsignedConst();
        if (shift >= width)
          {
            output = bm.CreateZeroConst(width);
          }
        else if (shift == 0)
          {
            output = a; // unchanged.
          }
        else
          {
            if (k == BVLEFTSHIFT)
              {
                CBV cbv = CONSTANTBV::BitVector_Create(width, true);
                CONSTANTBV::BitVector_Bit_On(cbv, shift);
                ASTNode c = bm.CreateBVConst(cbv, width);

                output = nf->CreateTerm(BVMULT, width, a, c);
                BVTypeCheck(output);
                //cout << output;
                //cout << a << b << endl;
              }
            else if (k == BVRIGHTSHIFT)
              {
                ASTNode zero = bm.CreateZeroConst(shift);
                ASTNode hi = bm.CreateBVConst(32, width - 1);
                ASTNode low = bm.CreateBVConst(32, shift);
                ASTNode extract = nf->CreateTerm(BVEXTRACT, width - shift, a, hi, low);
                BVTypeCheck(extract);
                output = nf->CreateTerm(BVCONCAT, width, zero, extract);
                BVTypeCheck(output);
              }
            else
              FatalError("herasdf");
          }
      }
    return output;
  }

  //This function simplifies terms based on their kind
  ASTNode
  Simplifier::SimplifyTerm(const ASTNode& actualInputterm, ASTNodeMap* VarConstMap)
  {
    assert(_bm->UserFlags.optimize_flag);

    if (actualInputterm.isConstant())
      return actualInputterm;

    ASTNode inputterm(actualInputterm); // mutable local copy.

    //cout << "SimplifyTerm: input: " << actualInputterm << endl;
    // if (!optimize_flag)
    //       {
    //         return inputterm;
    //       }

    ASTNode output = inputterm;
    assert(BVTypeCheck(inputterm));

    //########################################
    //########################################

    if (CheckSubstitutionMap(inputterm, output))
      {
        //cout << "SolverMap:" << inputterm << " output: " << output << endl;
        return SimplifyTerm(output, VarConstMap);
      }

    if (CheckSimplifyMap(inputterm, output, false, VarConstMap))
      {
        //cerr << "SimplifierMap:" << inputterm << " output: " <<
        //output << endl;
        return output;
      }
    //########################################
    //########################################

    Kind k = inputterm.GetKind();
    if (!is_Term_kind(k))
      {
        FatalError("SimplifyTerm: You have input a Non-term", inputterm);
      }

    const unsigned int inputValueWidth = inputterm.GetValueWidth();

      {
        assert(k != BVCONST);
        if (k != SYMBOL) // const and symbols need to be created specially.
          {
            ASTVec v;
            ASTVec toProcess = actualInputterm.GetChildren();
            if (actualInputterm.GetKind() == BVAND || actualInputterm.GetKind() == BVOR
                || actualInputterm.GetKind() == BVPLUS)
              {
                // If we didn't flatten these, then we'd start flattening each of these
                // from the bottom up. Potentially creating tons of the nodes along the way.
                toProcess = FlattenKind(actualInputterm.GetKind(), toProcess);
              }

            v.reserve(toProcess.size());
            for (unsigned i = 0; i < toProcess.size(); i++)
              {
                if (toProcess[i].GetType() == BITVECTOR_TYPE)
                  v.push_back(SimplifyTerm(toProcess[i], VarConstMap));
                else if (toProcess[i].GetType() == BOOLEAN_TYPE)
                  v.push_back(SimplifyFormula(toProcess[i], VarConstMap));
                else
                  v.push_back(toProcess[i]);
              }

            assert(v.size() > 0);
            if (v != actualInputterm.GetChildren()) // short-cut.
              {
                output = nf->CreateArrayTerm(k, actualInputterm.GetIndexWidth(), inputValueWidth, v);
              }
            else
              output = actualInputterm;

            if (inputterm != output)
              {
                UpdateSimplifyMap(inputterm, output, false);
                inputterm = output;
              }
          }

        const ASTVec& children = inputterm.GetChildren();
        k = inputterm.GetKind();

        // Perform constant propagation if possible.
        // This should do nothing if the simplifyingnodefactory is used.
        if (k != BEEV::UNDEFINED && k != BEEV::SYMBOL)
          {
            bool allConstant = true;

            for (unsigned i = 0; i < children.size(); i++)
              if (!children[i].isConstant())
                {
                  allConstant = false;
                  break;
                }

            if (allConstant)
              {
                const ASTNode& c = BVConstEvaluator(inputterm);
                assert(c.isConstant());
                UpdateSimplifyMap(inputterm, c, false, VarConstMap);
                return c;
              }
          }
      }

      {
        ASTNode pulledUp = PullUpITE(inputterm);
        if (pulledUp != inputterm)
          {
            ASTNode r = SimplifyTerm(pulledUp);
            UpdateSimplifyMap(actualInputterm, r, false, NULL);
            UpdateSimplifyMap(inputterm, r, false, NULL);
            return r;
          }
      }

    //Check that each of the bit-vector operands is simplified.
    //I haven't measured if this is worth the expense.
      {
        bool notSimplified = false;
        for (int i = 0; i < inputterm.Degree(); i++)
          if (inputterm[i].GetType() != ARRAY_TYPE)
            if (!hasBeenSimplified(inputterm[i]))
              {
                notSimplified = true;
                break;
              }
        if (notSimplified)
          {
            ASTNode r = SimplifyTerm(inputterm);
            UpdateSimplifyMap(actualInputterm, r, false, NULL);
            UpdateSimplifyMap(inputterm, r, false, NULL);
            return r;
          }
      }

    switch (k)
      {
    case BVCONST:
      output = inputterm;
      break;
    case SYMBOL:
      if (CheckMap(VarConstMap, inputterm, output))
        {
          return output;
        }
      if (CheckSubstitutionMap(inputterm, output))
        {
          return SimplifyTerm(output, VarConstMap);
        }
      output = inputterm;
      break;
    case BVMULT:
      // follow on.
    case BVPLUS:
      {
        const ASTVec c = FlattenKind(k, inputterm.GetChildren());

        ASTVec constkids, nonconstkids;

        //go through the childnodes, and separate constant and
        //nonconstant nodes. combine the constant nodes using the
        //constevaluator. if the resultant constant is zero and k ==
        //BVPLUS, then ignore it (similarily for 1 and BVMULT).  else,
        //add the computed constant to the nonconst vector, flatten,
        //sort, and create BVPLUS/BVMULT and return
        for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it != itend; it++)
          {
            ASTNode aaa = *it;

            assert(hasBeenSimplified(aaa));

            if (BVCONST == aaa.GetKind())
              {
                constkids.push_back(aaa);
              }
            else
              {
                nonconstkids.push_back(aaa);
              }
          }

        const ASTNode one = _bm->CreateOneConst(inputValueWidth);
        const ASTNode max = _bm->CreateMaxConst(inputValueWidth);
        const ASTNode zero = _bm->CreateZeroConst(inputValueWidth);

        //initialize constoutput to zero, in case there are no elements
        //in constkids
        ASTNode constoutput = (k == BVPLUS) ? zero : one;

        if (1 == constkids.size())
          {
            //only one element in constkids
            constoutput = constkids[0];
          }
        else if (1 < constkids.size())
          {
            //many elements in constkids. simplify it
            constoutput = nf->CreateTerm(k, inputterm.GetValueWidth(), constkids);
            constoutput = BVConstEvaluator(constoutput);
          }

        if (BVMULT == k && zero == constoutput)
          {
            output = zero;
          }
        else if (BVMULT == k && 1 == nonconstkids.size() && constoutput == max)
          {
            //useful special case opt: when input is BVMULT(max_const,t),
            //then output = BVUMINUS(t). this is easier on the bitblaster
            output = nf->CreateTerm(BVUMINUS, inputValueWidth, nonconstkids);
          }
        else
          {
            if (0 < nonconstkids.size())
              {
                // ignore identities.
                if (BVPLUS == k && constoutput != zero)
                  {
                    nonconstkids.push_back(constoutput);
                  }
                else if (BVMULT == k && constoutput != one)
                  {
                    nonconstkids.push_back(constoutput);
                  }

                if (1 == nonconstkids.size())
                  {
                    //exactly one element in nonconstkids. output is exactly
                    //nonconstkids[0]
                    output = nonconstkids[0];
                  }
                else if (BVMULT == k)
                  {

                    SortByArith(nonconstkids);
                    if (k == BVMULT && nonconstkids.size() > 2)
                      output = makeTower(k, nonconstkids);
                    else
                      output = nf->CreateTerm(k, inputValueWidth, nonconstkids);
                    output = DistributeMultOverPlus(output, true);
                  }
                else // pluss.
                  {
                    assert(BVPLUS == k);
                    //SortByArith(nonconstkids);
                    //output = nf->CreateTerm(k, inputValueWidth, nonconstkids);
                    //output = Flatten(output);
                    //output = CombineLikeTerms(output);
                    output = CombineLikeTerms(nonconstkids);
                  }
              }
            else
              {
                //nonconstkids was empty, all childnodes were constant, hence
                //constoutput is the output.
                output = constoutput;
              }
          }

        // propagate bvuminus upwards through multiplies.
        if (BVMULT == output.GetKind())
          {
            ASTVec d = output.GetChildren();
            int uminus = 0;
            for (unsigned i = 0; i < d.size(); i++)
              {
                if (d[i].GetKind() == BVUMINUS)
                  {
                    d[i] = d[i][0];
                    uminus++;
                  }
              }
            if (uminus != 0)
              {
                SortByArith(d);
                output = nf->CreateTerm(BVMULT, output.GetValueWidth(), d);
                if ((uminus & 0x1) != 0) // odd, pull up the uminus.
                  {
                    output = nf->CreateTerm(BVUMINUS, output.GetValueWidth(), output);
                  }
              }
          }

        if ((BVMULT == output.GetKind() || BVPLUS == output.GetKind()) && output.GetChildren().size() == 2
            && output.GetChildren()[0].GetKind() == BVSX && output.GetChildren()[1].GetKind() == BVSX)
          {
            output = pullUpBVSX(output);
          }
        else if (BVMULT == output.GetKind())
          {
            output = makeTower(BVMULT, output.GetChildren());
          }
        else if (BVPLUS == output.GetKind())
          {
            ASTVec d = output.GetChildren();
            SortByArith(d);
            output = nf->CreateTerm(output.GetKind(), output.GetValueWidth(), d);
          }
        break;
      }
    case BVSUB:
      {
        assert(inputterm.Degree() == 2);

        const ASTNode& a0 = inputterm[0];
        const ASTNode& a1 = inputterm[1];

        if (a0 == a1)
          output = _bm->CreateZeroConst(inputValueWidth);
        else
          {
            //covert x-y into x+(-y) and simplify. this transformation
            //triggers more simplifications
            //
            output = nf->CreateTerm(BVPLUS, inputValueWidth, a0, nf->CreateTerm(BVUMINUS, inputValueWidth, a1));
          }
        break;
      }
    case BVUMINUS:
      {
        //important to treat BVUMINUS as a special case, because it
        //helps in arithmetic transformations. e.g.  x + BVUMINUS(x) is
        //actually 0. One way to reveal this fact is to strip bvuminus
        //out, and replace with something else so that combineliketerms
        //can catch this fact.

        const ASTNode& a0 = inputterm[0];
        const Kind k1 = a0.GetKind();
        const ASTNode one = _bm->CreateOneConst(inputValueWidth);
        assert(k1 != BVCONST);
        switch (k1)
          {
        case BVUMINUS:
          output = a0[0];
          break;
        case BVNEG:
          {
            output = nf->CreateTerm(BVPLUS, inputValueWidth, a0[0], one);
            break;
          }
        case BVMULT:
          {
            if (BVUMINUS == a0[0].GetKind())
              {
                output = nf->CreateTerm(BVMULT, inputValueWidth, a0[0][0], a0[1]);
              }
            else if (BVUMINUS == a0[1].GetKind())
              {
                output = nf->CreateTerm(BVMULT, inputValueWidth, a0[0], a0[1][0]);
              }
            else
              {
                // If the first argument to the multiply is a
                // constant, push it through.  Without regard for
                // the splitting of nodes (hmm.)  This is
                // necessary because the bitvector solver can
                // process -3*x, but not -(3*x).
                if (BVCONST == a0[0].GetKind())
                  {
                    ASTNode a00 = SimplifyTerm(nf->CreateTerm(BVUMINUS, inputValueWidth, a0[0]), VarConstMap);
                    output = nf->CreateTerm(BVMULT, inputValueWidth, a00, a0[1]);
                  }
                else
                  output = inputterm;
              }
            break;
          }
        case BVPLUS:
          {
            //push BVUMINUS over all the monomials of BVPLUS. Simplify
            //along the way
            //
            //BVUMINUS(a1x1 + a2x2 + ...) <=> BVPLUS(BVUMINUS(a1x1) +
            //BVUMINUS(a2x2) + ...
            const ASTVec& c = a0.GetChildren();
            ASTVec o;
            for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it != itend; it++)
              {
                //Simplify(BVUMINUS(a1x1))
                ASTNode aaa = SimplifyTerm(nf->CreateTerm(BVUMINUS, inputValueWidth, *it), VarConstMap);
                o.push_back(aaa);
              }

            output = nf->CreateTerm(BVPLUS, inputValueWidth, o);
            break;
          }
        case BVSUB:
          {
            //BVUMINUS(BVSUB(x,y)) <=> BVSUB(y,x)
            output = nf->CreateTerm(BVSUB, inputValueWidth, a0[1], a0[0]);
            break;
          }
        case BVAND:
          if (a0.Degree() == 2 && (a0[1].GetKind() == BVUMINUS) && a0[1][0] == a0[0])
            {
              output = nf->CreateTerm(BVOR, inputValueWidth, a0[0], a0[1]);
            }
          break;
        case BVOR:
          if (a0.Degree() == 2 && (a0[1].GetKind() == BVUMINUS) && a0[1][0] == a0[0])
            {
              output = nf->CreateTerm(BVAND, inputValueWidth, a0[0], a0[1]);
            }
          break;
        case BVLEFTSHIFT:
          if (a0[0].GetKind() == BVCONST)
            output = nf->CreateTerm(BVLEFTSHIFT, inputValueWidth, nf->CreateTerm(BVUMINUS, inputValueWidth, a0[0]),
                a0[1]);
          break;
        case ITE:
          {
            //BVUMINUS(ITE(c,t1,t2)) <==> ITE(c,BVUMINUS(t1),BVUMINUS(t2))
            ASTNode c = a0[0];
            ASTNode t1 = SimplifyTerm(nf->CreateTerm(BVUMINUS, inputValueWidth, a0[1]), VarConstMap);
            ASTNode t2 = SimplifyTerm(nf->CreateTerm(BVUMINUS, inputValueWidth, a0[2]), VarConstMap);
            output = CreateSimplifiedTermITE(c, t1, t2);
            break;
          }
        default:
          {
            output = inputterm;
            break;
          }
          }
        break;
      }
    case BVEXTRACT:
      {
        //it is important to take care of wordlevel transformation in
        //BVEXTRACT. it exposes oppurtunities for later simplification
        //and solving (variable elimination)
        const ASTNode& a0 = inputterm[0];

        const Kind k1 = a0.GetKind();

        //indices for BVEXTRACT
        ASTNode i = inputterm[1];
        ASTNode j = inputterm[2];
        const ASTNode zero = _bm->CreateZeroConst(32);

        //recall that the indices of BVEXTRACT are always 32 bits
        //long. therefore doing a GetBVUnsigned is ok.
        unsigned int i_val = i.GetUnsignedConst();
        unsigned int j_val = j.GetUnsignedConst();

        // a0[i:0] and len(a0)=i+1, then return a0
        if (inputValueWidth == a0.GetValueWidth())
          {
            assert(0 == j_val);
            output = a0;
            break;
          }

        assert(k1 != BVCONST);

        switch (k1)
          {
        case BVEXTRACT:
          {
            const unsigned innerLow = a0[2].GetUnsignedConst();
            const unsigned innerHigh = a0[1].GetUnsignedConst();

            output = nf->CreateTerm(BVEXTRACT, inputValueWidth, a0[0], _bm->CreateBVConst(32, i_val + innerLow),
                _bm->CreateBVConst(32, j_val + innerLow));
            assert(BVTypeCheck(output));
            break;
          }

        case BVCONCAT:
          {
            //assumes concatenation is binary
            //
            //input is of the form a0[i:j]
            //
            //a0 is the conatentation t@u, and a0[0] is t, and a0[1] is u
            ASTNode t = a0[0];
            ASTNode u = a0[1];
            const unsigned int len_a0 = a0.GetValueWidth();
            const unsigned int len_u = u.GetValueWidth();

            if (len_u > i_val)
              {
                //Apply the following rule:
                // (t@u)[i:j] <==> u[i:j], if len(u) > i
                //
                output = nf->CreateTerm(BVEXTRACT, inputValueWidth, u, i, j);
              }
            else if (len_a0 > i_val && j_val >= len_u)
              {
                //Apply the rule: (t@u)[i:j] <==>
                // t[i-len_u:j-len_u], if len(t@u) > i >= j >=
                // len(u)
                i = _bm->CreateBVConst(32, i_val - len_u);
                j = _bm->CreateBVConst(32, j_val - len_u);
                output = nf->CreateTerm(BVEXTRACT, inputValueWidth, t, i, j);
              }
            else
              {
                //Apply the rule:
                // (t@u)[i:j] <==> t[i-len_u:0] @ u[len_u-1:j]
                i = _bm->CreateBVConst(32, i_val - len_u);
                ASTNode m = _bm->CreateBVConst(32, len_u - 1);
                t = SimplifyTerm(nf->CreateTerm(BVEXTRACT, i_val - len_u + 1, t, i, zero), VarConstMap);
                u = SimplifyTerm(nf->CreateTerm(BVEXTRACT, len_u - j_val, u, m, j), VarConstMap);
                output = nf->CreateTerm(BVCONCAT, inputValueWidth, t, u);
              }
            break;
          }
        case BVPLUS:
        case BVMULT:
          {
            // (BVMULT(n,t,u))[i:j] <==> BVMULT(i+1,t[i:0],u[i:0])[i:j]
            //similar rule for BVPLUS
            ASTVec c = a0.GetChildren();
            ASTVec o;
            for (ASTVec::iterator jt = c.begin(), jtend = c.end(); jt != jtend; jt++)
              {
                ASTNode aaa = *jt;
                aaa = SimplifyTerm(nf->CreateTerm(BVEXTRACT, i_val + 1, aaa, i, zero), VarConstMap);
                o.push_back(aaa);
              }
            output = nf->CreateTerm(a0.GetKind(), i_val + 1, o);
            if (j_val != 0)
              {
                //add extraction only if j is not zero
                output = nf->CreateTerm(BVEXTRACT, inputValueWidth, output, i, j);
              }
            break;
          }

          // This can increase the number of nodes exponentially.
          // If turned on bitrev2048 will blow out main memory, with
          // this disabled it takes 12MB.
#if 0

          case BVAND:
          case BVOR:
          case BVXOR:
            {
              assert(a0.Degree() == 2);

              //assumes these operators are binary
              //
              // (t op u)[i:j] <==> t[i:j] op u[i:j]
              ASTNode t = a0[0];
              ASTNode u = a0[1];
              t =
              SimplifyTerm(nf->CreateTerm(BVEXTRACT,
                      a_len, t, i, j),
                  VarConstMap);
              u =
              SimplifyTerm(nf->CreateTerm(BVEXTRACT,
                      a_len, u, i, j),
                  VarConstMap);
              BVTypeCheck(t);
              BVTypeCheck(u);
              //output = nf->CreateTerm(k1, a_len, t, u);

              output = inputterm;
              break;
            }
#endif
        case BVNEG:
          {
            // (~t)[i:j] <==> ~(t[i:j])
            ASTNode t = a0[0];
            t = SimplifyTerm(nf->CreateTerm(BVEXTRACT, inputValueWidth, t, i, j), VarConstMap);
            output = nf->CreateTerm(BVNEG, inputValueWidth, t);
            break;
          }
          // case BVSX:{ //(BVSX(t,n)[i:j] <==> BVSX(t,i+1), if n
          //        >= i+1 and j=0 ASTNode t = a0[0]; unsigned int
          //        bvsx_len = a0.GetValueWidth(); if(bvsx_len <
          //        a_len) { FatalError("SimplifyTerm: BVEXTRACT
          //        over BVSX:" "the length of BVSX term must be
          //        greater than extract-len",inputterm); } if(j
          //        != zero) { output =
          //        nf->CreateTerm(BVEXTRACT,a_len,a0,i,j); }
          //        else { output =
          //        nf->CreateTerm(BVSX,a_len,t,
          //                        _bm->CreateBVConst(32,a_len));
          //        } break; }

          /*
           * On deeply nested ITES, this can cause an exponential number
           * of nodes to be produced. Especially if there are different
           * extracts over the same node.
           *
           case ITE:
           {
           const ASTNode& t0 = a0[0];
           ASTNode t1 =
           SimplifyTerm(nf->CreateTerm(BVEXTRACT,
           a_len, a0[1], i, j),
           VarConstMap);
           ASTNode t2 =
           SimplifyTerm(nf->CreateTerm(BVEXTRACT,
           a_len, a0[2], i, j),
           VarConstMap);
           output = CreateSimplifiedTermITE(t0, t1, t2);
           break;
           }
           */
        default:
          {
            output = inputterm;
            break;
          }
          }
        break;
      }
    case BVNEG:
      {
        const ASTNode& a0 = inputterm[0];

        assert(a0.GetKind() != BVCONST);

        switch (a0.GetKind())
          {
        case BVNEG:
          output = a0[0];
          break;
        case ITE:
          if (a0[1].isConstant() && a0[2].isConstant())
            {
              ASTNode t = SimplifyTerm(nf->CreateTerm(BVNEG, inputValueWidth, a0[1]));
              ASTNode f = SimplifyTerm(nf->CreateTerm(BVNEG, inputValueWidth, a0[2]));
              output = nf->CreateTerm(ITE, inputValueWidth, a0[0], BVConstEvaluator(t), BVConstEvaluator(f));
              break;
            }
          //follow on
        default:
          output = inputterm;
          break;
          }
        break;
      }

    case BVSX:
      {
        //a0 is the expr which is being sign extended
        ASTNode a0 = inputterm[0];

        //a1 represents the length of the term BVSX(a0)
        const ASTNode& a1 = inputterm[1];

        if (a0.GetValueWidth() == inputValueWidth)
          {
            //nothing to signextend
            output = a0;
            break;
          }

        // If the msb is known. Then puts 0's or the 1's infront.
        if (mostSignificantConstants(a0) > 0)
          {
            if (getConstantBit(a0, 0) == 0)
              output = nf->CreateTerm(BVCONCAT, inputValueWidth,
                  _bm->CreateZeroConst(inputValueWidth - a0.GetValueWidth()), a0);
            else
              output = nf->CreateTerm(BVCONCAT, inputValueWidth,
                  _bm->CreateMaxConst(inputValueWidth - a0.GetValueWidth()), a0);
            break;
          }

        assert(a0.GetKind() != BVCONST);

        switch (a0.GetKind())
          {
        case BVNEG:
          output = nf->CreateTerm(a0.GetKind(), inputValueWidth, nf->CreateTerm(BVSX, inputValueWidth, a0[0], a1));
          break;
        case BVAND:
        case BVOR:
          {
            const ASTVec& c = a0.GetChildren();
            ASTVec newChildren;
            newChildren.reserve(c.size());
            for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it != itend; it++)
              {
                newChildren.push_back(nf->CreateTerm(BVSX, inputValueWidth, *it, a1));
              }
            output = nf->CreateTerm(a0.GetKind(), inputValueWidth, newChildren);
          }
          break;
        case BVPLUS:
          {
            //BVSX(m,BVPLUS(n,BVSX(t1),BVSX(t2))) <==>
            //BVPLUS(m,BVSX(m,t1),BVSX(m,t2))
            const ASTVec& c = a0.GetChildren();
            bool returnflag = false;
            for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it != itend; it++)
              {
                if (BVSX != it->GetKind())
                  {
                    returnflag = true;
                    break;
                  }
              }
            if (!returnflag)
              {
                ASTVec o;
                o.reserve(c.size());
                for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it != itend; it++)
                  {
                    ASTNode aaa = SimplifyTerm(nf->CreateTerm(BVSX, inputValueWidth, *it, a1), VarConstMap);
                    o.push_back(aaa);
                  }
                output = nf->CreateTerm(a0.GetKind(), inputValueWidth, o);
              }
            break;
          }
        case BVSX:
          {
            //if you have BVSX(m,BVSX(n,a)) then you can drop the inner
            //BVSX provided m is greater than n.
            a0 = a0[0];
            assert(hasBeenSimplified(a0));

            output = nf->CreateTerm(BVSX, inputValueWidth, a0, a1);
            break;
          }
        case ITE:
          {
            const ASTNode& cond = a0[0];
            ASTNode thenpart = SimplifyTerm(nf->CreateTerm(BVSX, inputValueWidth, a0[1], a1), VarConstMap);
            ASTNode elsepart = SimplifyTerm(nf->CreateTerm(BVSX, inputValueWidth, a0[2], a1), VarConstMap);
            output = CreateSimplifiedTermITE(cond, thenpart, elsepart);
            break;
          }
        default:
          output = inputterm;
          break;
          }
        break;
      }
    case BVAND:
    case BVOR:
      {
        // turn BVAND(CONCAT CONCAT) into concat(BVAND() BVAND()). i.e. push ops through concat.
        if (inputterm.Degree() == 2 && inputterm[0].GetKind() == BVCONCAT && inputterm[1].GetKind() == BVCONCAT
            && inputterm[0][0].GetValueWidth() == inputterm[1][0].GetValueWidth())
          {
            output = nf->CreateTerm(BVCONCAT, inputterm.GetValueWidth(),
                nf->CreateTerm(k, inputterm[0][0].GetValueWidth(), inputterm[0][0], inputterm[1][0]),
                nf->CreateTerm(k, inputterm[0][1].GetValueWidth(), inputterm[0][1], inputterm[1][1]));
            break;
          }

        const ASTNode max = _bm->CreateMaxConst(inputValueWidth);
        const ASTNode zero = _bm->CreateZeroConst(inputValueWidth);

        const ASTNode identity = (BVAND == k) ? max : zero;
        const ASTNode annihilator = (BVAND == k) ? zero : max;
        ASTVec c = FlattenKind(inputterm.GetKind(), inputterm.GetChildren());
        SortByArith(c);
        ASTVec constants;
        ASTVec o;
        for (ASTVec::iterator it = c.begin(), itend = c.end(); it != itend; it++)
          {
            ASTNode aaa = *it;
            assert(hasBeenSimplified(aaa));

            if (aaa == annihilator)
              {
                output = annihilator;
                //memoize
                UpdateSimplifyMap(inputterm, output, false, VarConstMap);
                UpdateSimplifyMap(actualInputterm, output, false, VarConstMap);
                //cerr << "output of SimplifyTerm: " << output << endl;
                return output;
              }

            if (o.size() > 0 && o.back() == aaa)
              {
                continue; // duplicate.
              }

            // nb: There's no guarantee that the bvneg will immediately follow
            // the thing it's negating if the degree > 2.
            if (o.size() > 0 && aaa.GetKind() == BVNEG && o.back() == aaa[0])
              {
                output = annihilator;
                UpdateSimplifyMap(inputterm, output, false, VarConstMap);
                UpdateSimplifyMap(actualInputterm, output, false, VarConstMap);
                return output;
              }

            if (BVCONST == aaa.GetKind())
              {
                constants.push_back(aaa);
              }
            else
              {
                o.push_back(aaa);
              }
          }

        while (constants.size() >= 2)
          {
            ASTNode a = constants.back();
            constants.pop_back();
            ASTNode b = constants.back();
            constants.pop_back();

            ASTNode c = BVConstEvaluator(nf->CreateTerm(inputterm.GetKind(), inputterm.GetValueWidth(), a, b));

            constants.push_back(c);

          }
        if (constants.size() != 0 && constants.back() != identity)
          o.push_back(constants.back());

        switch (o.size())
          {
        case 0:
          output = identity;
          break;
        case 1:
          output = o[0];
          break;
        default:
          SortByArith(o);
          output = nf->CreateTerm(inputterm.GetKind(), inputterm.GetValueWidth(), o);
          break;
          }

        // This don't make it faster, just makes the graphs easier to understand.
        if (output.GetKind() == BVAND)
          {
            assert(output.Degree() != 0);
            bool allconv = true;
            for (ASTVec::const_iterator it = output.begin(), itend = output.end(); it != itend; it++)
              {
                if (!isPropositionToTerm(*it))
                  {
                    allconv = false;
                    break;
                  }
              }
            if (allconv)
              {
                const ASTNode zero = _bm->CreateZeroConst(1);
                ASTVec children;
                for (ASTVec::const_iterator it = output.begin(), itend = output.end(); it != itend; it++)
                  {
                    const ASTNode& n = *it;

                    if (n[1] == zero)
                      children.push_back(nf->CreateNode(NOT, n[0]));
                    else
                      children.push_back(n[0]);
                  }
                output = nf->CreateTerm(ITE, 1, nf->CreateNode(AND, children), _bm->CreateOneConst(1), zero);
                assert(BVTypeCheck(output));
              }

            assert(BVTypeCheck(output));

            // If the leading bits are zero. Replace it by a concat with zero.
            int i;
            if (output.GetKind() == BVAND && output.Degree() == 2 && ((i = numberOfLeadingZeroes(output[0])) > 0))
              {
                // i contains the number of leading zeroes.
                if (i < output.GetValueWidth())
                  output = nf->CreateTerm(
                      BVCONCAT,
                      output.GetValueWidth(),
                      _bm->CreateZeroConst(i),
                      nf->CreateTerm(
                          BVAND,
                          output.GetValueWidth() - i,
                          nf->CreateTerm(BVEXTRACT, output.GetValueWidth() - i, output[0],
                              _bm->CreateBVConst(32, output.GetValueWidth() - i - 1), _bm->CreateBVConst(32, 0)),
                          nf->CreateTerm(BVEXTRACT, output.GetValueWidth() - i, output[1],
                              _bm->CreateBVConst(32, output.GetValueWidth() - i - 1), _bm->CreateBVConst(32, 0))));

                assert(BVTypeCheck(output));
              }
          }
        if (output.GetKind() == BVAND)
          {
            int trailingZeroes = 0;
            for (int i = 0; i < output.Degree(); i++)
              {
                const ASTNode& n = output[i];
                if (n.GetKind() != BVCONST)
                  continue;
                int j;
                for (j = 0; j < n.GetValueWidth(); j++)
                  if (CONSTANTBV::BitVector_bit_test(n.GetBVConst(), j))
                    break;

                if (j > trailingZeroes)
                  trailingZeroes = j;
              }
            if (trailingZeroes > 0)
              {
                if (trailingZeroes == output.GetValueWidth())
                  output = _bm->CreateZeroConst(trailingZeroes);
                else
                  {
                    //cerr << "old" << output;
                    ASTNode zeroes = _bm->CreateZeroConst(trailingZeroes);
                    ASTVec newChildren;
                    for (int i = 0; i < output.Degree(); i++)
                      newChildren.push_back(
                          nf->CreateTerm(BVEXTRACT, output.GetValueWidth() - trailingZeroes, output[i],
                              _bm->CreateBVConst(32, output.GetValueWidth() - 1),
                              _bm->CreateBVConst(32, trailingZeroes)));

                    ASTNode newAnd = nf->CreateTerm(BVAND, output.GetValueWidth() - trailingZeroes, newChildren);
                    output = nf->CreateTerm(BVCONCAT, output.GetValueWidth(), newAnd, zeroes);
                    assert(BVTypeCheck(output));
                    //cerr << "new" << output;
                  }
              }

          }

        break;
      }
    case BVCONCAT:
      {
        const ASTNode& t = inputterm[0];
        const ASTNode& u = inputterm[1];

        const Kind tkind = t.GetKind();
        const Kind ukind = u.GetKind();

        assert(BVCONST != tkind || BVCONST != ukind);

        if (BVEXTRACT == tkind && BVEXTRACT == ukind && t[0] == u[0])
          {
            //to handle the case x[m:n]@x[n-1:k] <==> x[m:k]
            const ASTNode& t_hi = t[1];
            const ASTNode& t_low = t[2];
            const ASTNode& u_hi = u[1];
            const ASTNode& u_low = u[2];
            ASTNode c = BVConstEvaluator(nf->CreateTerm(BVPLUS, 32, u_hi, _bm->CreateOneConst(32)));
            if (t_low == c)
              {
                output = nf->CreateTerm(BVEXTRACT, inputValueWidth, t[0], t_hi, u_low);
              }
            else
              {
                output = nf->CreateTerm(BVCONCAT, inputValueWidth, t, u);
              }
          }
        else if (t.GetKind() == BVCONCAT && t[0].GetKind() != BVCONCAT)
          {

            /// This makes the left hand child of every concat not a concat.
            const ASTNode& left = t[0];
            ASTNode bottom = nf->CreateTerm(BVCONCAT, t[1].GetValueWidth() + u.GetValueWidth(), t[1], u);
            output = nf->CreateTerm(BVCONCAT, inputValueWidth, left, bottom);
            assert(BVTypeCheck(output));
          }
        else
          {
            output = nf->CreateTerm(BVCONCAT, inputValueWidth, t, u);
          }
        break;
      }

    case BVLEFTSHIFT:
    case BVRIGHTSHIFT:

      { // If the shift amount is known. Then replace it by an extract.
        const ASTNode a = inputterm[0];
        const ASTNode b = inputterm[1];

        const unsigned int width = a.GetValueWidth();
        if (BVCONST == b.GetKind()) // known shift amount.
          {
            output = convertKnownShiftAmount(k, inputterm.GetChildren(), *_bm, nf);
          }
        else if (a == _bm->CreateZeroConst(width))
          {
            output = _bm->CreateZeroConst(width);
          }
        else
          output = inputterm;
      }
      break;

    case BVDIV:
      {
        if (inputterm[0] == inputterm[1])
          {
            output = _bm->CreateOneConst(inputValueWidth);
            break;
          }
        if (inputterm[1] == _bm->CreateOneConst(inputValueWidth))
          {
            output = inputterm[0];
            break;
          }
        unsigned int nlz=  numberOfLeadingZeroes(inputterm[0]);
        if (nlz > 0)
          {
            nlz = std::min(inputValueWidth-1,nlz);
            int rest = inputValueWidth-nlz;
            ASTNode low = _bm->CreateBVConst(32,rest);
            ASTNode high =_bm->CreateBVConst(32,inputValueWidth-1);

            ASTNode cond = nf->CreateNode(EQ,_bm->CreateZeroConst(nlz),
                           nf->CreateTerm(BVEXTRACT, nlz, inputterm[1], high,low));

            ASTNode top = nf->CreateTerm(BVEXTRACT, rest, inputterm[0], _bm->CreateBVConst(32,rest-1),_bm->CreateZeroConst(32));
            ASTNode bottom = nf->CreateTerm(BVEXTRACT, rest, inputterm[1], _bm->CreateBVConst(32,rest-1),_bm->CreateZeroConst(32));

            ASTNode div = nf->CreateTerm(BVDIV,rest,top,bottom);
            div = nf->CreateTerm(BVCONCAT,inputValueWidth,_bm->CreateZeroConst(inputValueWidth-rest),div);

            output = nf->CreateTerm(ITE, inputValueWidth, cond, div, _bm->CreateZeroConst(inputValueWidth));
            break;
          }

        ASTNode lessThan = SimplifyFormula(nf->CreateNode(BVLT, inputterm[0], inputterm[1]), false, NULL);
        if (lessThan == ASTTrue)
          output = _bm->CreateZeroConst(inputValueWidth);
        else
          output = inputterm;
      }
      break;
    case BVMOD:
      {
        if (inputterm[0] == inputterm[1])
          {
            output = _bm->CreateZeroConst(inputValueWidth);
            break;
          }
        if (inputterm[1] == _bm->CreateOneConst(inputValueWidth))
          {
            output = _bm->CreateZeroConst(inputValueWidth);
            break;
          }

        unsigned int nlz=  numberOfLeadingZeroes(inputterm[0]);
       if (nlz > 0)
         {
           nlz = std::min(inputValueWidth-1,nlz);
           int rest = inputValueWidth-nlz;
           ASTNode low = _bm->CreateBVConst(32,rest);
           ASTNode high =_bm->CreateBVConst(32,inputValueWidth-1);

           ASTNode cond = nf->CreateNode(EQ,_bm->CreateZeroConst(nlz),
                          nf->CreateTerm(BVEXTRACT, nlz, inputterm[1], high,low));

           ASTNode top = nf->CreateTerm(BVEXTRACT, rest, inputterm[0], _bm->CreateBVConst(32,rest-1),_bm->CreateZeroConst(32));
           ASTNode bottom = nf->CreateTerm(BVEXTRACT, rest, inputterm[1], _bm->CreateBVConst(32,rest-1),_bm->CreateZeroConst(32));

           // nb. This differs from the bvdiv case.
           ASTNode div = nf->CreateTerm(BVMOD,rest,top,bottom);
           div = nf->CreateTerm(BVCONCAT,inputValueWidth,_bm->CreateZeroConst(inputValueWidth-rest),div);

           // nb. This differs from the bvdiv case.
           output = nf->CreateTerm(ITE, inputValueWidth, cond, div, inputterm[0]);
           break;
         }

        ASTNode lessThan = SimplifyFormula(nf->CreateNode(BVLT, inputterm[0], inputterm[1]), false, NULL);

        if (lessThan == ASTTrue)
          output = inputterm[0];
        else
          output = inputterm;
      }
      break;

    case BVXOR:
      {
        if (inputterm.Degree() == 2 && inputterm[0] == inputterm[1])
          {
            output = _bm->CreateZeroConst(inputterm.GetValueWidth());
            break;
          }
        if (inputterm.Degree() == 2 && inputterm[0].GetKind() == BVCONCAT && inputterm[1].GetKind() == BVCONCAT
            && inputterm[0][0].GetValueWidth() == inputterm[1][0].GetValueWidth())
          {
            output = nf->CreateTerm(BVCONCAT, inputterm.GetValueWidth(),
                nf->CreateTerm(k, inputterm[0][0].GetValueWidth(), inputterm[0][0], inputterm[1][0]),
                nf->CreateTerm(k, inputterm[0][1].GetValueWidth(), inputterm[0][1], inputterm[1][1]));
            break;
          }
        if (inputterm.Degree() == 2 && inputterm[0] == _bm->CreateZeroConst(inputterm.GetValueWidth()))
          {
            output = inputterm[1];
            break;
          }
      }

      output = inputterm;
      break;
    case BVXNOR:
    case BVNAND:
    case BVNOR:
    case BVVARSHIFT:
    case BVSRSHIFT:
      {
        output = inputterm;
        break;
      }
    case READ:
      {
        ASTNode out1;

        ASTNode array_term = SimplifyArrayTerm(inputterm[0], VarConstMap);
        ASTNode read_index = SimplifyTerm(inputterm[1], VarConstMap);

        if (SYMBOL == array_term.GetKind())
          {
            out1 = nf->CreateTerm(READ, inputterm.GetValueWidth(), array_term, read_index);
          }
        else if (WRITE == array_term.GetKind())
          {
            ASTNode eq = CreateSimplifiedEQ(read_index, array_term[1]);
            if (eq == ASTTrue)
              out1 = array_term[2];
            else if (eq == ASTFalse)
              {
                out1 = nf->CreateTerm(READ, inputterm.GetValueWidth(), array_term[0], read_index);
                out1 = SimplifyTerm(out1, VarConstMap);
              }
            else
              {
                out1 = nf->CreateTerm(READ, inputterm.GetValueWidth(), array_term, read_index);
              }
          }
        else if (ITE == array_term.GetKind())
          {
            // Pushes the READ through ITES, which is potentially exponential.
            // At present, because there's no write refinement or similar, the
            // array transformer is going to do this later anyway. So, we do it
            // here. But it's ugggglly.

            ASTNode cond = SimplifyFormula(inputterm[0][0], false, VarConstMap);
            ASTNode read1 = nf->CreateTerm(READ, inputValueWidth, inputterm[0][1], read_index);
            ASTNode read2 = nf->CreateTerm(READ, inputValueWidth, inputterm[0][2], read_index);
            read1 = SimplifyTerm(read1, VarConstMap);
            read2 = SimplifyTerm(read2, VarConstMap);
            out1 = CreateSimplifiedTermITE(cond, read1, read2);
          }
        else
          {
            FatalError("ffff");
          }

        assert(!out1.IsNull());

        //process only if not  in the substitution map. simplifymap
        //has been checked already
#if 0
        if (!CheckSubstitutionMap(out1, out1) && out1.GetKind() == READ && WRITE == out1[0].GetKind())
          out1 = RemoveWrites_TopLevel(out1);
#endif

        //it is possible that after all the procesing the READ term
        //reduces to READ(Symbol,const) and hence we should check the
        //substitutionmap once again.
        if (!CheckSubstitutionMap(out1, output))
          output = out1;
        break;
      }
    case ITE:
      {
        output = CreateSimplifiedTermITE(inputterm[0], inputterm[1], inputterm[2]);
        break;
      }
    case SBVREM:
    case SBVMOD:
      {
        if (inputterm[0] == inputterm[1])
          {
            output = _bm->CreateZeroConst(inputValueWidth);
            break;
          }

        output = inputterm;
        break;
      }
    case SBVDIV:
      {
        output = inputterm;
        if (inputterm[0] == inputterm[1])
          {
            output = _bm->CreateOneConst(inputValueWidth);
            break;
          }
        if (SBVDIV == output.GetKind() && output.GetChildren().size() == 2 && output.GetChildren()[0].GetKind() == BVSX
            && output.GetChildren()[1].GetKind() == BVSX)
          output = pullUpBVSX(output);

        break;
      }
    case WRITE:
    default:
      FatalError("SimplifyTerm: Control should never reach here:", inputterm, k);
      return inputterm;
      break;
      }assert(!output.IsNull());

    if (inputterm != output)
      output = SimplifyTerm(output);
    //memoize
    UpdateSimplifyMap(inputterm, output, false, VarConstMap);
    UpdateSimplifyMap(actualInputterm, output, false, VarConstMap);

    //cerr << "SimplifyTerm: output" << output << endl;

    assert(!output.IsNull());
    assert(inputterm.GetValueWidth() == output.GetValueWidth());
    assert(inputterm.GetIndexWidth() == output.GetIndexWidth());
    assert(hasBeenSimplified(output));

#ifndef NDEBUG
    for (int i = 0; i < output.Degree(); i++)
      {
        if (output[i].GetType() != ARRAY_TYPE)
          if (!hasBeenSimplified(output[i]))
            {
              cout << output;
              cout << i;
              assert(hasBeenSimplified(output[i]));
            }
      }
#endif

    return output;
  } //end of SimplifyTerm()

  //this function assumes that the input is a vector of childnodes of
  //a BVPLUS term. it combines like terms and returns a bvplus
  //term. e.g. 1.x + 2.x is converted to 3.x
  ASTNode
  Simplifier::CombineLikeTerms(const ASTNode& a)
  {
    if (BVPLUS != a.GetKind())
      return a;

    ASTNode output;
    if (CheckSimplifyMap(a, output, false))
      {
        //check memo table
        //cerr << "output of SimplifyTerm Cache: " << output << endl;
        return output;
      }

    return CombineLikeTerms(a.GetChildren());
  }

  ASTNode
  Simplifier::CombineLikeTerms(const ASTVec& c)
  {
    ASTNode output;
    //map from variables to vector of constants
    ASTNodeToVecMap vars_to_consts;
    //vector to hold constants
    ASTVec constkids;
    ASTVec outputvec;

    //useful constants
    unsigned int len = c[0].GetValueWidth();
    ASTNode one = _bm->CreateOneConst(len);
    ASTNode zero = _bm->CreateZeroConst(len);
    ASTNode max = _bm->CreateMaxConst(len);

    //go over the childnodes of the input bvplus, and collect like
    //terms in a map. the key of the map are the variables, and the
    //values are stored in a ASTVec
    for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it != itend; it++)
      {
        const ASTNode& aaa = *it;
        if (SYMBOL == aaa.GetKind())
          {
            vars_to_consts[aaa].push_back(one);
          }
        else if (BVMULT == aaa.GetKind() && BVUMINUS == aaa[0].GetKind() && BVCONST == aaa[0][0].GetKind())
          {
            //(BVUMINUS(c))*(y) <==> compute(BVUMINUS(c))*y
            ASTNode compute_const = BVConstEvaluator(aaa[0]);
            vars_to_consts[aaa[1]].push_back(compute_const);
          }
        else if (BVMULT == aaa.GetKind() && BVUMINUS == aaa[1].GetKind() && BVCONST == aaa[0].GetKind())
          {
            //c*(BVUMINUS(y)) <==> compute(BVUMINUS(c))*y
            ASTNode cccc = BVConstEvaluator(nf->CreateTerm(BVUMINUS, len, aaa[0]));
            vars_to_consts[aaa[1][0]].push_back(cccc);
          }
        else if (BVMULT == aaa.GetKind() && BVCONST == aaa[0].GetKind())
          {
            //assumes that BVMULT is binary
            vars_to_consts[aaa[1]].push_back(aaa[0]);
          }
        else if (BVMULT == aaa.GetKind() && BVUMINUS == aaa[0].GetKind())
          {
            //(-1*x)*(y) <==> -1*(xy)
            ASTNode cccc = nf->CreateTerm(BVMULT, len, aaa[0][0], aaa[1]);
            ASTVec cNodes = cccc.GetChildren();
            SortByArith(cNodes);
            vars_to_consts[cccc].push_back(max);
          }
        else if (BVMULT == aaa.GetKind() && BVUMINUS == aaa[1].GetKind())
          {
            //x*(-1*y) <==> -1*(xy)
            ASTNode cccc = nf->CreateTerm(BVMULT, len, aaa[0], aaa[1][0]);
            ASTVec cNodes = cccc.GetChildren();
            SortByArith(cNodes);
            vars_to_consts[cccc].push_back(max);
          }
        else if (BVCONST == aaa.GetKind())
          {
            constkids.push_back(aaa);
          }
        else if (BVUMINUS == aaa.GetKind())
          {
            //helps to convert BVUMINUS into a BVMULT. here the max
            //constant represents -1. this transformation allows us to
            //conclude that x + BVUMINUS(x) is 0.
            vars_to_consts[aaa[0]].push_back(max);
          }
        else
          vars_to_consts[aaa].push_back(one);
      } //end of for loop

    //go over the map from variables to vector of values. combine the
    //vector of values, multiply to the variable, and put the
    //resultant monomial in the output BVPLUS.
    for (ASTNodeToVecMap::iterator it = vars_to_consts.begin(), itend = vars_to_consts.end(); it != itend; it++)
      {
        const ASTVec& ccc = it->second;

        ASTNode constant;
        if (1 < ccc.size())
          {
            constant = nf->CreateTerm(BVPLUS, ccc[0].GetValueWidth(), ccc);
            constant = BVConstEvaluator(constant);
          }
        else
          constant = ccc[0];

        //constant * var
        ASTNode monom;
        if (zero == constant)
          monom = zero;
        else if (one == constant)
          monom = it->first;
        else
          {
            monom = SimplifyTerm(nf->CreateTerm(BVMULT, constant.GetValueWidth(), constant, it->first));
          }
        if (zero != monom)
          {
            outputvec.push_back(monom);
          }
      } //end of for loop

    if (constkids.size() > 1)
      {
        ASTNode output = NonMemberBVConstEvaluator(_bm, BVPLUS, constkids, constkids[0].GetValueWidth());
        if (output != zero)
          outputvec.push_back(output);
      }
    else if (constkids.size() == 1)
      {
        if (constkids[0] != zero)
          outputvec.push_back(constkids[0]);
      }

    if (outputvec.size() > 1)
      {
        output = nf->CreateTerm(BVPLUS, len, outputvec);
      }
    else if (outputvec.size() == 1)
      {
        output = outputvec[0];
      }
    else
      {
        output = zero;
      }

    //memoize
    //UpdateSimplifyMap(a,output,false);
    return output;
  } //end of CombineLikeTerms()

  //accepts lhs and rhs, and returns lhs - rhs = 0. The function
  //assumes that lhs and rhs have already been simplified. although
  //this assumption is not needed for correctness, it is essential for
  //performance. The function also assumes that lhs is a BVPLUS
  ASTNode
  Simplifier::LhsMinusRhs(const ASTNode& eq)
  {
    //if input is not an equality, simply return it
    if (EQ != eq.GetKind())
      return eq;

    ASTNode lhs = eq[0];
    ASTNode rhs = eq[1];
    const Kind k_lhs = lhs.GetKind();
    const Kind k_rhs = rhs.GetKind();
    //either the lhs has to be a BVPLUS or the rhs has to be a
    //BVPLUS
    if (!(BVPLUS == k_lhs || BVPLUS == k_rhs || (BVMULT == k_lhs && BVMULT == k_rhs)))
      {
        return eq;
      }

    ASTNode output;
    if (CheckSimplifyMap(eq, output, false))
      {
        //check memo table
        //cerr << "output of SimplifyTerm Cache: " << output << endl;
        return output;
      }

    //if the lhs is not a BVPLUS, but the rhs is a BVPLUS, then swap
    //the lhs and rhs
    //bool swap_flag = false;
    if (BVPLUS != k_lhs && BVPLUS == k_rhs)
      {
        ASTNode swap = lhs;
        lhs = rhs;
        rhs = swap;
        // swap_flag = true;
      }

    unsigned int len = lhs.GetValueWidth();
    ASTNode zero = _bm->CreateZeroConst(len);
    //right is -1*(rhs): Simplify(-1*rhs)
    rhs = SimplifyTerm(nf->CreateTerm(BVUMINUS, len, rhs));

    ASTVec lvec = lhs.GetChildren();
    ASTVec rvec = rhs.GetChildren();
    ASTNode lhsplusrhs;
    if (BVPLUS != lhs.GetKind() && BVPLUS != rhs.GetKind())
      {
        lhsplusrhs = nf->CreateTerm(BVPLUS, len, lhs, rhs);
      }
    else if (BVPLUS == lhs.GetKind() && BVPLUS == rhs.GetKind())
      {
        //combine the childnodes of the left and the right
        lvec.insert(lvec.end(), rvec.begin(), rvec.end());
        lhsplusrhs = nf->CreateTerm(BVPLUS, len, lvec);
      }
    else if (BVPLUS == lhs.GetKind() && BVPLUS != rhs.GetKind())
      {
        lvec.push_back(rhs);
        lhsplusrhs = nf->CreateTerm(BVPLUS, len, lvec);
      }
    else
      {
        lhsplusrhs = nf->CreateTerm(BVPLUS, len, lhs, rhs);
      }

    //combine like terms
    output = CombineLikeTerms(lhsplusrhs);
    output = SimplifyTerm(output);
    //
    //Now make output into: lhs-rhs = 0
    output = CreateSimplifiedEQ(output, zero);
    //sort if BVPLUS
    if (BVPLUS == output.GetKind())
      {
        ASTVec outv = output.GetChildren();
        SortByArith(outv);
        output = nf->CreateTerm(BVPLUS, len, outv);
      }

    //memoize
    //UpdateSimplifyMap(eq,output,false);
    return output;
  } //end of LhsMinusRHS()

  //THis function accepts a BVMULT(t1,t2) and distributes the mult
  //over plus if either or both t1 and t2 are BVPLUSes.
  //
  // x*(y1 + y2 + ...+ yn) <==> x*y1 + x*y2 + ... + x*yn
  //
  // (y1 + y2 + ...+ yn)*x <==> x*y1 + x*y2 + ... + x*yn
  //
  // The function assumes that the BVPLUSes have been flattened
  ASTNode
  Simplifier::DistributeMultOverPlus(const ASTNode& a, bool startdistribution)
  {
    if (!startdistribution)
      return a;
    Kind k = a.GetKind();
    if (BVMULT != k)
      return a;

    assert(a.Degree() == 2);

    ASTNode left = a[0];
    ASTNode right = a[1];
    Kind left_kind = left.GetKind();
    Kind right_kind = right.GetKind();

    ASTNode output;
    if (CheckSimplifyMap(a, output, false))
      {
        //check memo table
        //cerr << "output of SimplifyTerm Cache: " << output << endl;
        return output;
      }

    //special case optimization: c1*(c2*t1) <==> (c1*c2)*t1
    if (BVCONST == left_kind && BVMULT == right_kind && BVCONST == right[0].GetKind())
      {
        ASTNode c = BVConstEvaluator(nf->CreateTerm(BVMULT, a.GetValueWidth(), left, right[0]));
        c = nf->CreateTerm(BVMULT, a.GetValueWidth(), c, right[1]);
        return c;
        left = c[0];
        right = c[1];
        left_kind = left.GetKind();
        right_kind = right.GetKind();
      }

    //special case optimization: c1*(t1*c2) <==> (c1*c2)*t1
    if (BVCONST == left_kind && BVMULT == right_kind && BVCONST == right[1].GetKind())
      {
        ASTNode c = BVConstEvaluator(nf->CreateTerm(BVMULT, a.GetValueWidth(), left, right[1]));
        c = nf->CreateTerm(BVMULT, a.GetValueWidth(), c, right[0]);
        return c;
        left = c[0];
        right = c[1];
        left_kind = left.GetKind();
        right_kind = right.GetKind();
      }

    //atleast one of left or right have to be BVPLUS
    if (!(BVPLUS == left_kind || BVPLUS == right_kind))
      {
        return a;
      }

    //if left is BVPLUS and right is not, then swap left and right. we
    //can do this since BVMULT is communtative
    ASTNode swap;
    if (BVPLUS == left_kind && BVPLUS != right_kind)
      {
        swap = left;
        left = right;
        right = swap;
      }
    left_kind = left.GetKind();
    right_kind = right.GetKind();

    //by this point we are gauranteed that right is a BVPLUS, but left
    //may not be
    ASTVec rightnodes = right.GetChildren();
    ASTVec outputvec;
    unsigned len = a.GetValueWidth();
    ASTNode zero = _bm->CreateZeroConst(len);
    ASTNode one = _bm->CreateOneConst(len);
    if (BVPLUS != left_kind)
      {
        //if the multiplier is not a BVPLUS then we have a special case
        // x*(y1 + y2 + ...+ yn) <==> x*y1 + x*y2 + ... + x*yn
        if (zero == left)
          {
            outputvec.push_back(zero);
          }
        else if (one == left)
          {
            outputvec.push_back(left);
          }
        else
          {
            for (ASTVec::iterator j = rightnodes.begin(), jend = rightnodes.end(); j != jend; j++)
              {
                ASTNode out = SimplifyTerm(nf->CreateTerm(BVMULT, len, left, *j));
                outputvec.push_back(out);
              }
          }
      }
    else
      {
        ASTVec leftnodes = left.GetChildren();
        // (x1 + x2 + ... + xm)*(y1 + y2 + ...+ yn) <==> x1*y1 + x1*y2 +
        // ... + x2*y1 + ... + xm*yn
        for (ASTVec::iterator i = leftnodes.begin(), iend = leftnodes.end(); i != iend; i++)
          {
            ASTNode multiplier = *i;
            for (ASTVec::iterator j = rightnodes.begin(), jend = rightnodes.end(); j != jend; j++)
              {
                ASTNode out = SimplifyTerm(nf->CreateTerm(BVMULT, len, multiplier, *j));
                outputvec.push_back(out);
              }
          }
      }

    //compute output here
    if (outputvec.size() > 1)
      {
        output = CombineLikeTerms(nf->CreateTerm(BVPLUS, len, outputvec));
        output = SimplifyTerm(output);
      }
    else
      output = SimplifyTerm(outputvec[0]);

    //memoize
    //UpdateSimplifyMap(a,output,false);
    return output;
  } //end of distributemultoverplus()

#if 0
  //converts the BVSX(len, a0) operator into ITE( check top bit,
  //extend a0 by 1, extend a0 by 0)
  ASTNode
  Simplifier::ConvertBVSXToITE(const ASTNode& a)
  {
    if (BVSX != a.GetKind())
      return a;

    ASTNode output;
    if (CheckSimplifyMap(a, output, false))
      {
        //check memo table
        //cerr << "output of ConvertBVSXToITE Cache: " << output << endl;
        return output;
      }

    ASTNode a0 = a[0];
    unsigned a_len = a.GetValueWidth();
    unsigned a0_len = a0.GetValueWidth();

    if (a0_len > a_len)
      {
        FatalError("Trying to sign_extend a larger BV into a smaller BV");
        return ASTUndefined;
      }

    //sign extend
    unsigned extensionlen = a_len - a0_len;
    if (0 == extensionlen)
      {
        UpdateSimplifyMap(a, output, false);
        return a;
      }

    std::string ones;
    for (unsigned c = 0; c < extensionlen; c++)
      ones += '1';
    std::string zeros;
    for (unsigned c = 0; c < extensionlen; c++)
      zeros += '0';

    //string of oness of length extensionlen
    BEEV::ASTNode BVOnes = _bm->CreateBVConst(ones.c_str(), 2);
    //string of zeros of length extensionlen
    BEEV::ASTNode BVZeros = _bm->CreateBVConst(zeros.c_str(), 2);

    //string of ones BVCONCAT a0
    BEEV::ASTNode concatOnes = nf->CreateTerm(BEEV::BVCONCAT, a_len, BVOnes, a0);
    //string of zeros BVCONCAT a0
    BEEV::ASTNode concatZeros = nf->CreateTerm(BEEV::BVCONCAT, a_len, BVZeros, a0);

    //extract top bit of a0
    BEEV::ASTNode hi = _bm->CreateBVConst(32, a0_len - 1);
    BEEV::ASTNode low = _bm->CreateBVConst(32, a0_len - 1);
    BEEV::ASTNode topBit = nf->CreateTerm(BEEV::BVEXTRACT, 1, a0, hi, low);

    //compare topBit of a0 with 0bin1
    BEEV::ASTNode condition = CreateSimplifiedEQ(_bm->CreateBVConst(1, 1), topBit);

    //ITE(topbit = 0bin1, 0bin1111...a0, 0bin000...a0)
    output = CreateSimplifiedTermITE(condition, concatOnes, concatZeros);
    UpdateSimplifyMap(a, output, false);
    return output;
  } //end of ConvertBVSXToITE()
#endif

#if 0
  ASTNode
  Simplifier::RemoveWrites_TopLevel(const ASTNode& term)
  {
    if (READ != term.GetKind() || WRITE != term[0].GetKind())
      {
        FatalError("RemovesWrites: Input must be a READ over a WRITE", term);
      }

    if (!_bm->Begin_RemoveWrites && !_bm->SimplifyWrites_InPlace_Flag && !_bm->start_abstracting)
      {
        return term;
      }
    else if (!_bm->Begin_RemoveWrites && _bm->SimplifyWrites_InPlace_Flag && !_bm->start_abstracting)
      {
        //return term;
        return SimplifyWrites_InPlace(term);
      }
    else
      {
        return RemoveWrites(term);
      }
  } //end of RemoveWrites_TopLevel()
#endif

  // recursively simplify things that are of type array.

  ASTNode
  Simplifier::SimplifyArrayTerm(const ASTNode& term, ASTNodeMap* VarConstMap)
  {

    const unsigned iw = term.GetIndexWidth();
    assert(iw > 0);

    ASTNode output;
    if (CheckSimplifyMap(term, output, false))
      {
        return output;
      }

    switch (term.GetKind())
      {
    case SYMBOL:
      return term;
    case ITE:
      {
        output = CreateSimplifiedTermITE(SimplifyFormula(term[0], VarConstMap), SimplifyArrayTerm(term[1], VarConstMap),
            SimplifyArrayTerm(term[2], VarConstMap));
        assert(output.GetIndexWidth() == iw);
      }
      break;
    case WRITE:
      {
        ASTNode array = SimplifyArrayTerm(term[0], VarConstMap);
        ASTNode idx = SimplifyTerm(term[1]);
        ASTNode val = SimplifyTerm(term[2]);

        output = nf->CreateArrayTerm(WRITE, iw, term.GetValueWidth(), array, idx, val);
      }

      break;
    default:
      FatalError("2313456331");
      }

    UpdateSimplifyMap(term, output, false);
    assert(term.GetIndexWidth() == output.GetIndexWidth());
    assert(BVTypeCheck(output));
    return output;
  }

#if 0
  ASTNode
  Simplifier::SimplifyWrites_InPlace(const ASTNode& term, ASTNodeMap* VarConstMap)
  {
    ASTNodeMultiSet WriteIndicesSeenSoFar;
    bool SeenNonConstWriteIndex = false;

    if ((READ != term.GetKind()) || (WRITE != term[0].GetKind()))
      {
        FatalError("RemovesWrites: Input must be a READ over a WRITE", term);
      }

    ASTNode output;
    if (CheckSimplifyMap(term, output, false))
      {
        return output;
      }

    ASTVec writeIndices, writeValues;
    unsigned int width = term.GetValueWidth();
    //ASTNode original_write = term[0];
    ASTNode write = term[0];
    unsigned indexwidth = write.GetIndexWidth();
    ASTNode readIndex = SimplifyTerm(term[1]);

    do
      {
        ASTNode writeIndex = SimplifyTerm(write[1]);
        ASTNode writeVal = SimplifyTerm(write[2]);

        //compare the readIndex and the current writeIndex and see if they
        //simplify to TRUE or FALSE or UNDETERMINABLE at this stage
        ASTNode compare_readwrite_indices = SimplifyFormula(CreateSimplifiedEQ(writeIndex, readIndex), false,
            VarConstMap);

        //if readIndex and writeIndex are equal
        if (ASTTrue == compare_readwrite_indices && !SeenNonConstWriteIndex)
          {
            UpdateSimplifyMap(term, writeVal, false);
            return writeVal;
          }

        if (!(ASTTrue == compare_readwrite_indices || ASTFalse == compare_readwrite_indices))
          {
            SeenNonConstWriteIndex = true;
          }

        //if (readIndex=writeIndex <=> FALSE)
        if (ASTFalse == compare_readwrite_indices
            || (WriteIndicesSeenSoFar.find(writeIndex) != WriteIndicesSeenSoFar.end()))
          {
            //drop the current level write
            //do nothing
          }
        else
          {
            writeIndices.push_back(writeIndex);
            writeValues.push_back(writeVal);
          }

        //record the write indices seen so far
        //if(BVCONST == writeIndex.GetKind()) {
        WriteIndicesSeenSoFar.insert(writeIndex);
        //}

        //Setup the write for the new iteration, one level inner write
        write = write[0];
      }
    while (WRITE == write.GetKind());assert(BVTypeCheck(write));
    assert(write.GetIndexWidth() >0);

    // todo write[1] and write[2] should be simplified too.
    if (ITE == write.GetKind())
      {
        write = SimplifyArrayTerm(write, VarConstMap);
      }

    ASTVec::reverse_iterator it_index = writeIndices.rbegin();
    ASTVec::reverse_iterator itend_index = writeIndices.rend();
    ASTVec::reverse_iterator it_values = writeValues.rbegin();
    ASTVec::reverse_iterator itend_values = writeValues.rend();

    // May be a symbol, or an ITE.
    for (; it_index != itend_index; it_index++, it_values++)
      {
        write = nf->CreateTerm(WRITE, width, write, *it_index, *it_values);
        write.SetIndexWidth(indexwidth);
      }

    output = nf->CreateTerm(READ, width, write, readIndex);
    assert(BVTypeCheck(output));

    if (ITE == write.GetKind())
      {
        output = SimplifyTerm(output, VarConstMap);
        assert(BVTypeCheck(output));
      }

    //UpdateSimplifyMap(original_write, write, false);
    UpdateSimplifyMap(term, output, false);
    return output;
  } //end of SimplifyWrites_In_Place()

  //accepts a read over a write and returns a term without the write
  //READ(WRITE(A i val) j) <==> ITE(i=j,val,READ(A,j)). We use a memo
  //table for this function called RemoveWritesMemoMap
  ASTNode
  Simplifier::RemoveWrites(const ASTNode& input)
  {
    //unsigned int width = input.GetValueWidth();
    if (READ != input.GetKind() || WRITE != input[0].GetKind())
      {
        FatalError("RemovesWrites: Input must be a READ over a WRITE", input);
      }

    ASTNodeMap::iterator it;
    ASTNode output = input;
    if (CheckSimplifyMap(input, output, false))
      {
        return output;
      }

    if (!_bm->start_abstracting && _bm->Begin_RemoveWrites)
      {
        output = ReadOverWrite_To_ITE(input);
      }

    if (_bm->start_abstracting)
      {
        ASTNode newVar;
        if (!CheckSimplifyMap(input, newVar, false))
          {
            newVar = _bm->CreateFreshVariable(0, input.GetValueWidth(), "v_solver");
            (*ReadOverWrite_NewName_Map)[input] = newVar;
            NewName_ReadOverWrite_Map[newVar] = input;

            UpdateSimplifyMap(input, newVar, false);
            _bm->ASTNodeStats("New Var Name which replace Read_Over_Write: ", newVar);
          }
        output = newVar;
      } //end of start_abstracting if condition

    //memoize
    UpdateSimplifyMap(input, output, false);
    return output;
  } //end of RemoveWrites()


  ASTNode
  Simplifier::ReadOverWrite_To_ITE(const ASTNode& term, ASTNodeMap* VarConstMap)
  {
    unsigned int width = term.GetValueWidth();
    ASTNode input = term;
    if (READ != term.GetKind() || WRITE != term[0].GetKind())
      {
        FatalError("RemovesWrites: Input must be a READ over a WRITE", term);
      }

    ASTNodeMap::iterator it;
    ASTNode output;
    // if(CheckSimplifyMap(term,output,false)) {
    //       return output;
    //     }

    ASTNode partialITE = term;
    ASTNode writeA = ASTTrue;
    ASTNode oldRead = term;
    //iteratively expand read-over-write
    do
      {
        ASTNode write = input[0];
        ASTNode readIndex = SimplifyTerm(input[1]);
        //DO NOT CALL SimplifyTerm() on write[0]. You will go into an
        //infinite loop
        writeA = write[0];
        ASTNode writeIndex = SimplifyTerm(write[1]);
        ASTNode writeVal = SimplifyTerm(write[2]);

        ASTNode cond = SimplifyFormula(CreateSimplifiedEQ(writeIndex, readIndex), false, VarConstMap);
        ASTNode newRead = nf->CreateTerm(READ, width, writeA, readIndex);
        ASTNode newRead_memoized = newRead;
        if (CheckSimplifyMap(newRead, newRead_memoized, false))
          {
            newRead = newRead_memoized;
          }

        if (ASTTrue == cond && (term == partialITE))
          {
            //found the write-value in the first iteration
            //itself. return it
            output = writeVal;
            UpdateSimplifyMap(term, output, false);
            return output;
          }

        if (READ == partialITE.GetKind() && WRITE == partialITE[0].GetKind())
          {
            //first iteration or (previous cond==ASTFALSE and
            //partialITE is a "READ over WRITE")
            partialITE = CreateSimplifiedTermITE(cond, writeVal, newRead);
          }
        else if (ITE == partialITE.GetKind())
          {
            //ITE(i1 = j, v1, R(A,j))
            ASTNode ElseITE = CreateSimplifiedTermITE(cond, writeVal, newRead);
            //R(W(A,i1,v1),j) <==> ITE(i1 = j, v1, R(A,j))
            UpdateSimplifyMap(oldRead, ElseITE, false);
            //ITE(i2 = j, v2, R(W(A,i1,v1),j)) <==> ITE(i2 = j, v2,
            //ITE(i1 = j, v1, R(A,j)))
            partialITE = SimplifyTerm(partialITE);
          }
        else
          {
            FatalError("RemoveWrites: Control should not reach here\n");
          }

        if (ASTTrue == cond)
          {
            //no more iterations required
            output = partialITE;
            UpdateSimplifyMap(term, output, false);
            return output;
          }

        input = newRead;
        oldRead = newRead;
      }
    while (READ == input.GetKind() && WRITE == input[0].GetKind());

    output = partialITE;

    //memoize
    //UpdateSimplifyMap(term,output,false);
    return output;
  } //ReadOverWrite_To_ITE()
#endif

  //compute the multiplicative inverse of the input
  ASTNode
  Simplifier::MultiplicativeInverse(const ASTNode& d)
  {
    ASTNode c = d;
    if (BVCONST != c.GetKind())
      {
        FatalError("Input must be a constant", c);
      }

    if (!BVConstIsOdd(c))
      {
        FatalError("MultiplicativeInverse: Input must be odd: ", c);
      }

    //cerr << "input to multinverse function is: " << d << endl;
    ASTNode inverse;
    if (CheckMultInverseMap(d, inverse))
      {
        //cerr << "found the inverse of: " << d << "and it is: " <<
        //inverse << endl;
        return inverse;
      }

    inverse = c;
    unsigned inputwidth = c.GetValueWidth();

    //Compute the multiplicative inverse of c using the extended
    //euclidian algorithm
    //
    //create a '0' which is 1 bit long
    ASTNode onebit_zero = _bm->CreateZeroConst(1);
    //zero pad t0, i.e. 0 @ t0
    c = BVConstEvaluator(nf->CreateTerm(BVCONCAT, inputwidth + 1, onebit_zero, c));

    //construct 2^(inputwidth), i.e. a bitvector of length
    //'inputwidth+1', which is max(inputwidth)+1
    //
    //all 1's
    ASTNode max = _bm->CreateMaxConst(inputwidth);
    //zero pad max
    max = BVConstEvaluator(nf->CreateTerm(BVCONCAT, inputwidth + 1, onebit_zero, max));
    //_bm->Create a '1' which has leading zeros of length 'inputwidth'
    ASTNode inputwidthplusone_one = _bm->CreateOneConst(inputwidth + 1);
    //add 1 to max
    max = nf->CreateTerm(BVPLUS, inputwidth + 1, max, inputwidthplusone_one);
    max = BVConstEvaluator(max);
    ASTNode zero = _bm->CreateZeroConst(inputwidth + 1);
    ASTNode max_bvgt_0 = nf->CreateNode(BVGT, max, zero);
    ASTNode quotient, remainder;
    ASTNode x, x1, x2;

    //x1 initialized to zero
    x1 = zero;
    //x2 initialized to one
    x2 = _bm->CreateOneConst(inputwidth + 1);
    while (ASTTrue == BVConstEvaluator(max_bvgt_0))
      {
        //quotient = (c divided by max)
        quotient = BVConstEvaluator(nf->CreateTerm(BVDIV, inputwidth + 1, c, max));

        //remainder of (c divided by max)
        remainder = BVConstEvaluator(nf->CreateTerm(BVMOD, inputwidth + 1, c, max));

        //x = x2 - q*x1
        x = nf->CreateTerm(BVSUB, inputwidth + 1, x2, nf->CreateTerm(BVMULT, inputwidth + 1, quotient, x1));
        x = BVConstEvaluator(x);

        //fix the inputs to the extended euclidian algo
        c = max;
        max = remainder;
        max_bvgt_0 = nf->CreateNode(BVGT, max, zero);

        x2 = x1;
        x1 = x;
      }

    ASTNode hi = _bm->CreateBVConst(32, inputwidth - 1);
    ASTNode low = _bm->CreateZeroConst(32);
    inverse = nf->CreateTerm(BVEXTRACT, inputwidth, x2, hi, low);
    inverse = BVConstEvaluator(inverse);

    UpdateMultInverseMap(d, inverse);
    //cerr << "output of multinverse function is: " << inverse << endl;
    return inverse;
  } //end of MultiplicativeInverse()

  //returns true if the input is odd
  bool
  Simplifier::BVConstIsOdd(const ASTNode& c)
  {
    if (BVCONST != c.GetKind())
      {
        FatalError("Input must be a constant", c);
      }

    ASTNode zero = _bm->CreateZeroConst(1);
    ASTNode hi = _bm->CreateZeroConst(32);
    ASTNode low = hi;
    ASTNode lowestbit = nf->CreateTerm(BVEXTRACT, 1, c, hi, low);
    lowestbit = BVConstEvaluator(lowestbit);

    if (lowestbit == zero)
      {
        return false;
      }
    else
      {
        return true;
      }
  } //end of BVConstIsOdd()

  // in ext/hash_map, and tr/unordered_map, there is no provision to
  // shrink down the number of buckets in a hash map. If the hash_map
  // has previously held a lot of data, then it will have a lot of
  // buckets. Slowing down iterators and clears() in particular.
  void
  Simplifier::ResetSimplifyMaps()
  {
    // clear() is extremely expensive for hash_maps with a lot of
    // buckets, in the EXT_MAP implementation it visits every bucket,
    // checking whether each bucket is empty or not, if non-empty it
    // deletes the contents.  The destructor seems to clear everything
    // anyway.

    //SimplifyMap->clear();
    delete SimplifyMap;
    SimplifyMap = new ASTNodeMap(INITIAL_TABLE_SIZE);

    //SimplifyNegMap->clear();
    delete SimplifyNegMap;
    SimplifyNegMap = new ASTNodeMap(INITIAL_TABLE_SIZE);
  }

  void
  Simplifier::printCacheStatus()
  {
    cerr << "SimplifyMap:" << SimplifyMap->size() << ":" << SimplifyMap->bucket_count() << endl;
    cerr << "SimplifyNegMap:" << SimplifyNegMap->size() << ":" << SimplifyNegMap->bucket_count() << endl;
    cerr << "AlwaysTrueFormSet" << AlwaysTrueHashSet.size() << ":" << AlwaysTrueHashSet.bucket_count() << endl;
    cerr << "MultInverseMap" << MultInverseMap.size() << ":" << MultInverseMap.bucket_count() << endl;

#if 0
    cerr << "ReadOverWrite_NewName_Map" << ReadOverWrite_NewName_Map->size() << ":"
        << ReadOverWrite_NewName_Map->bucket_count() << endl;
    cerr << "NewName_ReadOverWrite_Map" << NewName_ReadOverWrite_Map.size() << ":"
        << NewName_ReadOverWrite_Map.bucket_count() << endl;
#endif
    cerr << "substn_map" << substitutionMap.Return_SolverMap()->size() << ":"
        << substitutionMap.Return_SolverMap()->bucket_count() << endl;

  } //printCacheStatus()
}
;
//end of namespace
