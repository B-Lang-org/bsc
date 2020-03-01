/********************************************************************
 * AUTHORS: David L. Dill, Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
// -*- c++ -*-
#include <cmath>
#include <cassert>
#include "BitBlaster.h"
#include "AIG/BBNodeManagerAIG.h"
#include "ASTNode/BBNodeManagerASTNode.h"
#include "../simplifier/constantBitP/FixedBits.h"
#include "../simplifier/constantBitP/ConstantBitPropagation.h"
#include "../simplifier/constantBitP/NodeToFixedBitsMap.h"
#include "../simplifier/simplifier.h"
#include "../AST/ArrayTransformer.h"

namespace BEEV
{

  /********************************************************************
   * BitBlast
   *
   * Convert bitvector terms and formulas to boolean formulas.  A term
   * is something that can represent a multi-bit bitvector, such as
   * BVPLUS or BVXOR (or a BV variable or constant).  A formula (form)
   * represents a boolean value, such as EQ or BVLE.  Bit blasting a
   * term representing an n-bit bitvector with BBTerm yields a vector
   * of n boolean formulas (returning BBNodeVec).  Bit blasting a formula
   * returns a single boolean formula (type BBNode).  A bitblasted
   * term is a vector of BBNodes for formulas.  The 0th element of
   * the vector corresponds to bit 0 -- the low-order bit.
   ********************************************************************/

  using simplifier::constantBitP::FixedBits;
  using simplifier::constantBitP::NodeToFixedBitsMap;

#define BBNodeVec vector<BBNode>
#define BBNodeVecMap map<ASTNode, vector<BBNode> >
#define BBNodeSet set<BBNode>

  vector<BBNodeAIG> _empty_BBNodeAIGVec;

// Bit blast a bitvector term.  The term must have a kind for a
// bitvector term.  Result is a ref to a vector of formula nodes
// representing the boolean formula.

// This prints out each constant expression that the bitblaster
// discovers. I use this to check that the expressions that are
// reaching the bitblaster don't have obvious simplifications
// that should have already been applied.
  const bool debug_do_check = false;
  const bool debug_bitblaster = false;

  const bool conjoin_to_top = true;


  template<class BBNode>
  class BBVecHasher
  {
  public:
    size_t operator()(const vector<BBNode>& n) const
    {
      int hash =0;
      for (int i=0; i <  std::min(n.size(),(size_t)6); i++)
        hash += n[i].GetNodeNum();
       return hash;
    }
  };

  template<class BBNode>
  class BBVecEquals
  {
  public:
    bool operator()(const vector<BBNode>& n0, const vector<BBNode>& n1) const
    {
      if (n0.size() != n1.size())
        return false;

      for (int i=0; i <  n0.size(); i++)
        {
          if (!(n0[i] == n1[i]))
            return false;
        }
      return true;
    }
  };


// Look through the maps to see what the bitblaster has discovered (if anything) is constant.
// then looks through for AIGS that are mapped to from different ASTNodes.
  template<class BBNode, class BBNodeManagerT>
    void
    BitBlaster<BBNode, BBNodeManagerT>::getConsts(const ASTNode& form, ASTNodeMap& fromTo, ASTNodeMap& equivs)
    {
      assert(form.GetType() == BOOLEAN_TYPE);

      BBNodeSet support;
      BBForm(form, support);

      assert(support.size() ==0);

        {
        typename map<ASTNode, BBNode>::iterator it;
        for (it = BBFormMemo.begin(); it != BBFormMemo.end(); it++)
          {
          const ASTNode& n = it->first;
          const BBNode& x = it->second;
          if (n.isConstant())
            continue;

          if (x != BBTrue && x != BBFalse)
            continue;

          assert(n.GetType() == BOOLEAN_TYPE);

          ASTNode result;
          if (x == BBTrue)
            result = n.GetSTPMgr()->ASTTrue;
          else
            result = n.GetSTPMgr()->ASTFalse;

          if (n.GetKind() != SYMBOL)
            fromTo.insert(make_pair(n, result));
          else
            simp->UpdateSubstitutionMap(n, result);
          }
        }

      typename BBNodeVecMap::iterator it;
      for (it = BBTermMemo.begin(); it != BBTermMemo.end(); it++)
        {
        const ASTNode& n = it->first;
        assert(n.GetType() == BITVECTOR_TYPE);

        if (n.isConstant())
          continue;

        vector<BBNode>& x = it->second;
        assert(x.size() == n.GetValueWidth());

        bool constNode = true;
        for (int i = 0; i < (int) x.size(); i++)
          {
          if (x[i] != BBTrue && x[i] != BBFalse)
            {
            constNode = false;
            break;
            }
          }
        if (!constNode)
          continue;

        CBV val = CONSTANTBV::BitVector_Create(n.GetValueWidth(), true);
        for (int i = 0; i < (int) x.size(); i++)
          {
          if (x[i] == BBTrue)
            CONSTANTBV::BitVector_Bit_On(val, i);
          }

        ASTNode r = n.GetSTPMgr()->CreateBVConst(val, n.GetValueWidth());
        if (n.GetKind() == SYMBOL)
          simp->UpdateSubstitutionMap(n, r);
        else
          fromTo.insert(make_pair(n, r));
        }

      if (form.GetSTPMgr()->UserFlags.isSet("bb-equiv","1"))
      {
        HASHMAP <intptr_t ,ASTNode> nodeToFn;
        typename map<ASTNode, BBNode>::iterator it;
        for (it = BBFormMemo.begin(); it != BBFormMemo.end(); it++)
          {
          const ASTNode& n = it->first;
          if (n.isConstant())
            continue;

          const BBNode& x = it->second;
          if (x == BBTrue || x == BBFalse)
            continue;

          if (nodeToFn.find(x.GetNodeNum()) == nodeToFn.end())
            {
              nodeToFn.insert(make_pair(x.GetNodeNum(),n));
            }
          else
            {
              const ASTNode other = (nodeToFn.find(x.GetNodeNum()))->second;
              std::pair<ASTNode,ASTNode> p;
              if (other.GetNodeNum() > n.GetNodeNum())
                p = make_pair(other,n);
              else
                p = make_pair(n,other);

              equivs.insert(p);
              //std::cerr << "from" << p.first << " to" << p.second;
              //ASTNode equals = ASTNF->CreateNode(NOT,ASTNF->CreateNode(EQ,p.first,p.second));
              //printer::SMTLIB2_PrintBack(std::cerr,p.second);
            }
          }
      }

      typedef HASHMAP<vector<BBNode>, ASTNode,BBVecHasher <BBNode>, BBVecEquals<BBNode> > M;
      if (form.GetSTPMgr()->UserFlags.isSet("bb-equiv","1"))
        {
          M lookup;
          typename std::map<ASTNode, vector<BBNode> >::iterator it;
          for (it = BBTermMemo.begin(); it != BBTermMemo.end(); it++)
            {
              const ASTNode& n = it->first;
              if (n.isConstant())
                continue;

              const vector<BBNode>& x = it->second;

              bool constNode = true;
              for (int i = 0; i < (int) x.size(); i++)
                {
                  if (x[i] != BBTrue && x[i] != BBFalse)
                    {
                      constNode = false;
                      break;
                    }
                }
              if (!constNode)
                continue;

              if (lookup.find(x) == lookup.end())
                {
                  lookup.insert(make_pair(x, n));
                }
              else
                {
                  const ASTNode other = (lookup.find(x))->second;
                  std::pair<ASTNode, ASTNode> p;
                  if (other.GetNodeNum() > n.GetNodeNum())
                    p = make_pair(other, n);
                  else
                    p = make_pair(n, other);

                  //cerr << "EQUIV";
                  equivs.insert(p);
                }
            }
        }
    }


  template<class BBNode, class BBNodeManagerT>
    void
    BitBlaster<BBNode, BBNodeManagerT>::commonCheck(const ASTNode& n)
    {
      cerr << "Non constant is constant:";
      cerr << n << endl;

      if (cb == NULL)
        return;
      if (cb->fixedMap->map->find(n) != cb->fixedMap->map->end())
        {
        FixedBits* b = cb->fixedMap->map->find(n)->second;
        cerr << "fixed bits are:" << *b << endl;
        }
    }

// If x isn't a constant, and the bit-blasted version is. Print out the
// AST nodes and the fixed bits.
  template<class BBNode, class BBNodeManagerT>
    void
    BitBlaster<BBNode, BBNodeManagerT>::check(const BBNode& x, const ASTNode& n)
    {
      if (n.isConstant())
        return;

      if (x != BBTrue && x != BBFalse)
        return;

      commonCheck(n);
    }

  template<class BBNode, class BBNodeManagerT>
    void
    BitBlaster<BBNode, BBNodeManagerT>::check(const vector<BBNode>& x, const ASTNode& n)
    {
      if (n.isConstant())
        return;

      for (int i = 0; i < (int) x.size(); i++)
        {
        if (x[i] != BBTrue && x[i] != BBFalse)
          return;
        }

      commonCheck(n);
    }

  template<class BBNode, class BBNodeManagerT>
    bool
    BitBlaster<BBNode, BBNodeManagerT>::update(const ASTNode&n, const int i, simplifier::constantBitP::FixedBits* b,
        BBNode& bb, BBNodeSet& support)
    {
      if (b->isFixed(i) && (!(bb == BBTrue || bb == BBFalse)))
        {
        //We have a fixed bit, but the bitblasted values aren't constant true or false.
        if (conjoin_to_top && (fixedFromBottom.find(n) == fixedFromBottom.end()))
          {
          if (b->getValue(i))
            support.insert(bb);
          else
            support.insert(nf->CreateNode(NOT, bb));
          }

        bb = b->getValue(i) ? BBTrue : BBFalse;
        }
      else if (!b->isFixed(i) && (bb == BBTrue || bb == BBFalse))
        {
        b->setFixed(i, true);
        b->setValue(i, bb == BBTrue ? true : false);
        return true; // Need to propagate.
        }

      return false;
    }

  template<class BBNode, class BBNodeManagerT>
    void
    BitBlaster<BBNode, BBNodeManagerT>::updateForm(const ASTNode&n, BBNode& bb, BBNodeSet& support)
    {
      if (cb == NULL || n.isConstant())
        return;

      BBNodeVec v(1, bb);
      updateTerm(n, v, support);
      bb = v[0];
    }

  template<class BBNode, class BBNodeManagerT>
    void
    BitBlaster<BBNode, BBNodeManagerT>::updateTerm(const ASTNode&n, BBNodeVec& bb, BBNodeSet& support)
    {

      if (cb == NULL)
        return;

      if (cb->isUnsatisfiable())
        return;

      if (n.isConstant())
        {
        // This doesn't hold any longer because we convert BVSDIV and friends to ASTNodes.
#if 0
        simplifier::constantBitP::NodeToFixedBitsMap::NodeToFixedBitsMapType::const_iterator it;
        it = cb->fixedMap->map->find(n);
        if (it == cb->fixedMap->map->end())
          {
          cerr << n;
          assert(it != cb->fixedMap->map->end());
          }assert(it->second->isTotallyFixed());
#endif
        return;
        }

      bool bbFixed = false;
      for (int i = 0; i < (int) bb.size(); i++)
        {
        if (bb[i] == BBTrue || bb[i] == BBFalse)
          {
          bbFixed = true;
          break;
          }
        }

      FixedBits * b = NULL;

      simplifier::constantBitP::NodeToFixedBitsMap::NodeToFixedBitsMapType::const_iterator it;
      if ((it = cb->fixedMap->map->find(n)) == cb->fixedMap->map->end())
        {
        if (bbFixed)
          {
          b = new FixedBits(n.GetType() == BOOLEAN_TYPE ? 1 : n.GetValueWidth(), n.GetType() == BOOLEAN_TYPE);
          cb->fixedMap->map->insert(pair<ASTNode, FixedBits*>(n, b));
          if (debug_bitblaster)
            cerr << "inserting" << n.GetNodeNum() << endl;
          }
        else
          return; // nothing to update.
        }
      else
        b = it->second;

      assert(b != NULL);
      FixedBits old(*b);

      bool changed = false;
      for (int i = 0; i < (int) bb.size(); i++)
        if (update(n, i, b, bb[i], support))
          changed = true; // don't break, we want to run update(..) on each bit.
      if (changed)
        {
        cb->scheduleNode(n);
        cb->scheduleUp(n);
        cb->propagate();
        }

      //If it's changed, the propagation may have caused new bits to be fixed.
      if (changed && !FixedBits::equals(*b, old))
        {
        updateTerm(n, bb, support);
        return;
        }

      // There may be a conflict between the AIGs and the constant bits (if the problem is unsatisfiable).
      // So we can't ensure that if one is fixed to true (say), that the other should be true also.

      if (!cb->isUnsatisfiable())
        for (int i = 0; i < (int) bb.size(); i++)
          {
          if (b->isFixed(i))
            assert(bb[i] == BBTrue || bb[i] == BBFalse);

          if (bb[i] == BBFalse || bb[i] == BBTrue)
            assert( b->isFixed(i));
          }
    }

  template<class BBNode, class BBNodeManagerT>
    bool
    BitBlaster<BBNode, BBNodeManagerT>::isConstant(const BBNodeVec& v)
    {
      for (int i = 0; i < v.size(); i++)
        {
        if (v[i] != nf->getTrue() && v[i] != nf->getFalse())
          return false;
        }

      return true;
    }

  template<class BBNode, class BBNodeManagerT>
    ASTNode
    BitBlaster<BBNode, BBNodeManagerT>::getConstant(const BBNodeVec& v, const ASTNode&n)
    {
      if (n.GetType() == BOOLEAN_TYPE)
        {
        if (v[0] == nf->getTrue())
          return ASTNF->getTrue();
        else
          return ASTNF->getFalse();
        }

      CBV bv = CONSTANTBV::BitVector_Create(v.size(), true);

      for (int i = 0; i < v.size(); i++)
        if (v[i] == nf->getTrue())
          CONSTANTBV::BitVector_Bit_On(bv, i);

      return ASTNF->CreateConstant(bv, v.size());

    }

  template<class BBNode, class BBNodeManagerT>
    const BBNodeVec
    BitBlaster<BBNode, BBNodeManagerT>::BBTerm(const ASTNode& _term, BBNodeSet& support)
    {
      ASTNode term = _term; // mutable local copy.

      typename BBNodeVecMap::iterator it = BBTermMemo.find(term);
      if (it != BBTermMemo.end())
        {
        // Constant bit propagation may have updated something.
        updateTerm(term, it->second, support);
        return it->second;
        }

      // This block checks if the bitblasting/fixed bits have discovered
      // any new constants. If they've discovered a new constant, then
      // the simplification function is called on a new term with the constant
      // value replacing what used to be a variable child. For instance, if
      // the term is ite(x,y,z), and we now know that x is true. Then we will
      // call SimplifyTerm on ite(true,y,z), which will do the expected simplification.
      // Then the term that we bitblast will by "y".

      if (uf != NULL && uf->optimize_flag && uf->simplify_during_BB_flag)
        {
        const int numberOfChildren = term.Degree();
        vector<BBNodeVec> ch;
        ch.reserve(numberOfChildren);

        for (int i = 0; i < numberOfChildren; i++)
          {
          if (term[i].GetType() == BITVECTOR_TYPE)
            {
            ch.push_back(BBTerm(term[i], support));
            }
          else if (term[i].GetType() == BOOLEAN_TYPE)
            {
            BBNodeVec t;
            t.push_back(BBForm(term[i], support));
            ch.push_back(t);
            }
          else
            throw "sdfssfa";
          }

        bool newConst = false;
        for (int i = 0; i < numberOfChildren; i++)
          {
          if (term[i].isConstant())
            continue;

          if (isConstant(ch[i]))
            {
            // it's only interesting if the child isn't a constant,
            // but the bitblasted version is.
            newConst = true;
            break;
            }
          }

        // Something is now constant that didn't used to be.
        if (newConst)
          {
          ASTVec new_ch;
          new_ch.reserve(numberOfChildren);
          for (int i = 0; i < numberOfChildren; i++)
            {
            if (!term[i].isConstant() && isConstant(ch[i]))
              new_ch.push_back(getConstant(ch[i], term[i]));
            else
              new_ch.push_back(term[i]);
            }

          ASTNode n_term = simp->SimplifyTerm(ASTNF->CreateTerm(term.GetKind(), term.GetValueWidth(), new_ch));
          assert(BVTypeCheck(n_term));
          // n_term is the potentially simplified version of term.

          if (cb != NULL)
            {
            // Add all the nodes to the worklist that have a constant as a child.
            cb->initWorkList(n_term);

            simplifier::constantBitP::NodeToFixedBitsMap::NodeToFixedBitsMapType::iterator it;
            it = cb->fixedMap->map->find(n_term);
            FixedBits* nBits;
            if (it == cb->fixedMap->map->end())
              {
              nBits = new FixedBits(std::max((unsigned) 1, n_term.GetValueWidth()), term.GetType() == BOOLEAN_TYPE);
              cb->fixedMap->map->insert(pair<ASTNode, FixedBits*>(n_term, nBits));
              }
            else
              nBits = it->second;

            if (n_term.isConstant())
              {
              // It's assumed elsewhere that constants map to themselves in the fixed map.
              // That doesn't happen here unless it's added explicitly.
              *nBits = FixedBits::concreteToAbstract(n_term);
              }

            it = cb->fixedMap->map->find(term);
            if (it != cb->fixedMap->map->end())
              {
              // Copy over to the (potentially) new node. Everything we know about the old node.
              nBits->mergeIn(*(it->second));
              }

            cb->scheduleUp(n_term);
            cb->scheduleNode(n_term);
            cb->propagate();

            if (it != cb->fixedMap->map->end())
              {
              // Copy to the old node, all we know about the new node. This means that
              // all the parents of the old node get the (potentially) updated fixings.
              it->second->mergeIn(*nBits);
              }
            // Propagate through all the parents of term.
            cb->scheduleUp(term);
            cb->scheduleNode(term);
            cb->propagate();
            // Now we've propagated.
            }
          term = n_term;

          // check if we've already done the simplified one.
          it = BBTermMemo.find(term);
          if (it != BBTermMemo.end())
            {
            // Constant bit propagation may have updated something.
            updateTerm(term, it->second, support);
            return it->second;
            }
          }
        }

      BBNodeVec result;

      const Kind k = term.GetKind();
      if (!is_Term_kind(k))
        FatalError("BBTerm: Illegal kind to BBTerm", term);

      const ASTVec::const_iterator kids_end = term.end();
      const unsigned int num_bits = term.GetValueWidth();
      switch (k)
        {
      case BVNEG:
        {
        // bitwise complement
        const BBNodeVec& bbkids = BBTerm(term[0], support);
        result = BBNeg(bbkids);
        break;
        }

      case BVRIGHTSHIFT:
      case BVSRSHIFT:
      case BVLEFTSHIFT:
        {
        // Barrel shifter
        const BBNodeVec& bbarg1 = BBTerm(term[0], support);
        const BBNodeVec& bbarg2 = BBTerm(term[1], support);

        // Signed right shift, need to copy the sign bit.
        BBNode toFill;
        if (BVSRSHIFT == k)
          toFill = bbarg1.back();
        else
          toFill = nf->getFalse();

        BBNodeVec temp_result(bbarg1);
        // if any bit is set in bbarg2 higher than log2Width, then we know that the result is zero.
        // Add one to make allowance for rounding down. For example, given 300 bits, the log2 is about
        // 8.2 so round up to 9.

        const unsigned width = bbarg1.size();
        const unsigned log2Width = (unsigned) log2(width) + 1;

        if (k == BVSRSHIFT || k == BVRIGHTSHIFT)
          for (unsigned int i = 0; i < log2Width; i++)
            {
            if (bbarg2[i] == nf->getFalse())
              continue; // Not shifting by anything.

            unsigned int shift_amount = 1 << i;

            for (unsigned int j = 0; j < width; j++)
              {
              if (j + shift_amount >= width)
                temp_result[j] = nf->CreateNode(ITE, bbarg2[i], toFill, temp_result[j]);
              else
                temp_result[j] = nf->CreateNode(ITE, bbarg2[i], temp_result[j + shift_amount], temp_result[j]);
              }
            }
        else
          for (unsigned int i = 0; i < log2Width; i++)
            {
            if (bbarg2[i] == nf->getFalse())
              continue; // Not shifting by anything.

            int shift_amount = 1 << i;

            for (signed int j = width - 1; j >= 0; j--)
              {
              if (j < shift_amount)
                temp_result[j] = nf->CreateNode(ITE, bbarg2[i], toFill, temp_result[j]);
              else
                temp_result[j] = nf->CreateNode(ITE, bbarg2[i], temp_result[j - shift_amount], temp_result[j]);
              }
            }

        // If any of the remainder are true. Then the whole thing gets the fill value.
        BBNode remainder = nf->getFalse();
        for (unsigned int i = log2Width; i < width; i++)
          {
          remainder = nf->CreateNode(OR, remainder, bbarg2[i]);
          }

        for (unsigned int i = 0; i < width; i++)
          {
          temp_result[i] = nf->CreateNode(ITE, remainder, toFill, temp_result[i]);
          }

        result = temp_result;
        }
        break;

      case ITE:
        {
        // Term version of ITE.
        const BBNode& cond = BBForm(term[0], support);
        const BBNodeVec& thn = BBTerm(term[1], support);
        const BBNodeVec& els = BBTerm(term[2], support);
        result = BBITE(cond, thn, els);
        break;
        }

      case BVSX:
      case BVZX:
        {
        // Replicate high-order bit as many times as necessary.
        // Arg 0 is expression to be sign extended.
        const ASTNode& arg = term[0];
        const unsigned long result_width = term.GetValueWidth();
        const unsigned long arg_width = arg.GetValueWidth();
        const BBNodeVec& bbarg = BBTerm(arg, support);

        if (result_width == arg_width)
          {
          //nothing to sign extend
          result = bbarg;
          break;
          }
        else
          {
          //we need to sign extend
          const BBNode& msb = (k == BVSX) ? bbarg.back() : BBFalse;

          BBNodeVec tmp_res(result_width);

          typename BBNodeVec::const_iterator bb_it = bbarg.begin();
          typename BBNodeVec::iterator res_it = tmp_res.begin();
          typename BBNodeVec::iterator res_ext = res_it + arg_width; // first bit of extended part
          typename BBNodeVec::iterator res_end = tmp_res.end();

          // copy LSBs directly from bbvec
          for (; res_it < res_ext; (res_it++, bb_it++))
            {
            *res_it = *bb_it;
            }
          // repeat MSB to fill up rest of result.
          for (; res_it < res_end; (res_it++))
            {
            *res_it = msb;
            }

          result = tmp_res;
          break;
          }
        }

      case BVEXTRACT:
        {
        // bitblast the child, then extract the relevant bits.
        // Note: This could be optimized by not bitblasting the bits
        // that aren't fetched.  But that would be tricky, especially
        // with memo-ization.

        const BBNodeVec& bbkids = BBTerm(term[0], support);
        const unsigned int high = term[1].GetUnsignedConst();
        const unsigned int low = term[2].GetUnsignedConst();

        typename BBNodeVec::const_iterator bbkfit = bbkids.begin();
        // I should have used pointers to BBNodeVec, to avoid this crock

        result = BBNodeVec(bbkfit + low, bbkfit + high + 1);
        break;
        }
      case BVCONCAT:
        {
        const BBNodeVec& vec1 = BBTerm(term[0], support);
        const BBNodeVec& vec2 = BBTerm(term[1], support);

        BBNodeVec tmp_res(vec2);
        tmp_res.insert(tmp_res.end(), vec1.begin(), vec1.end());
        result = tmp_res;
        break;
        }
      case BVPLUS:
        {
        assert(term.Degree() >=1);
        if (bvplus_variant)
          {
          // Add children pairwise and accumulate in BBsum

          ASTVec::const_iterator it = term.begin();
          BBNodeVec tmp_res = BBTerm(*it, support);
          for (++it; it < kids_end; it++)
            {
            const BBNodeVec& tmp = BBTerm(*it, support);
            assert(tmp.size() == num_bits);
            BBPlus2(tmp_res, tmp, nf->getFalse());
            }

          result = tmp_res;
          }
        else
          {
          // Add all the children up using an addition network.
          vector<BBNodeVec> results;
          for (int i = 0; i < term.Degree(); i++)
            results.push_back(BBTerm(term[i], support));

          const int bitWidth = term[0].GetValueWidth();
          std::vector<list<BBNode> > products(bitWidth+1);
          for (int i = 0; i < bitWidth; i++)
            {
            for (int j = 0; j < results.size(); j++)
              products[i].push_back(results[j][i]);
            }

          result = buildAdditionNetworkResult(products, support, term);
          }
        break;
        }
      case BVUMINUS:
        {
        const BBNodeVec& bbkid = BBTerm(term[0], support);
        result = BBUminus(bbkid);
        break;
        }
      case BVSUB:
        {
        // complement of subtrahend
        // copy, since BBSub writes into it.

        BBNodeVec tmp_res = BBTerm(term[0], support);

        const BBNodeVec& bbkid1 = BBTerm(term[1], support);
        BBSub(tmp_res, bbkid1, support);
        result = tmp_res;
        break;
        }
      case BVMULT:
        {
        assert(BVTypeCheck(term));
        assert(term.Degree() == 2);

        BBNodeVec mpcd1 = BBTerm(term[0], support);
        const BBNodeVec& mpcd2 = BBTerm(term[1], support);
        updateTerm(term[0], mpcd1, support);

        assert(mpcd1.size() == mpcd2.size());
        result = BBMult(mpcd1, mpcd2, support, term);
        break;
        }
      case SBVREM:
      case SBVMOD:
      case SBVDIV:
        {
        ASTNode p = ArrayTransformer::TranslateSignedDivModRem(term,ASTNF,term.GetSTPMgr());
        result = BBTerm(p,support);
        break;
        }

      case BVDIV:
      case BVMOD:
        {
        const BBNodeVec& dvdd = BBTerm(term[0], support);
        const BBNodeVec& dvsr = BBTerm(term[1], support);
        assert(dvdd.size() == num_bits);
        assert(dvsr.size() == num_bits);
        BBNodeVec q(num_bits);
        BBNodeVec r(num_bits);
        BBDivMod(dvdd, dvsr, q, r, num_bits, support);
        if (k == BVDIV)
          {
          if (uf->division_by_zero_returns_one_flag)
            {
            BBNodeVec zero(term.GetValueWidth(), BBFalse);

            BBNode eq = BBEQ(zero, dvsr);
            BBNodeVec one(term.GetValueWidth(), BBFalse);
            one[0] = BBTrue;

            result = BBITE(eq, one, q);
            }
          else
            {
            result = q;
            }
          }
        else
          result = r;
        break;
        }
        //  n-ary bitwise operators.
      case BVXOR:
      case BVXNOR:
      case BVAND:
      case BVOR:
      case BVNOR:
      case BVNAND:
        {
        // Add children pairwise and accumulate in BBsum
        ASTVec::const_iterator it = term.begin();
        Kind bk = UNDEFINED; // Kind of individual bit op.
        switch (k)
          {
        case BVXOR:
          bk = XOR;
          break;
        case BVXNOR:
          bk = IFF;
          break;
        case BVAND:
          bk = AND;
          break;
        case BVOR:
          bk = OR;
          break;
        case BVNOR:
          bk = NOR;
          break;
        case BVNAND:
          bk = NAND;
          break;
        default:
          FatalError("BBTerm: Illegal kind to BBTerm", term);
          break;
          }

        // Sum is destructively modified in the loop, so make a copy of value
        // returned by BBTerm.
        BBNodeVec temp = BBTerm(*it, support);
        BBNodeVec sum(temp); // First operand.

        // Iterate over remaining bitvector term operands
        for (++it; it < kids_end; it++)
          {
          //FIXME FIXME FIXME: Why does using a temp. var change the behavior?
          temp = BBTerm(*it, support);
          const BBNodeVec& y = temp;

          assert(y.size() == num_bits);
          for (unsigned i = 0; i < num_bits; i++)
            {
            sum[i] = nf->CreateNode(bk, sum[i], y[i]);
            }
          }
        result = sum;
        break;
        }
      case SYMBOL:
        {
        assert(num_bits >0);

        BBNodeVec bbvec;
        bbvec.reserve(num_bits);

        for (unsigned int i = 0; i < num_bits; i++)
          {
          BBNode bit_node = nf->CreateSymbol(term, i);
          bbvec.push_back(bit_node);
          }
        result = bbvec;
        break;
        }
      case BVCONST:
        {
        BBNodeVec tmp_res(num_bits);
        CBV bv = term.GetBVConst();
        for (unsigned int i = 0; i < num_bits; i++)
          {
          tmp_res[i] = CONSTANTBV::BitVector_bit_test(bv, i) ? nf->getTrue() : nf->getFalse();
          }
        result = tmp_res;
        break;
        }
      default:
        FatalError("BBTerm: Illegal kind to BBTerm", term);
        }

      assert(result.size() == term.GetValueWidth());

      if (debug_do_check)
        check(result, term);

      updateTerm(term, result, support);
      return (BBTermMemo[term] = result);
    }

  template<class BBNode, class BBNodeManagerT>
    const BBNode
    BitBlaster<BBNode, BBNodeManagerT>::BBForm(const ASTNode& form)
    {

      if (conjoin_to_top && cb != NULL)
        {
        ASTNodeMap n = cb->getAllFixed();
        for (ASTNodeMap::const_iterator it = n.begin(); it != n.end(); it++)
          fixedFromBottom.insert(it->first);

        // Mark the top node as true.
        cb->setNodeToTrue(form);
        cb->propagate();
        }

      BBNodeSet support;
      BBNode r = BBForm(form, support);

      vector<BBNode> v;
      v.insert(v.end(), support.begin(), support.end());
      v.push_back(r);

      if (!conjoin_to_top)
        {
        assert(support.size() ==0);
        }

      if (cb != NULL && !cb->isUnsatisfiable())
        {
        ASTNodeSet visited;
        assert(cb->checkAtFixedPoint(form,visited));
        }
      if (v.size() == 1)
        return v[0];
      else
        return nf->CreateNode(AND, v);
    }

// bit blast a formula (boolean term).  Result is one bit wide,
  template<class BBNode, class BBNodeManagerT>
    const BBNode
    BitBlaster<BBNode, BBNodeManagerT>::BBForm(const ASTNode& form, BBNodeSet& support)
    {
      typename map<ASTNode, BBNode>::iterator it = BBFormMemo.find(form);
      if (it != BBFormMemo.end())
        {
        // already there.  Just return it.
        return it->second;
        }

      BBNode result;

      const Kind k = form.GetKind();
      if (!is_Form_kind(k))
        {
        FatalError("BBForm: Illegal kind: ", form);
        }

      //  Not returning until end, and memoizing everything, makes it easier
      // to trace coherently.

      // Various special cases
      switch (k)
        {

      case TRUE:
        {
        result = nf->getTrue();
        break;
        }

      case FALSE:
        {
        result = nf->getFalse();
        break;
        }

      case SYMBOL:
        assert(form.GetType() == BOOLEAN_TYPE);

        result = nf->CreateSymbol(form, 0); // 1 bit symbol.
        break;

      case NOT:
        result = nf->CreateNode(NOT, BBForm(form[0], support));
        break;

      case ITE:
        result = nf->CreateNode(ITE, BBForm(form[0], support), BBForm(form[1], support), BBForm(form[2], support));
        break;

      case AND:
      case OR:
      case NAND:
      case NOR:
      case IFF:
      case XOR:
      case IMPLIES:
        {
        BBNodeVec bbkids; // bit-blasted children (formulas)

        ASTVec::const_iterator kids_end = form.end();
        for (ASTVec::const_iterator it = form.begin(); it != kids_end; it++)
          {
          bbkids.push_back(BBForm(*it, support));
          }
        result = nf->CreateNode(k, bbkids);
        break;
        }

      case EQ:
        {
        const BBNodeVec left = BBTerm(form[0], support);
        const BBNodeVec right = BBTerm(form[1], support);
        assert(left.size() == right.size());

        result = BBEQ(left, right);
        break;
        }

      case BVLE:
      case BVGE:
      case BVGT:
      case BVLT:
      case BVSLE:
      case BVSGE:
      case BVSGT:
      case BVSLT:
        {
        result = BBcompare(form, support);
        break;
        }
      default:
        FatalError("BBForm: Illegal kind: ", form);
        break;
        }

      assert(!result.IsNull());

      if (debug_do_check)
        check(result, form);

      updateForm(form, result, support);

      return (BBFormMemo[form] = result);
    }

// Bit blast a sum of two equal length BVs.
// Update sum vector destructively with new sum.
  template<class BBNode, class BBNodeManagerT>
    void
    BitBlaster<BBNode, BBNodeManagerT>::BBPlus2(BBNodeVec& sum, const BBNodeVec& y, BBNode cin)
    {

      const int bitWidth = sum.size();
      assert(y.size() == (unsigned)bitWidth);
      // Revision 320 avoided creating the nextcin, at I suspect unjustified cost.
      for (int i = 0; i < bitWidth; i++)
        {
        BBNode nextcin = Majority(sum[i], y[i], cin);
        sum[i] = nf->CreateNode(XOR, sum[i], y[i], cin);
        cin = nextcin;
        }
    }

// Stores result - x in result, destructively
  template<class BBNode, class BBNodeManagerT>
    void
    BitBlaster<BBNode, BBNodeManagerT>::BBSub(BBNodeVec& result, const BBNodeVec& y, BBNodeSet& support)
    {
      BBNodeVec compsubtrahend = BBNeg(y);
      BBPlus2(result, compsubtrahend, nf->getTrue());
    }

// Add one bit
  template<class BBNode, class BBNodeManagerT>
    BBNodeVec
    BitBlaster<BBNode, BBNodeManagerT>::BBAddOneBit(const BBNodeVec& x, BBNode cin)
    {
      BBNodeVec result;
      result.reserve(x.size());
      const typename BBNodeVec::const_iterator itend = x.end();
      for (typename BBNodeVec::const_iterator it = x.begin(); it < itend; it++)
        {
        BBNode nextcin = nf->CreateNode(AND, *it, cin);
        result.push_back(nf->CreateNode(XOR, *it, cin));
        cin = nextcin;
        }
      return result;
    }

// Increment bit-blasted vector and return result.
  template<class BBNode, class BBNodeManagerT>
    BBNodeVec
    BitBlaster<BBNode, BBNodeManagerT>::BBInc(const BBNodeVec& x)
    {
      return BBAddOneBit(x, nf->getTrue());
    }

// Return formula for majority function of three bits.
// Pass arguments by reference to reduce refcounting.
  template<class BBNode, class BBNodeManagerT>
    BBNode
    BitBlaster<BBNode, BBNodeManagerT>::Majority(const BBNode& a, const BBNode& b, const BBNode& c)
    {
      // Checking explicitly for constant a, b and c could
      // be more efficient, because they are repeated in the logic.
      if (nf->getTrue() == a)
        {
        return nf->CreateNode(OR, b, c);
        }
      else if (nf->getFalse() == a)
        {
        return nf->CreateNode(AND, b, c);
        }
      else if (nf->getTrue() == b)
        {
        return nf->CreateNode(OR, a, c);
        }
      else if (nf->getFalse() == b)
        {
        return nf->CreateNode(AND, a, c);
        }
      else if (nf->getTrue() == c)
        {
        return nf->CreateNode(OR, a, b);
        }
      else if (nf->getFalse() == c)
        {
        return nf->CreateNode(AND, a, b);
        }
      // there are lots more simplifications, but I'm not sure they're
      // worth doing explicitly (e.g., a = b, a = ~b, etc.)
      else
        {
        return nf->CreateNode(OR, nf->CreateNode(AND, a, b), nf->CreateNode(AND, b, c), nf->CreateNode(AND, a, c));
        }
    }

// Bitwise complement
  template<class BBNode, class BBNodeManagerT>
    BBNodeVec
    BitBlaster<BBNode, BBNodeManagerT>::BBNeg(const BBNodeVec& x)
    {
      BBNodeVec result;
      result.reserve(x.size());
      // Negate each bit.
      const typename BBNodeVec::const_iterator& xend = x.end();
      for (typename BBNodeVec::const_iterator it = x.begin(); it < xend; it++)
        {
        result.push_back(nf->CreateNode(NOT, *it));
        }
      return result;
    }

// Compute unary minus
  template<class BBNode, class BBNodeManagerT>
    BBNodeVec
    BitBlaster<BBNode, BBNodeManagerT>::BBUminus(const BBNodeVec& x)
    {
      BBNodeVec xneg = BBNeg(x);
      return BBInc(xneg);
    }

// AND each bit of vector y with single bit b and return the result.
  template<class BBNode, class BBNodeManagerT>
    BBNodeVec
    BitBlaster<BBNode, BBNodeManagerT>::BBAndBit(const BBNodeVec& y, BBNode b)
    {
      if (nf->getTrue() == b)
        {
        return y;
        }

      BBNodeVec result;
      result.reserve(y.size());

      const typename BBNodeVec::const_iterator yend = y.end();
      for (typename BBNodeVec::const_iterator yit = y.begin(); yit < yend; yit++)
        {
        result.push_back(nf->CreateNode(AND, *yit, b));
        }
      return result;
    }

  typedef enum
  {
    SYMBOL_MT, ZERO_MT, ONE_MT, MINUS_ONE_MT
  } mult_type;

  void
  printP(mult_type* m, int width)
  {
    for (int i = width - 1; i >= 0; i--)
      {
      if (m[i] == SYMBOL_MT)
        cerr << "s";
      else if (m[i] == ZERO_MT)
        cerr << "0";
      else if (m[i] == ONE_MT)
        cerr << "1";
      else if (m[i] == MINUS_ONE_MT)
        cerr << "-1";
      }
  }

  template<class BBNode, class BBNodeManagerT>
    void
    convert(const BBNodeVec& v, BBNodeManagerT*nf, mult_type* result)
    {
      const BBNode& BBTrue = nf->getTrue();
      const BBNode& BBFalse = nf->getFalse();

      for (int i = 0; i < v.size(); i++)
        {
        if (v[i] == BBTrue)
          result[i] = ONE_MT;
        else if (v[i] == BBFalse)
          result[i] = ZERO_MT;
        else
          result[i] = SYMBOL_MT;
        }

      // find runs of ones.
      int lastOne = -1;
      for (int i = 0; i < v.size(); i++)
        {
        assert(result[i] != MINUS_ONE_MT);

        if (result[i] == ONE_MT && lastOne == -1)
          lastOne = i;

        if (result[i] != ONE_MT && lastOne != -1 && (i - lastOne >= 3))
          {
          result[lastOne] = MINUS_ONE_MT;
          for (int j = lastOne + 1; j < i; j++)
            result[j] = ZERO_MT;
          // Should this be lastOne = i?
          lastOne = i;
          result[i] = ONE_MT;
          }
        else if (result[i] != ONE_MT)
          lastOne = -1;
        }

      // finished with a one.
      if (lastOne != -1 && (v.size() - lastOne > 1))
        {
        result[lastOne] = MINUS_ONE_MT;
        for (int j = lastOne + 1; j < v.size(); j++)
          result[j] = ZERO_MT;
        }
    }

// Multiply "multiplier" by y[start ... bitWidth].
  template<class BBNode, class BBNodeManagerT>
    void
    pushP(vector<vector<BBNode> >& products, const int start, const BBNodeVec& y, const BBNode& multiplier, BBNodeManagerT*nf)
    {
      const int bitWidth = y.size();

      int c = 0;
      for (int i = start; i < bitWidth; i++)
        {
        BBNode n = nf->CreateNode(AND, y[c], multiplier);
        if (n != nf->getFalse())
          products[i].push_back(n);
        c++;
        }
    }

  const bool debug_multiply = false;

  /* Cryptominisat2. 5641x5693.smt.   SAT Solving time only!
   * adder_variant1 = true.    Solving: 12.3s, 12.1s
   * adder_variant1 = false.   Solving: 26.5s, 26.0s
   *
   * Cryptominisat2. mult63bit.smt2.
   * adder_variant1 = true.    Solving: 8.1s, 8.2s
   * adder_variant1 = false.   Solving: 11.1s, 11.0s
   *
   * Cryptominisat2. conscram2.smt2.
   * adder_variant1 = true.   Solving:115s, 103s, 303s
   * adder_variant1 = false.  Solving:181s, 471s, 215s
   * */

  template<class BBNode, class BBNodeManagerT>
    BBNodeVec
    BitBlaster<BBNode, BBNodeManagerT>::buildAdditionNetworkResult(vector<list<BBNode> >& products, set<BBNode>& support,
        const ASTNode& n)
    {
      const int bitWidth = n.GetValueWidth();

      // If we have details of the partial products which can be true,
      int ignore = -1;
      simplifier::constantBitP::MultiplicationStats* ms = getMS(n, ignore);
      if (!upper_multiplication_bound)
        ms = NULL;

      BBNodeVec results;
      for (int i = 0; i < bitWidth; i++)
        {

        buildAdditionNetworkResult(products[i], products[i+1], support, (i + 1 == bitWidth), (ms != NULL && (ms->sumH[i] == 0)));

        assert(products[i].size() == 1);
        results.push_back(products[i].back());
        }

      assert(products[bitWidth].size() ==0); // products[bitwidth] is defined but should never be used.
      assert(results.size() == ((unsigned)bitWidth));
      return results;
    }

// Use full adders to create an addition network that adds together each of the
// partial products. Puts the carries into the "to" list.

  template<class BBNode, class BBNodeManagerT>
    void
    BitBlaster<BBNode, BBNodeManagerT>::buildAdditionNetworkResult(list<BBNode>& from, list<BBNode>& to,
        set<BBNode>& support, const bool at_end, const bool all_false)
    {

      while (from.size() >= 2)
        {
        BBNode c;

        if (from.size() == 2)
          c = nf->getFalse();
        else
          {
          c = from.back();
          from.pop_back();
          }

        const BBNode a = from.back();
        from.pop_back();
        const BBNode b = from.back();
        from.pop_back();

        // Nothing can be true. All must be false.
        if (conjoin_to_top && all_false)
          {
          if (BBFalse != a)
            support.insert(nf->CreateNode(NOT, a));
          if (BBFalse != b)
            support.insert(nf->CreateNode(NOT, b));
          if (BBFalse != c)
            support.insert(nf->CreateNode(NOT, c));
          continue;
          }

        BBNode carry, sum;

        if (adder_variant)
          {
          carry = Majority(a, b, c);
          sum = nf->CreateNode(XOR, a, b, c);
          }
        else
          {
          carry = nf->CreateNode(OR, nf->CreateNode(AND, a, b), nf->CreateNode(AND, b, c), nf->CreateNode(AND, a, c));
          sum = nf->CreateNode(XOR, nf->CreateNode(XOR, c, b), a);
          }

        if (debug_multiply)
          {
          cerr << "a" << a;
          cerr << "b" << b;
          cerr << "c" << c;
          cerr << "Carry" << carry;
          cerr << "Sum" << sum;
          }

        from.push_back(sum);

        if (!at_end && carry != BBFalse)
          to.push_back(carry);

        }
      if (0 == from.size())
        from.push_back(BBFalse);

      assert(1==from.size());
    }

  const bool debug_bounds = false;

  template<class BBNode, class BBNodeManagerT>
    bool
    BitBlaster<BBNode, BBNodeManagerT>::statsFound(const ASTNode& n)
    {
      if (NULL == cb)
        return false;

      if (NULL == cb->msm)
        return false;

      if (booth_recoded.find(n) != booth_recoded.end()) // Sums are wrong for recoded.
        return false;

      simplifier::constantBitP::MultiplicationStatsMap::NodeToStats::const_iterator it;
      it = cb->msm->map.find(n);
      return (it != cb->msm->map.end());
    }

// Make sure x and y are the parameters in the correct order. THIS ISNT COMMUTATIVE.
  template<class BBNode, class BBNodeManagerT>
    BBNodeVec
    BitBlaster<BBNode, BBNodeManagerT>::multWithBounds(const ASTNode&n, vector<list<BBNode> >& products,
        BBNodeSet& toConjoinToTop)
    {
      const int bitWidth = n.GetValueWidth();

      int ignored=0;
      assert(upper_multiplication_bound);
      simplifier::constantBitP::MultiplicationStats& ms = *getMS(n, ignored);



      // If all of the partial products in the column must be zero, then replace
      for (int i = 0; i < bitWidth; i++)
        {
        if (conjoin_to_top && ms.columnH[i] == 0)
          {
          while (products[i].size() > 0)
            {
            BBNode c = products[i].back(); // DONT take a reference of the back().
            products[i].pop_back();
            toConjoinToTop.insert(nf->CreateNode(NOT, c));
            }
          products[i].push_back(nf->getFalse());
          }
        }

      BBNodeVec result;

      if (debug_bounds)
        {
        ms.print();
        }

      vector<BBNode> prior;
      for (int i = 0; i < bitWidth; i++)
        {
        if (debug_bounds)
          {
          cerr << "  " << products[i].size();
          cerr << "[" << ms.columnL[i] << ":" << ms.columnH[i] << "][" << ms.sumL[i] << ":" << ms.sumH[i] << "]";
          }

          vector<BBNode> output;

          mult_BubbleSorterWithBounds(toConjoinToTop, products[i], output, prior, ms.sumL[i], ms.sumH[i]);
          prior = output;

        assert(products[i].size() == 1);
        result.push_back(products[i].back());
        }

      if (debug_bitblaster)
        cerr << endl << endl;

      assert(result.size() == ((unsigned)bitWidth));
      return result;
    }

  template<class BBNode, class BBNodeManagerT>
    void
    BitBlaster<BBNode, BBNodeManagerT>::mult_Booth(const BBNodeVec& x_i, const BBNodeVec& y_i, BBNodeSet& support,
        const ASTNode& xN, const ASTNode& yN, vector<list<BBNode> >& products, const ASTNode& n)
    {
      const int bitWidth = x_i.size();
      assert(x_i.size() == y_i.size());

      const BBNodeVec& x = x_i;
      const BBNodeVec& y = y_i;

      const BBNode& BBTrue = nf->getTrue();
      const BBNode& BBFalse = nf->getFalse();

      for (int i = 0; i < bitWidth; i++)
        {
        assert(products[i].size() == 0);
        }

      BBNodeVec notY;
      for (int i = 0; i < y.size(); i++)
        {
        notY.push_back(nf->CreateNode(NOT, y[i]));
        }

      mult_type xt[x.size()];
      convert(x, nf, xt);

      if (debug_multiply)
        {
        cerr << "--------" << endl;
        cerr << "x:";
        printP(xt, x.size());
        cerr << xN << endl;
        }

      mult_type yt[x.size()];
      convert(y, nf, yt);

      if (debug_multiply)
        {
        cerr << "y:";
        printP(yt, y.size());
        cerr << yN << endl;
        }

      // We store them into here before sorting them.
      vector<vector<BBNode> > t_products(bitWidth);

      for (int i = 0; i < bitWidth; i++)
        {
        if (x[i] != BBTrue && x[i] != BBFalse)
          {
          pushP(t_products, i, y, x[i], nf);
          }

        // A bit can not be true or false, as well as one of these two.
        if (xt[i] == MINUS_ONE_MT)
          {
          pushP(t_products, i, notY, BBTrue, nf);
          t_products[i].push_back(BBTrue);
          booth_recoded.insert(n);
          }

        else if (xt[i] == ONE_MT)
          {
          pushP(t_products, i, y, BBTrue, nf);
          }

        if (t_products[i].size() == 0)
          t_products[i].push_back(BBFalse);

        sort(t_products[i].begin(), t_products[i].end());
        for (int j = 0; j < t_products[i].size(); j++)
          products[i].push_back(t_products[i][j]);
        }
    }

// Uses addition networks explicitly.
// I've copied this in from my the "trevor" branch r482.
// I've not measured if this is better than the current variant.
  template<class BBNode, class BBNodeManagerT>
    void
    BitBlaster<BBNode, BBNodeManagerT>::mult_allPairs(const BBNodeVec& x, const BBNodeVec& y, BBNodeSet& support,
        vector<list<BBNode> >& products)
    {
      // Make a table of partial products.
      const int bitWidth = x.size();
      assert(x.size() == y.size());
      assert(bitWidth > 0);

      for (int i = 0; i < bitWidth; i++)
        {
        assert(!x[i].IsNull());
        assert(!y[i].IsNull());
        }

      for (int i = 0; i < bitWidth; i++)
        {
        for (int j = 0; j <= i; j++)
          {
          BBNode n = nf->CreateNode(AND, x[i - j], y[j]);

          if (n != nf->getFalse())
            products[i].push_back(n);
          }

        if (0 == products[i].size())
          products[i].push_back(nf->getFalse());

        }
    }

  template<class BBNode, class BBNodeManagerT>
    MultiplicationStats*
    BitBlaster<BBNode, BBNodeManagerT>::getMS(const ASTNode&n, int& highestZero)
    {
      MultiplicationStats * ms;
      highestZero = -1;

      if (statsFound(n))
        {
        simplifier::constantBitP::MultiplicationStatsMap::NodeToStats::iterator it;
        it = cb->msm->map.find(n);
        if (it != cb->msm->map.end())
          {
          ms = &(it->second);

          assert(ms->x.getWidth() == ms->y.getWidth());
          assert(ms->r.getWidth() == ms->y.getWidth());
          assert(ms->r.getWidth() == (int)ms->bitWidth);
          }

        for (int i = 0; i < n.GetValueWidth(); i++)
          if (ms->sumH[i] == 0)
            highestZero = i;

        return ms;
        }

      return NULL;
    }

  // Each bit of 'x' is taken in turn and multiplied by a shifted y.
  template<class BBNode, class BBNodeManagerT>
    BBNodeVec
    BitBlaster<BBNode, BBNodeManagerT>::mult_normal(const BBNodeVec& x, const BBNodeVec& y, BBNodeSet& support,
        const ASTNode&n)
    {
      const int bitWidth = n.GetValueWidth();

      // If we have details of the partial products which can be true,
      int highestZero = -1;
      const simplifier::constantBitP::MultiplicationStats* ms = getMS(n, highestZero);
      if (!upper_multiplication_bound)
        ms = NULL;

      BBNodeVec ycopy(y);

      BBNodeVec prod = BBNodeVec(BBAndBit(y, *x.begin()));       // start prod with first partial product.

      for (int i = 1; i < bitWidth; i++)       // start loop at next bit.
        {
        const BBNode& xit = x[i];

        // shift first
        BBLShift(ycopy, 1);

        if (nf->getFalse() == xit)
          {
          // If this bit is zero, the partial product will
          // be zero.  No reason to add that in.
          continue;
          }

        BBNodeVec pprod = BBAndBit(ycopy, xit);

        // Iterate through from the current location upwards, setting anything to zero that can be..
        if (ms != NULL && highestZero >= i)
          {
          for (int column = i; column <= highestZero; column++)
            {
            if (ms->sumH[column] == 0 && (nf->getFalse() != prod[column]))
              {
              support.insert(nf->CreateNode(NOT, prod[column]));
              prod[column] = BBFalse;
              }
            }
          }

        BBPlus2(prod, pprod, nf->getFalse());
        }
      return prod;
    }

  // assumes the prior column is sorted.
  template<class BBNode, class BBNodeManagerT>
    void
    BitBlaster<BBNode, BBNodeManagerT>::mult_BubbleSorterWithBounds(BBNodeSet& support, list<BBNode>& current,
        vector<BBNode>& currentSorted, vector<BBNode>& priorSorted, const int minTrue, const int maxTrue)
    {

      // Add the carry from the prior column. i.e. each second sorted formula.
      for (int k = 1; k < priorSorted.size(); k += 2)
        {
        current.push_back(priorSorted[k]);
        }

      const int height = current.size();

      // Set the current sorted to all false.
      currentSorted.clear();
        {
        vector<BBNode> temp(height, nf->getFalse());
        currentSorted = temp;
        }

      // n^2 sorting network.
      for (int l = 0; l < height; l++)
        {
        vector<BBNode> oldSorted(currentSorted);
        BBNode c = current.back();
        current.pop_back();
        currentSorted[0] = nf->CreateNode(OR, oldSorted[0], c);

        for (int j = 1; j <= l; j++)
          {
          currentSorted[j] = nf->CreateNode(OR, nf->CreateNode(AND, oldSorted[j - 1], c), oldSorted[j]);
          }
        }

      assert(current.size() == 0);

      for (int k = 0; k < height; k++)
        assert(!currentSorted[k].IsNull());

      if (conjoin_to_top)
        {
        for (int j = 0; j < minTrue; j++)
          {
          support.insert(currentSorted[j]);
          currentSorted[j] = BBTrue;
          }

        for (int j = height - 1; j >= maxTrue; j--)
          {
          support.insert(nf->CreateNode(NOT, currentSorted[j]));
          currentSorted[j] = BBFalse;
          }
        }

      BBNode resultNode = nf->getFalse();

      // Constrain to equal the result
      for (int k = 1; k < height; k += 2)
        {
        BBNode part = nf->CreateNode(AND, nf->CreateNode(NOT, currentSorted[k]), currentSorted[k - 1]);
        resultNode = nf->CreateNode(OR, resultNode, part);
        }

      // constraint the all '1's case.
      if (height % 2 == 1)
        resultNode = nf->CreateNode(OR, resultNode, currentSorted.at(height - 1));

      current.push_back(resultNode);
    }

// If a bit has a fixed value, then it should equal BBTrue or BBFalse in the input vectors.
  template<class BBNode, class BBNodeManagerT>
    void
    BitBlaster<BBNode, BBNodeManagerT>::checkFixed(const BBNodeVec& v, const ASTNode& n)
    {
      if (cb == NULL)
        return;

      if (cb->isUnsatisfiable())
        return;

      if (cb->fixedMap->map->find(n) != cb->fixedMap->map->end())
        {
        FixedBits* b = cb->fixedMap->map->find(n)->second;
        for (int i = 0; i < b->getWidth(); i++)
          {
          if (b->isFixed(i))
            if (b->getValue(i))
              {
              assert(v[i]== BBTrue);
              }
            else
              {
              if (v[i] != BBFalse)
                {
                cerr << *b;
                cerr << i << endl;
                cerr << n;
                cerr << (v[i] == BBTrue) << endl;
                }

              assert(v[i]== BBFalse);
              }
          }
        }
    }

  // If it's not booth encoded, and the column sum is zero,
  // then set that all the partial products must be zero.
  // For this to do anything constant bit propagation must be
  // turned on, and upper_multiplication_bound must be set.
  template<class BBNode, class BBNodeManagerT>
    void
    BitBlaster<BBNode, BBNodeManagerT>::setColumnsToZero(vector<list<BBNode> >& products, set<BBNode>& support,
        const ASTNode&n)
    {
      const int bitWidth = n.GetValueWidth();

      // If we have details of the partial products which can be true,
      int highestZero = -1;
      simplifier::constantBitP::MultiplicationStats* ms = getMS(n, highestZero);
      if (!upper_multiplication_bound)
        ms = NULL;

      if (ms == NULL)
        return;

      for (int i = 0; i < bitWidth; i++)
        {
        if (ms->sumH[i] == 0)
          {
          while (products[i].size() > 0)
            {
            BBNode curr = products[i].back();
            products[i].pop_back();

            if (BBFalse == curr)
              continue;

            support.insert(nf->CreateNode(NOT, curr));
            }
          products[i].push_back(BBFalse);

          }
        }
    }


// Multiply two bitblasted numbers
  template<class BBNode, class BBNodeManagerT>
    BBNodeVec
    BitBlaster<BBNode, BBNodeManagerT>::BBMult(const BBNodeVec& _x, const BBNodeVec& _y, BBNodeSet& support,
        const ASTNode& n)
    {

      if (uf->isSet("print_on_mult", "0"))
        cerr << "--mult--";

      BBNodeVec x = _x;
      BBNodeVec y = _y;

      if ((BVCONST != n[0].GetKind()) && (BVCONST == n[1].GetKind()))
        {
        x = _y;
        y = _x;
        }

      const int bitWidth = n.GetValueWidth();
      assert(x.size() == bitWidth);
      assert(y.size() == bitWidth);

      std::vector<list<BBNode> > products(bitWidth+1); // Create one extra to avoid special cases.

      if (multiplication_variant == "1")
        {
        return mult_normal(x, y, support, n);
        }
      //else if (multiplication_variant == "2")
        // V2 used to be V3 with normal rather than booth recoding.
        // To recreate V2, use V3 and turn off Booth recoding.
      else if (multiplication_variant == "3")
        {
        mult_Booth(_x, _y, support, n[0], n[1], products, n);
        setColumnsToZero(products,support,n);
        return buildAdditionNetworkResult(products, support, n);
        }
      else if (multiplication_variant == "4")
        {
        //cerr << "v4";
        mult_Booth(_x, _y, support, n[0], n[1], products, n);
        vector<BBNode> prior;

        for (int i = 0; i < bitWidth; i++)
          {
          vector<BBNode> output;
          mult_BubbleSorterWithBounds(support, products[i], output, prior);
          prior = output;
          assert(products[i].size() == 1);
          }
        return buildAdditionNetworkResult(products, support, n);
        }
      else if (multiplication_variant == "5")
              {
              if (!statsFound(n) || !upper_multiplication_bound)
                {
                mult_Booth(_x, _y, support, n[0], n[1], products, n);
                setColumnsToZero(products,support,n);
                return buildAdditionNetworkResult(products, support, n);
                }


        mult_allPairs(x, y, support, products);
        setColumnsToZero(products,support,n);
        return multWithBounds(n, products, support);
        }
      else if (multiplication_variant == "6")
        {
          mult_Booth(_x, _y, support,n[0],n[1],products,n);
          setColumnsToZero(products,support,n);
          return v6(products, support, n);
        }
      else if (multiplication_variant == "7")
        {
        mult_Booth(_x, _y, support, n[0], n[1], products,n);
        setColumnsToZero(products,support,n);
        return v7(products, support, n);
        }
      else if (multiplication_variant == "8")
        {
        mult_Booth(_x, _y, support, n[0], n[1], products,n);
        setColumnsToZero(products,support,n);
        return v8(products, support, n);
        }
      else if (multiplication_variant == "9")
        {
        mult_Booth(_x, _y, support, n[0], n[1], products,n);
        setColumnsToZero(products,support,n);
        return v9(products, support,n);
        }
      else if (multiplication_variant == "13")
        {
        mult_Booth(_x, _y, support, n[0], n[1], products,n);
        setColumnsToZero(products,support,n);
        return v13(products, support,n);
        }
      else
        {
        cerr << "Unk variant" << multiplication_variant;
        FatalError("sda44f");
        }

    }

  // Takes an unsorted array, and returns a sorted array.
  template <class BBNode, class BBNodeManagerT>
  BBNodeVec BitBlaster<BBNode,BBNodeManagerT>::batcher(const vector<BBNode>& in)
  {
    assert(in.size() != 0);

    if (in.size() ==1)
      return in;

    vector<BBNode> a;
    vector<BBNode> b;

    // half way rounded up.
    const int halfWay = (((in.size()%2)==0? 0:1) + (in.size()/2) );
    for (int i =0; i < halfWay;i++)
        a.push_back(in[i]);

    for (int i =halfWay; i < in.size();i++)
        b.push_back(in[i]);

    assert(a.size() >= b.size());
    assert(a.size() + b.size() == in.size());
    vector <BBNode> result=  mergeSorted(batcher(a), batcher(b));

    for (int k = 0; k < result.size(); k++)
      assert(!result[k].IsNull());

    assert(result.size() == in.size());
    return result;
  }



  // assumes that the prior column is sorted.
  template<class BBNode, class BBNodeManagerT>
    void
    BitBlaster<BBNode, BBNodeManagerT>::sortingNetworkAdd(BBNodeSet& support, list<BBNode>& current, vector<BBNode>& currentSorted,
        vector<BBNode>& priorSorted)
    {

      vector<BBNode> toSort;

      // convert the list to a vector.
      while (current.size() != 0)
        {
        BBNode currentN = current.front();
        assert(!currentN.IsNull());
        toSort.push_back(currentN);
        current.pop_front();
        }

      vector<BBNode> sorted = batcher(toSort);

      assert(sorted.size() == toSort.size());

      vector<BBNode> sortedCarryIn;
      for (int k = 1; k < priorSorted.size(); k += 2)
        {
        sortedCarryIn.push_back(priorSorted[k]);
        }

      if (sorted.size() >= sortedCarryIn.size())
        currentSorted = mergeSorted(sorted, sortedCarryIn);
      else
        currentSorted = mergeSorted(sortedCarryIn, sorted);

      assert(currentSorted.size() == sortedCarryIn.size() + toSort.size());
      int height = currentSorted.size();

      assert(current.size() == 0);

      for (int k = 0; k < height; k++)
        assert(!currentSorted[k].IsNull());

      BBNode resultNode = nf->getFalse();

      // Constrain to equal the result
      for (int k = 1; k < height; k += 2)
        {
        BBNode part = nf->CreateNode(AND, nf->CreateNode(NOT, currentSorted[k]), currentSorted[k - 1]);
        resultNode = nf->CreateNode(OR, resultNode, part);
        }

      // constraint the all '1's case.
      if (height % 2 == 1)
        resultNode = nf->CreateNode(OR, resultNode, currentSorted.at(height - 1));

      current.push_back(resultNode);
    }

  template<class BBNode, class BBNodeManagerT>
  BBNodeVec
  BitBlaster<BBNode, BBNodeManagerT>::v6(vector<list<BBNode> >& products, set<BBNode>& support,  const ASTNode&n)
  {
    const int bitWidth = n.GetValueWidth();

  vector<BBNode> prior;

  for (int i = 0; i < bitWidth; i++)
    {
        vector<BBNode> output;
        sortingNetworkAdd(support,  products[i], output ,prior);
        prior = output;
        assert(products[i].size() == 1);
    }

  // This converts the array of lists to a vector.
  return buildAdditionNetworkResult(products ,support, n);
  }

  template<class BBNode, class BBNodeManagerT>
    BBNodeVec
    BitBlaster<BBNode, BBNodeManagerT>::v13(vector<list<BBNode> >& products, set<BBNode>& support, const ASTNode&n)
    {
      const int bitWidth = n.GetValueWidth();

      int ignore = -1;
      simplifier::constantBitP::MultiplicationStats* ms = getMS(n, ignore);
      if (!upper_multiplication_bound)
        ms = NULL;

      bool done = false;

      vector<BBNode> a(bitWidth);
      vector<BBNode> b(bitWidth);

      while (!done)
        {
        done = true;

        for (int i = 0; i < bitWidth; i++)
          {
          if (products[i].size() > 2)
            done = false;
          if (products[i].size() > 0)
            {
            a[i] = products[i].back();
            products[i].pop_back();
            }
          else
            a[i] = BBFalse;

          if (products[i].size() > 0)
            {
            b[i] = products[i].back();
            products[i].pop_back();
            }
          else
            b[i] = BBFalse;

          if (ms != NULL && ms->sumH[i] == 0)
            {
            if (a[i] != BBFalse)
              {
              support.insert(nf->CreateNode(NOT, a[i]));
              a[i] = BBFalse;
              }

            if (b[i] != BBFalse)
              {
              support.insert(nf->CreateNode(NOT, b[i]));
              b[i] = BBFalse;
              }
            }assert(!a[i].IsNull());
          assert(!b[i].IsNull());

          }
        BBPlus2(a, b, BBFalse);
        for (int i = 0; i < bitWidth; i++)
          products[i].push_back(a[i]);
        }

      BBNodeVec results;
      for (int i = 0; i < bitWidth; i++)
        {
        assert(products[i].size() ==1);
        results.push_back(products[i].back());
        }

      assert(results.size() == ((unsigned)bitWidth));
      return results;
    }



  // Sorting network that delivers carries directly to the correct column.
  // For instance, if there are 6 true in a column, then a carry will flow to column+1, and column+2.
  template<class BBNode, class BBNodeManagerT>
    BBNodeVec
    BitBlaster<BBNode, BBNodeManagerT>::v9(vector<list<BBNode> >& products, set<BBNode>& support,const ASTNode&n)
    {
    const int bitWidth = n.GetValueWidth();

    vector< vector< BBNode> > toAdd(bitWidth);

    for (int column = 0; column < bitWidth; column++)
      {
          vector<BBNode> sorted; // The current column (sorted) gets put into here.
          vector<BBNode> prior; // Prior is always empty in this..

          const int size=  products[column].size();
          sortingNetworkAdd(support,  products[column], sorted ,prior);

          assert(products[column].size() == 1);
          assert(sorted.size() == size);

          for (int k = 2; k <= sorted.size(); k++)
            {
              BBNode part;
              if (k==sorted.size())
                part = sorted[k - 1];
              else
                {
                // We expect the 1's to be sorted first.
                assert((sorted[k-1] != BBFalse) || (sorted[k] != BBTrue));
                part = nf->CreateNode(AND, nf->CreateNode(NOT, sorted[k]), sorted[k - 1]);

                if (part == BBFalse)
                  continue; // shortcut.
                }

              int position =k;
              int increment =1;
              while (position != 0)
                {
                  if (column+increment >= bitWidth)
                    break;

                  position >>=1;
                  if ((position &  1) !=0) // bit is set.
                          toAdd[column+increment].push_back(part);

                  increment++;
                }
            }

          for (int carry_column =column+1; carry_column < bitWidth; carry_column++)
            {
              if (toAdd[carry_column].size() ==0)
                continue ;
              BBNode disjunct = BBFalse;
              for (int l = 0; l < toAdd[carry_column].size();l++)
                    {
                        disjunct = nf->CreateNode(OR,disjunct,toAdd[carry_column][l]);
                    }

              if(disjunct != BBFalse)
                products[carry_column].push_back(disjunct);
              toAdd[carry_column].clear();
            }
      }
    for (int i = 0; i < bitWidth; i++)
      {
        assert(toAdd[i].size() == 0);
      }

    // This converts the array of lists to a vector.
    return buildAdditionNetworkResult(products ,support, n);
    }


  template<class BBNode, class BBNodeManagerT>
  BBNodeVec
  BitBlaster<BBNode, BBNodeManagerT>::v7(vector<list<BBNode> >& products, set<BBNode>& support, const ASTNode&n)
  {
    const int bitWidth = n.GetValueWidth();

    // If we have details of the partial products which can be true,
    int ignore = -1;
    simplifier::constantBitP::MultiplicationStats* ms = getMS(n, ignore);
    if (!upper_multiplication_bound)
      ms = NULL;


      std::vector<list<BBNode> > later(bitWidth+1);
      std::vector<list<BBNode> > next(bitWidth+1);

      for (int i = 0; i < bitWidth; i++)
          {
              next[i+1].clear();
              buildAdditionNetworkResult(products[i], next[i + 1], support, bitWidth == i+1, (ms!=NULL && (ms->sumH[i]==0)));

              // Calculate the carries of carries.
              for (int j = i + 1; j < bitWidth; j++)
                  {
                      if (next[j].size() == 0)
                          break;

                      next[j+1].clear();
                      buildAdditionNetworkResult(next[j], next[j + 1], support, bitWidth == j+1, false);
                  }

              // Put the carries of the carries away until later.
              for (int j = i + 1; j < bitWidth; j++)
                  {
                      if (next[j].size() == 0)
                          break;

                      assert(next[j].size() <=1);
                      later[j].push_back(next[j].back());
                  }
          }


      for (int i = 0; i < bitWidth; i++)
      {
              // Copy all the laters into products
              while(later[i].size() > 0)
              {
                      products[i].push_front(later[i].front());
                      later[i].pop_front();
              }
      }

      BBNodeVec results;
      for (int i = 0; i < bitWidth; i++)
      {

              buildAdditionNetworkResult((products[i]), (products[i + 1]), support, bitWidth == i+1, false);


          results.push_back(products[i].back());
          products[i].pop_back();
      }

      assert(results.size() == ((unsigned)bitWidth));
      return results;
  }


  template<class BBNode, class BBNodeManagerT>
  BBNodeVec
  BitBlaster<BBNode, BBNodeManagerT>::v8(vector<list<BBNode> >& products, set<BBNode>& support, const ASTNode&n)
  {
    const int bitWidth = n.GetValueWidth();

    // If we have details of the partial products which can be true,
    int ignore = -1;
    simplifier::constantBitP::MultiplicationStats* ms = getMS(n, ignore);
    if (!upper_multiplication_bound)
      ms = NULL;



      std::vector<list<BBNode> > later(bitWidth+1); // +1 then ignore the topmost.
      std::vector<list<BBNode> > next(bitWidth+1);

      for (int i = 0; i < bitWidth; i++)
          {
              // Put all the products into next.
              next[i+1].clear();
              buildAdditionNetworkResult((products[i]), (next[i + 1]), support, i+1 ==bitWidth, (ms!=NULL && (ms->sumH[i]==0)));

              // Calculate the carries of carries.
              for (int j = i + 1; j < bitWidth; j++)
                  {
                      if (next[j].size() == 0)
                          break;

                      next[j+1].clear();
                      buildAdditionNetworkResult(next[j], next[j + 1], support, j+1 ==bitWidth, false);
                  }

              // Put the carries of the carries away until later.
              for (int j = i + 1; j < bitWidth; j++)
                  {
                      if (next[j].size() == 0)
                          break;

                      assert(next[j].size() <=1);
                      later[j].push_back(next[j].back());
                  }
          }


      for (int i = 0; i < bitWidth; i++)
      {
              // Copy all the laters into products
              while(later[i].size() > 0)
              {
                      products[i].push_back(later[i].back());
                      later[i].pop_back();
              }
      }

      BBNodeVec results;
      for (int i = 0; i < bitWidth; i++)
      {
          buildAdditionNetworkResult(products[i], products[i + 1], support, i+1 ==bitWidth, false);
          results.push_back(products[i].back());
          products[i].pop_back();
      }

      assert(results.size() == ((unsigned)bitWidth));
      return results;
  }


  // compare element 1 with 2, 3 with 4, and so on.
  template<class BBNode, class BBNodeManagerT>
  vector<BBNode>
  BitBlaster<BBNode, BBNodeManagerT>::  compareOddEven(const vector<BBNode>& in)
    {
      vector<BBNode> result(in);

      for (int i = 2; i < in.size(); i =i+ 2)
        {
            BBNode a = in[i-1];
            BBNode b = in[i];
            //comparators++;
            result[i-1] = nf->CreateNode(OR,a,b);
            result[i] = nf->CreateNode(AND,a,b);
        }
      return result;
    }


  template<class BBNode, class BBNodeManagerT>
  vector<BBNode>
  BitBlaster<BBNode, BBNodeManagerT>::mergeSorted(const vector<BBNode>& in1, const vector<BBNode>& in2)
    {

    assert(in1.size() >= in2.size());
    assert(in1.size() >0);

    vector <BBNode>result;

      if (in2.size() ==0)
        {
          result = in1;
        }
      else if (in1.size() == 1 && in2.size() ==1)
      {
          //comparators++;
          result.push_back(nf->CreateNode(OR,in1[0], in2[0]));
          result.push_back(nf->CreateNode(AND,in1[0], in2[0]));

      }
      else
        {
          vector <BBNode> evenL;
          vector <BBNode> oddL;
          for (int i =0; i < in1.size();i++)
            {
                if (i%2 ==0)
                  evenL.push_back(in1[i]);
                else
                  oddL.push_back(in1[i]);
            }

          vector <BBNode> evenR;  // Take the even of each.
          vector <BBNode> oddR;   // Take the odd of each
            for (int i =0; i < in2.size();i++)
              {
                  if (i%2 ==0)
                    evenR.push_back(in2[i]);
                  else
                    oddR.push_back(in2[i]);
              }

            vector <BBNode> even = evenL.size()< evenR.size() ? mergeSorted(evenR,evenL) : mergeSorted(evenL,evenR);
            vector <BBNode> odd = oddL.size() < oddR.size() ? mergeSorted(oddR,oddL) : mergeSorted(oddL,oddR);

            for (int i =0; i < std::max(even.size(),odd.size());i++)
              {
                if (even.size() > i)
                  result.push_back(even[i]);

                if (odd.size() > i)
                  result.push_back(odd[i]);
              }
          result = compareOddEven(result);
        }

      assert(result.size() == in1.size() + in2.size());
      return result;

    }



// All combinations of division_variant_1, _2, _3
  /* on factoring12bitsx12.cvc with MINISAT2.
   000:    0m2.764s
   001:    0m4.060s
   010:    0m2.750s
   011:    0m4.173s
   100:    0m3.064s
   101:    0m3.217s
   110:    0m3.064s
   111:    0m3.230s
   */

// This implements a variant of binary long division.
// q and r are "out" parameters.  rwidth puts a bound on the
// recursion depth.
  template<class BBNode, class BBNodeManagerT>
    void
    BitBlaster<BBNode, BBNodeManagerT>::BBDivMod(const BBNodeVec &y, const BBNodeVec &x, BBNodeVec &q, BBNodeVec &r,
        unsigned int rwidth, BBNodeSet& support)
    {
      const unsigned int width = y.size();
      const BBNodeVec zero = BBfill(width, nf->getFalse());
      BBNodeVec one = zero;
      one[0] = nf->getTrue();

      // check if y is already zero.
      bool isZero = true;
      for (int i = 0; i < rwidth; i++)
        if (y[i] != nf->getFalse())
          {
          isZero = false;
          break;
          }

      if (isZero || rwidth == 0)
        {
        // When we have shifted the entire width, y is guaranteed to be 0.
        q = zero;
        r = zero;
        }
      else
        {
        BBNodeVec q1, r1;
        BBNodeVec yrshift1(y);
        BBRShift(yrshift1, 1);

        // recursively divide y/2 by x.
        BBDivMod(yrshift1, x, q1, r1, rwidth - 1, support);

        BBNodeVec q1lshift1(q1);
        BBLShift(q1lshift1, 1);

        BBNodeVec r1lshift1(r1);
        BBLShift(r1lshift1, 1);

        BBNodeVec r1lshift1plusyodd(r1lshift1);
        r1lshift1plusyodd[0] = y[0];

        // By extending rminusx by one bit, we can use that top-bit
        // to check whether r>=x. We need to compute rminusx anyway,
        // so this saves having a separate compare circut.
        BBNodeVec rminusx(r1lshift1plusyodd);
        rminusx.push_back(nf->getFalse());
        BBNodeVec xCopy(x);
        xCopy.push_back(nf->getFalse());
        BBSub(rminusx, xCopy, support);
        BBNode sign = rminusx[width];
        rminusx.pop_back();

        // Adjusted q, r values when when r is too large.
        //q1lshift1 has zero in the least significant digit.
        //BBNodeVec ygtrxqval = BBITE(sign, q1lshift1, BBInc(q1lshift1));
        q1lshift1[0] = nf->CreateNode(NOT, sign);
        BBNodeVec ygtrxrval = BBITE(sign, r1lshift1plusyodd, rminusx);

        BBNodeVec notylessxqval;
        BBNodeVec notylessxrval;

        /* variant_1 removes the equality check of (x=y). When we get to here I think
         that r and q already have the proper values.
         Let x =y, so we are solving y/y.
         As a first step solve (y/2)/y.
         If y != 0, then y/2 < y. (strictly less than).
         By the last rule in this block, that will return q=0, r=(y/2)
         On return, that will be rightshifted, and the parity bit added back,
         giving q = 0, r=y.
         By the immediately preceeding rule, 0 <= 0 is true, so q becomes 1,
         and r becomes 0.
         So q and r are already set correctly when we get here.

         If y=0 & x=0, then (y/2)/0 will return q=0, r=0.
         By the preceeding rule  0 <= 0 is true, so q =1, r=0.
         So q and r are already set correctly when we get here.
         */

        if (division_variant_1)
          {
          notylessxqval = q1lshift1;
          notylessxrval = ygtrxrval;
          }
        else
          {
          // q & r values when y >= x
          BBNode yeqx = BBEQ(y, x);
          // *** Problem: the bbfill for qval is wrong.  Should be 1, not -1.
          notylessxqval = BBITE(yeqx, one, q1lshift1);
          notylessxrval = BBITE(yeqx, zero, ygtrxrval);
          }

        /****************/
        BBNode ylessx;
        if (division_variant_2)
          {
          ylessx = BBBVLE(y, x, false, true);
          }
        else
          {
          // y < x <=> not x >= y.
          ylessx = nf->CreateNode(NOT, BBBVLE(x, y, false));
          }

        if (division_variant_3)
          {
          q = notylessxqval;
          r = notylessxrval;
          }
        else
          {
          // This variant often helps somehow. I don't know why.
          // Even though it uses more memory..
          q = BBITE(ylessx, zero, notylessxqval);
          r = BBITE(ylessx, y, notylessxrval);
          }
        }
    }

// build ITE's (ITE cond then[i] else[i]) for each i.
  template<class BBNode, class BBNodeManagerT>
    BBNodeVec
    BitBlaster<BBNode, BBNodeManagerT>::BBITE(const BBNode& cond, const BBNodeVec& thn, const BBNodeVec& els)
    {
      // Fast exits.
      if (cond == nf->getTrue())
        {
        return thn;
        }
      else if (cond == nf->getFalse())
        {
        return els;
        }

      BBNodeVec result;
      result.reserve(els.size());
      const typename BBNodeVec::const_iterator th_it_end = thn.end();
      typename BBNodeVec::const_iterator el_it = els.begin();
      for (typename BBNodeVec::const_iterator th_it = thn.begin(); th_it < th_it_end; th_it++, el_it++)
        {
        result.push_back(nf->CreateNode(ITE, cond, *th_it, *el_it));
        }
      return result;
    }

//  smt-test/transitive400.smt2
// Minisat 2:  bbbvle_variant = true. 8 ms
// Minisat 2:  bbbvle_variant = false. 577 ms

// Workhorse for comparison routines.  This does a signed BVLE if is_signed
// is true, else it's unsigned.  All other comparison operators can be reduced
// to this by swapping args or complementing the result bit.
  template<class BBNode, class BBNodeManagerT>
    BBNode
    BitBlaster<BBNode, BBNodeManagerT>::BBBVLE(const BBNodeVec& left, const BBNodeVec& right, bool is_signed,
        bool is_bvlt)
    {
      if (bbbvle_variant)
        return BBBVLE_variant1(left, right, is_signed, is_bvlt);
      else
        return BBBVLE_variant2(left, right, is_signed, is_bvlt);
    }

  template<class BBNode, class BBNodeManagerT>
    BBNode
    BitBlaster<BBNode, BBNodeManagerT>::BBBVLE_variant1(const BBNodeVec& left_, const BBNodeVec& right_, bool is_signed,
        bool is_bvlt)
    {
      const BBNodeVec& left = !is_bvlt ? left_ : right_;
      const BBNodeVec& right = !is_bvlt ? right_ : left_;

      // "thisbit" represents BVLE of the suffixes of the BVs
      // from that position .  if R < L, return TRUE, else if L < R
      // return FALSE, else return BVLE of lower-order bits.  MSB is
      // treated separately, because signed comparison is done by
      // complementing the MSB of each BV, then doing an unsigned
      // comparison.
      typename BBNodeVec::const_iterator lit = left.begin();
      typename BBNodeVec::const_iterator litend = left.end();
      typename BBNodeVec::const_iterator rit = right.begin();
      BBNode prevbit = nf->getTrue();
      for (; lit < litend - 1; lit++, rit++)
        {
        BBNode thisbit = nf->CreateNode(ITE, nf->CreateNode(IFF, *rit, *lit), prevbit, *rit);
        prevbit = thisbit;
        }

      // Handle MSB -- negate MSBs if signed comparison
      BBNode lmsb = *lit;
      BBNode rmsb = *rit;
      if (is_signed)
        {
        lmsb = nf->CreateNode(NOT, *lit);
        rmsb = nf->CreateNode(NOT, *rit);
        }

      BBNode msb = nf->CreateNode(ITE, nf->CreateNode(IFF, rmsb, lmsb), prevbit, rmsb);

      if (is_bvlt)
        {
        msb = nf->CreateNode(NOT, msb);
        }
      return msb;
    }

  template<class BBNode, class BBNodeManagerT>
    BBNode
    BitBlaster<BBNode, BBNodeManagerT>::BBBVLE_variant2(const BBNodeVec& left, const BBNodeVec& right, bool is_signed,
        bool is_bvlt)
    {
      typename BBNodeVec::const_reverse_iterator lit = left.rbegin();
      const typename BBNodeVec::const_reverse_iterator litend = left.rend();
      typename BBNodeVec::const_reverse_iterator rit = right.rbegin();

      BBNode this_compare_bit =
          is_signed ? nf->CreateNode(AND, *lit, nf->CreateNode(NOT, *rit)) :
              nf->CreateNode(AND, nf->CreateNode(NOT, *lit), *rit);

      BBNodeVec bit_comparisons;
      bit_comparisons.reserve(left.size() + 1);

      bit_comparisons.push_back(this_compare_bit);

      //(lit IFF rit) is the same as (NOT(lit) XOR rit)
      BBNode prev_eq_bit = nf->CreateNode(XOR, nf->CreateNode(NOT, *lit), *rit);
      for (lit++, rit++; lit < litend; lit++, rit++)
        {
        this_compare_bit = nf->CreateNode(AND, nf->CreateNode(NOT, *lit), *rit);

        BBNode thisbit_output = nf->CreateNode(AND, this_compare_bit, prev_eq_bit);
        bit_comparisons.push_back(thisbit_output);

        BBNode this_eq_bit = nf->CreateNode(AND, nf->CreateNode(XOR, nf->CreateNode(NOT, *lit), *rit), prev_eq_bit);
        prev_eq_bit = this_eq_bit;
        }

      if (!is_bvlt)
        {
        bit_comparisons.push_back(prev_eq_bit);
        }

      // Either zero or one of the nodes in bit_comparisons can be true.

      BBNode output;
#ifdef CRYPTOMINISAT__2
      if (bit_comparisons.size() > 1)
      output = nf->CreateNode(XOR, bit_comparisons);
      else
      output = bit_comparisons[0];
#else
      output = nf->CreateNode(OR, bit_comparisons);
#endif
      return output;
    }

// Left shift  within fixed field inserting zeros at LSB.
// Writes result into first argument.
  template<class BBNode, class BBNodeManagerT>
    void
    BitBlaster<BBNode, BBNodeManagerT>::BBLShift(BBNodeVec& x, unsigned int shift)
    {
      // left shift x (destructively) within width.
      // loop backwards so that copy to self works correctly. (DON'T use STL insert!)
      for (int i = ((int) x.size()) - 1; i >= 0; i--)
        {
        if (i - (int) shift >= 0)
          x[i] = x[i - (int) shift];
        else
          x[i] = nf->getFalse(); // new LSB is zero.
        }
    }

// Right shift within fixed field inserting zeros at MSB.
// Writes result into first argument.
  template<class BBNode, class BBNodeManagerT>
    void
    BitBlaster<BBNode, BBNodeManagerT>::BBRShift(BBNodeVec& x, unsigned int shift)
    {
      // right shift x (destructively) within width.
      const typename BBNodeVec::iterator xend = x.end();
      typename BBNodeVec::iterator xit = x.begin();
      for (; xit < xend; xit++)
        {
        if (xit + shift < xend)
          *xit = *(xit + shift);
        else
          *xit = nf->getFalse(); // new MSB is zero.
        }
    }

// Return bit-blasted form for BVLE, BVGE, BVGT, SBLE, etc.
  template<class BBNode, class BBNodeManagerT>
    BBNode
    BitBlaster<BBNode, BBNodeManagerT>::BBcompare(const ASTNode& form, BBNodeSet& support)
    {
      const BBNodeVec& left = BBTerm(form[0], support);
      const BBNodeVec& right = BBTerm(form[1], support);

      const Kind k = form.GetKind();
      switch (k)
        {
      case BVLE:
        {
        return BBBVLE(left, right, false);
        break;
        }
      case BVGE:
        {
        return BBBVLE(right, left, false);
        break;
        }
      case BVGT:
        {
        return BBBVLE(right, left, false, true);
        break;
        }
      case BVLT:
        {
        return BBBVLE(left, right, false, true);
        break;
        }
      case BVSLE:
        {
        return BBBVLE(left, right, true);
        break;
        }
      case BVSGE:
        {
        return BBBVLE(right, left, true);
        break;
        }
      case BVSGT:
        {
        return nf->CreateNode(NOT, BBBVLE(left, right, true));
        break;
        }
      case BVSLT:
        {
        return nf->CreateNode(NOT, BBBVLE(right, left, true));
        break;
        }
      default:
        cerr << "BBCompare: Illegal kind" << form << endl;
        FatalError("", form);
        }
    }

// return a vector with n copies of fillval
  template<class BBNode, class BBNodeManagerT>
    BBNodeVec
    BitBlaster<BBNode, BBNodeManagerT>::BBfill(unsigned int width, BBNode fillval)
    {
      BBNodeVec zvec(width, fillval);
      return zvec;
    }

  template<class BBNode, class BBNodeManagerT>
    BBNode
    BitBlaster<BBNode, BBNodeManagerT>::BBEQ(const BBNodeVec& left, const BBNodeVec& right)
    {
      BBNodeVec andvec;
      andvec.reserve(left.size());
      typename BBNodeVec::const_iterator lit = left.begin();
      const typename BBNodeVec::const_iterator litend = left.end();
      typename BBNodeVec::const_iterator rit = right.begin();

      if (left.size() > 1)
        {
        for (; lit != litend; lit++, rit++)
          {
          BBNode biteq = nf->CreateNode(IFF, *lit, *rit);
          // fast path exit
          if (biteq == nf->getFalse())
            {
            return nf->getFalse();
            }
          else
            {
            andvec.push_back(biteq);
            }
          }
        BBNode n = nf->CreateNode(AND, andvec);
        return n;
        }
      else
        return nf->CreateNode(IFF, *lit, *rit);
    }

  std::ostream&
  operator<<(std::ostream& output, const BBNodeAIG& h)
  {
    FatalError("This isn't implemented  yet sorry;");
    return output;
  }

// This creates all the specialisations of the class that are ever needed.
  template class BitBlaster<ASTNode, BBNodeManagerASTNode> ;
  template class BitBlaster<BBNodeAIG, BBNodeManagerAIG> ;

#undef BBNodeVec
#undef BBNodeVecMap
#undef BBNodeSet

} // BEEV namespace
