#include "ConstantBitPropagation.h"
#include "../../AST/AST.h"
#include "../../extlib-constbv/constantbv.h"
#include "../../printer/printers.h"
#include "../../AST/NodeFactory/NodeFactory.h"
#include "../../simplifier/simplifier.h"
#include "ConstantBitP_Utility.h"
#include <iostream>
#include <fstream>
#include "ConstantBitP_TransferFunctions.h"
#include "ConstantBitP_MaxPrecision.h"

using std::endl;
using std::cout;

using namespace BEEV;

/*
 *	Propagates known fixed 0 or 1 bits, as well as TRUE/FALSE values through the formula.
 *
 *	Our approach differs from others because the transfer functions are (mostly) optimally precise.
 *
 *	FixedBits stores booleans in 1 bit-bitvectors.
 */

namespace simplifier
{
  namespace constantBitP
  {
    NodeToFixedBitsMap* PrintingHackfixedMap; // Used when debugging.

    Result
    dispatchToTransferFunctions(const Kind k, vector<FixedBits*>& children,
        FixedBits& output, const ASTNode n, MultiplicationStatsMap *msm = NULL);

    const bool debug_cBitProp_messages = false;
    const bool output_mult_like = false;
    const bool debug_print_graph_after = false;

    ////////////////////

    void
    ConstantBitPropagation::printNodeWithFixings()
    {
      NodeToFixedBitsMap::NodeToFixedBitsMapType::const_iterator it =
          fixedMap->map->begin();

      cerr << "+Nodes with fixings" << endl;

      for (/**/; it != fixedMap->map->end(); it++) // iterates through all the pairs of node->fixedBits.
        {
          cerr << (it->first).GetNodeNum() << " " << *(it->second) << endl;
        }
      cerr << "-Nodes with fixings" << endl;

    }

    // Used when outputting when debugging.
    // Outputs the fixed bits for a particular node.
    string
    toString(const ASTNode& n)
    {
      NodeToFixedBitsMap::NodeToFixedBitsMapType::const_iterator it =
          PrintingHackfixedMap->map->find(n);
      if (it == PrintingHackfixedMap->map->end())
        return "";

      std::stringstream s;
      s << *it->second;
      return s.str();
    }

    // If the bits are totally fixed, then return a new matching ASTNode.
    ASTNode
    bitsToNode(const ASTNode& node, const FixedBits& bits)
    {
      ASTNode result;
      STPMgr & beev = *node.GetSTPMgr();

      assert (bits.isTotallyFixed());
      assert (!node.isConstant()); // Peformance. Shouldn't waste time calling it on constants.

      if (node.GetType() == BOOLEAN_TYPE)
        {
          if (bits.getValue(0))
            {
              result = beev.CreateNode(TRUE);
            }
          else
            {
              result = beev.CreateNode(FALSE);
            }
        }
      else if (node.GetType() == BITVECTOR_TYPE)
        {
          result = beev.CreateBVConst(bits.GetBVConst(), node.GetValueWidth());
        }
      else
        FatalError("sadf234s");

      assert(result.isConstant());
      return result;
    }

    // Put anything that's entirely fixed into a from->to map.
    ASTNodeMap
    ConstantBitPropagation::getAllFixed()
    {
      NodeToFixedBitsMap::NodeToFixedBitsMapType::iterator it;

      ASTNodeMap toFrom;

      // iterates through all the pairs of node->fixedBits.
      for (it = fixedMap->map->begin(); it != fixedMap->map->end(); it++)
        {
          const ASTNode& node = (it->first);
          const FixedBits& bits = *it->second;

          // Don't constrain nodes we already know all about.
          if (node.isConstant())
              continue;

          // Concat doesn't change the fixings. Ignore it.
          if (BVCONCAT == node.GetKind())
            continue;

          if (bits.isTotallyFixed())
            {
              toFrom.insert(std::make_pair(node, bitsToNode(node, bits)));
            }
        }

      return toFrom;
    }

    void
    ConstantBitPropagation::setNodeToTrue(const ASTNode& top)
    {
      assert(!topFixed);
      topFixed = true;

      FixedBits & topFB = *getCurrentFixedBits(top);
      topFB.setFixed(0, true);
      topFB.setValue(0, true);
      workList->push(top);
    }

    // Propagates. No writing in of values. Doesn't assume the top is true.
    ConstantBitPropagation::ConstantBitPropagation(BEEV::Simplifier* _sm, NodeFactory* _nf,const ASTNode & top)
    {
      assert (BOOLEAN_TYPE == top.GetType());
      assert (top.GetSTPMgr()->UserFlags.bitConstantProp_flag);

      status = NO_CHANGE;
      simplifier = _sm;
      nf = _nf;
      fixedMap = new NodeToFixedBitsMap(1000); // better to use the function that returns the number of nodes.. whatever that is.
      workList = new WorkList(top);
      dependents = new Dependencies(top); // List of the parents of a node.
      msm = new MultiplicationStatsMap();


      // not fixing the topnode.
      propagate();

      if (debug_cBitProp_messages)
        {
          cerr << "status:" << status <<endl;
          cerr << "ended propagation" << endl;
          printNodeWithFixings();
        }

      // is there are good reason to clear out some of them??
#if 0
      // remove constants, and things with nothing fixed.
      NodeToFixedBitsMap::NodeToFixedBitsMapType::iterator it =
          fixedMap->map->begin();
      NodeToFixedBitsMap::NodeToFixedBitsMapType::iterator it_end =
          fixedMap->map->end();
      while (it != it_end)
        {
          // No constants, nothing completely unfixed.
          if (  (it->second)->countFixed() == 0 )
            {
              delete it->second;
              // making this a reference causes reading from freed memory.
              const ASTNode n = it->first;
              it++;
              fixedMap->map->erase(n);
            }
          else
            it++;
        }
#endif

      topFixed = false;
    }

    // Both way propagation. Initialising the top to "true".
    // The hardest thing to understand is the two cases:
    // 1) If we get the fixed bits of a node, without assuming the top node is true,
    //    then we can replace that node by its fixed bits.
    // 2) But if we assume the top node is true, then get the bits, we need to conjoin it.

    // NB: This expects that the constructor was called with the same node. Sorry.
    ASTNode
    ConstantBitPropagation::topLevelBothWays(const ASTNode& top, bool setTopToTrue, bool conjoinToTop)
    {
      assert(top.GetSTPMgr()->UserFlags.bitConstantProp_flag);
      assert (BOOLEAN_TYPE == top.GetType());

      propagate();
      status = NO_CHANGE;

      //Determine what must always be true.
      ASTNodeMap fromTo = getAllFixed();
      {
        ASTNodeMap::iterator it = fromTo.begin();
        while(it != fromTo.end())
          {
          // I don't think there should be a constant in here ever.
          assert(it->first.GetKind() != SYMBOL);
          it++;
          }
      }


      if (debug_cBitProp_messages)
        {
          cerr << "Number removed by bottom UP:" << fromTo.size() << endl;
        }

      if (setTopToTrue)
    	  setNodeToTrue(top);

      if (debug_cBitProp_messages)
        {
          cerr << "starting propagation" << endl;
          printNodeWithFixings();
          cerr << "Initial Tree:" << endl;
          cerr << top;
        }

      propagate();

      if (debug_cBitProp_messages)
        {
          cerr << "status:" << status <<endl;
          cerr << "ended propagation" << endl;
          printNodeWithFixings();
        }

      // propagate may have stopped with a conflict.
      if (CONFLICT == status)
          return top.GetSTPMgr()->CreateNode(FALSE);

      ASTVec toConjoin;

      // go through the fixedBits. If a node is entirely fixed.
      // "and" it onto the top. Creates redundancy. Check that the
      // node doesn't already depend on "top" directly.

      for (NodeToFixedBitsMap::NodeToFixedBitsMapType::iterator it = fixedMap->map->begin(); it != fixedMap->map->end(); it++) // iterates through all the pairs of node->fixedBits.
        {
          const FixedBits& bits = *it->second;

          const ASTNode& node = (it->first);

          if (false && node.GetKind() == SYMBOL && !bits.isTotallyFixed() && bits.countFixed() > 0)
            {
              // replace partially known variables with new variables.
              int leastFixed = bits.leastUnfixed();
              int mostFixed = bits.mostUnfixed();
              const int width = node.GetValueWidth();

              int new_width = mostFixed - leastFixed +1;
              assert(new_width > 0);
              ASTNode fresh = node.GetSTPMgr()->CreateFreshVariable(0,new_width,"STP_REPLACE");
              ASTNode a,b;
              if (leastFixed > 0)
                a= node.GetSTPMgr()->CreateBVConst(bits.GetBVConst( leastFixed-1,  0), leastFixed);
              if (mostFixed != width-1)
                b =  node.GetSTPMgr()->CreateBVConst(bits.GetBVConst( width-1,  mostFixed+1),width-1-mostFixed);
              if (!a.IsNull())
                fresh = nf->CreateTerm(BVCONCAT, a.GetValueWidth() + fresh.GetValueWidth(), fresh, a);
              if (!b.IsNull())
                fresh = nf->CreateTerm(BVCONCAT, b.GetValueWidth() + fresh.GetValueWidth(), b, fresh);
              assert(fresh.GetValueWidth() == node.GetValueWidth());
              bool r = simplifier->UpdateSubstitutionMap(node, fresh);
              assert(r);
            }

          if (!bits.isTotallyFixed())
            continue;


          // Don't constrain nodes we already know all about.
          if (node.isConstant())
            continue;

          // other nodes will contain the same information (the extract doesn't change the fixings).
          if (BVEXTRACT == node.GetKind() || BVCONCAT == node.GetKind())
            continue;

          // toAssign: conjoin it with the top level.
          // toReplace: replace all references to it (except the one conjoined to the top) with this.
          ASTNode propositionToAssert;
          ASTNode constantToReplaceWith;
          // skip the assigning and replacing.
          bool doAssign = false;

            {
              // If it is already contained in the fromTo map, then it's one of the values
              // that have fully been determined (previously). Not conjoined.
              if (fromTo.find(node) != fromTo.end())
                continue;

              ASTNode constNode = bitsToNode(node,bits);

              if (node.GetType() == BOOLEAN_TYPE)
                {
                  if (SYMBOL == node.GetKind())
                    {
                      bool r = simplifier->UpdateSubstitutionMap(node, constNode);
                      assert(r);
                      doAssign = false;
                    }
                  else if (conjoinToTop && bits.getValue(0))
                    {
                      propositionToAssert = node;
                      constantToReplaceWith = constNode;
                      doAssign=true;
                    }
                  else if (conjoinToTop)
                    {
                      propositionToAssert = nf->CreateNode(NOT, node);
                      constantToReplaceWith = constNode;
                      doAssign=true;
                    }
                }
              else if (node.GetType() == BITVECTOR_TYPE)
                {
                  assert(((unsigned)bits.getWidth()) == node.GetValueWidth());
                  if (SYMBOL == node.GetKind())
                    {
                      bool r = simplifier->UpdateSubstitutionMap(node, constNode);
                      assert(r);
                      doAssign = false;
                    }
                  else if (conjoinToTop)
                    {
                      propositionToAssert = nf->CreateNode(EQ, node, constNode);
                      constantToReplaceWith = constNode;
                      doAssign=true;
                    }
                }
              else
                FatalError("sadf234s");
            }

          if (doAssign && top != propositionToAssert
              && !dependents->nodeDependsOn(top, propositionToAssert))
            {
              assert(!constantToReplaceWith.IsNull());
              assert(constantToReplaceWith.isConstant());
              assert(propositionToAssert.GetType() == BOOLEAN_TYPE);
              assert(node.GetValueWidth() == constantToReplaceWith.GetValueWidth());

              fromTo.insert(make_pair(node, constantToReplaceWith));
              toConjoin.push_back(propositionToAssert);
              assert(conjoinToTop);
            }
        }

     // Write the constants into the main graph.
      ASTNodeMap cache;
      ASTNode result = SubstitutionMap::replace(top, fromTo, cache,nf);

      if (0 != toConjoin.size())
        {
          // It doesn't happen very often. But the "toConjoin" might contain a variable
          // that was added to the substitution map (because the value was determined just now
          // during propagation.
          ASTNode conjunct = (1 == toConjoin.size())? toConjoin[0]: nf->CreateNode(AND,toConjoin);
          conjunct = simplifier->applySubstitutionMap(conjunct);

          result = nf->CreateNode(AND, result, conjunct); // conjoin the new conditions.
        }


  	if (debug_print_graph_after)
		{
			ofstream file;
			file.open("afterCbitp.gdl");
			PrintingHackfixedMap = fixedMap;
			printer::GDL_Print(file,top,&toString);
			file.close();
		}


      assert(BVTypeCheck(result));
      assert(status != CONFLICT); // conflict should have been seen earlier.
      return result;
    }

    void
    notHandled(const Kind& k)
    {
      if (READ != k && WRITE != k)
      if (debug_cBitProp_messages)
        {
          cerr << "!" << k << endl;
        }
    }


    // add to the work list any nodes that take the result of the "n" node.
    void
    ConstantBitPropagation::scheduleUp(const ASTNode& n)
    {
      const set<ASTNode>* toAdd = dependents->getDependents(n);
      set<ASTNode>::iterator it = toAdd->begin();
      while (it != toAdd->end())
        {
          workList->push(*it);
          it++;
        }
    }

    void
    ConstantBitPropagation::scheduleDown(const ASTNode& n)
    {
      for (int i = 0; i < n.Degree(); i++)
        workList->push(n[i]);
    }

    void
    ConstantBitPropagation::scheduleNode(const ASTNode& n)
    {
      workList->push(n);
    }

    bool
    ConstantBitPropagation::checkAtFixedPoint(const ASTNode& n, ASTNodeSet & visited)
    {
      if (status == CONFLICT)
        return true; // can't do anything.

      if (visited.find(n) != visited.end())
        return true;

      visited.insert(n);

      // get the current for the children.
      vector<FixedBits> childrenFixedBits;
      childrenFixedBits.reserve(n.GetChildren().size());

      // get a copy of the current fixing from the cache.
      for (unsigned i = 0; i < n.GetChildren().size(); i++)
        {
          childrenFixedBits.push_back(*getCurrentFixedBits(n[i]));
        }
      FixedBits current = *getCurrentFixedBits(n);
      FixedBits newBits = *getUpdatedFixedBits(n);

      assert(FixedBits::equals(newBits, current));

      for (int i = 0; i < n.Degree(); i++)
        {
          if (!FixedBits::equals(*getUpdatedFixedBits(n[i]),
              childrenFixedBits[i]))
            {
              cerr << "Not fixed point";
              assert(false);
            }

          checkAtFixedPoint(n[i], visited);
        }
      return true;
    }

    void
    ConstantBitPropagation::propagate()
    {
      if (CONFLICT == status)
        return;

      assert(NULL != fixedMap);

      while (!workList->isEmpty())
        {
          // get the next node from the worklist.
          const ASTNode& n = workList->pop();

          assert (!n.isConstant()); // shouldn't get into the worklist..
          assert (CONFLICT != status); // should have stopped already.

          if (debug_cBitProp_messages)
            {
              cerr << "[" << workList->size() << "]working on" << n.GetNodeNum() << endl;
            }

          // get a copy of the current fixing from the cache.
          int previousTop = getCurrentFixedBits(n)->countFixed();

          // get the current for the children.
          previousChildrenFixedCount.clear();

          // get a copy of the current fixing from the cache.
          for (unsigned i = 0; i < n.GetChildren().size(); i++)
            {
              previousChildrenFixedCount.push_back(getCurrentFixedBits(n[i])->countFixed());
            }

          // derive the new ones.
          int newCount = getUpdatedFixedBits(n)->countFixed();

          if (CONFLICT == status)
            return;

          // Not all transfer function update the status. But if they report NO_CHANGE. There really is no change.
          if (status != NO_CHANGE)
            {
              if (newCount != previousTop) // has been a change.
                {
                      assert(newCount >= previousTop);
                      scheduleUp(n); // schedule everything that depends on n.
                }

              for (unsigned i = 0; i < n.GetChildren().size(); i++)
                {
                  if (getCurrentFixedBits(n[i])->countFixed() != previousChildrenFixedCount[i])
                    {
                      if (debug_cBitProp_messages)
                        {
                          cerr << "Changed: " << n[i].GetNodeNum() << " from:" << previousChildrenFixedCount[i] << "to:"
                              << *getCurrentFixedBits(n[i]) << endl;
                        }

                      assert(!n[i].isConstant());

                      // All the immediate parents of this child need to be rescheduled.
                      // Shouldn't reschuedule 'n' but it does.
                      scheduleUp(n[i]);

                      // Scheduling the child updates all the values that feed into it.
                      workList->push(n[i]);
                    }
                }
            }
        }
    }

    // get the current value from the map. If no value is in the map. Make a new value.
    FixedBits*
    ConstantBitPropagation::getCurrentFixedBits(const ASTNode& n)
    {
      assert (NULL != fixedMap);

      NodeToFixedBitsMap::NodeToFixedBitsMapType::iterator it = fixedMap->map->find(n);
      if (it != fixedMap->map->end())
        {
          return it->second;
        }

      int bw;
      if (0 == n.GetValueWidth())
        {
          bw = 1;
        }
      else
        {
          bw = n.GetValueWidth();
        }

      FixedBits* output = new FixedBits(bw, (BOOLEAN_TYPE == n.GetType()));

      if (BVCONST == n.GetKind() || BITVECTOR == n.GetKind())
        {
          // the CBV doesn't leak. it is a copy of the cbv inside the node.
          CBV cbv = n.GetBVConst();

          for (unsigned int j = 0; j < n.GetValueWidth(); j++)
            {
              output->setFixed(j, true);
              output->setValue(j, CONSTANTBV::BitVector_bit_test(cbv, j));
            }
        }
      else if (TRUE == n.GetKind())
        {
          output->setFixed(0, true);
          output->setValue(0, true);
        }
      else if (FALSE == n.GetKind())
        {
          output->setFixed(0, true);
          output->setValue(0, false);
        }

       fixedMap->map->insert(pair<ASTNode, FixedBits*> (n, output));
      return output;
    }

    // For the given node, update which bits are fixed.

    FixedBits*
    ConstantBitPropagation::getUpdatedFixedBits(const ASTNode& n)
    {
      FixedBits* output = getCurrentFixedBits(n);
      const Kind k = n.GetKind();

      if (n.isConstant())
        {
          assert(output->isTotallyFixed());
          return output;
        }

      if (SYMBOL == k)
        return output; // No transfer functions for these.

      vector<FixedBits*> children;
      const int numberOfChildren = n.GetChildren().size();
      children.reserve(numberOfChildren);

      for (int i = 0; i < numberOfChildren; i++)
        {
          children.push_back(getCurrentFixedBits(n.GetChildren()[i]));
        }

      assert(status != CONFLICT);
      status = dispatchToTransferFunctions(k, children, *output, n, msm);
      //result = dispatchToMaximallyPrecise(k, children, *output, n,msm);

      assert(((unsigned)output->getWidth()) == n.GetValueWidth() || output->getWidth() ==1);

      return output;
    }

    Result
    dispatchToTransferFunctions(const Kind k, vector<FixedBits*>& children,
        FixedBits& output, const ASTNode n, MultiplicationStatsMap * msm)
    {
      Result result = NO_CHANGE;

      assert(!n.isConstant());

      Result(*transfer)(vector<FixedBits*>&, FixedBits&);

      switch (k)
        {
          case READ:
          case WRITE:
          // do nothing. Seems difficult to track properly.
          return NO_CHANGE;
          break;

#define MAPTFN(caseV, FN) case caseV: transfer = FN; break;

          // Shifting
          MAPTFN(BVLEFTSHIFT, bvLeftShiftBothWays)
          MAPTFN(BVRIGHTSHIFT, bvRightShiftBothWays)
          MAPTFN(BVSRSHIFT, bvArithmeticRightShiftBothWays)

          // Unsigned Comparison.
          MAPTFN(BVLT,bvLessThanBothWays)
          MAPTFN(BVLE,bvLessThanEqualsBothWays)
          MAPTFN(BVGT, bvGreaterThanBothWays)
          MAPTFN(BVGE, bvGreaterThanEqualsBothWays)

          // Signed Comparison.
          MAPTFN(BVSLT, bvSignedLessThanBothWays)
          MAPTFN(BVSGT,bvSignedGreaterThanBothWays)
          MAPTFN(BVSLE, bvSignedLessThanEqualsBothWays)
          MAPTFN(BVSGE, bvSignedGreaterThanEqualsBothWays)

          // Logic.
          MAPTFN(XOR,bvXorBothWays)
          MAPTFN(BVXOR, bvXorBothWays)
          MAPTFN(OR, bvOrBothWays)
          MAPTFN(BVOR, bvOrBothWays)
          MAPTFN(AND,bvAndBothWays)
          MAPTFN(BVAND,bvAndBothWays)
          MAPTFN(IFF, bvEqualsBothWays)
          MAPTFN(EQ, bvEqualsBothWays)
          MAPTFN(IMPLIES,bvImpliesBothWays)
          MAPTFN(NOT,bvNotBothWays)
          MAPTFN(BVNEG, bvNotBothWays)

          // OTHER
          MAPTFN(BVZX, bvZeroExtendBothWays)
          MAPTFN(BVSX, bvSignExtendBothWays)
          MAPTFN(BVUMINUS,bvUnaryMinusBothWays)
          MAPTFN(BVEXTRACT,bvExtractBothWays)
          MAPTFN(BVPLUS, bvAddBothWays)
          MAPTFN(BVSUB, bvSubtractBothWays)
          MAPTFN(ITE,bvITEBothWays)
          MAPTFN(BVCONCAT, bvConcatBothWays)


          case BVMULT: // handled specially later.
          case BVDIV:
          case BVMOD:
          case SBVDIV:
          case SBVREM:
          case SBVMOD:
          transfer = NULL;
          break;

          default:
            {
              notHandled(k);
              return NO_CHANGE;
            }
        }
#undef MAPTFN
      bool mult_like = false;
      const bool lift_to_max = false;

      // safe approximation to no overflow multiplication.
      if (k == BVMULT)
        {
          MultiplicationStats ms;
          result = bvMultiplyBothWays(children, output, n.GetSTPMgr(),&ms);
          		if (CONFLICT != result)
          			msm->map[n] = ms;
 	  mult_like=true;
        }
      else if (k == BVDIV)
        {
          result = bvUnsignedDivisionBothWays(children, output, n.GetSTPMgr());
          mult_like=true;
        }
      else if (k == BVMOD)
        {
          result = bvUnsignedModulusBothWays(children, output, n.GetSTPMgr());
          mult_like=true;
        }
      else if (k == SBVDIV)
        {
          result = bvSignedDivisionBothWays(children, output, n.GetSTPMgr());
          mult_like=true;
        }
      else if (k == SBVREM)
        {
          result = bvSignedRemainderBothWays(children, output, n.GetSTPMgr());
          mult_like=true;
        }
      else if (k == SBVMOD)
        {
          // This propagator is very slow. It needs to be reimplemented.
          //result = bvSignedModulusBothWays(children, output, n.GetSTPMgr());
          mult_like=true;
        }
      else
        result = transfer(children, output);

      if (mult_like && lift_to_max)
        {
        int bits_before = output.countFixed() + children[0]->countFixed() + children[1]->countFixed();
        result = merge(result, maxPrecision(children, output, k, n.GetSTPMgr())? CONFLICT :NOT_IMPLEMENTED);
        int difference =  (output.countFixed() + children[0]->countFixed() + children[1]->countFixed()) - bits_before;
        assert(difference >= 0);
        cerr << "Bits fixed" << difference << endl;
        }

      if (mult_like && output_mult_like)
        {
          cerr << output << "=";
          cerr << *children[0] << k;
          cerr << *children[1] << std::endl;
        }

      return result;

    }
  }
}

