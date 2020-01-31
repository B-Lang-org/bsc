/*
 * Performs a basic unsigned interval analysis.
 */

#ifndef ESTABLISHINTERVALS_H_
#define ESTABLISHINTERVALS_H_
#include "../AST/AST.h"
#include "../STPManager/STPManager.h"
#include "simplifier.h"
#include "../AST/NodeFactory/SimplifyingNodeFactory.h"
#include "../boost/noncopyable.hpp"

namespace BEEV
{
  class EstablishIntervals : boost::noncopyable
  {
  private:
    struct IntervalType
    {
      CBV minV;
      CBV maxV;
      IntervalType(CBV _min, CBV _max)
      {
        minV = _min;
        maxV = _max;
        assert(minV != NULL);
        assert(maxV != NULL);
        assert(size_(minV) == size_(maxV));
      }

      void print()
      {

            unsigned char * a = CONSTANTBV::BitVector_to_Dec(minV);
            unsigned char * b = CONSTANTBV::BitVector_to_Dec(maxV);
            cerr << a << " " << b << endl;
            free(a);
            free(b);

      }

      bool isConstant()
      {
    	  return !CONSTANTBV::BitVector_Lexicompare(minV, maxV);
      }

      bool isComplete()
      {
        return (CONSTANTBV::BitVector_is_empty(minV) && CONSTANTBV::BitVector_is_full(maxV));
      }

      void checkUnsignedInvariant()
      {
        assert( CONSTANTBV::BitVector_Lexicompare(minV, maxV) <=0);

        // We use NULL to represent the complete domain.
        assert( !isComplete());
      }

      // If the interval is interpreted as a clockwise interval.
      bool crossesSignedUnsigned(int width)
      {
        bool minMSB = CONSTANTBV::BitVector_bit_test(minV,  width- 1);
        bool maxMSB = CONSTANTBV::BitVector_bit_test(maxV,  width- 1);

        // If the min is zero, and the max is one, then it must cross.
        if (!minMSB && maxMSB)
          return true;
        if (!(minMSB ^ maxMSB)) // bits are the same.
          return CONSTANTBV::BitVector_Compare(minV, maxV) >0;
        return false;
      }

    };

    vector<EstablishIntervals::IntervalType * > toDeleteLater;
    vector<CBV> likeAutoPtr;

    IntervalType * freshUnsignedInterval(int width)
    {
      assert(width > 0);
      IntervalType *it = createInterval(makeCBV(width), makeCBV(width));
      CONSTANTBV::BitVector_Fill(it->maxV);
      return it;
    }

    IntervalType * createInterval(CBV min, CBV max)
    {
      IntervalType *it = new IntervalType(min,max);
      toDeleteLater.push_back(it);
      return it ;
    }

    CBV makeCBV(int width)
    {
        CBV result = CONSTANTBV::BitVector_Create(width, true);
        likeAutoPtr.push_back(result);
        return result;
    }

    // A special version that handles the lhs appearing in the rhs of the fromTo map.
    ASTNode replace(const ASTNode& n, ASTNodeMap& fromTo, ASTNodeMap& cache)
    {
      if (n.isAtom())
        return n;

      if (cache.find(n) != cache.end())
        return (*(cache.find(n))).second;

      ASTNode result = n;

      if (fromTo.find(n) != fromTo.end())
        {
          result = (*fromTo.find(n)).second;
          fromTo.erase(n); // this is how it differs from the everyday replace.
        }

      ASTVec new_children;
      new_children.reserve(result.GetChildren().size());

      for (int i =0; i < result.Degree();i++)
        new_children.push_back(replace(result[i],fromTo,cache));

      if (new_children == result.GetChildren())
        {
          cache.insert(make_pair(n,result));
          return result;
        }

      if (n.GetValueWidth() == 0) // n.GetType() == BOOLEAN_TYPE
        {
          result = nf->CreateNode(result.GetKind(), new_children);
        }
      else
        {
          // If the index and value width aren't saved, they are reset sometimes (??)
          result = nf->CreateArrayTerm(result.GetKind(), result.GetIndexWidth(), result.GetValueWidth(), new_children);
        }

      cache.insert(make_pair(n,result));
      return result;
    }

  public:
    // Replace some of the things that unsigned intervals can figure out for us.
    // Reduce from signed to unsigned if possible.
    ASTNode topLevel_unsignedIntervals(const ASTNode&top)
    {
      bm.GetRunTimes()->start(RunTimes::IntervalPropagation);
      map<const ASTNode, IntervalType*> visited;
      map<const ASTNode, IntervalType*> clockwise;
      visit(top,visited, clockwise);
      ASTNodeMap fromTo;
      ASTNodeMap onePass;
      for (map<const ASTNode, IntervalType*>::const_iterator it = visited.begin(); it != visited.end(); it++)
      {
          const ASTNode& n = it->first;
          IntervalType *interval = it->second;
          const int width = n.GetValueWidth();

          if (n.isConstant())
            continue;

          const Kind k = n.GetKind();

          // We do this rule if we don't know for certain the result.
          // If the leading bits are false then we can reduce from signed to unsigned comparison.
          if ((interval == NULL || !interval->isConstant())
            && (k == BVSGT || k == BVSGE || k == SBVDIV || k == BVSRSHIFT || k == SBVREM || k == BVSX))
                {
                  map<const ASTNode, IntervalType*>::const_iterator l = visited.find(n[0]);
                  map<const ASTNode, IntervalType*>::const_iterator r = visited.find(n[1]);

                  bool lhs, rhs; // isFalse.

                  if (l == visited.end())
                    lhs = false;
                  else
                    {
                      IntervalType * a = (*l).second;
                      if (a == NULL)
                        lhs = false;
                      else
                        {
                          lhs = !CONSTANTBV::BitVector_bit_test(a->maxV, n[0].GetValueWidth() - 1);
                        }
                    }

                  if (r == visited.end())
                    rhs = false;
                  else
                    {
                      IntervalType * b = (*r).second;
                      if (b == NULL)
                        rhs = false;
                      else
                        rhs = !CONSTANTBV::BitVector_bit_test(b->maxV, n[0].GetValueWidth() - 1);
                    }

                  switch (n.GetKind())
                    {
                  case BVSGT:
                  case BVSGE:
                    if (lhs && rhs)
                      {
                        ASTNode newN = nf->CreateNode(n.GetKind() == BVSGT ? BVGT : BVGE,  n[0], n[1]);
                        fromTo.insert(make_pair(n, newN));
                      }
                    break;

                  case SBVDIV:
                    if (lhs && rhs)
                      {
                        ASTNode newN = nf->CreateTerm(BVDIV, n.GetValueWidth(), n[0], n[1]);
                        fromTo.insert(make_pair(n, newN));
                      }
                    break;

                  case SBVREM:
                    if (lhs && rhs)
                      {
                        ASTNode newN = nf->CreateTerm(BVMOD, n.GetValueWidth(), n[0], n[1]);
                        fromTo.insert(make_pair(n, newN));
                      }
                    break;

                  case BVSRSHIFT:
                    if (lhs)
                      {
                        ASTNode newN = nf->CreateTerm(BVRIGHTSHIFT, n.GetValueWidth(), n[0], n[1]);
                        fromTo.insert(make_pair(n, newN));
                      }
                    break;

                  case BVSX:
                    if (lhs && n[0].GetValueWidth() != n.GetValueWidth())
                      {
                          // If it's really a zero extend..
                          ASTNode copyN = nf->CreateTerm(BVCONCAT, n.GetValueWidth(), bm.CreateZeroConst(n.GetValueWidth() - n[0].GetValueWidth()),n[0]);
                          fromTo.insert(make_pair(n,copyN));
                      }
                    break;
                  default:
                    FatalError("Never here");
                }
          }
          if (interval == NULL)
            continue;
          if (interval->isConstant() && n.GetType() == BOOLEAN_TYPE)
            {
              if (0 == CONSTANTBV::BitVector_Lexicompare(interval->maxV, littleOne))
                fromTo.insert(make_pair(n, bm.ASTTrue));
              else
                fromTo.insert(make_pair(n, bm.ASTFalse));
            }
          else if (interval->isConstant() && n.GetType() == BITVECTOR_TYPE)
            {
              CBV clone = CONSTANTBV::BitVector_Clone(interval->maxV);
              ASTNode new_const = bm.CreateBVConst(clone, n.GetValueWidth());
              fromTo.insert(make_pair(n, new_const));
            }
          else if (false && n.GetType() == BITVECTOR_TYPE && n.GetKind() != SYMBOL && n.GetKind() != BVCONCAT)
            {
              // Looks for leading or trailing zeroes/ones, and replaces the node with a
              // concat and an extract.

              // This slows things down. I suspect because the extracts are "simplified" and split too many things.
              bool leadingValue = CONSTANTBV::BitVector_bit_test(interval->maxV,width-1);
              int leadingSame = 0;
              for (int i=width-1; i >=0 ;i--)
                {
                  if (CONSTANTBV::BitVector_bit_test(interval->maxV,i) ^ leadingValue)
                    break;

                  if (CONSTANTBV::BitVector_bit_test(interval->minV,i) ^ leadingValue)
                     break;
                  leadingSame++;
                }

              assert(leadingSame != width); // That'd be a constant (another case).

              if (leadingSame >0)
                {
                  ASTNode prefix;
                  if (leadingValue)
                    prefix = bm.CreateMaxConst(leadingSame);
                  else
                    prefix = bm.CreateZeroConst(leadingSame);


              ASTNode top = bm.CreateBVConst(32,width-leadingSame-1);
              ASTNode bottom = bm.CreateZeroConst(32);
              ASTNode remainder = nf->CreateTerm(BVEXTRACT, width-leadingSame, n, top,bottom);
              ASTNode replaced = nf->CreateTerm(BVCONCAT, width, prefix,remainder);
              onePass.insert(make_pair(n,replaced));
                }
            }
      }

      ASTNode result = top;
      if (onePass.size() > 0)
        {
          // The rhs of the map contains the lhs, so it needs to be applied specially.
          ASTNodeMap cache;
          result =  replace(top, onePass, cache);
        }

      if (fromTo.size() > 0)
        {
          ASTNodeMap cache;

          bm.GetRunTimes()->stop(RunTimes::IntervalPropagation);
          return SubstitutionMap::replace(result,fromTo,cache,top.GetSTPMgr()->defaultNodeFactory);
        }

      bm.GetRunTimes()->stop(RunTimes::IntervalPropagation);
      return result;
    }


  private:
    // A single pass through the problem replacing things that must be true of false.
    // clockwise are intervals that go clockwise around the circle from low to high.
    IntervalType* visit(const ASTNode& n, map<const ASTNode, IntervalType*> & visited, map<const ASTNode, IntervalType*> & clockwise)
    {
      map<const ASTNode, IntervalType*>::iterator it;
      if ((it = visited.find(n)) != visited.end())
        return it->second;

      const int number_children = n.Degree();
      vector<IntervalType* > children;
      children.reserve(number_children);
      for (int i=0; i < number_children;i++)
        {
          children.push_back(visit(n[i],visited,clockwise));
        }

      IntervalType * result = NULL;
      const unsigned int width = n.GetValueWidth();
      const bool knownC0 = number_children <1 ? false : (children[0] != NULL);
      const bool knownC1 = number_children <2 ? false : (children[1] != NULL);

      switch (n.GetKind())
        {
      case BVCONST:
      case BITVECTOR:
        {
        // the CBV doesn't leak. it is a copy of the cbv inside the node.
        CBV cbv = n.GetBVConst();
        result = createInterval(cbv, cbv);
        }
        break;
      case TRUE:
        result = createInterval(littleOne, littleOne);
        break;
      case FALSE:
        result = createInterval(littleZero, littleZero);
        break;
      case NOT:
      if (knownC0)
      {
    	  assert(children[0]->isConstant());
    	  if (!CONSTANTBV::BitVector_Lexicompare(children[0]->minV, littleOne))
    		  result = createInterval(littleZero,littleZero);
    	  else
    		  result = createInterval(littleOne,littleOne);
      }
      break;
      case EQ:
        if (knownC0 && knownC1)
      {
    	  if ((CONSTANTBV::BitVector_Lexicompare(children[1]->minV,children[0]->maxV) >0)
    		  || (CONSTANTBV::BitVector_Lexicompare(children[0]->minV,children[1]->maxV) >0))
    		  result = createInterval(littleZero, littleZero);
      }
        break;
      case BVGT:
      case BVSGT:
      if (
          (BVGT == n.GetKind() && knownC0 && knownC1) ||
          (BVSGT == n.GetKind() && knownC0 && knownC1
              && !CONSTANTBV::BitVector_bit_test(children[0]->maxV, n[0].GetValueWidth()-1)
              && !CONSTANTBV::BitVector_bit_test(children[1]->maxV, n[0].GetValueWidth()-1)
          ))
          {
              if (CONSTANTBV::BitVector_Lexicompare(children[0]->minV,children[1]->maxV) >0)
                result = createInterval(littleOne, littleOne);

              if (CONSTANTBV::BitVector_Lexicompare(children[1]->minV,children[0]->maxV) >=0)
                result = createInterval(littleZero, littleZero);
          }
      if (BVSGT == n.GetKind() && result ==NULL)
        {
          map<const ASTNode, IntervalType*>::iterator clock_it;
          clock_it = clockwise.find(n[0]);
          IntervalType* clock0 = NULL;
          IntervalType* clock1 = NULL;
          if (clock_it != clockwise.end())
            clock0 = clock_it->second;
          clock_it = clockwise.find(n[1]);
          if (clock_it != clockwise.end())
            clock1 = clock_it->second;

          if (clock0 != NULL || clock1 !=NULL)
            {
              if (clock0 == NULL)
                clock0 = children[0];
              if (clock1 == NULL)
                clock1 = children[1];

              if (clock0 != NULL && clock1 != NULL)
                {
/*
                  clock0->print();
                  clock1->print();
                  cerr << clock0->crossesSignedUnsigned(n[0].GetValueWidth()) << endl;
                  cerr << clock1->crossesSignedUnsigned(n[0].GetValueWidth()) << endl;
                  cerr << n;
*/

                  // if the rhs doesn't cross +ve/-ve boundary, and the min > max
                  if (!clock0->crossesSignedUnsigned(n[0].GetValueWidth())  && !clock1->crossesSignedUnsigned(n[1].GetValueWidth()))
                    {
                      if (CONSTANTBV::BitVector_Compare(clock0->minV,clock1->maxV) >0)
                        result = createInterval(littleOne, littleOne);

                      if (CONSTANTBV::BitVector_Compare(clock1->minV,clock0->maxV) >=0)
                        result = createInterval(littleZero, littleZero);
                    }
                }
            }
        }

      break;
      case BVGE:
      case BVSGE:
      if ((BVGE == n.GetKind() && knownC0 && knownC1) ||
               (BVSGE == n.GetKind() && knownC0 && knownC1
              && !CONSTANTBV::BitVector_bit_test(children[0]->maxV, n[0].GetValueWidth()-1)
              && !CONSTANTBV::BitVector_bit_test(children[1]->maxV, n[0].GetValueWidth()-1)
          ))
        {
          if (CONSTANTBV::BitVector_Lexicompare(children[0]->minV,children[1]->maxV) >=0)
            result = createInterval(littleOne, littleOne);
          if (CONSTANTBV::BitVector_Lexicompare(children[1]->minV,children[0]->maxV) > 0)
            result = createInterval(littleZero, littleZero);
        }
      break;
      case BVDIV:
      if (knownC1)
      {
    	  // When we're dividing by zero, we know nothing.
    	  if (!CONSTANTBV::BitVector_is_empty(children[1]->minV))
    	  {
              IntervalType * top =  (children[0] == NULL) ? freshUnsignedInterval(width) : children[0];
              result = freshUnsignedInterval(width);

              CBV remainder = CONSTANTBV::BitVector_Create(width, true);

              CBV tmp0 = CONSTANTBV::BitVector_Clone(top->minV);
              CONSTANTBV::ErrCode e = CONSTANTBV::BitVector_Div_Pos(result->minV, tmp0, children[1]->maxV, remainder);
              assert(0 == e);
              CONSTANTBV::BitVector_Destroy(tmp0);

              tmp0 = CONSTANTBV::BitVector_Clone(top->maxV);
              e = CONSTANTBV::BitVector_Div_Pos(result->maxV, tmp0, children[1]->minV, remainder);
              assert(0 == e);

              CONSTANTBV::BitVector_Destroy(tmp0);
              CONSTANTBV::BitVector_Destroy(remainder);
    	  }
      }
      break;
      case BVMOD:
      if (knownC1)
        {
          // When we're dividing by zero, we know nothing.
          if (!CONSTANTBV::BitVector_is_empty(children[1]->minV))
            {
              result = freshUnsignedInterval(n.GetValueWidth());
              CONSTANTBV::BitVector_Copy(result->maxV , children[1]->maxV);
              CONSTANTBV::BitVector_decrement(result->maxV);

              // If the top is known, and it's maximum is less, use that.
              if (knownC0 && CONSTANTBV::BitVector_Lexicompare(children[0]->maxV,result->maxV) < 0)
                CONSTANTBV::BitVector_Copy(result->maxV , children[0]->maxV);

            }
        }
      break;
      case BVSX:
      if (knownC0 && knownC1)
      {
    	  // If the maximum doesn't have the top bit set, then zero extend it.
    	  if (!CONSTANTBV::BitVector_bit_test(children[0]->maxV,n[0].GetValueWidth()-1))
    	  {
              result = freshUnsignedInterval(n.GetValueWidth());

              // Copy in the minimum and maximum.
        	  for (int i=0; i < n[0].GetValueWidth();i++)
        	  {
        		  if (CONSTANTBV::BitVector_bit_test(children[0]->maxV,i))
        			  CONSTANTBV::BitVector_Bit_On(result->maxV,i);
        		  else
        			  CONSTANTBV::BitVector_Bit_Off(result->maxV,i);

        		  if (CONSTANTBV::BitVector_bit_test(children[0]->minV,i))
        			  CONSTANTBV::BitVector_Bit_On(result->minV,i);
        		  else
        			  CONSTANTBV::BitVector_Bit_Off(result->minV,i);
        	  }

        	  for (int i=n[0].GetValueWidth(); i < n.GetValueWidth();i++)
        		  CONSTANTBV::BitVector_Bit_Off(result->maxV,i);
    	  }
      } else if (knownC1)
      {
          // Ignores what's already there for now..

          IntervalType * circ_result = freshUnsignedInterval(n.GetValueWidth());
          for (int i=0; i < n[0].GetValueWidth()-1;i++)
          {
              CONSTANTBV::BitVector_Bit_On(circ_result->maxV,i);
              CONSTANTBV::BitVector_Bit_Off(circ_result->minV,i);
          }

          for (int i=n[0].GetValueWidth()-1; i < n.GetValueWidth();i++)
          {
              CONSTANTBV::BitVector_Bit_Off(circ_result->maxV,i);
              CONSTANTBV::BitVector_Bit_On(circ_result->minV,i);
          }

          clockwise.insert(make_pair(n, circ_result));
      }

      break;
      case BVNEG:
      if (knownC0) // NOT of the bitvector.
        {
          result = freshUnsignedInterval(width);
          CONSTANTBV::BitVector_Copy(result->maxV,  children[0]->minV);
          CONSTANTBV::BitVector_Flip(result->maxV);
          CONSTANTBV::BitVector_Copy(result->minV,  children[0]->maxV);
          CONSTANTBV::BitVector_Flip(result->minV);
        }
      break;
      case BVUMINUS:
      if (knownC0)
        {
          // Imagine it's {00, 01},  the unary minus of these is: {00,11},
          // i.e. it's everything. When there's a zero, (except for [0,0]),
          // it will be everything.

          if (!CONSTANTBV::BitVector_is_empty(children[0]->minV))
            {
              result = freshUnsignedInterval(width);
              CONSTANTBV::BitVector_Copy(result->maxV, children[0]->minV);
              CONSTANTBV::BitVector_Flip(result->maxV);
              CONSTANTBV::BitVector_increment(result->maxV);

              CONSTANTBV::BitVector_Copy(result->minV, children[0]->maxV);
              CONSTANTBV::BitVector_Flip(result->minV);
              CONSTANTBV::BitVector_increment(result->minV);
            }
        }
      break;
      case ITE:
      if (children[1] != NULL && children[2] != NULL)
        {
          // Both terms and propositions.
          result = freshUnsignedInterval(width==0? 1: width);
          CBV min, max;
          if (CONSTANTBV::BitVector_Lexicompare(children[1]->minV, children[2]->minV) >0)
            min = children[2]->minV;
          else
            min = children[1]->minV;

          if (CONSTANTBV::BitVector_Lexicompare(children[1]->maxV, children[2]->maxV) >0)
            max = children[1]->maxV;
          else
            max = children[2]->maxV;

          CONSTANTBV::BitVector_Copy(result->minV, min);
          CONSTANTBV::BitVector_Copy(result->maxV, max);
        }
      break;
      case BVMULT:
      if (knownC0 && knownC1)
        {
          //  >=2 arity.
          CBV min,max;
          min = CONSTANTBV::BitVector_Create(2*width, true);
          max = CONSTANTBV::BitVector_Create(2*width, true);

          // Make the result interval 1.
          result = freshUnsignedInterval(width);
          CONSTANTBV::BitVector_increment(result->minV);
          CONSTANTBV::BitVector_Flip(result->maxV);
          CONSTANTBV::BitVector_increment(result->maxV);

          bool bad= false;
          for (int i =0; i < children.size(); i++)
            {
              if (children[i] == NULL)
                {
                  bad = true;
                  break;
                }
              CONSTANTBV::ErrCode e = CONSTANTBV::BitVector_Multiply(min, result->minV, children[i]->minV);
              assert (0 == e);

              e = CONSTANTBV::BitVector_Multiply(max, result->maxV, children[i]->maxV);
              assert (0 == e);

              if (CONSTANTBV::Set_Max(max) >= width)
                bad = true;

              for (int j = width; j < 2 * width; j++)
                {
                  if (CONSTANTBV::BitVector_bit_test(min, j))
                    bad = true;
                }

              CONSTANTBV::BitVector_Interval_Copy(result->minV, min, 0, 0, width);
              CONSTANTBV::BitVector_Interval_Copy(result->maxV, max, 0, 0, width);
            }
          CONSTANTBV::BitVector_Destroy(min);
          CONSTANTBV::BitVector_Destroy(max);
          if (bad)
            result = NULL;
        }
      break;
      //case BVLEFTSHIFT:
      // case BVAND:
      //case BVSRSHIFT:
       {
          // Todo two cases.
          // 1) The maximum shift of the maximum value doesn't overflow, and,
          // 2) The minimum shift of the minimum value completely overflows (to zero).
       }

      case BVRIGHTSHIFT:
      if (knownC0 || knownC1)
           {
             result = freshUnsignedInterval(width);

             if (children[0] == NULL)
               children[0] = freshUnsignedInterval(width);
             if (children[1] == NULL)
               children[1] = freshUnsignedInterval(width);

             // The maximum result is the maximum >> (minimum shift).
             if (CONSTANTBV::Set_Max(children[1]->minV) > 1 + log2(width) ||  *(children[1]->minV) > width)
             {
                 // The maximum is zero.
                 CONSTANTBV::BitVector_Flip(result->maxV);
             }
             else
             {
                 unsigned shift_amount = *(children[1]->minV);
                 CONSTANTBV::BitVector_Copy(result->maxV, children[0]->maxV);
                 while (shift_amount-- > 0)
                   {
                     CONSTANTBV::BitVector_shift_right(result->maxV,0);
                   }
             }

             // The minimum result is the minimum >> (maximum shift).
             if (CONSTANTBV::Set_Max(children[1]->maxV) > 1 + log2(width) || *(children[1]->maxV) > width)
             {
                   // The mimimum is zero. (which it's set to by default.).
             }
             else
             {
                 unsigned shift_amount = *(children[1]->maxV);
                 CONSTANTBV::BitVector_Copy(result->minV, children[0]->minV);
                 while (shift_amount-- > 0)
                    CONSTANTBV::BitVector_shift_right(result->minV,0);
             }
           }
      break;
      case BVPLUS:
      if (knownC0 && knownC1)
        {
          //  >=2 arity.
          result = freshUnsignedInterval(width);
          CONSTANTBV::BitVector_Flip(result->maxV); // make the max zero too.

          bool carry = false;

          for (int i =0; i < children.size(); i++)
            {
              if (children[i] == NULL)
                {
                  carry = true;
                  break;
                }

              CONSTANTBV::BitVector_add(result->maxV,result->maxV, children[i]->maxV,  &carry);
              if (carry)
                break;
              CONSTANTBV::BitVector_add(result->minV,result->minV, children[i]->minV,  &carry);
              if (carry)
                break;
            }

          if (carry)
            result = NULL;
        }
        break;
      case BVCONCAT:
      if ( (knownC0 || knownC1))
      {
          result = freshUnsignedInterval(n.GetValueWidth());

          // Copy in the lower part.
          if (knownC1)
          {
        	  // Copy in the minimum and maximum.
        	  for (int i=0; i < n[1].GetValueWidth();i++)
        	  {
        		  if (CONSTANTBV::BitVector_bit_test(children[1]->maxV,i))
        			  CONSTANTBV::BitVector_Bit_On(result->maxV,i);
        		  else
        			  CONSTANTBV::BitVector_Bit_Off(result->maxV,i);

        		  if (CONSTANTBV::BitVector_bit_test(children[1]->minV,i))
        			  CONSTANTBV::BitVector_Bit_On(result->minV,i);
        		  else
        			  CONSTANTBV::BitVector_Bit_Off(result->minV,i);
        	  }
          }

          if (knownC0)
          {
        	  // Copy in the minimum and maximum.
        	  for (int i=n[1].GetValueWidth(); i < n.GetValueWidth();i++)
        	  {
        		  if (CONSTANTBV::BitVector_bit_test(children[0]->maxV,i- n[1].GetValueWidth()))
        			  CONSTANTBV::BitVector_Bit_On(result->maxV,i);
        		  else
        			  CONSTANTBV::BitVector_Bit_Off(result->maxV,i);

        		  if (CONSTANTBV::BitVector_bit_test(children[0]->minV,i - n[1].GetValueWidth()))
        			  CONSTANTBV::BitVector_Bit_On(result->minV,i);
        		  else
        			  CONSTANTBV::BitVector_Bit_Off(result->minV,i);
        	  }
          }
      }
      break;
      default:
      {
          // Debugging!

    	  bool nonNull = true;
    	  // If all the children are known, output 'em.
    	  for (int i=0; i < n.Degree();i++)
    	  {
    		  if (children[i]== NULL)
    			  nonNull=false;
    	  }

    	  if (false && nonNull && n.GetKind() != SYMBOL && n.GetKind() != AND)
    	  {
    	      cerr << n;
    	      for (int i=0; i < n.Degree();i++)
    	        children[i]->print();
    	  }
      }
      }

      if (result != NULL && result->isComplete())
        result = NULL;

      if (result != NULL)
          result->checkUnsignedInvariant();

      // result will often be null (which we take to mean the maximum range).
      visited.insert(make_pair(n,result));
      return result;
    }

    STPMgr& bm;
    CBV littleOne;
    CBV littleZero;
    NodeFactory *nf;

  public:
    EstablishIntervals(STPMgr& _bm) : bm(_bm)
    {
      littleZero = makeCBV(1);
      littleOne = makeCBV(1);
      CONSTANTBV::BitVector_Fill(littleOne);
      nf = bm.defaultNodeFactory;
    }

    ~EstablishIntervals()
    {
      for (int i =0; i < toDeleteLater.size();i++)
        delete toDeleteLater[i];

      for (int i =0; i < likeAutoPtr.size();i++)
        CONSTANTBV::BitVector_Destroy(likeAutoPtr[i]);

      likeAutoPtr.clear();
      toDeleteLater.clear();
    }
  };
}
;
#endif /* ESTABLISHINTERVALS_H_ */
