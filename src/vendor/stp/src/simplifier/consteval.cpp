// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include <cassert>
#include "simplifier.h"

namespace BEEV
{

  //error printing
  static void BVConstEvaluatorError(CONSTANTBV::ErrCode e)
  {
    std::string ss("BVConstEvaluator:");
    ss += (const char*) BitVector_Error(e);
    FatalError(ss.c_str());
  }



// Const evaluator logical and arithmetic operations.
  ASTNode NonMemberBVConstEvaluator(STPMgr* _bm , const Kind k, const ASTVec& input_children, unsigned int inputwidth)
  {
	ASTNode OutputNode;

    ASTNode& ASTTrue = _bm->ASTTrue;
    ASTNode& ASTFalse = _bm->ASTFalse;

    unsigned int outputwidth = inputwidth;
    CBV output = NULL;

    CBV tmp0 = NULL;
    CBV tmp1 = NULL;

    unsigned int number_of_children = input_children.size();
    assert(number_of_children >=1);
    assert(k != BVCONST);

    ASTVec children;
    children.reserve(number_of_children);
    for (int i =0; i < number_of_children; i++)
    {
    	if (input_children[i].isConstant())
    		children.push_back(input_children[i]);
    	else
    		children.push_back(NonMemberBVConstEvaluator(input_children[i]));
    }

    if ((number_of_children ==2 || number_of_children == 1) && input_children[0].GetType() == BITVECTOR_TYPE)
    {
    //saving some typing. BVPLUS does not use these variables. if the
    //input BVPLUS has two nodes, then we want to avoid setting these
    //variables.
    if (1 == number_of_children)
      {
        tmp0 = children[0].GetBVConst();
      }
    else if (2 == number_of_children && k != BVPLUS)
      {
        tmp0 = children[0].GetBVConst();
        tmp1 = children[1].GetBVConst();
      }
	}

    switch (k)
      {
      case UNDEFINED:
      case READ:
      case WRITE:
      case SYMBOL:
    	    FatalError("BVConstEvaluator: term is not a constant-term");
        break;
      //case BVCONST:
//        OutputNode = t;
  //      break;
      case BVNEG:
        {
          output = CONSTANTBV::BitVector_Create(inputwidth, true);
          CONSTANTBV::Set_Complement(output, tmp0);
          OutputNode = _bm->CreateBVConst(output, outputwidth);
          break;
        }
      case BVSX:
      case BVZX:
        {
          output = CONSTANTBV::BitVector_Create(inputwidth, true);
          unsigned t0_width = input_children[0].GetValueWidth();
          if (inputwidth == t0_width)
            {
              CONSTANTBV::BitVector_Copy(output, tmp0);
              OutputNode = _bm->CreateBVConst(output, outputwidth);
            }
          else
            {
              bool topbit_sign = (k == BVSX)?(CONSTANTBV::BitVector_Sign(tmp0) < 0): false;

              if (topbit_sign)
                {
                  CONSTANTBV::BitVector_Fill(output);
                }
              CONSTANTBV::BitVector_Interval_Copy(output, tmp0, 0, 0, t0_width);
              OutputNode = _bm->CreateBVConst(output, outputwidth);
            }
          break;
        }

      case BVLEFTSHIFT:
      case BVRIGHTSHIFT:
      case BVSRSHIFT:
        {
          // load in the bitWidth.
          CBV width = CONSTANTBV::BitVector_Create(inputwidth, true);
          for (unsigned i = 0; i < sizeof(inputwidth) * 8; i++)
            if ((inputwidth & (0x1 << i)) != 0)
              CONSTANTBV::BitVector_Bit_On(width, i);

          output = CONSTANTBV::BitVector_Create(inputwidth, true);

          // Number of bits to shift it.
          ASTNode shiftNode = children[1];

          bool msb = CONSTANTBV::BitVector_msb_(tmp0);

          // If this shift is greater than the bitWidth, make it zero.
          if (CONSTANTBV::BitVector_Lexicompare(width, shiftNode.GetBVConst()) < 0)
            {
              if (k == BVSRSHIFT && msb)
                CONSTANTBV::Set_Complement(output, output);
            }
          else
            {
              // the shift is destructive, get a copy.
              CONSTANTBV::BitVector_Interval_Copy(output, tmp0, 0, 0, inputwidth);

              unsigned int shift = shiftNode.GetUnsignedConst();

              if (k == BVLEFTSHIFT)
                CONSTANTBV::BitVector_Move_Left(output, shift);
              else
                CONSTANTBV::BitVector_Move_Right(output, shift);

              if (k == BVSRSHIFT && msb)
                {
                  // signed shift, and the number was originally negative.
                  // Shift may be larger than the inputwidth.
                  for (unsigned int i = 0; i < min(shift, inputwidth); i++)
                    {
                      CONSTANTBV::BitVector_Bit_On(output, (inputwidth - 1 - i));
                    }
                  assert(CONSTANTBV::BitVector_Sign(output) == -1); //must be negative.
                }
            }

          OutputNode = _bm->CreateBVConst(output, outputwidth);

          CONSTANTBV::BitVector_Destroy(width);
          break;
        }


      case BVAND:
        {
        	assert(1 <= number_of_children);

        	output = CONSTANTBV::BitVector_Create(inputwidth, true);
        	CONSTANTBV::BitVector_Fill(output);

            for (ASTVec::iterator it = children.begin(), itend = children.end(); it != itend; it++)
              {
                CBV kk = (*it).GetBVConst();
                CONSTANTBV::Set_Intersection(output, output, kk);
              }

            OutputNode = _bm->CreateBVConst(output, outputwidth);
            break;
        }
      case BVOR:
        {
        	assert(1 <= number_of_children);

        	output = CONSTANTBV::BitVector_Create(inputwidth, true);

            for (ASTVec::iterator it = children.begin(), itend = children.end(); it != itend; it++)
              {
                CBV kk = (*it).GetBVConst();
                CONSTANTBV::Set_Union(output, output, kk);
              }

            OutputNode = _bm->CreateBVConst(output, outputwidth);
            break;
        }
      case BVXOR:
        {
          assert(2==number_of_children);
          output = CONSTANTBV::BitVector_Create(inputwidth, true);
          CONSTANTBV::Set_ExclusiveOr(output, tmp0, tmp1);
          OutputNode = _bm->CreateBVConst(output, outputwidth);
          break;
        }
      case BVSUB:
        {
          assert(2==number_of_children);
          output = CONSTANTBV::BitVector_Create(inputwidth, true);
          bool carry = false;
          CONSTANTBV::BitVector_sub(output, tmp0, tmp1, &carry);
          OutputNode = _bm->CreateBVConst(output, outputwidth);
          break;
        }
      case BVUMINUS:
        {
          output = CONSTANTBV::BitVector_Create(inputwidth, true);
          CONSTANTBV::BitVector_Negate(output, tmp0);
          OutputNode = _bm->CreateBVConst(output, outputwidth);
          break;
        }
      case BVEXTRACT:
        {
          output = CONSTANTBV::BitVector_Create(inputwidth, true);
          tmp0 = children[0].GetBVConst();
          unsigned int hi = children[1].GetUnsignedConst();
          unsigned int low = children[2].GetUnsignedConst();
          unsigned int len = hi - low + 1;

          CONSTANTBV::BitVector_Destroy(output);
          output = CONSTANTBV::BitVector_Create(len, false);
          CONSTANTBV::BitVector_Interval_Copy(output, tmp0, 0, low, len);
          outputwidth = len;
          OutputNode = _bm->CreateBVConst(output, outputwidth);
          break;
        }

      case BVCONCAT:
        {
          assert(2==number_of_children);
          output = CONSTANTBV::BitVector_Create(inputwidth, true);
          unsigned t0_width = children[0].GetValueWidth();
          unsigned t1_width = children[1].GetValueWidth();
          CONSTANTBV::BitVector_Destroy(output);

          output = CONSTANTBV::BitVector_Concat(tmp0, tmp1);
          outputwidth = t0_width + t1_width;
          OutputNode = _bm->CreateBVConst(output, outputwidth);

          break;
        }
      case BVMULT:
        {
        output = CONSTANTBV::BitVector_Create(inputwidth, true);
        CONSTANTBV::BitVector_increment(output);

        CBV tmp = CONSTANTBV::BitVector_Create(2 * inputwidth, true);

        for (ASTVec::iterator it = children.begin(), itend = children.end(); it != itend; it++)
          {
            CBV kk = (*it).GetBVConst();
            CONSTANTBV::ErrCode e = CONSTANTBV::BitVector_Multiply(tmp, output, kk);

            if (0 != e)
              {
                BVConstEvaluatorError(e);
              }
            CONSTANTBV::BitVector_Interval_Copy(output, tmp, 0, 0, inputwidth);

          }

        OutputNode = _bm->CreateBVConst(output, outputwidth);
        CONSTANTBV::BitVector_Destroy(tmp);
        break;
      }
      case BVPLUS:
        {
          output = CONSTANTBV::BitVector_Create(inputwidth, true);
          bool carry = false;
          for (ASTVec::iterator it = children.begin(), itend = children.end(); it != itend; it++)
            {
              CBV kk = (*it).GetBVConst();
              CONSTANTBV::BitVector_add(output, output, kk, &carry);
              carry = false;
            }
          OutputNode = _bm->CreateBVConst(output, outputwidth);
          break;
        }

        // SBVREM : Result of rounding the quotient towards
        // zero. i.e. (-10)/3, has a remainder of -1 
        //
        // SBVMOD : Result of rounding the quotient towards
        // -infinity. i.e. (-10)/3, has a modulus of 2.  EXCEPT THAT
        // if it divides exactly and the signs are different, then
        // it's equal to the dividend.
      case SBVDIV:
      case SBVREM:
        {
          assert(2==number_of_children);
          CBV quotient = CONSTANTBV::BitVector_Create(inputwidth, true);
          CBV remainder = CONSTANTBV::BitVector_Create(inputwidth, true);

          if (_bm->UserFlags.division_by_zero_returns_one_flag 
              && CONSTANTBV::BitVector_is_empty(tmp1))
            {
              // Expecting a division by zero. Just return one.
        	  if (k==SBVREM)
        		  OutputNode = children[0];
        	  else
        		  {
        	              if (CONSTANTBV::BitVector_bit_test(tmp0, inputwidth-1))
        	                OutputNode = _bm->CreateMaxConst(inputwidth);
        	              else
        	                OutputNode = _bm->CreateOneConst(inputwidth);
        		  }

        	  CONSTANTBV::BitVector_Destroy(remainder);
              CONSTANTBV::BitVector_Destroy(quotient);
            }
          else
            {
              CONSTANTBV::ErrCode e = 
                CONSTANTBV::BitVector_Divide(quotient, tmp0, tmp1, remainder);

              if (e != 0)
                {
                  cerr << "WARNING" << endl;
                  FatalError((const char*) CONSTANTBV::BitVector_Error(e));
                }

              if (SBVDIV == k)
                {
                  OutputNode = _bm->CreateBVConst(quotient, outputwidth);
                  CONSTANTBV::BitVector_Destroy(remainder);
                }
              else
                {
                  OutputNode = _bm->CreateBVConst(remainder, outputwidth);
                  CONSTANTBV::BitVector_Destroy(quotient);

                }
            }
          break;
        }

      case SBVMOD:
        {
          assert(2==number_of_children);
/*
          (bvsmod s t) abbreviates
              (let ((?msb_s ((_ extract |m-1| |m-1|) s))
                    (?msb_t ((_ extract |m-1| |m-1|) t)))
                (let ((abs_s (ite (= ?msb_s #b0) s (bvneg s)))
                      (abs_t (ite (= ?msb_t #b0) t (bvneg t))))
                  (let ((u (bvurem abs_s abs_t)))
                    (ite (= u (_ bv0 m))
                         u
                    (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
                         u
                    (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
                         (bvadd (bvneg u) t)
                    (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
                         (bvadd u t)
                         (bvneg u))))))))
*/

          assert(input_children[0].GetValueWidth() == input_children[1].GetValueWidth());

          bool isNegativeS = CONSTANTBV::BitVector_msb_(tmp0);
          bool isNegativeT = CONSTANTBV::BitVector_msb_(tmp1);

          CBV quotient = CONSTANTBV::BitVector_Create(inputwidth, true);
          CBV remainder = CONSTANTBV::BitVector_Create(inputwidth, true);
          tmp0 = CONSTANTBV::BitVector_Clone(tmp0);
          tmp1 = CONSTANTBV::BitVector_Clone(tmp1);

          if (_bm->UserFlags.division_by_zero_returns_one_flag
              && CONSTANTBV::BitVector_is_empty(tmp1))
            {
              // Return the top for a division be zero.
              OutputNode = children[0];
              CONSTANTBV::BitVector_Destroy(remainder);
            }
          else
            {
              if (!isNegativeS && !isNegativeT)
                {
                  // Signs are both positive
                  CONSTANTBV::ErrCode e = CONSTANTBV::BitVector_Div_Pos(quotient, tmp0, tmp1, remainder);
                  if (e != CONSTANTBV::ErrCode_Ok)
                    {
                      cerr << "Error code was:" << e << endl;
                      assert(e == CONSTANTBV::ErrCode_Ok);
                    }
                  OutputNode = _bm->CreateBVConst(remainder, outputwidth);
                }
              else if (isNegativeS && !isNegativeT)
                {
                  // S negative, T positive.
                  CBV tmp0b = CONSTANTBV::BitVector_Create(inputwidth, true);
                  CONSTANTBV::BitVector_Negate(tmp0b, tmp0);

                  CONSTANTBV::ErrCode e = CONSTANTBV::BitVector_Div_Pos(quotient, tmp0b, tmp1, remainder);
                  assert(e == CONSTANTBV::ErrCode_Ok);

                  CBV remb = CONSTANTBV::BitVector_Create(inputwidth, true);
                  CONSTANTBV::BitVector_Negate(remb, remainder);

                  if (CONSTANTBV::BitVector_is_empty(remb))
                  {
					OutputNode = _bm->CreateZeroConst(outputwidth);
                  }
                  else
                  {
                	CBV res = CONSTANTBV::BitVector_Create(inputwidth, true);
                	bool carry = false;
                	CONSTANTBV::BitVector_add(res, remb, tmp1, &carry);
					OutputNode = _bm->CreateBVConst(res, outputwidth);
                  }

                  CONSTANTBV::BitVector_Destroy(remb);
                  CONSTANTBV::BitVector_Destroy(tmp0b);
                  CONSTANTBV::BitVector_Destroy(remainder);
                }
              else if (!isNegativeS && isNegativeT)
                {
                  // If s is positive and t is negative
                  CBV tmp1b = CONSTANTBV::BitVector_Create(inputwidth, true);
                  CONSTANTBV::BitVector_Negate(tmp1b, tmp1);

                  CONSTANTBV::ErrCode e = CONSTANTBV::BitVector_Div_Pos(quotient, tmp0, tmp1b, remainder);

                  assert(e == CONSTANTBV::ErrCode_Ok);

                  if (CONSTANTBV::BitVector_is_empty(remainder))
                  {
					OutputNode = _bm->CreateZeroConst(outputwidth);
				  }
					else
				  {
					CBV res = CONSTANTBV::BitVector_Create(inputwidth, true);
	                bool carry = false;
					CONSTANTBV::BitVector_add(res, remainder, tmp1, &carry);
					OutputNode = _bm->CreateBVConst(res, outputwidth);
				  }

                  CONSTANTBV::BitVector_Destroy(tmp1b);
                  CONSTANTBV::BitVector_Destroy(remainder);
                }
              else if (isNegativeS && isNegativeT)
                {
                  // Signs are both negative
                  CBV tmp0b = CONSTANTBV::BitVector_Create(inputwidth, true);
                  CBV tmp1b = CONSTANTBV::BitVector_Create(inputwidth, true);
                  CONSTANTBV::BitVector_Negate(tmp0b, tmp0);
                  CONSTANTBV::BitVector_Negate(tmp1b, tmp1);

                  CONSTANTBV::ErrCode e = CONSTANTBV::BitVector_Div_Pos(quotient, tmp0b, tmp1b, remainder);
                  assert(e == CONSTANTBV::ErrCode_Ok);

                  CBV remb = CONSTANTBV::BitVector_Create(inputwidth, true);
                  CONSTANTBV::BitVector_Negate(remb, remainder);

                  OutputNode = _bm->CreateBVConst(remb, outputwidth);
                  CONSTANTBV::BitVector_Destroy(tmp0b);
                  CONSTANTBV::BitVector_Destroy(tmp1b);
                  CONSTANTBV::BitVector_Destroy(remainder);
                }
              else
                {
                  FatalError("never get called");
                }
            }

          CONSTANTBV::BitVector_Destroy(tmp0);
          CONSTANTBV::BitVector_Destroy(tmp1);
          CONSTANTBV::BitVector_Destroy(quotient);
        }
        break;

      case BVDIV:
      case BVMOD:
        {
          assert(2==number_of_children);

          if (_bm->UserFlags.division_by_zero_returns_one_flag 
              && CONSTANTBV::BitVector_is_empty(tmp1))
            {
              // a = bq + r, where b!=0 implies r < b. q is quotient, r remainder. i.e. a/b = q.
              // It doesn't matter what q is when b=0, but r needs to be a.
              if (k == BVMOD)
                OutputNode = children[0];
              else
                OutputNode = _bm->CreateOneConst(outputwidth);
                // Expecting a division by zero. Just return one.

            }
          else
            {
              CBV quotient = CONSTANTBV::BitVector_Create(inputwidth, true);
              CBV remainder = CONSTANTBV::BitVector_Create(inputwidth, true);

              // tmp0 is dividend, tmp1 is the divisor All parameters
              //to BitVector_Div_Pos must be distinct unlike
              //BitVector_Divide FIXME the contents of the second
              //parameter to Div_Pos is destroyed As tmp0 is currently
              //the same as the copy belonging to an ASTNode input_children[0] this
              //must be copied.
              tmp0 = CONSTANTBV::BitVector_Clone(tmp0);
              CONSTANTBV::ErrCode e = CONSTANTBV::BitVector_Div_Pos(quotient, tmp0, tmp1, remainder);
              CONSTANTBV::BitVector_Destroy(tmp0);

              if (0 != e)
                {
            	  CONSTANTBV::BitVector_Destroy(quotient);
            	  CONSTANTBV::BitVector_Destroy(remainder);
            	  //error printing
                  if (_bm->counterexample_checking_during_refinement)
                    {
                      output = CONSTANTBV::BitVector_Create(inputwidth, true);
                      OutputNode = _bm->CreateBVConst(output, outputwidth);
                      _bm->bvdiv_exception_occured = true;

                      //  CONSTANTBV::BitVector_Destroy(output);
                      break;
                    }
                  else
                    {
                      BVConstEvaluatorError(e);
                    }
                } //end of error printing

              //FIXME Not very standard in the current scheme
              if (BVDIV == k)
                {
                  OutputNode = _bm->CreateBVConst(quotient, outputwidth);
                  CONSTANTBV::BitVector_Destroy(remainder);
                }
              else
                {
                  OutputNode = _bm->CreateBVConst(remainder, outputwidth);
                  CONSTANTBV::BitVector_Destroy(quotient);
                }
            }
          break;
        }
      case ITE:
        {
          if (ASTTrue == input_children[0])
            OutputNode = children[1];
          else if (ASTFalse == input_children[0])
            OutputNode = children[2];
          else
            {
              cerr << tmp0;
              FatalError("BVConstEvaluator: ITE condiional must be either TRUE or FALSE:");
            }
        }
        break;
      case EQ:
        assert(2==number_of_children);
        if (CONSTANTBV::BitVector_equal(tmp0, tmp1))
          OutputNode = ASTTrue;
        else
          OutputNode = ASTFalse;
        break;
      case BVLT:
        assert(2==number_of_children);
        if (-1 == CONSTANTBV::BitVector_Lexicompare(tmp0, tmp1))
          OutputNode = ASTTrue;
        else
          OutputNode = ASTFalse;
        break;
      case BVLE:
        {
          assert(2==number_of_children);
          int comp = CONSTANTBV::BitVector_Lexicompare(tmp0, tmp1);
          if (comp <= 0)
            OutputNode = ASTTrue;
          else
            OutputNode = ASTFalse;
          break;
        }
      case BVGT:
        assert(2==number_of_children);
        if (1 == CONSTANTBV::BitVector_Lexicompare(tmp0, tmp1))
          OutputNode = ASTTrue;
        else
          OutputNode = ASTFalse;
        break;
      case BVGE:
        {
          assert(2==number_of_children);
          int comp = CONSTANTBV::BitVector_Lexicompare(tmp0, tmp1);
          if (comp >= 0)
            OutputNode = ASTTrue;
          else
            OutputNode = ASTFalse;
          break;
        }
      case BVSLT:
        assert(2==number_of_children);
        if (-1 == CONSTANTBV::BitVector_Compare(tmp0, tmp1))
          OutputNode = ASTTrue;
        else
          OutputNode = ASTFalse;
        break;
      case BVSLE:
        {
          assert(2==number_of_children);
          signed int comp = CONSTANTBV::BitVector_Compare(tmp0, tmp1);
          if (comp <= 0)
            OutputNode = ASTTrue;
          else
            OutputNode = ASTFalse;
          break;
        }
      case BVSGT:
        assert(2==number_of_children);
        if (1 == CONSTANTBV::BitVector_Compare(tmp0, tmp1))
          OutputNode = ASTTrue;
        else
          OutputNode = ASTFalse;
        break;
      case BVSGE:
        {
          assert(2==number_of_children);
          int comp = CONSTANTBV::BitVector_Compare(tmp0, tmp1);
          if (comp >= 0)
            OutputNode = ASTTrue;
          else
            OutputNode = ASTFalse;
          break;
        }
        
              case TRUE:
    	  OutputNode = ASTTrue;
    	  break;
      case FALSE:
    	  OutputNode = ASTFalse;
          break;
      case NOT:
			  if (ASTTrue == input_children[0])
				  return ASTFalse;
			  else if (ASTFalse == input_children[0])
				  return ASTTrue;
			  else
				  {
				  cerr << ASTFalse;
				  cerr << input_children[0];
				  FatalError("BVConstEvaluator: unexpected not input");
				  }

      case OR:
    	  OutputNode = ASTFalse;
        for (ASTVec::const_iterator it = children.begin(), itend = children.end(); it != itend; it++)
          if (ASTTrue == *it)
        	  OutputNode = ASTTrue;


        break;

      case NOR:
       {
		ASTNode o = ASTFalse;
		for (ASTVec::const_iterator it = children.begin(), itend =
				children.end(); it != itend; it++)
			if (ASTTrue == (*it)) {
				o = ASTTrue;
				break;
			}
		if (o == ASTTrue)
			OutputNode = ASTFalse;
		else
			OutputNode = ASTTrue;
		break;
	}


      case XOR:
      {
     	bool output = false;
  		for (ASTVec::const_iterator it = children.begin(), itend =
  				children.end(); it != itend; it++)
  		{
  			if (ASTTrue == *it)
  				output = !output; //parity.
  		}

  		if (output)
  			OutputNode = ASTTrue;
  		else
  			OutputNode = ASTFalse;

  		break;


      }

      case AND:
      {
    	  OutputNode = ASTTrue;
      for (ASTVec::const_iterator it = children.begin(), itend = children.end(); it != itend; it++)
              {
                if (ASTFalse == (*it))
                  {
                    OutputNode = ASTFalse;
                    break;
                  }
              }
            break;
      }

      case NAND:
      { OutputNode = ASTFalse;
      for (ASTVec::const_iterator it = children.begin(), itend = children.end(); it != itend; it++)
              {
                if (ASTFalse == (*it))
                  {
                    OutputNode = ASTTrue;
                    break;
                  }
              }
            break;
      }


      case IFF:
      {
        assert(2==number_of_children);
        const ASTNode&  t0 = children[0];
    	  const ASTNode&  t1 = children[1];
             if ((ASTTrue == t0 && ASTTrue == t1) || (ASTFalse == t0 && ASTFalse == t1))
               OutputNode = ASTTrue;
             else
               OutputNode = ASTFalse;
             break;
      }

      case IMPLIES:
      {
        assert(2==number_of_children);
        const ASTNode& t0 = children[0];
		const ASTNode& t1 = children[1];
		if ((ASTFalse == t0) || (ASTTrue == t0 && ASTTrue == t1))
			OutputNode = ASTTrue;
		else
			OutputNode = ASTFalse;
		break;
	}
        
      default:
        FatalError("BVConstEvaluator: The input kind is not supported yet:");
        break;
      }
    /*
      if(BVCONST != k){
      cerr<<inputwidth<<endl;
      cerr<<"------------------------"<<endl;
      t.LispPrint(cerr);
      cerr<<endl;
      OutputNode.LispPrint(cerr);
      cerr<<endl<<"------------------------"<<endl;
      }
    */
    assert(OutputNode.isConstant());
    //UpdateSimplifyMap(t,OutputNode,false);
    return OutputNode;
  } //End of BVConstEvaluator

  // Const evaluator logical and arithmetic operations.
    ASTNode NonMemberBVConstEvaluator(const ASTNode& t)
    {
        if (t.isConstant())
    	 	return t;

    	return NonMemberBVConstEvaluator(t.GetSTPMgr(), t.GetKind(), t.GetChildren(),  t.GetValueWidth());
    }


  ASTNode Simplifier::BVConstEvaluator(const ASTNode& t)
  {
	  if (t.isConstant())
		return t;

	  ASTNode OutputNode;

	  if (CheckSubstitutionMap(t, OutputNode))
	      return OutputNode;

	  OutputNode = NonMemberBVConstEvaluator(t);
	  UpdateSolverMap(t, OutputNode);
	  return OutputNode;
  }
}; //end of namespace BEEV
