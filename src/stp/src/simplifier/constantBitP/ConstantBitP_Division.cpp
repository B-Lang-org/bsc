#include "ConstantBitP_TransferFunctions.h"
#include "ConstantBitP_Utility.h"
#include <set>
#include <stdexcept>
#include "../../AST/AST.h"
#include "../../simplifier/simplifier.h"

namespace simplifier {
namespace constantBitP {
using std::endl;
using std::pair;
using std::set;

const bool debug_division = false;
extern std::ostream& log;

using BEEV::STPMgr;

enum WhatIsOutput {
	REMAINDER_IS_OUTPUT, QUOTIENT_IS_OUTPUT
};

enum Operation {
	SIGNED_DIVISION, SIGNED_REMAINDER, SIGNED_MODULUS
};

// For unsigned 3-bit exhaustive, there are 1119 differences for unsigned division.


// a/b and a%b. a=bq +r. Where b!=0 implies r<b. Multiplication and addition don't overflow.

// returning true = conflict.
// Fix value of a to b.
bool fix(FixedBits& a, const FixedBits& b, const int i) {
	if (!b.isFixed(i))
		return false;

	if (a.isFixed(i) && b.isFixed(i) && (a.getValue(i) ^ b.getValue(i)))
		return true;

	if (!a.isFixed(i) && b.isFixed(i)) {
		a.setFixed(i, true);
		a.setValue(i, b.getValue(i));
		return false;
	}

	return false;
}

FixedBits cbvToFixedBits(BEEV::CBV low, unsigned width)
{
  FixedBits lowBits(width,false);
      for (int i = width - 1; i >= 0; i--)
        {
          if (CONSTANTBV::BitVector_bit_test(low, i))
            {
              lowBits.setFixed(i, true);
              lowBits.setValue(i, true);
            }
          else
            {
              lowBits.setFixed(i, true);
              lowBits.setValue(i, false);

            }
        }
      return lowBits;
    }


// The value "b" is in the range [low,high] inclusive.
// Unfortunately it's not idempotent, <....1> [5,6], doesn't completely set it.
Result fix(FixedBits& b, BEEV::CBV low, BEEV::CBV high)
{
    FixedBits init =b;
      const int width = b.getWidth();

	FixedBits highBits = cbvToFixedBits(high,width);
	FixedBits lowBits = cbvToFixedBits(low,width);

	vector<FixedBits*> c;
	c.push_back(&b);
	c.push_back(&highBits);


	FixedBits t(1,true);
	t.setFixed(0,true);
	t.setValue(0,true);
	Result result1 =  bvLessThanEqualsBothWays(c,t);

	c.clear();
	c.push_back(&lowBits);
        c.push_back(&b);
	Result result2 =  bvLessThanEqualsBothWays(c,t);

	Result result = merge(result1, result2);
	if (result == CONFLICT)
	  return CONFLICT;

	for (int i = width - 1; i >= 0; i--) {
		if ((CONSTANTBV::BitVector_bit_test(low, i)
				== CONSTANTBV::BitVector_bit_test(high, i))) {
			bool toFix = CONSTANTBV::BitVector_bit_test(low, i);
			if (b.isFixed(i)) {
				if (b.getValue(i) != toFix) {
					return CONFLICT;
				}
			} else {
				b.setFixed(i, true);
				b.setValue(i, toFix);
			}
		} else
			break;
	}

	if (!FixedBits::equals(init, b))
	  return CHANGED;
	return NO_CHANGE;
}

Result bvUnsignedQuotientAndRemainder2(vector<FixedBits*>& children,
		FixedBits& output, STPMgr* bm, WhatIsOutput whatIs);


Result bvUnsignedQuotientAndRemainder(vector<FixedBits*>& children,
		FixedBits& output, STPMgr* bm, WhatIsOutput whatIs) {
	assert(output.getWidth() == children[0]->getWidth());
	assert(output.getWidth() == children[1]->getWidth());
	assert(children.size() == 2);

	if (whatIs != QUOTIENT_IS_OUTPUT)
	{
		return bvUnsignedQuotientAndRemainder2(children, output, bm, whatIs);
	}

	FixedBits& a = *children[0];
	FixedBits& b = *children[1];

	const unsigned width = a.getWidth();

	BEEV::CBV minTop = CONSTANTBV::BitVector_Create(width, true);
	BEEV::CBV maxTop = CONSTANTBV::BitVector_Create(width, true);

	setUnsignedMinMax(a, minTop, maxTop);

	BEEV::CBV minBottom = CONSTANTBV::BitVector_Create(width, true);
	BEEV::CBV maxBottom = CONSTANTBV::BitVector_Create(width, true);

	setUnsignedMinMax(b, minBottom, maxBottom);

	BEEV::CBV minQuotient = CONSTANTBV::BitVector_Create(width, true);
	BEEV::CBV maxQuotient = CONSTANTBV::BitVector_Create(width, true);

	BEEV::CBV minRemainder = CONSTANTBV::BitVector_Create(width, true);
	BEEV::CBV maxRemainder = CONSTANTBV::BitVector_Create(width, true);

	if (whatIs == QUOTIENT_IS_OUTPUT) {
		setUnsignedMinMax(output, minQuotient, maxQuotient);

		for (int i = 0; i < width; i++)
			CONSTANTBV::BitVector_Bit_On(maxRemainder, i);
	}
	else
	{
		setUnsignedMinMax(output, minRemainder, maxRemainder);

		for (int i =0; i < width;i++)
			CONSTANTBV::BitVector_Bit_On(maxQuotient,i);
	}

	// need to clean up these at end.
	BEEV::CBV one = CONSTANTBV::BitVector_Create(width, true);
	CONSTANTBV::BitVector_increment(one);
	// quotient and remainder.
	BEEV::CBV q = CONSTANTBV::BitVector_Create(width, true);
	BEEV::CBV r = CONSTANTBV::BitVector_Create(width, true);
	// misc.
	BEEV::CBV copy = CONSTANTBV::BitVector_Create(width, true);
	BEEV::CBV copy2 = CONSTANTBV::BitVector_Create(width, true);
	BEEV::CBV multR = CONSTANTBV::BitVector_Create(width, true);

	if (debug_division) {
		log << "--" << endl;
		log << "initial" << endl;
		log << "a:[" << *minTop << "," << *maxTop << "]";
		log << " / b:[" << *minBottom << "," << *maxBottom << "] = ";
		log << "[" << *minQuotient << "," << *maxQuotient << "]";
		log << " rem [" << *minRemainder << "," << *maxRemainder << "]";
		log << endl;
	}

        // If a bit is changed, then we fixed point again.
        bool bitEverChanged = false;
        bool bitJustChanged = true;
	Result result = NO_CHANGE;

        // We loop. There are 6 cases.
	while (bitJustChanged) {
		bitJustChanged = false;

		bool changed = true;

		int iteration = 0;
		while (changed) {
			changed = false;
			CONSTANTBV::ErrCode e;

		        // The main loop doesn't work if there is a division by zero possible.
		        // If the minimum bottom is zero, but the minimum quotient is > 1, then in our semantics
		        // of 1/0 = 1
		        if (CONSTANTBV::BitVector_is_empty(minBottom) && CONSTANTBV::BitVector_Lexicompare(minQuotient, one) > 0)
		          {
		            CONSTANTBV::BitVector_increment(minBottom);
		            if (CONSTANTBV::BitVector_Lexicompare(minBottom, maxBottom) > 0)
		              {
		                result = CONFLICT;
		                goto end;
		              }
		          }

		        if (CONSTANTBV::BitVector_is_empty(minBottom))
		          {
		            goto end; // Possible division by zero. Hard to work with..
		          }

			bool carry_1 = false;
			CONSTANTBV::BitVector_sub(copy, minTop, minRemainder, &carry_1);
			if (!carry_1) // Not sure if it goes negative.
			{
				e = CONSTANTBV::BitVector_Div_Pos(q, copy, maxBottom, r);
				assert(e == CONSTANTBV::ErrCode_Ok);

				if (CONSTANTBV::BitVector_Lexicompare(minQuotient, q) < 0) {
					if (debug_division) {
						log << "1 minQ) " << *minTop;
						log << " / " << *maxBottom;
						log << " = " << *q;
						log << " r " << *r << endl;
					}

					// min quotient is bigger. Bring in.
					CONSTANTBV::BitVector_Copy(minQuotient, q);
					changed = true;
				}
			}

			CONSTANTBV::BitVector_Copy(copy, maxTop);
			//bool carry_2 = false;
			//CONSTANTBV::BitVector_sub(copy,maxTop,minRemainder,&carry_2);
			//assert(!carry_1); // Not sure if it goes negative.

			e = CONSTANTBV::BitVector_Div_Pos(q, copy, minBottom, r);
			assert(e == CONSTANTBV::ErrCode_Ok);

			if (CONSTANTBV::BitVector_Lexicompare(maxQuotient, q) > 0) {
				if (debug_division) {
					log << "2 maxQ) " << *maxTop;
					log << " / " << *minBottom;
					log << " = " << *q;
					log << " r " << *r << endl;
				}

				CONSTANTBV::BitVector_Copy(maxQuotient, q); // copy the reduced value in.
				changed = true;
			}

			CONSTANTBV::BitVector_Copy(copy, maxQuotient);
			e = CONSTANTBV::BitVector_Mul_Pos(multR, copy, maxBottom, true);
			bool carry = false;
			CONSTANTBV::BitVector_sub(copy, maxBottom, one, &carry);
			CONSTANTBV::BitVector_add(copy2, multR, copy, &carry);
			CONSTANTBV::BitVector_Copy(multR, copy2);
			// involved. eek.


			if (e == CONSTANTBV::ErrCode_Ok
					&& CONSTANTBV::BitVector_Lexicompare(maxTop, multR) > 0) {
				if (debug_division) {
					log << "3 maxT) " << *maxQuotient;
					log << " * " << *maxBottom;
					log << " = " << *multR << endl;
				}
				CONSTANTBV::BitVector_Copy(maxTop, multR);
				changed = true;
			}

			CONSTANTBV::BitVector_Copy(copy, minBottom);

			//  If this is strict then it seems to be treated as signed, so it is considered to overflow
			// if a bit moves into the top of multR.
			e = CONSTANTBV::BitVector_Mul_Pos(multR, copy, minQuotient, false);
			//cerr << e << endl;


			if (e == CONSTANTBV::ErrCode_Ok && CONSTANTBV::BitVector_Lexicompare(minTop, multR) < 0)
			  {
				if (debug_division) {
					log << "4 minT) " << *minQuotient;
					log << " * " << *minBottom;
					log << " = " << *multR << endl;
				}
				CONSTANTBV::BitVector_Copy(minTop, multR);
				changed = true;
			}

			if (CONSTANTBV::BitVector_Lexicompare(minQuotient, one) >= 0) {
				// not going to divide by zero.

				CONSTANTBV::BitVector_Copy(copy, maxTop);
				e = CONSTANTBV::BitVector_Div_Pos(q, copy, minQuotient, r);
				assert(e == CONSTANTBV::ErrCode_Ok);

				if (CONSTANTBV::BitVector_Lexicompare(maxBottom, q) > 0) {
					if (debug_division) {
						log << "5 maxB) " << *maxTop;
						log << " / " << *minQuotient;
						log << " = " << *q;
						log << " r " << *r << endl;
					}

					// min quotient is bigger. Bring in.
					CONSTANTBV::BitVector_Copy(maxBottom, q);
					changed = true;
				}
			}


			  // This rule increases the minimum of the bottom.
			 //  let a be the min of the top,
			 //  let q be the maximum of the quotient,
			 //  let b be the min. of the bottom.
			  // then a= bq +r
			  // so a = bq + (b-1)  // if the max. of r is one less than b.
			  // so (1+a) / (q+1) = b.
			 // We round the division up.
                         {
                           bool carry = false;
                           CONSTANTBV::BitVector_add(copy, minTop, one, &carry);
                           bool carry2 = false;
                           CONSTANTBV::BitVector_add(copy2, maxQuotient, one, &carry2);
                           if (!carry && !carry2)
                             {
                               e = CONSTANTBV::BitVector_Div_Pos(q, copy, copy2, r);
                               assert(e == CONSTANTBV::ErrCode_Ok);
                               if (CONSTANTBV::BitVector_Lexicompare(q, one) >= 0)
                                {
                                   CONSTANTBV::BitVector_add(copy, q, one, &carry);
                                   if (!carry && (CONSTANTBV::BitVector_Lexicompare(minBottom, q) < 0))
                                     {

                                       if (debug_division)
                                        {
                                          log << "6 min_3_B) ";
                                          log << "minBottom" << *minBottom << " " ;
                                          log << "q" << *q << endl;
                                        }

                                       // min quotient is bigger. Bring in.
                                       CONSTANTBV::BitVector_Copy(minBottom, q);
                                       changed = true;
                                     }
                                }


                             }
                         }

			// Don't know why we don't need to check the intervals on the others?
			if (CONSTANTBV::BitVector_Lexicompare(minQuotient, maxQuotient) > 0) {
				if (debug_division) {
					log << "conflict" << endl;
					log << "a:[" << *minTop << "," << *maxTop << "]";
					log << " / b:[" << *minBottom << "," << *maxBottom
							<< "] = ";
					log << "[" << *minQuotient << "," << *maxQuotient << "]";
					log << endl;
				}

				result = CONFLICT;
				goto end;
			}


			if (debug_division) {
				log << "intermediate" << endl;
				log << "a:[" << *minTop << "," << *maxTop << "]";
				log << " / b:[" << *minBottom << "," << *maxBottom << "] = ";
				log << "[" << *minQuotient << "," << *maxQuotient << "]";
				log << endl;
			}
			iteration++;
			//if (iteration==2 && changed)
					//exit(1);
		}

		if (debug_division) {
			log << "final" << endl;
			log << "a:[" << *minTop << "," << *maxTop << "]";
			log << " / b:[" << *minBottom << "," << *maxBottom << "] = ";
			log << "[" << *minQuotient << "," << *maxQuotient << "]";
			log << endl;
		}

		{
                Result r1 = fix(a, minTop, maxTop);
                if (r1 == CHANGED)
                  r1 = merge(r1,fix(a, minTop, maxTop));

                Result r2 = fix(b, minBottom, maxBottom);
                if (r2 == CHANGED) // We call is a second time because it's not idepotent..
                  r2 = merge(r2,fix(b, minBottom, maxBottom));

                Result r3;
                if (whatIs == QUOTIENT_IS_OUTPUT)
                  {
                    r3 = fix(output, minQuotient, maxQuotient);
                    if (r3 == CHANGED)
                      r3 = merge(r3,fix(output, minQuotient, maxQuotient));
                  }
                else
                        r3 = fix(output, minRemainder, maxRemainder);


			if (r1 == CONFLICT || r2 == CONFLICT || r3 == CONFLICT)
			{
				result = CONFLICT;
				goto end;
			}
			assert(result != CONFLICT);

			if (r1 == CHANGED || r2 == CHANGED || r3 == CHANGED)
				result = CHANGED;
		}

		// check that fixing bits hasn't tightened intervals. If it has we need to resolve.
		if (result == CHANGED) {
			bool tightened = false;

			setUnsignedMinMax(output, copy, copy2);

			if (whatIs == QUOTIENT_IS_OUTPUT)
			{
			if (CONSTANTBV::BitVector_Lexicompare(minQuotient, copy) < 0
					|| CONSTANTBV::BitVector_Lexicompare(maxQuotient, copy2)
							> 0)
				tightened = true;
			}
			else
			{
				if (CONSTANTBV::BitVector_Lexicompare(minRemainder, copy) < 0
						|| CONSTANTBV::BitVector_Lexicompare(maxRemainder, copy2)
								> 0)
					tightened = true;
			}

			setUnsignedMinMax(b, copy, copy2);
			if (CONSTANTBV::BitVector_Lexicompare(minBottom, copy) < 0
					|| CONSTANTBV::BitVector_Lexicompare(maxBottom, copy2) > 0)
				tightened = true;

			setUnsignedMinMax(a, copy, copy2);
			if (CONSTANTBV::BitVector_Lexicompare(minTop, copy) < 0
					|| CONSTANTBV::BitVector_Lexicompare(maxTop, copy2) > 0)
				tightened = true;

			if (tightened) {
				setUnsignedMinMax(a, minTop, maxTop);
				setUnsignedMinMax(b, minBottom, maxBottom);
				if (whatIs == QUOTIENT_IS_OUTPUT)
					setUnsignedMinMax(output, minQuotient, maxQuotient);
				else
					setUnsignedMinMax(output, minRemainder, maxRemainder);

				bitEverChanged = true;
				bitJustChanged = true;
			}
		}

	}

	end:
	// Destroy range variables.
	CONSTANTBV::BitVector_Destroy(minTop);
	CONSTANTBV::BitVector_Destroy(maxTop);
	CONSTANTBV::BitVector_Destroy(minBottom);
	CONSTANTBV::BitVector_Destroy(maxBottom);
	CONSTANTBV::BitVector_Destroy(minQuotient);
	CONSTANTBV::BitVector_Destroy(maxQuotient);
	CONSTANTBV::BitVector_Destroy(minRemainder);
	CONSTANTBV::BitVector_Destroy(maxRemainder);


	// Destroy helpers.
	CONSTANTBV::BitVector_Destroy(copy);
	CONSTANTBV::BitVector_Destroy(copy2);
	CONSTANTBV::BitVector_Destroy(multR);
	CONSTANTBV::BitVector_Destroy(q);
	CONSTANTBV::BitVector_Destroy(r);
	CONSTANTBV::BitVector_Destroy(one);

	if (result == CONFLICT)
		return CONFLICT;

	if (bitEverChanged)
		return CHANGED;
	return result;
}

// (a/b) = q
// Solving: (a = q * b + r) AND (r < b).
Result bvUnsignedQuotientAndRemainder2(vector<FixedBits*>& children,
		FixedBits& output, STPMgr* bm, WhatIsOutput whatIs) {
	assert(output.getWidth() == children[0]->getWidth());
	assert(output.getWidth() == children[1]->getWidth());
	assert(children.size() == 2);

	unsigned int newWidth = 2 * output.getWidth();
	// Create Widenend copies.
	FixedBits a(newWidth, false);
	FixedBits b(newWidth, false);

	FixedBits q(newWidth, false);
	FixedBits r(newWidth, false);

	// intermediate values.
	FixedBits times(newWidth, false);

	a.copyIn(*children[0]);
	b.copyIn(*children[1]);

	assert(!b.containsZero());

	if (whatIs == QUOTIENT_IS_OUTPUT)
		q.copyIn(output);
	else if (whatIs == REMAINDER_IS_OUTPUT)
		r.copyIn(output);
	else
		throw std::runtime_error("sdjjfas");

	FixedBits aCopy(newWidth, false);
	FixedBits bCopy(newWidth, false);
	FixedBits rCopy(newWidth, false);
	FixedBits qCopy(newWidth, false);

	// Times and plus must not overflow.
	for (unsigned i = (unsigned) output.getWidth(); i < newWidth; i++) {
		//No overflow.
		times.setFixed(i, true);
		times.setValue(i, false);

		// Everything is zero extended.
		a.setFixed(i, true);
		a.setValue(i, false);
		b.setFixed(i, true);
		b.setValue(i, false);

		//Multiplication must not overflow.
		r.setFixed(i, true);
		r.setValue(i, false);
		q.setFixed(i, true);
		q.setValue(i, false);
	}

	// True bit.
	FixedBits trueBit(1, true);
	trueBit.setFixed(0, true);
	trueBit.setValue(0, true);

	Result result = NO_CHANGE;

	vector<FixedBits*> addChildren;
	addChildren.push_back(&times);
	addChildren.push_back(&r);

	vector<FixedBits*> multiplicationChildren;
	multiplicationChildren.push_back(&q);
	multiplicationChildren.push_back(&b);

	do {
		aCopy = a;
		bCopy = b;
		rCopy = r;
		qCopy = q;

		if (debug_division) {
			log << "p1:" << a << "/" << b << "=" << q << "rem(" << r << ")"
					<< endl;
			log << "times" << times << endl;
		}

		result = bvLessThanBothWays(r, b, trueBit); // (r < b)
		if (result == CONFLICT)
			return CONFLICT;

		result = bvMultiplyBothWays(multiplicationChildren, times, bm);
		if (result == CONFLICT)
			return CONFLICT;

		result = bvAddBothWays(addChildren, a);
		if (result == CONFLICT)
			return CONFLICT;
	} while (!(FixedBits::equals(aCopy, a) && FixedBits::equals(bCopy, b)
			&& FixedBits::equals(rCopy, r) && FixedBits::equals(qCopy, q)));

	bool conflict = false;
	for (int i = 0; i < output.getWidth(); i++) {
		if (whatIs == QUOTIENT_IS_OUTPUT)
			conflict |= fix(output, q, i);
		else if (whatIs == REMAINDER_IS_OUTPUT)
			conflict |= fix(output, r, i);
		else
			throw std::runtime_error("sdjjfas");

		conflict |= fix(*children[0], a, i);
		conflict |= fix(*children[1], b, i);
	}

	if (debug_division)
		cerr << endl;

	if (conflict)
		return CONFLICT;

	return NOT_IMPLEMENTED;
}

Result bvUnsignedModulusBothWays(vector<FixedBits*>& children,
		FixedBits& output, STPMgr* bm) {



        Result r1 = NO_CHANGE;
        vector<FixedBits*> v;
      v.push_back(&output);
      v.push_back(children[0]);
      FixedBits truN(1,true);
       truN.setFixed(0,true);
       truN.setValue(0,true);
      r1= bvLessThanEqualsBothWays(v, truN);


	if (children[1]->containsZero())
		return r1;

	if (debug_division)
		log <<  *(children[0]) << "bvmod" << *(children[1]) << "="
				<< output << endl;

	Result r = bvUnsignedQuotientAndRemainder(children, output, bm,
			REMAINDER_IS_OUTPUT);

	// Doesn't even do constant propagation.
	// <10>bvmod<11>=<-->
	if (r != CONFLICT && children[0]->isTotallyFixed()
			&& children[1]->isTotallyFixed() && !output.isTotallyFixed()) {

	  if (debug_division)
	    {
	    log << "Not even constant prop!" << *(children[0]) << "bvmod"
				<< *(children[1]) << "=" << output << endl;
	    }

	  //assert(output.isTotallyFixed());
	}

	if (r == CONFLICT || r==CHANGED)
	  return r;

	return r1;
}

    Result
    bvUnsignedDivisionBothWays(vector<FixedBits*>& children, FixedBits& output, STPMgr* bm)
    {
      Result r0 = NO_CHANGE;

      // Enforce that the output must be less than the numerator.
      // Make special allowance for 0/0 = 1.
      for (int i = children[0]->getWidth() - 1; i > 0; i--)
        {
          if (children[0]->isFixedToZero(i))
            {
              if (output.isFixedToOne(i))
                return CONFLICT;
              else if (!output.isFixed(i))
                {
                  output.setFixed(i, true);
                  output.setValue(i, false);
                  r0 = CHANGED;
                }
            }
          else
            {
              break;
            }
        }

      Result r = bvUnsignedQuotientAndRemainder(children, output, bm, QUOTIENT_IS_OUTPUT);

      return merge(r0,r);
    }

bool canBe(const FixedBits& b, int index, bool value) {
	if (!b.isFixed(index))
		return true;
	else
		return (!(b.getValue(index) ^ value));
}

// This provides a way to call the process function with fewer arguments.
struct Data {
	FixedBits &tempA;
	FixedBits &tempB;
	FixedBits &tempOutput;
	FixedBits &workingA;
	FixedBits &workingB;
	FixedBits &workingOutput;
	unsigned int signBit;

	Data(FixedBits &_tempA, FixedBits &_tempB, FixedBits &_tempOutput,
			FixedBits &_workingA, FixedBits &_workingB,
			FixedBits &_workingOutput) :
		tempA(_tempA), tempB(_tempB), tempOutput(_tempOutput), workingA(
				_workingA), workingB(_workingB), workingOutput(_workingOutput) {
		signBit = tempOutput.getWidth() - 1;
	}

	void process(bool& first) {
		if (first) {
			workingA = tempA;
			workingB = tempB;
			workingOutput = tempOutput;
		} else {
			workingA = FixedBits::meet(workingA, tempA);
			workingB = FixedBits::meet(workingB, tempB);
			workingOutput = FixedBits::meet(workingOutput, tempOutput);
		}
		first = false;
	}

	void set(const FixedBits& a, const FixedBits&b, const FixedBits& output,
			bool aTop, bool bTop) {
		tempA = a;
		tempB = b;
		tempOutput = output;
		tempA.setFixed(signBit, true);
		tempA.setValue(signBit, aTop);

		tempB.setFixed(signBit, true);
		tempB.setValue(signBit, bTop);
	}

	void print() {
		cerr << "Working: ";
		cerr << workingA << "/";
		cerr << workingB << "=";
		cerr << workingOutput << endl;

		cerr << "Temps:    ";
		cerr << tempA << "/";
		cerr << tempB << "=";
		cerr << tempOutput << endl;
	}
};

Result negate(FixedBits& input, FixedBits& output) {
	vector<FixedBits*> negChildren;

	negChildren.push_back(&input);
	return bvUnaryMinusBothWays(negChildren, output);
}

// This is preposterously complicated. We execute four cases then take the union of them.
//
Result bvSignedDivisionRemainderBothWays(vector<FixedBits*>& children,
		FixedBits& output, STPMgr* bm, Result(*tf)(vector<FixedBits*>&,
				FixedBits&, STPMgr* bm), const Operation op) {
	assert(output.getWidth() == children[0]->getWidth());
	assert(output.getWidth() == children[1]->getWidth());
	assert(children.size() == 2);

	const FixedBits& a = *children[0];
	const FixedBits& b = *children[1];

	assert(&a != &b);

	const unsigned int inputWidth = output.getWidth();
	const unsigned int signBit = output.getWidth() - 1;

	FixedBits workingA(inputWidth, false);
	FixedBits workingB(inputWidth, false);
	FixedBits workingOutput(inputWidth, false);

	FixedBits tempA = a;
	FixedBits tempB = b;
	FixedBits tempOutput = output;

	vector<FixedBits*> tempChildren;
	tempChildren.push_back(&tempA);
	tempChildren.push_back(&tempB);
	Result r = NO_CHANGE;

	if (b.containsZero())
		return NO_CHANGE;

	Data data(tempA, tempB, tempOutput, workingA, workingB, workingOutput);

	while (true)
        {
          if (debug_division)
            {
              cerr << "start:";
              cerr << a << "/";
              cerr << b << "=";
              cerr << output << endl;
            }

		bool first = true;

		if (canBe(a, signBit, false) && canBe(b, signBit, false)) {
			//     (bvudiv s t)
			r = NO_CHANGE;
			data.set(a, b, output, false, false);

			r = tf(tempChildren, tempOutput, bm);
			if (r != CONFLICT) {
				if (debug_division)
					cerr << "case A" << endl;
				data.process(first);
			}
		}

		if (canBe(a, signBit, true) && canBe(b, signBit, false)) {
			// (bvneg (bvudiv (bvneg a) b))
			r = NO_CHANGE;
			data.set(a, b, output, true, false);

			FixedBits negA(inputWidth, false);

			vector<FixedBits*> negChildren;
			negChildren.push_back(&negA);
			r = bvUnaryMinusBothWays(negChildren, tempA); // get NegA
			//cerr << negA << " " << tempA << endl;
			assert(r != CONFLICT);

			//modulus: (bvadd (bvneg (bvurem (bvneg s) t)) t)
			FixedBits wO(inputWidth, false);
			if (op == SIGNED_MODULUS) {
				vector<FixedBits*> ch;
				ch.push_back(&wO);
				ch.push_back(&tempB);
				r = bvAddBothWays(ch, tempOutput);
				assert(r != CONFLICT);
			} else
				wO = tempOutput;

			FixedBits negOutput(inputWidth, false);
			negChildren.clear();
			negChildren.push_back(&negOutput);
			r = bvUnaryMinusBothWays(negChildren, wO);
			assert(r != CONFLICT);

			negChildren.clear();
			negChildren.push_back(&negA);
			negChildren.push_back(&tempB);

			r = tf(negChildren, negOutput, bm);
			if (r != CONFLICT) {
				negChildren.clear();
				negChildren.push_back(&wO);
				r = bvUnaryMinusBothWays(negChildren, negOutput);

				if (r != CONFLICT) {
					if (op == SIGNED_MODULUS) {
						vector<FixedBits*> ch;
						ch.push_back(&wO);
						ch.push_back(&tempB);
						r = bvAddBothWays(ch, tempOutput);
					} else
						tempOutput = wO;

					if (r != CONFLICT) {
						negChildren.clear();
						negChildren.push_back(&tempA);
						//cerr << negA << " " << tempA << endl;
						r = bvUnaryMinusBothWays(negChildren, negA);
						//data.print();
						if (r != CONFLICT) {

							if (debug_division)
								cerr << "case B" << endl;

							data.process(first);

						}
					}
				}
			}
		}

		if (canBe(a, signBit, false) && canBe(b, signBit, true)) {
			// (bvneg (bvudiv a (bvneg b)))
			r = NO_CHANGE;
			data.set(a, b, output, false, true);

			FixedBits negB(inputWidth, false);
			//FixedBits negA(inputWidth, false);

			vector<FixedBits*> negChildren;
			negChildren.push_back(&negB);
			r = bvUnaryMinusBothWays(negChildren, tempB); // get NegB
			assert(r != CONFLICT);

			// Create a negated version of the output if necessary. Modulus and remainder aren't both negated. Division is.
			FixedBits wO(inputWidth, false);
			if (op == SIGNED_DIVISION) {
				r = negate(tempOutput, wO);
				assert(r != CONFLICT);
			} else if (op == SIGNED_REMAINDER || op == SIGNED_MODULUS)
				wO = tempOutput;

			// (bvadd (bvurem s (bvneg t)) t)
			if (op == SIGNED_MODULUS) {
				FixedBits wTemp(inputWidth, false);
				vector<FixedBits*> ch;
				ch.push_back(&wTemp);
				ch.push_back(&tempB);
				r = bvAddBothWays(ch, tempOutput);
				assert(r != CONFLICT);
				wO = wTemp;
			}

			negChildren.clear();
			negChildren.push_back(&tempA);
			negChildren.push_back(&negB);

			r = tf(negChildren, wO, bm);
			if (r != CONFLICT) {
				FixedBits t(wO.getWidth(), false);
				if (op == SIGNED_MODULUS) {
					vector<FixedBits*> ch;
					ch.push_back(&wO);
					ch.push_back(&tempB);
					r = bvAddBothWays(ch, tempOutput);
					t = tempOutput;
				} else
					t = wO;

				if (r != CONFLICT) {
					if (op == SIGNED_DIVISION) {
						r = negate(tempOutput, t);
					} else if (op == SIGNED_REMAINDER || op == SIGNED_MODULUS) {
						tempOutput = t;
					}

					if (r != CONFLICT) {
						negChildren.clear();
						negChildren.push_back(&tempB);
						r = bvUnaryMinusBothWays(negChildren, negB);
						if (r != CONFLICT) {
							if (debug_division)
								cerr << "case C" << endl;

							data.process(first);
						}
					}
				}
			}
		}

		if (canBe(a, signBit, true) && canBe(b, signBit, true)) {
			//   (bvudiv (bvneg a) (bvneg b)))))))
			r = NO_CHANGE;
			data.set(a, b, output, true, true);

			FixedBits negA(inputWidth, false);
			FixedBits negB(inputWidth, false);

			vector<FixedBits*> negChildren;
			negChildren.push_back(&negA);
			r = bvUnaryMinusBothWays(negChildren, tempA); // get NegA
			assert(r != CONFLICT);

			negChildren.clear();
			negChildren.push_back(&negB);
			r = bvUnaryMinusBothWays(negChildren, tempB); // get NegB
			assert(r != CONFLICT);

			negChildren.clear();
			negChildren.push_back(&negA);
			negChildren.push_back(&negB);

			FixedBits wO(inputWidth, false);
			if (op == SIGNED_REMAINDER || op == SIGNED_MODULUS) {
				r = negate(tempOutput, wO);
				assert(r != CONFLICT);
			} else if (op == SIGNED_DIVISION)
				wO = tempOutput;

			r = tf(negChildren, wO, bm);
			if (r != CONFLICT) {
				negChildren.clear();
				negChildren.push_back(&tempB);
				r = bvUnaryMinusBothWays(negChildren, negB);

				if (r != CONFLICT) {
					negChildren.clear();
					negChildren.push_back(&tempA);
					r = bvUnaryMinusBothWays(negChildren, negA);
					//data.print();
					if (r != CONFLICT) {
						if (op == SIGNED_REMAINDER || op == SIGNED_MODULUS) {
							r = negate(tempOutput, wO);
						} else if (op == SIGNED_DIVISION)
							tempOutput = wO;

						if (r != CONFLICT) {
							if (debug_division)
								cerr << "case D" << endl;

							data.process(first);
						}
					}
				}
			}

		}

		if (first)
			return CONFLICT; // All are conflicts.

		// The results be subsets of the originals.
		assert(FixedBits::in(workingA, *children[0]));
		assert(FixedBits::in(workingB, *children[1]));
		assert(FixedBits::in(workingOutput, output));

		if (FixedBits::equals(a, workingA) && FixedBits::equals(b, workingB)
				&& FixedBits::equals(output, workingOutput))
			break;
		else
            {
              *children[0] = workingA;
              *children[1] = workingB;
              output = workingOutput;
            }
	}

	return NOT_IMPLEMENTED;
}

Result bvSignedModulusBothWays(vector<FixedBits*>& children, FixedBits& output,
		STPMgr* bm) {
	/*
	 (bvsmod s t) abbreviates
	 (let (?msb_s (extract[|m-1|:|m-1|] s))
	 (let (?msb_t (extract[|m-1|:|m-1|] t))
	 (ite (and (= ?msb_s bit0) (= ?msb_t bit0))
	 (bvurem s t)
	 (ite (and (= ?msb_s bit1) (= ?msb_t bit0))
	 (bvadd (bvneg (bvurem (bvneg s) t)) t)
	 (ite (and (= ?msb_s bit0) (= ?msb_t bit1))
	 (bvadd (bvurem s (bvneg t)) t)
	 (bvneg (bvurem (bvneg s) (bvneg t)))))))
	 */

        // I think this implements old style (broken) semantics, so avoiding it.
        return NO_CHANGE;

        if (children[0] == children[1]) // same pointer.
          {
              return NO_CHANGE;
          }

	return bvSignedDivisionRemainderBothWays(children, output, bm,
			bvUnsignedModulusBothWays, SIGNED_MODULUS);
}

Result bvSignedRemainderBothWays(vector<FixedBits*>& children,
		FixedBits& output, STPMgr* bm) {
	/*
	 (bvsrem s t) abbreviates
	 (let (?msb_s (extract[|m-1|:|m-1|] s))
	 (let (?msb_t (extract[|m-1|:|m-1|] t))
	 (ite (and (= ?msb_s bit0) (= ?msb_t bit0))
	 (bvurem s t)
	 (ite (and (= ?msb_s bit1) (= ?msb_t bit0))
	 (bvneg (bvurem (bvneg s) t))
	 (ite (and (= ?msb_s bit0) (= ?msb_t bit1))
	 (bvurem s (bvneg t)))
	 (bvneg (bvurem (bvneg s) (bvneg t)))))))
	 */


  if (children[0] == children[1]) // same pointer.
    {
        return NO_CHANGE;
    }


	return bvSignedDivisionRemainderBothWays(children, output, bm,
			bvUnsignedModulusBothWays, SIGNED_REMAINDER);
}

Result bvSignedDivisionBothWays(vector<FixedBits*>& children,
		FixedBits& output, STPMgr* bm) {
	/*
	 * (bvsdiv s t) abbreviates
	 (let (?msb_s (extract[|m-1|:|m-1|] s))
	 (let (?msb_t (extract[|m-1|:|m-1|] t))
	 (ite (and (= ?msb_s bit0) (= ?msb_t bit0))
	 (bvudiv s t)
	 (ite (and (= ?msb_s bit1) (= ?msb_t bit0))
	 (bvneg (bvudiv (bvneg s) t))
	 (ite (and (= ?msb_s bit0) (= ?msb_t bit1))
	 (bvneg (bvudiv s (bvneg t)))
	 (bvudiv (bvneg s) (bvneg t)))))))
	 *
	 */

  if (children[0] == children[1]) // same pointer.
    {
        return NO_CHANGE;
    }

  // unsigned division propagates much better than signed division does!
  const int top = children[0]->getWidth();
  if ((*children[0])[top-1] == '0' && (*children[1])[top-1] == '0')
    return bvUnsignedDivisionBothWays(children, output, bm);
  else
    return bvSignedDivisionRemainderBothWays(children, output, bm,
			bvUnsignedDivisionBothWays, SIGNED_DIVISION);
}
}
}
;
