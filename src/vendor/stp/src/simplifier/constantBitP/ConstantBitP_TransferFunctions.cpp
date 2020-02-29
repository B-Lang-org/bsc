#include "ConstantBitP_TransferFunctions.h"
#include "ConstantBitP_Utility.h"

namespace simplifier
{
namespace constantBitP
{

namespace BEEV
{
typedef unsigned int * CBV;
}

// Misc (easy) transfer functions.
// Trevor Hansen. BSD License.

// if the result is fixed to true. Then fix a==b.
// if the result is fixed to false, there is a single unspecied value, and all the rest are the same. Fix it to the opposite.

// if a==b then fix the result to true.
// if a!=b then fix the result to false.
Result bvEqualsBothWays(FixedBits& a, FixedBits& b, FixedBits& output)
{
	assert(a.getWidth() == b.getWidth());
	assert(1 == output.getWidth());

	const int childWidth = a.getWidth();

	Result r = NO_CHANGE;

	bool allSame = true;
	bool definatelyFalse = false;

	for (int i = 0; i < childWidth; i++)
	{
		// if both fixed
		if (a.isFixed(i) && b.isFixed(i))
		{
			// And have different values.
			if (a.getValue(i) != b.getValue(i))
			{
				definatelyFalse = true;
				break;
			}
			else
			{
				allSame &= true;
				continue;
			}
		}
		allSame &= false;
	}

	if (definatelyFalse)
	{
		if (output.isFixed(0) && output.getValue(0))
		{
			return CONFLICT;
		}
		else if (!output.isFixed(0))
		{
			output.setFixed(0, true);
			output.setValue(0, false);
			r = CHANGED;
		}
	}
	else if (allSame)
	{
		if (output.isFixed(0) && !output.getValue(0))
		{
			return CONFLICT;
		}
		else if (!output.isFixed(0))
		{
			output.setFixed(0, true);
			output.setValue(0, true);
			r = CHANGED;
		}
	}

	if (output.isFixed(0) && output.getValue(0)) // all should be the same.
	{
		for (int i = 0; i < childWidth; i++)
		{
			if (a.isFixed(i) && b.isFixed(i))
			{
				if (a.getValue(i) != b.getValue(i))
				{
					return CONFLICT;
				}
			}
			else if (a.isFixed(i) != b.isFixed(i)) // both same but only one is fixed.
			{
				if (a.isFixed(i))
				{
					b.setFixed(i, true);
					b.setValue(i, a.getValue(i));
					r = CHANGED;
				}
				else
				{
					a.setFixed(i, true);
					a.setValue(i, b.getValue(i));
					r = CHANGED;
				}
			}
		}
	}

	// if the result is fixed to false, there is a single unspecied value, and all the rest are the same. Fix it to the opposite.
	if (output.isFixed(0) && !output.getValue(0))
	{
		int unknown = 0;

		for (int i = 0; i < childWidth && unknown < 2; i++)
		{
			if (!a.isFixed(i))
				unknown++;
			if (!b.isFixed(i))
				unknown++;
			else if (a.isFixed(i) && b.isFixed(i) && a.getValue(i) != b.getValue(i))
			{
				unknown = 10; // hack, don't do the next loop.
				break;
			}
		}

		if (1 == unknown)
		{
			for (int i = 0; i < childWidth; i++)
			{
				if (!a.isFixed(i))
				{
					a.setFixed(i, true);
					a.setValue(i, !b.getValue(i));
					r = CHANGED;
				}
				if (!b.isFixed(i))
				{
					b.setFixed(i, true);
					b.setValue(i, !a.getValue(i));
					r = CHANGED;
				}
			}
		}
	}
	return r;
}

Result bvEqualsBothWays(vector<FixedBits*>& children, FixedBits& result)
{
	return bvEqualsBothWays(*(children[0]), *(children[1]), result);
}

Result bvZeroExtendBothWays(vector<FixedBits*>& children, FixedBits& output)
{
	assert(children.size() ==2 );
	// The second argument is a junk size arugment.


	FixedBits& input = *children[0];
	const int inputBitWidth = input.getWidth();
	const int outputBitWidth = output.getWidth();

	Result result = makeEqual(input, output, 0, inputBitWidth);
	if (CONFLICT == result)
		return CONFLICT;

	// Fix all the topmost bits of the output to zero.
	for (int i = inputBitWidth; i < outputBitWidth; i++)
	{
		if (output.isFixed(i) && output.getValue(i))
			return CONFLICT; // set to one. Never right.
		else if (!output.isFixed(i))
		{
			output.setFixed(i, true);
			output.setValue(i, false);
			result = CHANGED;
		}
	}
	return result;
}

Result bvSignExtendBothWays(vector<FixedBits*>& children, FixedBits& output)
{
	assert(children.size() ==2 );
	// The second argument is a junk size arugment.

	FixedBits& input = *children[0];
	const int inputBitWidth = input.getWidth();
	const int outputBitWidth = output.getWidth();
	assert(inputBitWidth <= outputBitWidth);

	Result result = makeEqual(input, output, 0, inputBitWidth);
	if (CONFLICT == result)
		return CONFLICT;

	// If any of the topmost bits of the output are fixed. Then they all should be.
	// They should all be fixed to the same value.
	bool found = false;
	bool setTo;
	for (int i = inputBitWidth - /**/1 /**/; i < outputBitWidth; i++)
	{
		if (output.isFixed(i))
		{
			setTo = output.getValue(i);
			found = true;
			break;
		}
	}

	if (found)
	{
		for (int i = inputBitWidth - 1; i < outputBitWidth; i++)
		{
			if (output.isFixed(i) && (output.getValue(i) != setTo))
				return CONFLICT; // if any are set to the wrong value! bad.
			else if (!output.isFixed(i))
			{
				output.setFixed(i, true);
				output.setValue(i, setTo);
				result = CHANGED;
			}
		}

		Result result2 = makeEqual(input, output, 0, inputBitWidth);
		if (CONFLICT == result2)
			return CONFLICT;

	}
	return result;
}

Result bvExtractBothWays(vector<FixedBits*>& children, FixedBits& output)
{
	const int numberOfChildren = children.size();
	const int outputBitWidth = output.getWidth();

	Result result = NO_CHANGE;

	assert(3 == numberOfChildren);

	int top = children[1]->getUnsignedValue();
	int bottom = children[2]->getUnsignedValue();

	FixedBits& input = *(children[0]);

	assert(top >= bottom);
	assert(bottom >=0);
	assert(top - bottom + 1 == outputBitWidth);
	assert(top < input.getWidth());

	for (int outputPosition = 0; outputPosition < outputBitWidth; outputPosition++)
	{
		int inputPosition = outputPosition + bottom;

		if (input.isFixed(inputPosition) && output.isFixed(outputPosition))
			if (input.getValue(inputPosition) ^ output.getValue(outputPosition))
				return CONFLICT;

		if (input.isFixed(inputPosition) ^ output.isFixed(outputPosition))
		{
			if (input.isFixed(inputPosition))
			{
				output.setFixed(outputPosition, true);
				output.setValue(outputPosition, input.getValue(inputPosition));
				result = CHANGED;
			}
			else
			{
				input.setFixed(inputPosition, true);
				input.setValue(inputPosition, output.getValue(outputPosition));
				result = CHANGED;
			}
		}
	}

	//cerr << "extract[" << top << ":" << bottom << "]" << input << "=" << output<< endl;

	return result;
}

// UMINUS, is NEG followed by +1
Result bvUnaryMinusBothWays(vector<FixedBits*>& children, FixedBits& output)
{
	assert(children.size() == 1);
	const int bitWidth = children[0]->getWidth();

	// If it's only one bit. This will be negative one.
	FixedBits one(bitWidth, false);
	one.fixToZero();
	one.setFixed(0, true);
	one.setValue(0, true);

	FixedBits notted(bitWidth, false);

	vector<FixedBits*> args;
	args.push_back(&notted);
	args.push_back(&one);

	Result result = NO_CHANGE;
	while (true) // until it fixed points
	{
		FixedBits initialNot(notted);
		FixedBits initialIn(*children[0]);
		FixedBits initialOut(output);

		result = bvNotBothWays(*children[0], notted);
		if (CONFLICT == result)
			return CONFLICT;

		result = bvAddBothWays(args, output);
		if (CONFLICT == result)
			return CONFLICT;

		if (FixedBits::equals(initialNot, notted) && FixedBits::equals(initialIn, *children[0]) && FixedBits::equals(initialOut, output))
			break;
	}

	return NOT_IMPLEMENTED; // don't set the status properly yet..
}

Result bvConcatBothWays(vector<FixedBits*>& children, FixedBits& output)
{
	Result r = NO_CHANGE;
	const int numberOfChildren = children.size();
	int current = 0;
	for (int i = numberOfChildren - 1; i >= 0; i--) // least significant is last.

	{
		FixedBits& child = *children[i];
		for (int j = 0; j < child.getWidth(); j++)
		{
			// values are different. Bad.
			if (output.isFixed(current) && child.isFixed(j) && (output.getValue(current) != child.getValue(j)))
				return CONFLICT;

			if (output.isFixed(current) && !child.isFixed(j))
			{
				// only output is fixed.
				child.setFixed(j, true);
				child.setValue(j, output.getValue(current));
				r = CHANGED;
			}
			else if (!output.isFixed(current) && child.isFixed(j))
			{
				// only input is fixed.
				output.setFixed(current, true);
				output.setValue(current, child.getValue(j));
				r = CHANGED;
			}
			current++;
		}
	}
	return r;
}

// If the guard is fixed, make equal the appropriate input and output.
// If one input can not possibly be the output. Then set the guard to make it the other one.
// If both values are the same. Set the output to that value.
Result bvITEBothWays(vector<FixedBits*>& children, FixedBits& output)
{
	Result result = NO_CHANGE;

	assert(3 == children.size());
	const int bitWidth = output.getWidth();
	FixedBits& guard = *children[0];
	FixedBits& c1 = *children[1];
	FixedBits& c2 = *children[2];

	assert(c1.getWidth() == c2.getWidth());
	assert(output.getWidth() == c2.getWidth());

	if (guard.isFixed(0) && guard.getValue(0))
	{ // guard fixed to true. So make (first arg == output)
		result = makeEqual(output, c1, 0, bitWidth);
		if (CONFLICT == result)
			return CONFLICT;

	}
	else if (guard.isFixed(0) && !guard.getValue(0))
	{
		result = makeEqual(output, c2, 0, bitWidth);
		if (CONFLICT == result)
			return CONFLICT;

	}
	else
	{
		for (int i = 0; i < bitWidth; i++)
		{
			if (c1.isFixed(i) && c2.isFixed(i) && (c1.getValue(i) == c2.getValue(i)))
			{

				if (output.isFixed(i) && (output.getValue(i) != c1.getValue(i)))
					return CONFLICT;

				if (!output.isFixed(i))
				{
					output.setFixed(i, true);
					output.setValue(i, c1.getValue(i));
					result = CHANGED;
				}
			}
		}
	}

	bool changed = false;
	if (CHANGED == result)
		changed = true;

	for (int i = 0; i < bitWidth; i++)
	{
		if (output.isFixed(i))
		{
			if (c1.isFixed(i) && (c1.getValue(i) != output.getValue(i)))
			{
				//c1 is fixed to a value that's not the same as the output.
				if (!guard.isFixed(0))
				{
					guard.setFixed(0, true);
					guard.setValue(0, false);
					result = bvITEBothWays(children, output);
					if (CONFLICT == result)
						return CONFLICT;
					changed = true;
				}
				else if (guard.getValue(0))
					return CONFLICT;
			}

			if (c2.isFixed(i) && (c2.getValue(i) != output.getValue(i)))
			{
				//c2 is fixed to a value that's not the same as the output.
				if (!guard.isFixed(0))
				{
					guard.setFixed(0, true);
					guard.setValue(0, true);
					result = bvITEBothWays(children, output);
					if (CONFLICT == result)
						return CONFLICT;
					changed = true;

				}
				else if (!guard.getValue(0))
					return CONFLICT;
			}
		}
	}

	if (result == CONFLICT)
		return CONFLICT;
	if (changed)
		return CHANGED;

	return result;
}

}

}
