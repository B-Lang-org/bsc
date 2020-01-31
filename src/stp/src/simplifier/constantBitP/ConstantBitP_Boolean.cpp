#include "ConstantBitP_TransferFunctions.h"
#include "ConstantBitP_Utility.h"

// AND, OR, XOR, NOT Transfer functions.
// Trevor Hansen. BSD License.



namespace simplifier
{
namespace constantBitP
{

Result bvXorBothWays(vector<FixedBits*>& operands, FixedBits& output)
{
	Result result = NO_CHANGE;
	const int bitWidth = output.getWidth();

	for (int i = 0; i < bitWidth; i++)
	{
		const stats status = getStats(operands, i);

		if (status.unfixed == 0) // if they are all fixed. We know the answer.
		{
			bool answer = (status.fixedToOne % 2) != 0;

			if (!output.isFixed(i))
			{
				output.setFixed(i, true);
				output.setValue(i, answer);
				result = CHANGED;
			}
			else if (output.getValue(i) != answer)
				return CONFLICT;
		}
		else if (status.unfixed == 1 && output.isFixed(i))
		{
			// If there is just one unfixed, and we have the answer --> We know the value.
			bool soFar = ((status.fixedToOne % 2) != 0);
			if (soFar != output.getValue(i))
			{ // result needs to be flipped.
				fixUnfixedTo(operands, i, true);
			}
			else
				fixUnfixedTo(operands, i, false);
			result = CHANGED;
		}
	}
	return result;
}

// if output bit is true. Fix all the operands.
// if all the operands are fixed. Fix the output.
// given 1,1,1,- == 0, fix - to 0.
Result bvAndBothWays(vector<FixedBits*>& operands, FixedBits& output)
{
	Result result = NO_CHANGE;
	const int bitWidth = output.getWidth();

	for (int i = 0; i < bitWidth; i++)
	{
		const stats status = getStats(operands, i);

		// output is fixed to one. But an input value is false!
		if (output.isFixed(i) && output.getValue(i) && status.fixedToZero > 0)
			return CONFLICT;

		// output is fixed to one. But an input value is false!
		if (output.isFixed(i) && !output.getValue(i) && status.fixedToZero == 0
				&& status.unfixed == 0)
			return CONFLICT;

		// output is fixed to one. So all should be one.
		if (output.isFixed(i) && output.getValue(i) && status.unfixed > 0)
		{
			fixUnfixedTo(operands, i, true);
			result = CHANGED;
		}

		// The output is unfixed. At least one input is false.
		if (!output.isFixed(i) && status.fixedToZero > 0)
		{
			output.setFixed(i, true);
			output.setValue(i, false);
			result = CHANGED;
		}

		// Everything is fixed to one!
		if (!output.isFixed(i) && status.fixedToZero == 0 && status.unfixed
				== 0)
		{
			output.setFixed(i, true);
			output.setValue(i, true);
			result = CHANGED;
		}

		// If the output is false, and there is a single unfixed value with everything else true..
		if (output.isFixed(i) && !output.getValue(i) && status.fixedToZero == 0
				&& status.unfixed == 1)
		{
			fixUnfixedTo(operands, i, false);
			result = CHANGED;
		}
	}
	return result;
}

Result bvOrBothWays(vector<FixedBits*>& children, FixedBits& output)
{
	Result r = NO_CHANGE;
	const int numberOfChildren = children.size();
	const int bitWidth = output.getWidth();

	for (int i = 0; i < bitWidth; i++)
	{
		bool answerKnown = output.isFixed(i);
		bool answer = false;
		if (answerKnown)
			answer = output.getValue(i);

		int unks = 0;
		int ones = 0;
		int zeroes = 0;

		for (int j = 0; j < numberOfChildren; j++)
		{
			assert(output.getWidth() == children[j]->getWidth());

			if (!children[j]->isFixed(i))
				unks++;
			else if (children[j]->getValue(i))
				ones++;
			else
				zeroes++;
		}

		if (ones > 0) // Atleast a single one found!

		{
			if (answerKnown && !answer)
				return CONFLICT;

			if (!answerKnown)
			{
				output.setFixed(i, true);
				output.setValue(i, true);
				r = CHANGED;
			}
		}

		if (zeroes == numberOfChildren) // all zeroes.

		{
			if (answerKnown && answer)
				return CONFLICT;

			if (!answerKnown)
			{
				r = CHANGED;
				output.setFixed(i, true);
				output.setValue(i, false);

			}
		}

		if (answerKnown && !answer) // known false

		{
			if (ones > 0)
				return CONFLICT;

			// set all the column to false.

			for (int j = 0; j < numberOfChildren; j++)
			{
				if (!children[j]->isFixed(i))
				{
					r = CHANGED;
					children[j]->setFixed(i, true);
					children[j]->setValue(i, false);
				}
			}

		}

		if (unks == 1 && answerKnown && answer && (zeroes == (numberOfChildren
				- 1)))
		{
			// A single unknown, everything else is false. The answer is true. So the unknown is true.

			for (int j = 0; j < numberOfChildren; j++)
			{
				if (!children[j]->isFixed(i))
				{
					r = CHANGED;
					children[j]->setFixed(i, true);
					children[j]->setValue(i, true);
				}
			}
		}

	}
	return r;
}

Result bvNotBothWays(vector<FixedBits*>& children, FixedBits& result)
{
	return bvNotBothWays(*(children[0]), result);
}

Result bvImpliesBothWays(vector<FixedBits*>& children, FixedBits& result)
{

	FixedBits& a = (*children[0]);
	FixedBits& b = (*children[1]);

	assert(a.getWidth() == result.getWidth());
	const int bitWidth = a.getWidth();
	assert (bitWidth == 1);

	Result r = NO_CHANGE;

	int i = 0;

	//  (false -> something) is always true.
	//  (something -> true ) is always true.
	if (a.isFixedToZero(i) || b.isFixedToOne(i))
	{
		if (!result.isFixed(i))
		{
			result.setFixed(i, true);
			result.setValue(i, true);
			r = CHANGED;
		} else if (result.isFixedToZero(i))
			return CONFLICT;
	}

	// If the result is false. it must be (true -> false)
	if (result.isFixedToZero(i))
	{
		if (a.isFixedToZero(i) || b.isFixedToOne(i))
			return CONFLICT;

		if (!a.isFixed(i))
		{
			a.setFixed(i, true);
			a.setValue(i, true);
			r = CHANGED;
		}
		if (!b.isFixed(i))
		{
			b.setFixed(i, true);
			b.setValue(i, false);
			r = CHANGED;
		}
	}

	if (result.isFixedToOne(i))
	{
		if (a.isFixedToOne(i))
		{
			if (!b.isFixed(i))
			{
				b.setFixed(i, true);
				b.setValue(i, true);
				r = CHANGED;
			}
			else if (b.isFixedToZero(i))
				return CONFLICT;
		}

		if (b.isFixedToZero(i))
		{
			if (!a.isFixed(i))
			{
				a.setFixed(i, true);
				a.setValue(i, false);
				r = CHANGED;
			}
		}
	}

	if (a.isFixedToOne(i) && b.isFixedToZero(i))
	{
		if (result.isFixedToOne(i))
			return CONFLICT;
		if (!result.isFixed(i))
		{
			result.setFixed(i, true);
			result.setValue(i, false);
			r = CHANGED;
		}
	}

	return r;

}

Result bvNotBothWays(FixedBits& a, FixedBits& output)
{
	assert(a.getWidth() == output.getWidth());
	const int bitWidth = a.getWidth();

	Result result = NO_CHANGE;

	for (int i = 0; i < bitWidth; i++)
	{
		// error if they are the same.
		if (a.isFixed(i) && output.isFixed(i) && (a.getValue(i)
				== output.getValue(i)))
		{
			return CONFLICT;
		}

		if (a.isFixed(i) && !output.isFixed(i))
		{
			output.setFixed(i, true);
			output.setValue(i, !a.getValue(i));
			result = CHANGED;
		}

		if (output.isFixed(i) && !a.isFixed(i))
		{
			a.setFixed(i, true);
			a.setValue(i, !output.getValue(i));
			result = CHANGED;
		}
	}
	return result;
}

}
}
