#include "ConstantBitP_TransferFunctions.h"
#include "ConstantBitP_Utility.h"

// Add, subtract.
// Trevor Hansen. BSD License.

namespace simplifier
{
namespace constantBitP
{

// Subtract is implemented in terms of plus.
Result bvSubtractBothWays(vector<FixedBits*>& children, FixedBits& output)
{
	assert(children.size() ==2);

	FixedBits & a = *children[0];
	FixedBits & b = *children[1];

	assert(a.getWidth() == b.getWidth());

	const int bitWidth = a.getWidth();

	FixedBits one(bitWidth, false);
	one.fixToZero();
	one.setFixed(0, true);
	one.setValue(0, true);

	FixedBits notB(bitWidth, false);

	vector<FixedBits*> Addargs;
	Addargs.push_back(&a);
	Addargs.push_back(&notB);
	Addargs.push_back(&one);

	bool changed = false;
	while (true) // until it fixed points
	{
		Result result;
		FixedBits initialNotB(notB);
		FixedBits initialA(a);
		FixedBits initialOut(output);

		result = bvNotBothWays(b, notB);
		if (CONFLICT == result)
			return CONFLICT;

		result = bvAddBothWays(Addargs, output);
		if (CONFLICT == result)
			return CONFLICT;

		if (FixedBits::equals(initialNotB, notB) && FixedBits::equals(initialA, a) && FixedBits::equals(initialOut, output))
			break;
		else
			changed = true;
	}

	return NOT_IMPLEMENTED;
}

/////////////// ADDITION>

const bool add_debug_messages = false;

// For a given number of children. The maximum size of the carry in for addition.
//
// For five arguments (say). The carry can be as big as 4. But into the second column
// it can be no bigger than 2.
unsigned maximumCarryInForAddition(int numberOfChildren, int index)
{
	assert(numberOfChildren > 1);
	assert(index >=0);

	if (0 == index)
		return 0;


	if (numberOfChildren==2)
		return 1; // Case that the (index==0) is already handled.


	unsigned result = 0;
	unsigned currIndex = 0;

	while (currIndex < (unsigned)index)
	{
		result = (result + numberOfChildren) >> 1;
		currIndex++;
	}

	//cerr << "max carry" << numberOfChildren << " " << index << " " << result << endl;
	return result;
}

// Given the current fixings to a particular column, as well as the range of the columns inflow,
// deduce values.
// index: Column we are working on.
// sum:   What the column must sum to.
// inflowMin: Minimum inflow expected, i.e. lowerbound of lower (index-1).

Result fixIfCanForAddition(vector<FixedBits*>& children, const int index, const int sum, const int inflowMin, const int inflowMax)
{
	Result result = NO_CHANGE;

	assert(inflowMin <= inflowMax);
	assert(inflowMin >=0);
	assert(index >=0);
	assert(index < children[0]->getWidth());

	const int maxCarryIn = maximumCarryInForAddition(children.size(), index);

	assert(inflowMax <= maxCarryIn);
	assert(sum <= (signed)children.size() + maxCarryIn );

	if (add_debug_messages)
		cerr << "fixIfCanForAddition " << index << " " << sum << endl;

	int unfixed = 0;
	int ones = 0;
	int zeroes = 0;
	for (unsigned i = 0; i < children.size(); i++)
	{
		if (children[i]->isFixed(index))
		{
			if (children[i]->getValue(index))
				ones++;
			if (!children[i]->getValue(index))
				zeroes++;
		}
		else
		{
			unfixed++;
		}
	}

	assert(ones >=0 && unfixed >=0 && zeroes >=0);
	assert(ones + unfixed + zeroes == (signed)children.size());

	ones = ones + inflowMin;

	if ((ones == sum) && unfixed > 0) // set em all to false. Already have as many as we need.
	{
		for (unsigned i = 0; i < children.size(); i++)
		{
			if (!children[i]->isFixed(index))
			{
				children[i]->setFixed(index, true);
				children[i]->setValue(index, false);
				result = CHANGED;
			}
		}
	}

	int sumUnfixed = unfixed + inflowMax - inflowMin;
	zeroes = zeroes + (maxCarryIn - inflowMax);

	assert(ones >=0 && sumUnfixed >=0 && zeroes >=0);
	assert(ones+sumUnfixed+zeroes == (signed) children.size()+ maxCarryIn);

	if (sum == (sumUnfixed + ones) && unfixed > 0) // need 'em all fixed to ones.
	{
		for (unsigned i = 0; i < children.size(); i++)
		{
			if (!children[i]->isFixed(index))
			{
				children[i]->setFixed(index, true);
				children[i]->setValue(index, true);
				result = CHANGED;
			}
		}
	}
	else if (sum > sumUnfixed + ones)
		return CONFLICT;

	if (sum < ones)
		return CONFLICT;

	return result;
}

// Count the number of fixed ones, and zeroes.  Update the low and high column counts.
// Counts should only be monitonically changed. So this can only be run once.
void initialiseColumnCounts(int columnL[], int columnH[], const int bitWidth, const int numberOfChildren, const vector<FixedBits*>& children)
{
	// setup the low and highs.
	for (int i = 0; i < bitWidth; i++)
	{
		columnL[i] = 0;
		columnH[i] = numberOfChildren;
	}

	// Set the column totals.
	for (int i = 0; i < bitWidth; i++)
	{
		for (int j = 0; j < numberOfChildren; j++)
		{
			if (children[j]->isFixed(i))
			{
				if (children[j]->getValue(i))
					columnL[i]++;
				else
					columnH[i]--;
			}
		}
	}
}

void printArray(int f[], int width)
{
	for (int i = width - 1; i >= 0; i--)
		std::cerr << f[i] << " ";
	std::cerr << std::endl;
}

void setValue(FixedBits& a, const int i, bool v)
{
  if (a.isFixed(i))
      return;

  a.setFixed(i,true);
  a.setValue(i,v);
}

// Specialisation for two operands.
    Result
    bvAddBothWays(FixedBits& x, FixedBits& y, FixedBits& output)
    {
      const int bitWidth = output.getWidth();
      FixedBits carry(bitWidth + 1, false);
      carry.setFixed(0, true);
      carry.setValue(0, false);

      //cerr << "input" << x << y << output << endl;

      for (int i = 0; i < bitWidth; i++)
        {
        //cerr << i << ":"<< x[i] << y[i] << carry[i] << "=" << output[i]<< endl;

        int lb = (x[i] == '1' ? 1 : 0) + (y[i] == '1' ? 1 : 0) + (carry[i] == '1' ? 1 : 0);
        int ub = (x[i] == '0' ? 0 : 1) + (y[i] == '0' ? 0 : 1) + (carry[i] == '0' ? 0 : 1);

        const int lb_initial = lb;
        const int ub_initial = ub;

        if (carry[i+1] == '1') // carry out is true.
          lb = std::max(2, lb);

        if (carry[i+1] == '0') // carry out is false.
          ub = std::min(1, ub);

        const char output_i = output[i];
        if (output_i == '1' && (lb % 2 == 0))
          lb++;

        if (output_i == '0' && (lb % 2 == 1))
          lb++;

        if (output_i == '1' && (ub % 2 == 0))
          ub--;

        if (output_i == '0' && (ub % 2 == 1))
          ub--;

        if (lb >= 2)
          setValue(carry, i+1, true);

        if (ub <= 1)
          setValue(carry, i+1, false);

        if (ub < lb)
          return CONFLICT;

        if (lb == ub)
          {
            setValue(output, i, ((lb % 2) == 1));

            if (lb_initial  ==lb)
              {
                if (!x.isFixed(i))
                  setValue(x, i, false);
                if (!y.isFixed(i))
                  setValue(y, i, false);
                if (!carry.isFixed(i))
                  {
                  setValue(carry, i, false);
                  i = std::max(i-2,-1); // go back to the prior column.
                  continue;
                  }
              }

            if (ub_initial ==lb)
              {
                if (!x.isFixed(i))
                  setValue(x, i, true);
                if (!y.isFixed(i))
                  setValue(y, i, true);
                if (!carry.isFixed(i))
                  {
                  setValue(carry, i, true);
                  i = std::max(i-2,-1); // go back to the prior column.
                  continue;
                  }

              }
          }
        //cerr << i << "[" << ub << ":" << lb << "]" << endl;
        }

      return NOT_IMPLEMENTED;
    }

Result bvAddBothWays(vector<FixedBits*>& children, FixedBits& output)
{
        const int numberOfChildren = children.size();
        if (numberOfChildren==2)
        {
          return bvAddBothWays(*children[0],*children[1],output);
        }

        Result result = NO_CHANGE;

	const int bitWidth = output.getWidth();


	for (int i = 0; i < numberOfChildren; i++)
	{
		assert(children[i]->getWidth() == bitWidth );
	}

	int columnL[bitWidth]; // minimum  ""            ""
	int columnH[bitWidth]; // maximum number of true partial products.

	initialiseColumnCounts(columnL, columnH, bitWidth, numberOfChildren, children);

	int sumH[bitWidth];
	int sumL[bitWidth];
	sumL[0] = columnL[0];
	sumH[0] = columnH[0];

	for (unsigned i = /**/1 /**/; i < (unsigned) bitWidth; i++)
	{
		assert((columnH[i] >= columnL[i]) && (columnL[i] >= 0));
		sumH[i] = columnH[i] + (sumH[i - 1] / 2);
		sumL[i] = columnL[i] + (sumL[i - 1] / 2);
	}

	// Now the sums counts are all updated. And consistent with each other.

	bool changed = true;
	while (changed)
	{
		changed = false;

		// Make sure each column's sum is consistent with the output.
		for (int i = 0; i < bitWidth; i++)
		{
			if (output.isFixed(i))
			{
				int expected = output.getValue(i) ? 1 : 0;

				// output is true. So the maximum and minimum can only be even.
				if (sumH[i] % 2 != expected)
				{
					sumH[i]--;
					changed = true;
				}
				if (sumL[i] % 2 != expected)
				{
					sumL[i]++;
					changed = true;
				}

				if (changed && ((sumH[i] < sumL[i]) || (sumL[i] < 0)))
					return CONFLICT;
			}
		}

		// update the column counts to make them consistent to the totals.
		for (int i = /**/0 /**/; i < bitWidth; i++)
		{
			if (sumH[i] < columnH[i])
			{
				columnH[i]--;
				changed = true;

				if (columnH[i] < columnL[i])
					return CONFLICT;
			}
		}

		// Go from low to high making each of the sums consistent.
		for (int i = /**/1 /**/; i < bitWidth; i++)
		{
			assert((columnH[i] >= columnL[i]) && (columnL[i] >= 0));
			if (sumH[i] > columnH[i] + (sumH[i - 1] / 2))
			{
				sumH[i] = columnH[i] + (sumH[i - 1] / 2);
				changed = true;
			}
			if (sumL[i] < columnL[i] + (sumL[i - 1] / 2))
			{
				sumL[i] = columnL[i] + (sumL[i - 1] / 2);
				changed = true;
			}

			if (changed && (sumH[i] < sumL[i] || sumL[i] < 0))
				return CONFLICT;

		}

		// go from high to low, making each of the sums consistent.
		for (int i = /**/bitWidth - 1 /**/; i >= 1; i--)
		{
			if ((sumH[i] == sumL[i]))
			{
				stats s = getStats(children, i);

				if (0 == s.unfixed)
				{
					// amount that the prior column needs to contribute.
					int toContribute = (sumH[i] - s.fixedToOne) * 2;

					if (sumH[i - 1] > (toContribute + 1))
					{
						changed = true;
						sumH[i - 1] = toContribute + 1; // plus one because of rounding down.
					}

					if (sumL[i - 1] < toContribute)
					{
						changed = true;
						sumL[i - 1] = toContribute;
					}

					if (sumH[i - 1] < sumL[i - 1])
					{
						return CONFLICT;
					}
				}
			}
		}

		if (add_debug_messages)
		{
			std::cerr << "bottom" << std::endl;
			cerr << "columnL:";
			printArray(columnL, bitWidth);
			cerr << "columnH:";
			printArray(columnH, bitWidth);
			cerr << "sumL:";
			printArray(sumL, bitWidth);
			cerr << "sumH:";
			printArray(sumH, bitWidth);
		}

		for (int column = 0; column < bitWidth; column++)
		{
			if (sumH[column] == sumL[column])
			{
				// (1) If the low and high sum is equal. Then the output is know.
				bool newResult = (sumH[column] % 2 == 0) ? false : true;

				if (!output.isFixed(column))
				{
					output.setFixed(column, true);
					output.setValue(column, newResult);
					result = CHANGED;
					changed = true;
				}
				else if (output.isFixed(column) && (output.getValue(column) != newResult))
					return CONFLICT;

				// (2) If this column has some unfixed values. Then we may be able to determine them.
				Result tempResult;
				if (0 == column)
					tempResult = fixIfCanForAddition(children, column, sumH[column], 0, 0);
				else
					tempResult = fixIfCanForAddition(children, column, sumH[column], sumL[column - 1] / 2, sumH[column - 1] / 2);

				if (CONFLICT == tempResult)
					return CONFLICT;

				if (CHANGED == tempResult)
					changed = true;

			}

		}
	}
	return NOT_IMPLEMENTED;
}

}
}
