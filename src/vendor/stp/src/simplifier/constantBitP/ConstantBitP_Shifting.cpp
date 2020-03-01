#include "ConstantBitP_TransferFunctions.h"
#include "ConstantBitP_Utility.h"
#include "../../extlib-constbv/constantbv.h"

// Left shift, right shift.
// Trevor Hansen. BSD License.

// smtlib & x86 semantics differ for what happens when a value is shifted by greater
// than the bitWidth. On x86, in 64-bit mode, only the bottom 6 bits of the shift are
// used. In SMTLIB the total value is used.


namespace simplifier
{
namespace constantBitP
{

const bool debug_shift = false;

Result bvRightShiftBothWays(vector<FixedBits*>& children, FixedBits& output)
{
	Result result = NO_CHANGE;
	const unsigned bitWidth = output.getWidth();

	assert(2 == children.size());

	FixedBits& op = *children[0];
	FixedBits& shift = *children[1];

	FixedBits outputReverse(bitWidth,false);
	FixedBits opReverse(bitWidth,false);

	// Reverse the output and the input.
	for (unsigned i =0; i < bitWidth;i++)
	{
		if (op.isFixed(i))
		{
			opReverse.setFixed(bitWidth-1-i,true);
			opReverse.setValue(bitWidth-1-i,op.getValue(i));
		}

		if (output.isFixed(i))
		{
			outputReverse.setFixed(bitWidth-1-i,true);
			outputReverse.setValue(bitWidth-1-i,output.getValue(i));
		}
	}

	vector<FixedBits*> args;
	args.push_back(&opReverse);
	args.push_back(&shift);  // shift is unmodified.
	result = bvLeftShiftBothWays(args, outputReverse);

	if (CONFLICT == result)
		return CONFLICT;

	// Now write the reversed values back.
	// Reverse the output and the input.
	for (unsigned i =0; i < bitWidth;i++)
	{
		if (opReverse.isFixed(i) && !op.isFixed(bitWidth-1-i))
		{
			op.setFixed(bitWidth-1-i,true);
			op.setValue(bitWidth-1-i,opReverse.getValue(i));
		}

		if (outputReverse.isFixed(i) && !output.isFixed(bitWidth-1-i))
		{
			output.setFixed(bitWidth-1-i,true);
			output.setValue(bitWidth-1-i,outputReverse.getValue(i));
		}
	}

	return result;
}

// Converts the array of possible shifts into a set that represents the values.
FixedBits getPossible(unsigned bitWidth, bool possibleShift[], unsigned numberOfPossibleShifts, const FixedBits& shift)
{
	FixedBits v(bitWidth, false);
	bool first = true;
	for (unsigned i = 0; i < numberOfPossibleShifts - 1; i++)
	{
		if (possibleShift[i])
		{
			if (first)
			{
				first = false;
				for (unsigned j = 0; j < (unsigned) v.getWidth(); j++)
				{
					v.setFixed(j, true);
					if (j < sizeof(unsigned) * 8)
						v.setValue(j, 0 != (i & (1 << j)));
					else
						v.setValue(j, false);
				}
			}
			else
			{
				// join.
				for (unsigned j = 0; j < (unsigned) v.getWidth() && j
						< sizeof(unsigned) * 8; j++)
				{
					if (v.isFixed(j))
					{
						// union.
						if (v.getValue(j) != (0 != (i & (1 << j))))
							v.setFixed(j, false);
					}
				}
			}
		}
	}

	unsigned firstShift;
	for (firstShift=0; firstShift<numberOfPossibleShifts; firstShift++)
		if (possibleShift[firstShift])
			break;


	// The top most entry of the shift table is special. It means all values of shift
	// that fill it completely with zeroes /ones. We take the union of all of the values >bitWidth
	// in this function.
	if (possibleShift[numberOfPossibleShifts - 1])
	{
		FixedBits bitWidthFB = FixedBits::fromUnsignedInt(bitWidth, bitWidth);
		FixedBits output(1, true);
		output.setFixed(0, true);
		output.setValue(0, true);
		FixedBits working(shift);

		vector<FixedBits*> args;
		args.push_back(&working);
		args.push_back(&bitWidthFB);

		//Write into working anything that can be determined given it's >=bitWidth.
		Result r = bvGreaterThanEqualsBothWays(args,output);
		assert(CONFLICT != r);

		// Get the union of "working" with the prior union.
		for (unsigned i = 0; i < bitWidth; i++)
		{
			if (!working.isFixed(i) && v.isFixed(i))
				v.setFixed(i, false);
			if (working.isFixed(i) && v.isFixed(i) && (working.getValue(i) != v.getValue(i)))
				v.setFixed(i, false);
			if (firstShift == numberOfPossibleShifts - 1) // no less shifts possible.
			{
				if (working.isFixed(i))
				{
					v.setFixed(i, true);
					v.setValue(i, working.getValue(i));
				}
			}
		}
	}

	if (debug_shift)
		cerr << "Set of possible shifts:" << v << endl;

	return v;
}


unsigned getMaxShiftFromValueViaAlternation(const unsigned bitWidth, const FixedBits& output)
{
	unsigned maxShiftFromValue = UINT_MAX;

	// The shift must be less than the position of the first alternation.
	bool foundTrue = false;
	bool foundFalse = false;
	for (int i = bitWidth - 1; i >= 0; i--)
	{
		if (output.isFixed(i))
		{
			if (output.getValue(i) && foundFalse)
			{
				maxShiftFromValue = i;
				break;
			}
			if (!output.getValue(i) && foundTrue)
			{
				maxShiftFromValue = i;
				break;
			}
			if (output.getValue(i))
				foundTrue = true;
			else if (!output.getValue(i))
				foundFalse = true;
		}
	}

	if (maxShiftFromValue != UINT_MAX)
		maxShiftFromValue = bitWidth - 2 - maxShiftFromValue;

	return maxShiftFromValue;
}

Result bvArithmeticRightShiftBothWays(vector<FixedBits*>& children, FixedBits& output)
{
	const unsigned bitWidth = output.getWidth();
	assert(2== children.size());
	assert(bitWidth > 0);
	assert(children[0]->getWidth() == children[1]->getWidth());
	const unsigned MSBIndex = bitWidth-1;

	Result result = NO_CHANGE;

	FixedBits& op = *children[0];
	FixedBits& shift = *children[1];

	// If the MSB isn't set, create a copy with it set each way and take the meet.
	if (!op.isFixed(MSBIndex))
	{
		vector<FixedBits*> children1;
		vector<FixedBits*> children2;
		FixedBits op1(op);
		FixedBits op2(op);
		FixedBits shift1(shift);
		FixedBits shift2(shift);
		FixedBits output1(output);
		FixedBits output2(output);

		children1.push_back(&op1);
		children1.push_back(&shift1);
		op1.setFixed(MSBIndex, true);
		op1.setValue(MSBIndex, true);

		children2.push_back(&op2);
		children2.push_back(&shift2);
		op2.setFixed(MSBIndex, true);
		op2.setValue(MSBIndex, false);

		Result r1 = bvArithmeticRightShiftBothWays(children1, output1);
		Result r2 = bvArithmeticRightShiftBothWays(children2, output2);

		if (r1 == CONFLICT && r2 == CONFLICT)
			return CONFLICT;

		if (r1 == CONFLICT)
		{
			op = op2;
			shift = shift2;
			output = output2;
			return r2;
		}

		if (r2 == CONFLICT)
		{
			op = op1;
			shift = shift1;
			output = output1;
			return r1;
		}

		op = FixedBits::meet(op1,op2);
		shift = FixedBits::meet(shift1,shift2);
		output = FixedBits::meet(output1,output2);
		return r1;

	}

	assert(op.isFixed(MSBIndex));

	if (debug_shift)
	{
		cerr << "=========" << endl;
		cerr <<  op << " >a> ";
		cerr <<  shift;
		cerr << " = " << output << endl;
	}

	// The topmost number of possible shifts corresponds to all
	// the values of shift that shift out everything.
	// i.e. possibleShift[bitWidth+1] is the SET of all operations that shift past the end.
	const unsigned numberOfPossibleShifts = bitWidth + 1;
	bool possibleShift[numberOfPossibleShifts];
	for (unsigned i = 0; i < numberOfPossibleShifts; i++)
		possibleShift[i] = false;


	// If either of the top two bits are fixed they should be equal.
	if (op.isFixed(MSBIndex) ^ output.isFixed(MSBIndex))
	{
		if (op.isFixed(MSBIndex))
		{
			output.setFixed(MSBIndex, true);
			output.setValue(MSBIndex, op.getValue(MSBIndex));
		}

		if (output.isFixed(MSBIndex))
		{
			op.setFixed(MSBIndex, true);
			op.setValue(MSBIndex, output.getValue(MSBIndex));
		}
	}

	// Both the MSB of the operand and the output should be fixed now..
	assert(output.isFixed(MSBIndex));

	unsigned minShiftFromShift, maxShiftFromShift; // The range of the "shift" value.
	shift.getUnsignedMinMax(minShiftFromShift, maxShiftFromShift);

	// The shift can't be any bigger than the topmost alternation in the output.
	// For example if the output is 0.01000, then the shift can not be bigger than
	// 3.
	unsigned maxShiftFromOutput = getMaxShiftFromValueViaAlternation(bitWidth, output);

	maxShiftFromShift = std::min(maxShiftFromShift, (unsigned) maxShiftFromOutput);

	if (debug_shift)
	{
			cerr << "minshift:" << minShiftFromShift << endl;
			cerr << "maxshift:" << maxShiftFromShift << endl;
			cerr << "total:" << maxShiftFromShift << endl;
	}


	for (unsigned i = minShiftFromShift; i <= std::min(bitWidth, maxShiftFromShift); i++)
	{
		// if the bit-pattern of 'i' is in the set represented by the 'shift'.
		if (shift.unsignedHolds(i))
			possibleShift[i] = true;
	}

	// Complication. Given a shift like [.1] possibleShift[2] is now false.
	// A shift of 2 isn't possible. But one of three is.
	// possibleShift[2] means any shift >=2 is possible. So it needs to be set
	// to true.
	{
		if (maxShiftFromShift >= bitWidth)
			possibleShift[bitWidth] = true;
	}

	// Now check one-by-one each shifting.
	// If we are shifting a zero to where a one is (say), then that shifting isn't possible.
	for (unsigned shiftIt = minShiftFromShift; shiftIt < numberOfPossibleShifts; shiftIt++)
	{
		if (possibleShift[shiftIt])
		{
			for (unsigned column = 0; column < bitWidth; column++)
			{
				// if they are fixed to different values. That's wrong.
				if (column + shiftIt <= bitWidth - 1)
				{
					if (output.isFixed(column) && op.isFixed(column + shiftIt)
							&& (output.getValue(column) != op.getValue(column
									+ shiftIt)))
					{
						possibleShift[shiftIt] = false;
						break;
					}
				}
			}
		}
	}

	int nOfPossibleShifts = 0;
	for (unsigned i = 0; i < numberOfPossibleShifts; i++)
	{
		if (possibleShift[i])
		{
			nOfPossibleShifts++;
			maxShiftFromShift = i;
			if (debug_shift)
			{
				std::cerr << "Possible Shift:" << i << std::endl;
			}
		}
	}

	if (debug_shift)
	{
		std::cerr << "Number of possible shifts:" << nOfPossibleShifts << endl;
	}

	// If it's empty. It's a conflict.
	if (0 == nOfPossibleShifts)
	{
		return CONFLICT;
	}

	// We have a list of all the possible shift amounts.
	// We take the union of all the bits that are possible.
	FixedBits setOfPossibleShifts = getPossible(bitWidth, possibleShift, numberOfPossibleShifts,shift);

	// Write in any fixed values to the shift.
	for (unsigned i = 0; i < bitWidth; i++)
	{
		if (setOfPossibleShifts.isFixed(i))
		{
			if (!shift.isFixed(i))
			{
				shift.setFixed(i, true);
				shift.setValue(i, setOfPossibleShifts.getValue(i));
				result = CHANGED;
			}
			else if (shift.isFixed(i) && shift.getValue(i)
					!= setOfPossibleShifts.getValue(i))
			{
				return CONFLICT;
			}
		}
	}

	// If a particular input bit appears in every possible shifting,
	// and if that bit is unfixed,
	// and if the result it is fixed to the same value in every position.
	// Then, that bit must be fixed.
	// E.g.  [--] << [0-] == [00]

	bool candidates[bitWidth];
	for (unsigned i = 0; i < bitWidth; i++)
	{
		candidates[i] = !op.isFixed(i);
	}

	// candidates: So far: the bits that are unfixed in the operand.

	for (unsigned i = 0; i < numberOfPossibleShifts; i++)
	{
		if (possibleShift[i])
		{
			// If this shift is possible, then some bits will be shifted out.
			for (unsigned j = 0; j < i; j++)
				candidates[j] = false;
		}
	}

	// candidates: So far: + the input bits that are unfixed.
	//                     + the input bits that are in every possible fixing.

	// Check all candidates have the same output values.
	for (unsigned candidate = 0; candidate < bitWidth; candidate++)
	{
		bool first = true;
		bool setTo = false; // value that's never read. To quieten gcc.

		if (candidates[candidate])
		{
			for (unsigned shiftIT = 0; shiftIT < bitWidth; shiftIT++)
			{
				// If the shift isn't possible continue.
				if (!possibleShift[shiftIT])
					continue;

				if (shiftIT > candidate)
					continue;

				unsigned idx = candidate - shiftIT;

				if (!output.isFixed(idx))
				{
					candidates[candidate] = false;
					break;
				}
				else
				{
					if (first)
					{
						first = false;
						setTo = output.getValue(idx);
					}
					else
					{
						if (setTo != output.getValue(idx))
						{
							candidates[candidate] = false;
							break;
						}

					}
				}
			}
		}

		if (candidates[candidate])
		{
			assert(!op.isFixed(candidate));
			op.setFixed(candidate, true);
			op.setValue(candidate, setTo);
		}
	}

	if (debug_shift)
		{
			cerr <<  op << " >a> ";
			cerr <<  shift;
			cerr << " = " << output << endl;
		}

	// Go through each of the possible shifts. If the same value is fixed
	// at every location. Then it's fixed too in the result.
	// Looping over the output columns.
	bool MSBValue = op.getValue(MSBIndex);

	for (unsigned column = 0; column < bitWidth; column++)
		{
			bool allFixedToSame = true;
			bool allFixedTo = false; // value that's never read. To quieten gcc.
			bool first = true;

			for (unsigned shiftIt = 0; (shiftIt < numberOfPossibleShifts)
					&& allFixedToSame; shiftIt++)
			{
				if (possibleShift[shiftIt])
				{
					// Will have shifted in something..
					if (shiftIt > (bitWidth - 1 -column))
					{
						if (first)
						{
							allFixedTo = MSBValue;
							first = false;
						}
						else
						{
							if (allFixedTo !=  MSBValue)
							{
								allFixedToSame = false;
							}
						}
					}
					else
					{
						unsigned index = column + shiftIt;
						if (!op.isFixed(index))
							allFixedToSame = false;
						else if (first && op.isFixed(index))
						{
							first = false;
							allFixedTo = op.getValue(index);
						}
						if (op.isFixed(index) && allFixedTo != op.getValue(
								index))
							allFixedToSame = false;
					}
				}
			}

			// If it can be just one possible value. Then we can fix 'em.
			if (allFixedToSame)
			{
				if (output.isFixed(column) && (output.getValue(column)
						!= allFixedTo))
				{
							return CONFLICT;
				}
				if (!output.isFixed(column))
				{
					output.setFixed(column, true);
					output.setValue(column, allFixedTo);
					result = CHANGED;
				}
			}
		}
	return NOT_IMPLEMENTED;
}

Result bvLeftShiftBothWays(vector<FixedBits*>& children, FixedBits& output)
{
	const unsigned bitWidth = output.getWidth();
	assert(2== children.size());
	assert(bitWidth > 0);

	Result result = NO_CHANGE;

	FixedBits& op = *children[0];
	FixedBits& shift = *children[1];

	if (debug_shift)
	{
		cerr << "op:" << op << endl;
		cerr << "shift:" << shift << endl;
		cerr << "output:" << output << endl;
	}

	// The topmost number of possible shifts corresponds to all
	// the values of shift that shift out everything.
	// i.e. possibleShift[bitWidth+1] is the SET of all operations that shift past the end.
	const unsigned numberOfPossibleShifts = bitWidth + 1;
	bool possibleShift[numberOfPossibleShifts];
	for (unsigned i = 0; i < numberOfPossibleShifts; i++)
		possibleShift[i] = false;

	unsigned minShift, maxShift;
	shift.getUnsignedMinMax(minShift,maxShift);

	// The shift must be less than the position of the first one in the output
	int positionOfFirstOne = -1;
	for (unsigned i = 0; i < bitWidth; i++)
	{
		if (output.isFixed(i) && output.getValue(i))
		{
			positionOfFirstOne = i;
			break;
		}
	}

	if (positionOfFirstOne >= 0)
	{
		if ((unsigned) positionOfFirstOne < minShift)
			return CONFLICT;

		maxShift = std::min(maxShift, (unsigned) positionOfFirstOne);
	}

	for (unsigned i = minShift; i <= std::min(bitWidth, maxShift); i++)
	{
		// if the bit-pattern of 'i' is in the set represented by the 'shift'.
		if (shift.unsignedHolds(i))
			possibleShift[i] = true;
	}

	// Complication. Given a shift like [-1]. possibleShift[2] is now false.
	// A shift of 2 isn't possible. But one of three is.
	// possibleShift[2] means any shift >=2 is possible. So it needs to be set
	// to true.
	{
		if (maxShift >= bitWidth)
			possibleShift[bitWidth] = true;
	}

	// Now check one-by-one each shifting.
	// If we are shifting a zero to where a one is (say), then that shifting isn't possible.
	for (unsigned shiftIt = 0; shiftIt < numberOfPossibleShifts; shiftIt++)
	{
		if (possibleShift[shiftIt])
		{
			for (unsigned column = 0; column < bitWidth; column++)
			{
				if (column < shiftIt)
				{
					if (output.isFixed(column) && output.getValue(column)) // output is one in the column. That's wrong.
					{
						possibleShift[shiftIt] = false;
						break;
					}
				}
				else
				{
					// if they are fixed to different values. That's wrong.
					if (output.isFixed(column) && op.isFixed(column - shiftIt) && (output.getValue(column) != op.getValue(column - shiftIt)))
					{
						possibleShift[shiftIt] = false;
						break;
					}
				}
			}
		}
	}

	int nOfPossibleShifts = 0;
	int shiftIndex = 0;
	for (unsigned i = 0; i < numberOfPossibleShifts; i++)
	{
		if (possibleShift[i])
		{
			nOfPossibleShifts++;
			shiftIndex = i;
			if (debug_shift)
			{
				std::cerr << "Possible:" << i << std::endl;
			}
		}
	}

	if (debug_shift)
	{
		std::cerr << "Number of possible shifts:" << nOfPossibleShifts << endl;
	}

	// If it's empty. It's a conflict.
	if (0 == nOfPossibleShifts)
		return CONFLICT;

	// We have a list of all the possible shift amounts.
	// We take the union of all the bits that are possible.

	FixedBits v(bitWidth, false);
	bool first = true;
	for (unsigned i = 0; i < numberOfPossibleShifts-1; i++)
	{
		if (possibleShift[i])
		{
			if (first)
			{
				first = false;
				for (unsigned j = 0; j < (unsigned) v.getWidth(); j++)
				{
					v.setFixed(j, true);
					if (j <  sizeof(unsigned)*8)
						v.setValue(j, 0 != (i & (1 << j)));
					else
						v.setValue(j, false);
				}
			}
			else
			{
				// join.
				for (unsigned j = 0; j < (unsigned) v.getWidth() && j <  sizeof(unsigned)*8; j++)
				{
					if (v.isFixed(j))
					{
						// union.
						if (v.getValue(j) != (0!=(i & (1 << j))))
							v.setFixed(j, false);
					}
				}
			}
		}
	}

	// The top most entry of the shift table is special. It means all values of shift
	// that fill it completely with zeroes. We take the union of all of the values >bitWidth
	// in this function.
	if (possibleShift[numberOfPossibleShifts - 1])
	{
		FixedBits bitWidthFB = FixedBits::fromUnsignedInt(bitWidth, bitWidth);
		FixedBits output(1, true);
		output.setFixed(0, true);
		output.setValue(0, true);
		FixedBits working(shift);

		vector<FixedBits*> args;
		args.push_back(&working);
		args.push_back(&bitWidthFB);

		//Write into working anything that can be determined given it's >=bitWidth.
		Result r = bvGreaterThanEqualsBothWays(args,output);
		assert(CONFLICT != r);

		// Get the union of "working" with the prior union.
		for (unsigned i = 0; i < bitWidth; i++)
		{
			if (!working.isFixed(i) && v.isFixed(i))
				v.setFixed(i, false);
			if (working.isFixed(i) && v.isFixed(i) && (working.getValue(i) != v.getValue(i)))
				v.setFixed(i, false);
			if (first) // no less shifts possible.
			{
				if (working.isFixed(i))
				{
					v.setFixed(i, true);
					v.setValue(i, working.getValue(i));
				}
			}
		}
	}

	if (debug_shift)
	{
		std::cerr << "Shift Amount:" << v << std::endl;
	}

	for (unsigned i = 0; i < bitWidth; i++)
	{
		if (v.isFixed(i))
		{
			if (!shift.isFixed(i))
			{
				shift.setFixed(i, true);
				shift.setValue(i, v.getValue(i));
				result = CHANGED;
			}
			else if (shift.isFixed(i) && shift.getValue(i) != v.getValue(i))
				return CONFLICT;
		}
	}

	// If a particular input bit appears in every possible shifting,
	// and if that bit is unfixed,
	// and if the result it is fixed to the same value in every position.
	// Then, that bit must be fixed.
	// E.g.  [--] << [0-] == [00]

	bool candidates[bitWidth];
	for (unsigned i = 0; i < bitWidth; i++)
	{
		candidates[i] = !op.isFixed(i);
	}

	// candidates: So far: the bits that are unfixed.

	for (unsigned i = 0; i < numberOfPossibleShifts; i++)
	{
		if (possibleShift[i])
		{
			// If this shift is possible, then some bits will be shifted out.
			for (unsigned j = 0; j < i; j++)
				candidates[bitWidth - 1 - j] = false;
		}
	}

	// candidates: So far: + the input bits that are unfixed.
	//                     + the input bits that are in every possible fixing.

	// Check all candidates have the same output values.
	for (unsigned candidate = 0; candidate < bitWidth; candidate++)
	{
		bool first = true;
		bool setTo = false; // value that's never read. To quieten gcc.

		if (candidates[candidate])
		{
			for (unsigned shiftIT = 0; shiftIT < bitWidth; shiftIT++)
			{
				// If the shift isn't possible continue.
				if (!possibleShift[shiftIT])
					continue;

				unsigned idx = candidate + shiftIT;

				if (!output.isFixed(idx))
				{
					candidates[candidate] = false;
					break;
				}
				else
				{
					if (first)
					{
						first = false;
						setTo = output.getValue(idx);
					}
					else
					{
						if (setTo != output.getValue(idx))
						{
							candidates[candidate] = false;
							break;
						}

					}
				}
			}
		}

		if (candidates[candidate])
		{
			assert(!op.isFixed(candidate));
			op.setFixed(candidate, true);
			op.setValue(candidate, setTo);
		}
	}

	// done.

	// Go through each of the possible shifts. If the same value is fixed
	// at every location. Then it's fixed too in the result.
	for (unsigned column = 0; column < bitWidth; column++)
	{
		bool allFixedToSame = true;
		bool allFixedTo = false; // value that's never read. To quieten gcc.
		bool first = true;

		for (unsigned shiftIt = minShift; (shiftIt < numberOfPossibleShifts) && allFixedToSame; shiftIt++)
		{
			if (possibleShift[shiftIt])
			{
				// Will have shifted in zeroes.
				if (shiftIt > column)
				{
					if (first)
					{
						allFixedTo = false;
						first = false;
					}
					else
					{
						if (allFixedTo)
						{
							allFixedToSame = false;
						}
					}
				}
				else
				{
					unsigned index = column - shiftIt;
					if (!op.isFixed(index))
						allFixedToSame = false;
					else if (first && op.isFixed(index))
					{
						first = false;
						allFixedTo = op.getValue(index);
					}
					if (op.isFixed(index) && allFixedTo != op.getValue(index))
						allFixedToSame = false;
				}
			}
		}

		// If it can be just one possible value. Then we can fix 'em.
		if (allFixedToSame)
		{
			if (output.isFixed(column) && (output.getValue(column) != allFixedTo))
				return CONFLICT;
			if (!output.isFixed(column))
			{
				output.setFixed(column, true);
				output.setValue(column, allFixedTo);
				result = CHANGED;
			}
		}
	}

	/*
	// If there is only one possible shift value. Then, we can push from the output back.
	if (1 == nOfPossibleShifts)
	{
		for (unsigned i = shiftIndex; i < bitWidth; i++)
		{
			if (!op.isFixed(i - shiftIndex) && output.isFixed(i))
			{
				op.setFixed(i - shiftIndex, true);
				op.setValue(i - shiftIndex, output.getValue(i));
				result = CHANGED;
			}
		}
	}
*/

	return NOT_IMPLEMENTED;
}

}
}
