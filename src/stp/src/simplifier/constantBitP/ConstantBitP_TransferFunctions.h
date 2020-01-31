/*
 * ConstantBitPropagation_TransferFunctions.h
 *
 */
// Trevor Hansen. BSD License.

#ifndef CONSTANTBITPROPAGATION_TRANSFERFUNCTIONS_H_
#define CONSTANTBITPROPAGATION_TRANSFERFUNCTIONS_H_

#include "ConstantBitPropagation.h"
namespace simplifier
{
namespace constantBitP
{
class MultiplicationStats;

// Multiply is not yet  maximally precise.
//!!!!!!!
Result bvMultiplyBothWays(vector<FixedBits*>& children, FixedBits& output, BEEV::STPMgr* bm, MultiplicationStats* ms = NULL);
Result bvUnsignedDivisionBothWays(vector<FixedBits*>& children, FixedBits& output, BEEV::STPMgr* bm);
Result bvUnsignedModulusBothWays(vector<FixedBits*>& children, FixedBits& output, BEEV::STPMgr* bm);
Result bvSignedDivisionBothWays(vector<FixedBits*>& children, FixedBits& output, BEEV::STPMgr* bm);
Result bvSignedRemainderBothWays(vector<FixedBits*>& children, FixedBits& output, BEEV::STPMgr* bm);
Result bvSignedModulusBothWays(vector<FixedBits*>& children, FixedBits& output, BEEV::STPMgr* bm);
//!!!!!!!


// BOTH WAY FUNCTIONS..-------MAXIMALLY PRECISE..........
Result bvEqualsBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvAndBothWays(vector<FixedBits*>& operands, FixedBits& output);

Result bvOrBothWays(vector<FixedBits*>& children, FixedBits& output);
Result bvXorBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvImpliesBothWays(vector<FixedBits*>& children, FixedBits& result);

Result bvAddBothWays(vector<FixedBits*>& children, FixedBits& output);
Result bvSubtractBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvNotBothWays(FixedBits& a, FixedBits& output);
Result bvNotBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvITEBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvExtractBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvConcatBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvSignExtendBothWays(vector<FixedBits*>& children, FixedBits& output);
Result bvZeroExtendBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvUnaryMinusBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvLeftShiftBothWays(vector<FixedBits*>& children, FixedBits& output);
Result bvRightShiftBothWays(vector<FixedBits*>& children, FixedBits& output);
Result bvArithmeticRightShiftBothWays(vector<FixedBits*>& children, FixedBits& output);

// FOUR signed operations.
Result bvSignedGreaterThanBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvSignedLessThanBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvSignedLessThanEqualsBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvSignedGreaterThanEqualsBothWays(vector<FixedBits*>& children, FixedBits& output);

// FOUR unsigned operations.

Result bvLessThanBothWays(vector<FixedBits*>& children, FixedBits& output);
Result bvLessThanBothWays(FixedBits& c0, FixedBits &c1, FixedBits& output);

Result bvLessThanEqualsBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvGreaterThanBothWays(vector<FixedBits*>& children, FixedBits& output);

Result bvGreaterThanEqualsBothWays(vector<FixedBits*>& children, FixedBits& output);

}
}

#endif /* CONSTANTBITPROPAGATION_TRANSFERFUNCTIONS_H_ */
