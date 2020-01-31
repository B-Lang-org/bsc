#ifndef CONSTANTBITP_UTILITY_H_
#define CONSTANTBITP_UTILITY_H_

#include "ConstantBitPropagation.h"

// Utility functions for use by the transfer functions.
// This should only be included by files defining transfer functions.

namespace simplifier
{
namespace constantBitP
{
using std::cerr;
using std::cout;
using std::endl;
using std::pair;

Result makeEqual(FixedBits& a, FixedBits& b, int from, int to);
void setSignedMinMax(FixedBits& v, BEEV::CBV min, BEEV::CBV max);
void setUnsignedMinMax(const FixedBits& v, BEEV::CBV min, BEEV::CBV max);
unsigned cbvTOInt(const BEEV::CBV v);
void fixUnfixedTo(vector<FixedBits*>& operands, const unsigned position, bool toFix);
int toInt(BEEV::CBV value);

// wraps the comparison function, including a check that the bitWidth is the same.
int unsignedCompare(const BEEV::CBV& lhs, const BEEV::CBV& rhs);
int signedCompare(const BEEV::CBV& lhs, const BEEV::CBV& rhs);

struct stats
{
	unsigned fixedToZero;
	unsigned fixedToOne;
	unsigned unfixed;
};

Result merge(Result r1, Result r2);

stats getStats(const vector<FixedBits*>& operands, const unsigned position);
}
}


#endif
