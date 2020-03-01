#ifndef __BLUESIM_SYSTEMC_H__
#define __BLUESIM_SYSTEMC_H__

#include <systemc.h>

#include "bluesim_types.h"
#include "bs_wide_data.h"

/* Note: These functions and the odd style of bs_convert_from_sys
 *       result from a need to write code which works for both
 *       tUWide and POD return types.  Since partial specialization
 *       is not allowed on function templates and overloading does
 *       not consider return types, this was the best solution.
 */

static void do_assign(tUWide& dst, unsigned int idx, unsigned int val)
{
  dst[idx] = val;
}

static void do_assign(tUInt64& dst, unsigned int idx, unsigned int val)
{
  tUInt64 mask = (1llu << 32) - 1;
  if (idx == 0)
  {
    dst &= ~mask; // clear out low 32 bits
    dst |= (tUInt64) val;
  }
  else
  {
    dst &= mask; // clear out upper 32 bits
    dst |= ((tUInt64) val) << 32;
  }
}

static void do_assign(tUInt32& dst, unsigned int /* unused */, unsigned int val)
{
  dst = val;
}

static void do_assign(tUInt8& dst, unsigned int /* unused */, unsigned int val)
{
  dst = val;
}

static unsigned int iter_count(tUWide& x)
{
  return x.numWords();
}

static unsigned int iter_count(tUInt64 /* unused */)
{
  return 2;
}

static unsigned int iter_count(tUInt32 /* unused */)
{
  return 1;
}

static unsigned int iter_count(tUInt8 /* unused */)
{
  return 1;
}

template<typename SCT, typename BST>
static BST bs_convert_from_sysc(SCT x)
{
  BST result;
  unsigned int len = x.length();
  unsigned int lo = 0;
  unsigned int hi;

  init_val(result, len);
  for (unsigned int idx = 0; idx < iter_count(result); ++idx)
  {
    hi = std::min(len-1,lo+31);
    do_assign(result, idx, x.range(hi,lo).to_uint());
    lo = hi+1;
  }

  return result;
}

template<>
tUInt8 bs_convert_from_sysc<bool,tUInt8>(bool x)
{
  tUInt8 result = x ? 1 : 0;
  return result;
}

template<typename SCT>
static SCT bs_convert_wide_to_sysc(tUWide x)
{
  SCT result;
  unsigned int len = x.size();
  unsigned int lo = 0;
  unsigned int hi;

  for (unsigned int idx = 0; idx < x.numWords(); ++idx)
  {
    hi = std::min(len-1,lo+31);
    result.range(hi,lo) = x[idx];
    lo = hi + 1;
  }
  return result;
}

#endif /* __BLUESIM_SYSTEMC_H__ */
