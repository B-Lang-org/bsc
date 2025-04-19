/* Implementations of $random and $random_range */
#include <cstdlib>
#include "bluesim_kernel_api.h"

tUInt32 dollar_random(tSimStateHdl simHdl)
{
  return (tUInt32) random();
}

tUInt32 dollar_urandom_range(tSimStateHdl simHdl,
    const char* /* size_str */,
    tUInt32 maxval,
    tUInt32 minval = 0)
{
  return (dollar_random(simHdl) % (maxval - minval + 1)) + minval;
}
