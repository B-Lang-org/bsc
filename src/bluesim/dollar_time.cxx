/* Implementations of $time and $stime */
#include <cstdlib>
#include "bluesim_kernel_api.h"

tUInt64 dollar_time(tSimStateHdl simHdl)
{
  return (tUInt64) bk_now(simHdl);
}

tUInt32 dollar_stime(tSimStateHdl simHdl)
{
  return (tUInt32) bk_now(simHdl);
}

tUInt32 dollar_random(tSimStateHdl simHdl)
{
  return (tUInt32) random();
}

tUInt32 dollar_random_range(tSimStateHdl simHdl,
      tUInt32 maxval,
      tUInt32 minval = 0)
{
  return (dollar_random(simHdl) % (maxval - minval + 1)) + minval;
}
