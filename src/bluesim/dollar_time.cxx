/* Implementations of $time and $stime */

#include "bluesim_kernel_api.h"

tUInt64 dollar_time(tSimStateHdl simHdl)
{
  return (tUInt64) bk_now(simHdl);
}

tUInt32 dollar_stime(tSimStateHdl simHdl)
{
  return (tUInt32) bk_now(simHdl);
}
