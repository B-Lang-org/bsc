/* Implementations of $stop and $finish */

#include "bluesim_kernel_api.h"

void dollar_stop(tSimStateHdl simHdl, const char* /* unused */, int status)
{
  bk_stop_now(simHdl, status);
}

void dollar_finish(tSimStateHdl simHdl, const char* /* unused */, int status)
{
  bk_finish_now(simHdl, status);
}
