#include <vector>
#include <cstring>
#include <cstdlib>

#include "bluesim_kernel_api.h"
#include "kernel.h"
#include "plusargs.h"
#include "portability.h"  // needs port_strdup

void clear_plusargs(tSimStateHdl simHdl)
{
  for (std::vector<const char*>::iterator n = simHdl->plus_args.begin();
       n != simHdl->plus_args.end();
       ++n)
  {
    free(const_cast<char*>(*n));
  }
  simHdl->plus_args.clear();
}

void bk_append_argument(tSimStateHdl simHdl, const char* arg)
{
  if (arg != NULL)
    simHdl->plus_args.push_back(port_strdup(arg));
}

const char* bk_match_argument(tSimStateHdl simHdl, const char* name)
{
  if (name == NULL)
    return NULL;

  for (std::vector<const char*>::iterator n = simHdl->plus_args.begin();
       n != simHdl->plus_args.end();
       ++n)
  {
    const char* arg = *n;
    unsigned int len = strlen(name);
    if (!strncmp(name, arg, len))
      return arg + len; // return trailing portion
  }

  return NULL;  // no match
}

