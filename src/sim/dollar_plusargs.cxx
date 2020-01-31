#include "bluesim_kernel_api.h"

#include <string>

bool dollar_test_dollar_plusargs(tSimStateHdl simHdl,
				 const char* /* size_str */,
				 const std::string* name)
{
  return (bk_match_argument(simHdl, name->c_str()) != NULL);
}
