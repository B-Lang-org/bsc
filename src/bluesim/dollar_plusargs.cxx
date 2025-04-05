#include "bluesim_kernel_api.h"

#include <string>
#include <cstring>

bool dollar_test_dollar_plusargs(tSimStateHdl simHdl,
				 const char* /* size_str */,
				 const std::string* name)
{
  return (bk_match_argument(simHdl, name->c_str()) != NULL);
}

tUInt64 dollar_value_dollar_plusargs(tSimStateHdl simHdl,
          const char* /* size_str */,
          const std::string* format)
{
  const char* fmt = format->c_str();
  const char* percent = strchr(fmt, '%');
  if (!percent) return 0;//no fromatted string

  std::string key(fmt, percent - fmt);

  const char* val_str = bk_match_argument(simHdl, key.c_str());
  if (!val_str) return 0;//no matching string

  switch (*(percent + 1)) {
    case 'd':
    case 'i':
      return static_cast<tUInt64>(strtoll(val_str, nullptr, 10));

    case 'f':
    case 'F': {
          double d = strtod(val_str, nullptr);
          tUInt64 u;
          std::memcpy(&u, &d, sizeof(double));
          return u;
        }

    default:
      return 0;//what is format?
  }
}
