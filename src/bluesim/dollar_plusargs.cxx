#include "bluesim_kernel_api.h"
#include "bs_wide_data.h"
#include <string>
#include <cstring>

bool dollar_test_dollar_plusargs(tSimStateHdl simHdl,
				 const char* /* size_str */,
				 const std::string* name)
{
  return (bk_match_argument(simHdl, name->c_str()) != NULL);
}

bool dollar_value_dollar_plusargs(tSimStateHdl simHdl,
          const char* /* size_str */,
          const std::string* format,
          WideData* result)
{
  const char* fmt = format->c_str();
  const char* percent = strchr(fmt, '%');
  if (!percent) return false; // No format found → Invalid

  std::string key(fmt, percent - fmt);

  const char* val_str = bk_match_argument(simHdl, key.c_str());
  if (!val_str) return false; // Not found → Invalid

  tUInt64 value = 0;

  switch (*(percent + 1)) {
    case 'd':
    case 'i':
      value = static_cast<tUInt64>(strtoll(val_str, nullptr, 10));
      break;
    case 'f':
    case 'F': {
      double d = strtod(val_str, nullptr);
      std::memcpy(&value, &d, sizeof(double));
      break;
    }
    default:
    return false; // Unsupported format → Invalid
  }
  result->clear();
  result->set_whole_word(static_cast<unsigned int>(value & 0xFFFFFFFFULL), 0);       // bits  31:0
  result->set_whole_word(static_cast<unsigned int>((value >> 32) & 0xFFFFFFFFULL), 1); // bits 63:32
  result->set_whole_word(0, 2);
  result->set_whole_word(0, 3);
  return true;
}
