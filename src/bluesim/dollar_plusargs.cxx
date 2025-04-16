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

// Universal C++ logic for $value$plusargs using void*
// Supports tUInt8*, tUInt32*, tUInt64*, and WideData*
bool local_dollar_value_dollar_plusargs(tSimStateHdl simHdl,
          const char* size_str,
          const std::string* format,
          void* result)
{
    const char* fmt = format->c_str();
    const char* percent = strchr(fmt, '%');
    if (!percent) return false; // no format

    std::string key(fmt, percent - fmt);
    const char* val_str = bk_match_argument(simHdl, key.c_str());
    if (!val_str) return false; // not found

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
        return false;
    }

    unsigned int bitwidth = 0;
    const char* comma = strchr(size_str, ',');
    if (comma) bitwidth = atoi(comma + 1);

    tUInt64 mask = bitwidth == 0 ? 0 : (1ULL << bitwidth) - 1;
    if (bitwidth <= 64)
      value &= mask;

    if (bitwidth <= 8) {
        *reinterpret_cast<tUInt8*>(result) = static_cast<tUInt8>(value);
    } else if (bitwidth <= 32) {
        *reinterpret_cast<tUInt32*>(result) = static_cast<tUInt32>(value);
    } else if (bitwidth <= 64) {
        *reinterpret_cast<tUInt64*>(result) = value;
    } else {
        WideData* wd = reinterpret_cast<WideData*>(result);
        wd->clear();
        wd->set_whole_word(value & 0xFFFFFFFFULL, 0);
        wd->set_whole_word(value >> 32, 1);
    }
    return true;
}

bool dollar_value_dollar_plusargs(tSimStateHdl simHdl,
  const char* size_str,
  const std::string* format,
  tUInt8* result)
{
  return local_dollar_value_dollar_plusargs(simHdl, size_str, format, result);
}

bool dollar_value_dollar_plusargs(tSimStateHdl simHdl,
  const char* size_str,
  const std::string* format,
  tUInt32* result)
{
  return local_dollar_value_dollar_plusargs(simHdl, size_str, format, result);
}

bool dollar_value_dollar_plusargs(tSimStateHdl simHdl,
  const char* size_str,
  const std::string* format,
  tUInt64* result)
{
  return local_dollar_value_dollar_plusargs(simHdl, size_str, format, result);
}

bool dollar_value_dollar_plusargs(tSimStateHdl simHdl,
  const char* size_str,
  const std::string* format,
  WideData* result)
{
  return local_dollar_value_dollar_plusargs(simHdl, size_str, format, result);
}
