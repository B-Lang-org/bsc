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

    int bitwidth = 0;
    const char* comma = strchr(size_str, ',');
    if (comma) bitwidth = atoi(comma + 1);

    tUInt64 value;
    bool is_string = false;

    switch (*(percent + 1)) {
      case 'b': // binary
        value = strtoull(val_str, nullptr, 2);
        break;

      case 'o': // octal
        value = strtoull(val_str, nullptr, 8);
        break;

      case 'd': // decimal
      case 'i':
        value = strtoull(val_str, nullptr, 10);
        break;

      case 'h': // hex
      case 'x':
        value = strtoull(val_str, nullptr, 16);
        break;

      case 'f': // float decimal
      case 'F':
      case 'e': // exponential
      case 'g': // general float
      case 'G': {
        double d = strtod(val_str, nullptr);
        std::memcpy(&value, &d, sizeof(double));
        break;
      }

      case 's': // string
        is_string = true;
        break;

      default:
        return false;
    }



    if (!is_string) {
      if(bitwidth<64)
        value &= ((1ULL << bitwidth) - 1);

      if (bitwidth <= 8) {
          *reinterpret_cast<tUInt8*>(result) = static_cast<tUInt8>(value);
      } else if (bitwidth <= 32) {
          *reinterpret_cast<tUInt32*>(result) = static_cast<tUInt32>(value);
      } else if (bitwidth <= 64) {
          *reinterpret_cast<tUInt64*>(result) = value;
      } else {
          WideData* wd = reinterpret_cast<WideData*>(result);
          wd->set_whole_word(static_cast<unsigned int>(value & 0xFFFFFFFFULL), 0);
          wd->set_whole_word(static_cast<unsigned int>(value >> 32), 1);
      }
    } else {
      size_t str_len = strlen(val_str);
      std::string reversed(val_str, str_len);
      std::reverse(reversed.begin(), reversed.end());
      const char* reversed_str = reversed.c_str();

      if (bitwidth <= 8) {
          std::memset(result, 0, sizeof(tUInt8));
          std::memcpy(result, reversed_str, std::min<size_t>(str_len, sizeof(tUInt8)));
      } else if (bitwidth <= 32) {
          std::memset(result, 0, sizeof(tUInt32));
          std::memcpy(result, reversed_str, std::min<size_t>(str_len, sizeof(tUInt32)));
      } else if (bitwidth <= 64) {
          std::memset(result, 0, sizeof(tUInt64));
          std::memcpy(result, reversed_str, std::min<size_t>(str_len, sizeof(tUInt64)));
      } else {
          WideData* wd = reinterpret_cast<WideData*>(result);
          wd->clear();
          unsigned int available_bytes = wd->numWords() * sizeof(unsigned int);
          size_t copy_len = std::min(str_len, static_cast<size_t>(available_bytes));
          std::memcpy(reinterpret_cast<void*>(wd->data), reversed_str, copy_len);
      }
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
