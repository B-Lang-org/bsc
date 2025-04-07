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

WideData dollar_value_dollar_plusargs(tSimStateHdl simHdl,
          const char* /* size_str */,
          const std::string* format)
{

  WideData result(128, NUM_WORDS(128));
  result.clear();

  const char* fmt = format->c_str();
  const char* percent = strchr(fmt, '%');
  if (!percent) return result; // No format found → Invalid

  std::string key(fmt, percent - fmt);

  const char* val_str = bk_match_argument(simHdl, key.c_str());
  if (!val_str) return result; // Not found → Invalid

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
    return result; // Unsupported format → Invalid
  }

  // LSB 64 = value
  result.set_whole_word(static_cast<unsigned int>(value & 0xFFFFFFFF), 0); // [31:0]
  result.set_whole_word(static_cast<unsigned int>(value >> 32), 1);        // [63:32]

  // MSB 64  = valid == 1
  result.set_whole_word(1, 2); // [95:64]
  result.set_whole_word(0, 3); // [127:96] — MSB 32 = 0

  return result;
}
