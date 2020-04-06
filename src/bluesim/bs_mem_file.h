#ifndef __BS_MEM_FILE_H__
#define __BS_MEM_FILE_H__

#include "bluesim_types.h"
#include "bs_wide_data.h"

// Status values returned by format handler calls
typedef enum { MF_ACCEPTED       // Address or data accepted
             , MF_BAD_FORMAT     // Address or data was not formatted correctly
             , MF_IGNORED        // Out-of-bound data was ignored
             , MF_OUT_OF_BOUNDS  // Issue out-of-bounds address error
             } tMemFileStatus;

// Interface for various format handling (binary, hex, etc.) engines
class FormatHandler
{
 public:
  FormatHandler() {}
  virtual ~FormatHandler() {}
  virtual tMemFileStatus updateAddress(const char* addr_str) = 0;
  virtual tMemFileStatus setEntry(const char* data_str) = 0;
  virtual void checkRange(const char* filename, const char* memname) = 0;
};

// This is the top-level file parser/loader
extern void read_mem_file(const char* filename,
                          const char* memname,
                          FormatHandler* handler);

// Utility functions used for writing FormatHandler parsers

extern bool parse_hex(tUInt8*  value, const char* str, unsigned int data_bits);
extern bool parse_hex(tUInt32* value, const char* str, unsigned int data_bits);
extern bool parse_hex(tUInt64* value, const char* str, unsigned int data_bits);
extern bool parse_hex(tUWide*  value, const char* str, unsigned int data_bits);

extern bool parse_bin(tUInt8*  value, const char* str, unsigned int data_bits);
extern bool parse_bin(tUInt32* value, const char* str, unsigned int data_bits);
extern bool parse_bin(tUInt64* value, const char* str, unsigned int data_bits);
extern bool parse_bin(tUWide*  value, const char* str, unsigned int data_bits);

#endif /* __BS_MEM_FILE_H__ */
