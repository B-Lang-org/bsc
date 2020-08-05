#include <cstdio>
#include <string>
#include <cstring>
#include <ctype.h>
#include <errno.h>

#include "bs_wide_data.h"
#include "bs_mem_defines.h"
#include "bs_mem_file.h"

// Parser states
typedef enum { START
             , BEGIN_COMMENT
             , IN_CPP_COMMENT
             , IN_C_COMMENT
             , END_C_COMMENT
             , IN_ADDR
             , IN_VALUE
             } tMemParserState;

// Wrapper for callback to handle address entries
const char* processAddress(const char* addr_str, FormatHandler* handler)
{
  tMemFileStatus status = handler->updateAddress(addr_str);
  if (status == MF_BAD_FORMAT)
    return "Malformed address";
  else if (status == MF_OUT_OF_BOUNDS)
    return "Address is outside of the allowed range";
  else
    return NULL;
}

// Wrapper for callback to handle value entries
const char* processData(const char* value_str, FormatHandler* handler)
{
  tMemFileStatus status = handler->setEntry(value_str);
  if (status == MF_BAD_FORMAT)
    return "Malformed value";
  else
    return NULL;
}

// Top-level routine to read a file
void read_mem_file(const char* filename,
                   const char* memname,
                   FormatHandler* handler)
{
  if (filename == NULL)
    return;

  FILE* in = fopen(filename, "r");
  if (!in)
  {
    printf("Error: failed to open file '%s' because %s\n",
           filename, strerror(errno));
    return;
  }

  // parse the file contents, passing addresses and data
  // to the handler as strings
  char buf[128];
  char err_buf[256];
  char* cptr;
  unsigned int comment_start_line = 0;
  unsigned int line = 1;
  unsigned int start_line = 1;
  std::string addr_str;
  std::string value_str;
  tMemParserState state = START;
  while (fgets(buf, 128, in))
  {
    cptr = buf;

    // when a line extends beyond a buffer, we may need to accumulate
    // in the current address or value string
    if (state == IN_VALUE)
      value_str += cptr;
    if (state == IN_ADDR)
      addr_str += cptr;

    // parse the current buffer contents character-by-character
    while (*cptr != '\0')
    {
      char c = *cptr;
      switch (state)
      {
        case START:
        {
          if (c == '/')
          {
            state = BEGIN_COMMENT;
          }
          else if (c == '@')
          {
            state = IN_ADDR;
            addr_str = cptr+1;
            start_line = line;
          }
          else if (isxdigit(c))
          {
            state = IN_VALUE;
            value_str = cptr;
            start_line = line;
          }
          else if (c == '\n')
          {
            ++line;
            // stay in START state
          }
          else if ((c == '\r') || isblank(c))
          {
            // stay in START state
          }
          else
          {
            printf("Error: syntax error at line %d of file '%s'\n",
                   line, filename);
            printf("       Encountered '%c' when expecting '/', '@', hex digit, end-of-line or whitespace.\n", c);
            fclose(in);
            return;
          }
          break;
        }

        case BEGIN_COMMENT:
        {
          if (c == '/')
          {
            state = IN_CPP_COMMENT;
          }
          else if (c == '*')
          {
            state = IN_C_COMMENT;
            comment_start_line = line;
          }
          else
          {
            printf("Error: syntax error at line %d of file '%s'\n",
                   line, filename);
            printf("       Malformed comment start sequence.\n");
            fclose(in);
            return;
          }
          break;
        }

        case IN_CPP_COMMENT:
        {
          if (c == '\n')
          {
            ++line;
            state = START;
          }
          else
          {
            // stay in IN_CPP_COMMENT state
          }
          break;
        }

        case IN_C_COMMENT:
        {
          if (c == '\n')
          {
            // stay in IN_C_COMMENT state
            ++line;
          }
          else if (c == '*')
          {
            state = END_C_COMMENT;
          }
          else
          {
            // stay in IN_C_COMMENT state
          }
          break;
        }

        case END_C_COMMENT:
        {
          if (c == '/')
          {
            state = START;
          }
          else
          {
            state = IN_C_COMMENT;
          }
          break;
        }

        case IN_ADDR:
        {
          const char* err = NULL;
          if ((c == '\n') || (c == '\r') || isblank(c))
          {
            err = processAddress(addr_str.c_str(), handler);
            if (c == '\n') ++line;
            state = START;
          }
          else if (c == '/')
          {
            err = processAddress(addr_str.c_str(), handler);
            state = BEGIN_COMMENT;

          }
          else if (isxdigit(c) || (c == '_') ||
                   (c == 'x')  || (c == 'X') ||
                   (c == 'z')  || (c == 'Z'))
          {
            // stay in IN_ADDR state
          }
          else
          {
            sprintf(err_buf,
                    "Encountered '%c' when expecting '/', hex digit, end-of-line or whitespace",
                    c);
            err = err_buf;
          }

          if (err)
          {
            printf("Error: address processing error at line %d of file '%s'\n",
                   start_line, filename);
            printf("       %s.\n", err);
            fclose(in);
            return;
          }

          break;
        }

        case IN_VALUE:
        {
          const char* err = NULL;
          if ((c == '\n') || (c == '\r') || isblank(c))
          {
            err = processData(value_str.c_str(), handler);
            if (c == '\n') ++line;
            state = START;
          }
          else if (c == '/')
          {
            err = processData(value_str.c_str(), handler);
            state = BEGIN_COMMENT;
          }
          else if (isxdigit(c) || (c == '_') ||
                   (c == 'x')  || (c == 'X') ||
                   (c == 'z')  || (c == 'Z'))
          {
            // stay in IN_VALUE state
          }
          else
          {
            sprintf(err_buf,
                    "Encountered '%c' when expecting '/', digit, end-of-line or whitespace",
                    c);
            err = err_buf;
          }

          if (err)
          {
            printf("Error: value processing error at line %d of file '%s'\n",
                   start_line, filename);
            printf("       %s.\n", err);
            fclose(in);
            return;
          }

          break;
        }
      }
      ++cptr;
    }
  }

  if (state == IN_C_COMMENT || state == END_C_COMMENT)
  {
    printf("Error: syntax error at line %d of file '%s'\n",
           comment_start_line, filename);
    printf("       Unterminated C-style comment.\n");

  }
  else if (state == IN_VALUE)
  {
    const char* err = processData(value_str.c_str(), handler);
    if (err)
    {
      printf("Error: value processing error at line %d of file '%s'\n",
             line, filename);
      printf("       %s.\n", err);
    }
  }

  handler->checkRange(filename, memname);

  fclose(in);
}

// Utility functions for use in writing FormatHandlers

static unsigned int fromHex(char c)
{
  if (c >= '0' && c <= '9')
    return c - '0';
  else if (c >= 'a' && c <= 'f')
    return 10 + (c - 'a');
  else if (c >= 'A' && c <= 'F')
    return 10 + (c - 'A');
  else
    return 0;
}

bool parse_bin(tUInt8* value, const char* str, unsigned int data_bits)
{
  char c;
  unsigned int bits = 0;
  tUInt8 x = 0;
  while ((c = *(str++)) != '\0')
  {
    if (c == '_')
    {
      // ignore separator
    }
    else if (c == '0' || c == 'x' || c == 'X' || c == 'z' || c == 'Z')
    {
      x = x << 1;
      ++bits;
    }
    else if (c == '1')
    {
      x = (x << 1) + 1;
      ++bits;
    }
    else if (c == '/' || c == '\n' || c == '\r' || isblank(c))
    {
      break;
    }
    else
      return false;

    if (bits > data_bits)
      return false;
  }

  *value = x;
  return true;
}

bool parse_hex(tUInt8* value, const char* str, unsigned int data_bits)
{
  char c;
  unsigned int bits = 0;
  tUInt8 x = 0;
  while ((c = *(str++)) != '\0')
  {
    if (c == '_')
    {
      // ignore separator
    }
    else if (isxdigit(c))
    {
      x = (x << 4) + fromHex(c);
      bits += 4;
    }
    else if (c == 'x' || c == 'X' || c == 'z' || c == 'Z')
    {
      x = x << 4;
      bits += 4;
    }
    else if (c == '/' || c == '\n' || c == '\r' || isblank(c))
    {
      break;
    }
    else
      return false;

    // only an error if we extend beyond the final nibble or
    // there is data in high bits which don't exist in the last
    // nibble.
    if ((bits/4 > (data_bits+3)/4) || ((bits/4 == (data_bits+3)/4) &&
                                       ((data_bits % 4) != 0) &&
                                       ((x >> data_bits) != 0)))
      return false;
  }

  *value = x;
  return true;
}

bool parse_bin(tUInt32* value, const char* str, unsigned int data_bits)
{
  char c;
  unsigned int bits = 0;
  tUInt32 x = 0;
  while ((c = *(str++)) != '\0')
  {
    if (c == '_')
    {
      // ignore separator
    }
    else if (c == '0' || c == 'x' || c == 'X' || c == 'z' || c == 'Z')
    {
      x = x << 1;
      ++bits;
    }
    else if (c == '1')
    {
      x = (x << 1) + 1;
      ++bits;
    }
    else if (c == '/' || c == '\n' || c == '\r' || isblank(c))
    {
      break;
    }
    else
      return false;

    if (bits > data_bits)
      return false;
  }

  *value = x;
  return true;
}

bool parse_hex(tUInt32* value, const char* str, unsigned int data_bits)
{
  char c;
  unsigned int bits = 0;
  tUInt32 x = 0;
  while ((c = *(str++)) != '\0')
  {
    if (c == '_')
    {
      // ignore separator
    }
    else if (isxdigit(c))
    {
      x = (x << 4) + fromHex(c);
      bits += 4;
    }
    else if (c == 'x' || c == 'X' || c == 'z' || c == 'Z')
    {
      x = x << 4;
      bits += 4;
    }
    else if (c == '/' || c == '\n' || c == '\r' || isblank(c))
    {
      break;
    }
    else
      return false;

    // only an error if we extend beyond the final nibble or
    // there is data in high bits which don't exist in the last
    // nibble.
    if ((bits/4 > (data_bits+3)/4) || ((bits/4 == (data_bits+3)/4) &&
                                       ((data_bits % 4) != 0) &&
                                       ((x >> data_bits) != 0)))
      return false;
  }

  *value = x;
  return true;
}

bool parse_bin(tUInt64* value, const char* str, unsigned int data_bits)
{
  char c;
  unsigned int bits = 0;
  tUInt64 x = 0llu;
  while ((c = *(str++)) != '\0')
  {
    if (c == '_')
    {
      // ignore separator
    }
    else if (c == '0' || c == 'x' || c == 'X' || c == 'z' || c == 'Z')
    {
      x = x << 1;
      ++bits;
    }
    else if (c == '1')
    {
      x = (x << 1) + 1;
      ++bits;
    }
    else if (c == '/' || c == '\n' || c == '\r' || isblank(c))
    {
      break;
    }
    else
      return false;

    if (bits > data_bits)
      return false;
  }

  *value = x;
  return true;
}

bool parse_hex(tUInt64* value, const char* str, unsigned int data_bits)
{
  char c;
  unsigned int bits = 0;
  tUInt64 x = 0llu;
  while ((c = *(str++)) != '\0')
  {
    if (c == '_')
    {
      // ignore separator
    }
    else if (isxdigit(c))
    {
      x = (x << 4) + fromHex(c);
      bits += 4;
    }
    else if (c == 'x' || c == 'X' || c == 'z' || c == 'Z')
    {
      x = x << 4;
      bits += 4;
    }
    else if (c == '/' || c == '\n' || c == '\r' || isblank(c))
    {
      break;
    }
    else
      return false;

    // only an error if we extend beyond the final nibble or
    // there is data in high bits which don't exist in the last
    // nibble.
    if ((bits/4 > (data_bits+3)/4) || ((bits/4 == (data_bits+3)/4) &&
                                       ((data_bits % 4) != 0) &&
                                       ((x >> data_bits) != 0llu)))
      return false;
  }

  *value = x;
  return true;
}

bool parse_bin(tUWide* value, const char* str, unsigned int data_bits)
{
  // find the end of the string
  const char* cptr = str;
  while (*cptr != '\0' && *cptr != '\n' && *cptr != '\r' &&
         *cptr != '/'  && !isblank(*cptr))
    ++cptr;

  // parse characters from LSB back
  char c;
  unsigned int word = 0;
  unsigned int idx = 0;
  unsigned int x = 0;
  unsigned int bits = 0;
  while (cptr != str)
  {
    c = *(--cptr);
    if (c == '_')
    {
      // ignore separator
    }
    else if (c == '0' || c == 'x' || c == 'X' || c == 'z' || c == 'Z')
    {
      ++bits;
      ++idx;
    }
    else if (c == '1')
    {
      x |= (1 << idx);
      ++bits;
      ++idx;
    }
    else
      return false;

    if (bits > data_bits)
      return false;

    if (idx == WORD_SIZE)
    {
      (*value)[word++] = x;
      idx = 0;
    }
  }

  // write partial word at end
  if (idx != 0)
    (*value)[word] = x;

  return true;
}

bool parse_hex(tUWide* value, const char* str, unsigned int data_bits)
{
  // find the end of the string
  const char* cptr = str;
  while (*cptr != '\0' && *cptr != '\n' && *cptr != '\r' &&
         *cptr != '/'  && !isblank(*cptr))
    ++cptr;

  // parse characters from LSB back
  char c;
  unsigned int word = 0;
  unsigned int idx = 0;
  unsigned int x = 0;
  unsigned int bits = 0;
  while (cptr != str)
  {
    c = *(--cptr);
    if (c == '_')
    {
      // ignore separator
    }
    else if (isxdigit(c))
    {
      x |= (fromHex(c) << idx);
      bits += 4;
      idx += 4;
    }
    else if (c == 'x' || c == 'X' || c == 'z' || c == 'Z')
    {
      bits += 4;
      idx += 4;
    }
    else
      return false;

    // only an error if we extend beyond the final nibble or
    // there is data in high bits which don't exist in the last
    // nibble.
    if ((bits/4 > (data_bits+3)/4) || ((bits/4 == (data_bits+3)/4) &&
                                       ((data_bits % 4) != 0) &&
                                       ((x >> (data_bits % WORD_SIZE)) != 0)))
      return false;

    if (idx == WORD_SIZE)
    {
      (*value)[word++] = x;
      x = 0;
      idx = 0;
    }
  }

  // write partial word at end
  if (idx != 0)
    (*value)[word] = x;

  return true;
}
