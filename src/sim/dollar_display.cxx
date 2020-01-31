#include <cstdarg>
#include <cstdio>
#include <cstring>
#include <algorithm>
#include <vector>
#include <string>

#include "bluesim_kernel_api.h"
#include "bs_wide_data.h"
#include "bs_module.h"
#include "bs_target.h"
#include "portability.h"  // needs port_strdup

// This structure is used to record information
// parsed from a format field specifier.
typedef struct
{
  char mode;         // mode character
  int width;         // width specifier (optional)
  int precision;     // precision (optional)
  const char* str;   // pointer to field spec in string (after '%')
  const char* after; // pointer to remainder of string (after mode char)
} tFieldDesc;

// This structure is used to unify different value representations
typedef struct
{
  bool         isSigned;
  bool         usingWideVal;
  bool         localStorage;
  unsigned int bits;
  union
  {
    bool               bitVal;
    signed long long   sVal;
    unsigned long long uVal;
    WideData*          wideVal;
  } data;
} tValue;

// cast tValue to double as best we can
double tValueToDouble(tValue& v) {
  if(v.usingWideVal) {
    return 0; // too lazy to do conversion right now
  }
  else if(v.bits == 1) {
    return(v.data.bitVal ? 1.0 : 0.0);
  }
  else if(v.isSigned) {
    return ((double)v.data.sVal);
  } else
    return ((double)v.data.uVal);
}

// utility functions for dealing with different digit classes
static bool isOctal(char c) { return ( c >= '0' && c <= '7'); }
static bool isDigit(char c) { return ( c >= '0' && c <= '9'); }
static int fromDigit(char c) { return (c - '0'); }

// Return the number of digits required by the widest N-bit value,
// represented in the specified base.
static unsigned int maxWidth(unsigned int nBits, bool isSigned,
                             unsigned int base=10)
{
  // handle power-of-2 bases
  switch (base)
  {
    case 2:  return nBits;
    case 8:  return (nBits + 2) / 3;
    case 16: return (nBits + 3) / 4;
  }

  // handle base 10;
  unsigned int digits = 0;
  unsigned int sign_digit = isSigned ? 1 : 0;

  if (nBits > 64)
    digits = WideData::max_decimal_digits(nBits, isSigned);
  else
  {
    signed int factor = 3;
    if (nBits > 12)
      factor = 2 - ((nBits - 3) / 10);
    else if (nBits > 0)
      factor = 2;
    digits = (nBits + factor) / 3;
  }

  return sign_digit + digits;
}

// Return the number of digits required to represent a given value
// in the specified base.
static unsigned int numDigits(const tValue& v, unsigned int base=10)
{
  if (v.bits < 2)
    return 1;

  if (v.bits > 64)
  {
    // this is expensive for wide data, so we use a different
    // technique for wide data + base 10
    return 0;
  }

  unsigned int digits = 0;
  unsigned long long x = 0L;

  if (v.isSigned)
  {
    if (base == 10)
    {
      digits = (v.data.sVal < 0ll) ? 1 : 0;  // leading minus sign
      x = llabs(v.data.sVal);
    }
    else
    {
      x = v.data.uVal;
      if (v.bits < 64)
        x &= (1llu << v.bits) - 1;
    }
  }
  else
  {
    x = v.data.uVal;
  }

  if (x == 0)
    digits += 1;

  while (x != 0)
  {
    ++digits;
    x /= base;
  }

  return digits;
}

void pad(signed int requested_width,
         unsigned int max_width,
         unsigned int value_width,
         char c,
         Target* dest)
{
  if (requested_width == 0)
    return; // %0* requests no padding

  // Pad with spaces if the requested width is greater than max_width.
  signed int places = requested_width - ((signed int) max_width);
  if (places > 0)
    dest->write_char(' ',places);

  // Pad with the given character if the value_width is less than max_width
  // and requested_width
  if (requested_width > 0)
    places = std::min(requested_width, (signed int) max_width);
  else
    places = (signed int) max_width;
  places -= (signed int) value_width;
  if (places > 0)
    dest->write_char(c,places);
}

// This class implements a handler for variadic functions
// which correlates the size string information with the
// va_list and safely manages the va_list when passed through
// multiple functions.
class ArgList
{
 private:
  char*        type_str;
  const char*  cptr;
  va_list*     ap_ptr;
  bool         has_sign;
  bool         is_pointer;
  bool         is_string;
  bool         is_cxx_string;
  bool         is_double;
  unsigned int size;

 public:
  ArgList(const char* str, va_list* ap)
    : ap_ptr(ap)
  {
    type_str = port_strdup(str);  // use malloc(), so pair with free()
    cptr = type_str;
    next();
  }

  ~ArgList() { free(type_str); }

 private:
  void next();

 public:
  bool isDone() const           { return (type_str == NULL); }
  unsigned int argSize() const  { return size; }
  bool isSigned() const         { return has_sign; }
  bool isPointer() const        { return is_pointer; }
  bool isString() const         { return is_string; }
  bool isCxxString() const      { return is_cxx_string; }
  bool isDouble() const         { return is_double; }

  bool getBit();
  unsigned char getUChar();
  signed char getSChar();
  unsigned int getUInt();
  signed int getSInt();
  unsigned long long getULongLong();
  signed long long getSLongLong();
  double getDouble();
  char* getString();
  std::string* getCxxString();
  void* getPointer();

  void skip() { next(); }
};

void ArgList::next()
{
  if (type_str == NULL)
    return;

  if (*cptr == '\0')
  {
    free(type_str);
    type_str = NULL;
    return;
  }

  // process sign information
  if (*cptr == '-')
  {
    has_sign = true;
    ++cptr;
  } else {
    has_sign = false;
  }

  // process next size value from string
  if (*cptr == '\0')
  {
    free(type_str);
    type_str = NULL;
    return;
  }

  size = 0;
  bool has_size = false;
  while ((*cptr != '\0') && isDigit(*cptr))
  {
    size = size * 10 + fromDigit(*cptr);
    has_size = true;
    ++cptr;
  }

  // process string/pointer/real annotation
  switch (*cptr)
  {
    case 's':
    {
      is_string     = has_size;
      is_cxx_string = !has_size;
      is_pointer    = false;
      is_double     = false;
      ++cptr;
      break;
    }
    case 'p':
    {
      is_pointer    = true;
      is_string     = false;
      is_cxx_string = false;
      is_double     = false;
      ++cptr;
      break;
    case 'r':
      is_double     = true;
      is_pointer    = false;
      is_string     = false;
      is_cxx_string = false;
      // we will convert to a signed long long
      // if a real number is not expected
      has_sign      = true;
      size          = 64;
      break;
    }
    default:
    {
      is_pointer    = false;
      is_string     = false;
      is_cxx_string = false;
      is_double     = false;
    }
  }

  // advance up to next comma
  while ((*cptr != '\0') && (*cptr != ',')) ++cptr;
  if (*cptr == ',') ++cptr;
}

bool ArgList::getBit()
{
  // variable argument lists promote bool to int
  int ret = va_arg(*ap_ptr,int);
  next();
  return (ret != 0);
}

unsigned char ArgList::getUChar()
{
  // variable argument lists promote char to int
  int ret = va_arg(*ap_ptr,int);
  next();
  return (unsigned char) ret;
}

signed char ArgList::getSChar()
{
  // variable argument lists promote char to int
  int ret = va_arg(*ap_ptr,int);
  if ((size < 8) && (ret & (1 << (size - 1))))
    ret |= ~((1 << size) - 1);
  next();
  return (signed char) ret;
}

unsigned int ArgList::getUInt()
{
  unsigned int ret = va_arg(*ap_ptr,unsigned int);
  next();
  return ret;
}

signed int ArgList::getSInt()
{
  signed int ret = va_arg(*ap_ptr,signed int);
  if ((size < 32) && (ret & (1 << (size - 1))))
    ret |= ~((1 << size) - 1);
  next();
  return ret;
}

unsigned long long ArgList::getULongLong()
{
  unsigned long long ret = va_arg(*ap_ptr,unsigned long long);
  next();
  return ret;
}

signed long long ArgList::getSLongLong()
{
  signed long long ret = va_arg(*ap_ptr,signed long long);
  if ((size < 64) && (ret & (1llu << (size - 1))))
    ret |= ~((1llu << size) - 1);
  next();
  return ret;
}

double ArgList::getDouble()
{
  double ret = va_arg(*ap_ptr,double);
  next();
  return ret;
}

char* ArgList::getString()
{
  char* ret = va_arg(*ap_ptr,char*);
  next();
  return ret;
}

std::string* ArgList::getCxxString()
{
  std::string* ret = va_arg(*ap_ptr,std::string*);
  next();
  return ret;
}

void* ArgList::getPointer()
{
  void* ret = va_arg(*ap_ptr,void*);
  next();
  return ret;
}

void fill_tValue(tValue& v, ArgList* args, Target* dest)
{
  v.isSigned = args->isSigned();
  v.usingWideVal = args->isPointer() || args->isString() || args->isCxxString();
  v.localStorage = args->isString() || args->isCxxString();
  v.bits = args->argSize();
  if (args->isPointer())
    v.data.wideVal = (WideData*) args->getPointer();
  else if (args->isString())
    v.data.wideVal = new WideData(v.bits,args->getString());
  else if (args->isCxxString())
  {
    const std::string* s = args->getCxxString();
    if (s)
    {
      v.bits = 8 * s->length();
      v.data.wideVal = new WideData(v.bits,s->c_str());
    }
    else
      v.data.wideVal = NULL;
  }
  else if (args->isDouble()) {
    dest->add_error("unexpected real number argument\n");
    v.data.sVal = (signed long long) args->getDouble();
  }
  else
  {
    if (v.bits == 1)
      v.data.bitVal = args->getBit();
    else if (v.isSigned)
    {
      if (v.bits <= 8)
        v.data.sVal = args->getSChar();
      else if (v.bits <= 32)
        v.data.sVal = args->getSInt();
      else
        v.data.sVal = args->getSLongLong();
    }
    else
    {
      if (v.bits <= 8)
        v.data.uVal = args->getUChar();
      else if (v.bits <= 32)
        v.data.uVal = args->getUInt();
      else
        v.data.uVal = args->getULongLong();
    }
  }
}

void discard_tValue(tValue& v)
{
  if (v.localStorage)
    delete v.data.wideVal;
}

const std::string* convert_to_string(ArgList* args, Target* dest)
{
  if (args->isDone())
    return NULL;

  if (args->isString() || args->isCxxString())
    return NULL;  // actually a bug if this occurs

  // to interpret a number as a string, the characters start at the
  // MSB and each byte is treated as a character moving toward the LSB,
  // but leading zeros should be ignored.
  tValue v;
  fill_tValue(v, args, dest);
  std::string* str = new std::string();
  if (v.usingWideVal)
  {
    unsigned int i = (v.data.wideVal->size() + 7) / 8;
    while ((i > 0) && (v.data.wideVal->getByte(i-1) == 0)) --i;
    while (i-- > 0)
      str->push_back(v.data.wideVal->getByte(i));
  }
  else if (v.bits == 1)
  {
    if (v.data.bitVal == 1) str->push_back(1);
  }
  else
  {
    unsigned int i = (v.bits + 7) / 8;
    while ((i > 0) && (((v.data.uVal >> (8*(i-1))) & 0xFF) == 0)) --i;
    while (i-- > 0)
      str->push_back((v.data.uVal >> (8*i)) & 0xFF);
  }

  discard_tValue(v);

  return str;
}

// This function is used to handle escape sequences beginning with '\'
const char* handle_escape(const char* cptr, Target* dest)
{
  switch (*cptr)
  {
    case '\0':  // backslash as last character -- no escape
    {
      dest->write_char('\\');
      break;
    }
    case 'n':   // emit newline
    {
      dest->write_char('\n');
      ++cptr;
      break;
    }
    case 't':   // emit tab
    {
      dest->write_char('\t');
      ++cptr;
      break;
    }
    case '\\':  // emit single backslash
    {
      dest->write_char('\\');
      ++cptr;
      break;
    }
    default:
    {
      // parse up to three octal digits and emit corresponding character
      int oct_val = 0;
      if (isOctal(*cptr))
      {
        oct_val = oct_val * 8 + fromDigit(*cptr);
        ++cptr;
        if (isOctal(*cptr))
        {
          oct_val = oct_val * 8 + fromDigit(*cptr);
          ++cptr;
          if (isOctal(*cptr))
          {
            oct_val = oct_val * 8 + fromDigit(*cptr);
            ++cptr;
          }
        }
        dest->write_char(oct_val);
      }
      else
      {
        // non-octal => just print character
        dest->write_char(*cptr);
        ++cptr;
      }
      break;
    }
  }

  return cptr;
}

// Printing routine for %d and %D formats
const char* print_decimal(tFieldDesc& spec, ArgList* args, Target* dest)
{
  if (args->isDone())
  {
    dest->write_char('%');
    return spec.str;  // there is no argument, so do not treat as format
  }

  tValue v;
  fill_tValue(v, args, dest);

  /* There are 2 cases:
   *  %d  => width determined by type size, left-padded with spaces
   *  %nd => minimum width is n, left-padded with spaces
   */

  unsigned int field_width = maxWidth(v.bits, v.isSigned);
  if (v.usingWideVal)
  {
    pad(spec.width, field_width, field_width, ' ', dest);
    if (spec.width == 0)
      v.data.wideVal->print_decimal(dest, 0, v.isSigned);
    else
      v.data.wideVal->print_decimal(dest, field_width, v.isSigned);
  }
  else if (v.bits == 1)
  {
    unsigned int value_width = numDigits(v);
    pad(spec.width, field_width, value_width, ' ', dest);
    if (v.isSigned && v.data.bitVal)
      dest->write_char('-');
    dest->write_char(v.data.bitVal ? '1' : '0');
  }
  else
  {
    unsigned int value_width = numDigits(v);
    pad(spec.width, field_width, value_width, ' ', dest);
    unsigned long long x;
    if (v.isSigned)
    {
      x = llabs(v.data.sVal);
      if (v.data.sVal < 0)
      {
        dest->write_char('-');
        --value_width;
      }
    }
    else
      x = v.data.uVal;
    char c;
    for (unsigned long long i = powll(10, (value_width - 1)); i > 0; i /= 10)
    {
      unsigned long long n = x / i;
      c = '0' + (char) n;
      dest->write_char(c);
      x -= n * i;
    }
  }

  discard_tValue(v);
  return spec.after;
}

// Printing routine for %h and %H formats
const char* print_hex(tFieldDesc& spec, ArgList* args, Target* dest)
{
  if (args->isDone())
  {
    dest->write_char('%');
    return spec.str;  // there is no argument, so do not treat as format
  }

  tValue v;
  fill_tValue(v, args, dest);

  /* There are 2 cases:
   *  %h  => width determined by type size, all bits shown
   *  %nh => minimum width is n, left-padded with zeros
   */
  unsigned int field_width = maxWidth(v.bits, v.isSigned, 16);
  if (v.usingWideVal)
  {
    pad(spec.width, field_width, field_width, '0', dest);
    if (spec.width == 0)
      v.data.wideVal->print_hex(dest, 0);
    else
      v.data.wideVal->print_hex(dest, field_width);
  }
  else if (v.bits == 1)
  {
    unsigned int value_width = numDigits(v,16);
    pad(spec.width, field_width, value_width, '0', dest);
    dest->write_char(v.data.bitVal ? '1' : '0');
  }
  else
  {
    unsigned int value_width = numDigits(v,16);
    pad(spec.width, field_width, value_width, '0', dest);
    unsigned long long x = v.data.uVal;
    if (v.bits < 64)
      x &= (1llu << v.bits) - 1;
    char c;
    for (int i = (value_width - 1)*4; i >= 0; i -= 4)
    {
      if (((x >> i) & 0xF) > 9)
        c = 'a' + (char) (((x >> i) & 0xF) - 10);
      else
        c = '0' + (char) ((x >> i) & 0xF);
      dest->write_char(c);
    }
  }

  discard_tValue(v);
  return spec.after;
}

// Printing routine for %o and %O formats
const char* print_octal(tFieldDesc& spec, ArgList* args, Target* dest)
{
  if (args->isDone())
  {
    dest->write_char('%');
    return spec.str;  // there is no argument, so do not treat as format
  }

  tValue v;
  fill_tValue(v, args, dest);

  /* There are 2 cases:
   *  %o  => width determined by type size, all bits shown
   *  %no => minimum width is n, left-padded with zeros
   */
  unsigned int field_width = maxWidth(v.bits, v.isSigned, 8);
  if (v.usingWideVal)
  {
    pad(spec.width, field_width, field_width, '0', dest);
    if (spec.width == 0)
      v.data.wideVal->print_octal(dest, 0);
    else
      v.data.wideVal->print_octal(dest, field_width);
  }
  else if (v.bits == 1)
  {
    unsigned int value_width = numDigits(v,8);
    pad(spec.width, field_width, value_width, '0', dest);
    dest->write_char(v.data.bitVal ? '1' : '0');
  }
  else
  {
    unsigned int value_width = numDigits(v,8);
    pad(spec.width, field_width, value_width, '0', dest);
    unsigned long long x = v.data.uVal;
    if (v.bits < 64)
      x &= (1llu << v.bits) - 1;
    char c;
    for (int i = (value_width - 1)*3; i >= 0; i -= 3)
    {
      c = '0' + (char) ((x >> i) & 0x7);
      dest->write_char(c);
    }
  }

  discard_tValue(v);
  return spec.after;
}

// Printing routine for %b and %B formats
const char* print_binary(tFieldDesc& spec, ArgList* args, Target* dest)
{
  if (args->isDone())
  {
    dest->write_char('%');
    return spec.str;  // there is no argument, so do not treat as format
  }

  tValue v;
  fill_tValue(v, args, dest);

  /* There are 2 cases:
   *  %b  => width determined by type size, all bits shown
   *  %nb => minimum width is n, left-padded with zeros
   */
  unsigned int field_width = maxWidth(v.bits, false, 2);
  if (v.usingWideVal)
  {
    pad(spec.width, field_width, field_width, '0', dest);
    if (spec.width == 0)
      v.data.wideVal->print_binary(dest, 0);
    else
      v.data.wideVal->print_binary(dest, field_width);
  }
  else
  {
    unsigned int value_width = numDigits(v,2);
    pad(spec.width, field_width, value_width, '0', dest);
    char buf[value_width+1];
    buf[value_width] = '\0';
    for (unsigned int bit=0, idx=value_width-1; bit < value_width; ++bit,--idx)
      buf[idx] = ((v.data.uVal & (1llu << bit)) != 0llu) ? '1' : '0';
    dest->write_data(buf,value_width,sizeof(char));
  }

  discard_tValue(v);
  return spec.after;
}

// Printing routine for %c format
const char* print_char(tFieldDesc& spec, ArgList* args, Target* dest)
{
  if (args->isDone())
  {
    dest->write_char('%');
    return spec.str;  // there is no argument, so do not treat as format
  }

  char c = args->getUChar();
  pad(spec.width, 1, 1, ' ', dest);
  dest->write_char(c);
  return spec.after;
}

// Printing routine for %s format
const char* print_string(tFieldDesc& spec, ArgList* args, Target* dest)
{
  if (args->isDone())
  {
    dest->write_char('%');
    return spec.str;  // there is no argument, so do not treat as format
  }

  // try to get string argument and determine length
  const char* str = NULL;
  unsigned int str_len = args->argSize() / 8;
  const std::string* alloced_str = NULL;
  if (args->isString())
    str = args->getString();
  else if (args->isCxxString())
  {
    const std::string* s = args->getCxxString();
    str = s->c_str();
    str_len = s->length();
  }
  else
  {
    alloced_str = convert_to_string(args, dest);
    str = alloced_str->c_str();
    str_len = alloced_str->length();
  }

  unsigned int value_width = str_len;
  pad(spec.width, value_width, value_width, ' ', dest);

  // print the string characters
  for (unsigned int i = 0; i < str_len; ++i)
    dest->write_char(str[i]);

  if (alloced_str)
    delete alloced_str;

  return spec.after;
}

// Printing routine for %t format
const char* print_time(tFieldDesc& spec, ArgList* args, Target* dest)
{
  // print as decimal, but with a min field width appropriate for a
  // 64 bit value, regardless of the input size (if not specified).
  if (spec.width == -1)
    spec.width = 20;
  return print_decimal(spec, args, dest);
}

// makes a string copy of the format in tFieldDesc
char* copy_format(tFieldDesc& spec) {

  // start with space for % and null
  size_t format_size = 2;
  const char* cur = spec.str;
  while (cur != spec.after) {
    cur++;
    format_size++;
  }

  char* format_copy = (char*)malloc(format_size);
  format_copy[0] = '%';
  char* copy_start = format_copy+1;
  strncpy(copy_start, spec.str, format_size - 2);
  format_copy[format_size - 1] = '\0';

  return(format_copy);
}

// Printing routine for real number formats
// We re-use printf's floating-point printing
const char* print_real(tFieldDesc& spec, ArgList* args, Target* dest)
{

  char* format_copy = copy_format(spec);

  double v; // value to print

  if (args->isDouble()) {
    v = args->getDouble();
  }
  else {
    // non-real where real expected
    dest->add_error("expected real argument, found non-real argument\n");
    tValue tv;
    fill_tValue(tv, args, dest);
    v = tValueToDouble(tv);
    discard_tValue(tv);
  }

  char* output_string = NULL;
  if (asprintf(&output_string, format_copy, v) != -1) {
    size_t idx = 0;
    while (output_string[idx] != '\0') {
      dest->write_char(output_string[idx]);
      idx++;
    }
    free(output_string);
  }
  else {
    char* error_string = NULL;
    if (asprintf(&error_string, "printing real number with format %s failed\n", format_copy) != -1) {
      dest->add_error(error_string);
      free(error_string);
    }
    else {
      // if this fails we're completely hosed, so give up
    }
  }

  free(format_copy);
  return spec.after;

}


// Dispatcher which parses field specifier and calls mode-specific fns
const char* handle_format(const char* str, Module* location, ArgList* args,
                          Target* dest)
{
  tFieldDesc spec;
  spec.mode = '\0';
  spec.width = -1;
  spec.precision = -1;
  spec.str = str;
  spec.after = NULL;

  const char* cptr = str;

  // parse width specifier
  while ((*cptr != '\0') && isDigit(*cptr))
  {
    if (spec.width < 0)
      spec.width = fromDigit(*cptr);
    else
      spec.width = spec.width * 10 + fromDigit(*cptr);
    ++cptr;
  }

  // parse precision
  if (*cptr == '.')
  {
    ++cptr;
    while ((*cptr != '\0') && isDigit(*cptr))
    {
      if (spec.precision < 0)
        spec.precision = fromDigit(*cptr);
      else
        spec.precision = spec.width * 10 + fromDigit(*cptr);
      ++cptr;
    }
  }

  // get mode
  spec.mode = *cptr;
  ++cptr;

  // handle the various format modes
  spec.after = cptr;
  switch (spec.mode)
  {
    case '%':
    {
      dest->write_char('%');
      return spec.after;
    }

    case 'b':
    case 'B':
    case 'u': // %u and %z are same as %b since we are only 2-state
    case 'U':
    case 'z':
    case 'Z': return print_binary(spec,args,dest);
    case 'c':
    case 'C': return print_char(spec,args,dest);
    case 'd':
    case 'D': return print_decimal(spec,args,dest);
    case 'h':
    case 'H':
    case 'x':
    case 'X': return print_hex(spec,args,dest);
    case 'm':
    case 'M': { location->write_name(dest); return spec.after; }
    case 'o':
    case 'O': return print_octal(spec,args,dest);
    case 's':
    case 'S': return print_string(spec,args,dest);
    case 't':
    case 'T': return print_time(spec,args,dest);
    case 'f':
    case 'F':
    case 'g':
    case 'G':
    case 'e':
    case 'E': return print_real(spec,args,dest);
    default: // not a supported format code
    {
      dest->write_char('%');
      return spec.str;
    }
  }
}

// This is a generic argument/format string processing routine used
// by many varieties of display and write system tasks.
void format(const char* default_format, Module* location, ArgList* args,
            Target* dest, bool restricted)
{
  unsigned int arg_num = 0;
  while (!args->isDone())
  {
    ++arg_num;
    bool is_str = args->isString() || args->isCxxString();
    bool is_fmt = (!restricted && is_str) || (restricted && (arg_num == 1));
    if (is_fmt)
    {
      // use this argument as a format string

      // Iterate over the string looking for escape and format
      // codes.  When one is found, print any prior characters
      // which haven't been printed and then process the special
      // character, possibly consuming arguments.
      const char* cptr = NULL;
      const std::string* alloced_str = NULL;
      if (args->isString())
      {
        cptr = args->getString();
      }
      else if (args->isCxxString())
      {
        const std::string* s = args->getCxxString();
        cptr = s->c_str();
      }
      else
      {
        // The value is not a string but must be interpreted as one
        alloced_str = convert_to_string(args, dest);
        cptr = alloced_str->c_str();
      }

      unsigned int len = 0;
      while (cptr && cptr[len] != '\0')
      {
        if (cptr[len] == '\\')
        {
          if (len > 0) dest->write_data(cptr, sizeof(char), len);
          cptr = handle_escape((cptr + len + 1), dest);
          len = 0;
        } else if (cptr[len] == '%') {
          if (len > 0) dest->write_data(cptr, sizeof(char), len);
          cptr = handle_format((cptr + len + 1), location, args, dest);
          len = 0;
        } else {
          // ordinary character, just record that we have another
          // character "in the buffer".
          ++len;
        }
      }

      // write any trailing characters
      if (len > 0) dest->write_data(cptr, sizeof(char), len);

      if (alloced_str)
        delete alloced_str;
    } else if (is_str) {
      // display the argument as a string literal
      handle_format("s", location, args, dest);
    } else {
      // display the argument in default format
      handle_format(default_format, location, args, dest);
    }
  }
}

/*
 * These are the actual system task definitions.
 */


// $display
void dollar_display(tSimStateHdl simHdl,
		    Module* location, const char* size_str ...)
{
  va_list ap;
  va_start(ap,size_str);

  if (!bk_finished(simHdl))
  {
    ArgList args(size_str, &ap);
    FileTarget dest(stdout);
    format("d", location, &args, &dest, false);
    dest.write_char('\n');
    dest.handle_errors();
  }

  va_end(ap);
}

// $display with no arguments (just prints a newline)
void dollar_display(tSimStateHdl simHdl, Module* /* unused */)
{
  if (!bk_finished(simHdl))
  {
    FileTarget dest(stdout);
    dest.write_char('\n');
    dest.handle_errors();
  }
}

// $displayb
void dollar_displayb(tSimStateHdl simHdl,
		     Module* location, const char* size_str ...)
{
  va_list ap;
  va_start(ap,size_str);

  if (!bk_finished(simHdl))
  {
    ArgList args(size_str, &ap);
    FileTarget dest(stdout);
    format("b", location, &args, &dest, false);
    dest.write_char('\n');
    dest.handle_errors();
  }

  va_end(ap);
}

// $displayb with no arguments (just prints a newline)
void dollar_displayb(tSimStateHdl simHdl, Module* /* unused */)
{
  if (!bk_finished(simHdl))
  {
    FileTarget dest(stdout);
    dest.write_char('\n');
    dest.handle_errors();
  }
}

// $displayo
void dollar_displayo(tSimStateHdl simHdl,
		     Module* location, const char* size_str ...)
{
  va_list ap;
  va_start(ap,size_str);

  if (!bk_finished(simHdl))
  {
    ArgList args(size_str, &ap);
    FileTarget dest(stdout);
    format("o", location, &args, &dest, false);
    dest.write_char('\n');
    dest.handle_errors();
  }

  va_end(ap);
}

// $displayo with no arguments (just prints a newline)
void dollar_displayo(tSimStateHdl simHdl, Module* /* unused */)
{
  if (!bk_finished(simHdl))
  {
    FileTarget dest(stdout);
    dest.write_char('\n');
    dest.handle_errors();
  }
}

// $displayh
void dollar_displayh(tSimStateHdl simHdl,
		     Module* location, const char* size_str ...)
{
  va_list ap;
  va_start(ap,size_str);

  if (!bk_finished(simHdl))
  {
    ArgList args(size_str, &ap);
    FileTarget dest(stdout);
    format("h", location, &args, &dest, false);
    dest.write_char('\n');
    dest.handle_errors();
  }

  va_end(ap);
}

// $displayh with no arguments (just prints a newline)
void dollar_displayh(tSimStateHdl simHdl, Module* /* unused */)
{
  if (!bk_finished(simHdl))
  {
    FileTarget dest(stdout);
    dest.write_char('\n');
    dest.handle_errors();
  }
}

// $write
void dollar_write(tSimStateHdl simHdl,
		  Module* location, const char* size_str ...)
{
  va_list ap;
  va_start(ap,size_str);

  if (!bk_finished(simHdl))
  {
    ArgList args(size_str, &ap);
    FileTarget dest(stdout);
    format("d", location, &args, &dest, false);
    dest.handle_errors();
  }

  va_end(ap);
}

// $write with no arguments (has no effect)
void dollar_write(tSimStateHdl /* unused */, Module* /* unused */)
{
  return;
}

// $writeb
void dollar_writeb(tSimStateHdl simHdl,
		   Module* location, const char* size_str ...)
{
  va_list ap;
  va_start(ap,size_str);

  if (!bk_finished(simHdl))
  {
    ArgList args(size_str, &ap);
    FileTarget dest(stdout);
    format("b", location, &args, &dest, false);
    dest.handle_errors();
  }

  va_end(ap);
}

// $writeb with no arguments (has no effect)
void dollar_writeb(tSimStateHdl /* unused */, Module* /* unused */)
{
  return;
}

// $writeo
void dollar_writeo(tSimStateHdl simHdl,
		   Module* location, const char* size_str ...)
{
  va_list ap;
  va_start(ap,size_str);

  if (!bk_finished(simHdl))
  {
    ArgList args(size_str, &ap);
    FileTarget dest(stdout);
    format("o", location, &args, &dest, false);
    dest.handle_errors();
  }

  va_end(ap);
}

// $writeo with no arguments (has no effect)
void dollar_writeo(tSimStateHdl /* unused */, Module* /* unused */)
{
  return;
}

// $writeh
void dollar_writeh(tSimStateHdl simHdl,
		   Module* location, const char* size_str ...)
{
  va_list ap;
  va_start(ap,size_str);

  if (!bk_finished(simHdl))
  {
    ArgList args(size_str, &ap);
    FileTarget dest(stdout);
    format("h", location, &args, &dest, false);
    dest.handle_errors();
  }

  va_end(ap);
}

// $writeh with no arguments (has no effect)
void dollar_writeh(tSimStateHdl /* unused */, Module* /* unused */)
{
  return;
}

// Copy a formatted string from the destination buffer into the
// target memory with proper alignment, left-padded zeros,
// no terminator, etc.
void copy_back(void* target, unsigned int bits, BufferTarget* dest)
{
  unsigned int n = dest->length();
  const char* s = dest->str();

  if (bits <= 8)
  {
    *((tUInt8*) target) = *s;
  }
  else if (bits <= 32)
  {
    tUInt32 x = 0;
    while (n--)
      x |= (*(s++) << (8*n));
    *((tUInt32*) target) = x;
  }
  else if (bits <= 64)
  {
    tUInt64 x = 0llu;
    while (n--)
      x |= ((tUInt64)(*(s++)) << (8*n));
    *((tUInt64*) target) = x;
  }
  else
  {
    WideData* x = (WideData*) target;
    if (bits > (8*n))
      x->clear(8*n);
    while (n--)
      x->setByte(n,*(s++));
  }
}

// $swrite
void dollar_swriteAV(tSimStateHdl simHdl,
		     Module* location, const char* size_str ...)
{
  va_list ap;
  va_start(ap,size_str);

  if (!bk_finished(simHdl))
  {
    ArgList args(size_str, &ap);

    // first argument is destination
    if (args.isDone() || !args.isPointer())
    {
      // this is an error
    }
    else
    {
      unsigned int bits = args.argSize();
      void* target = args.getPointer();
      BufferTarget dest((bits + 7) / 8);

      // remaining arguments are for format
      format("d", location, &args, &dest, false);

      copy_back(target, bits, &dest);
      dest.handle_errors();
    }
  }

  va_end(ap);
}

// $swriteb
void dollar_swritebAV(tSimStateHdl simHdl,
		      Module* location, const char* size_str ...)
{
  va_list ap;
  va_start(ap,size_str);

  if (!bk_finished(simHdl))
  {
    ArgList args(size_str, &ap);

    // first argument is destination
    if (args.isDone() || !args.isPointer())
    {
      // this is an error
    }
    else
    {
      unsigned int bits = args.argSize();
      void* target = args.getPointer();
      BufferTarget dest((bits + 7) / 8);

      // remaining arguments are for format
      format("b", location, &args, &dest, false);

      copy_back(target, bits, &dest);
      dest.handle_errors();
    }
  }

  va_end(ap);
}

// $swriteo
void dollar_swriteoAV(tSimStateHdl simHdl,
		      Module* location, const char* size_str ...)
{
  va_list ap;
  va_start(ap,size_str);

  if (!bk_finished(simHdl))
  {
    ArgList args(size_str, &ap);

    // first argument is destination
    if (args.isDone() || !args.isPointer())
    {
      // this is an error
    }
    else
    {
      unsigned int bits = args.argSize();
      void* target = args.getPointer();
      BufferTarget dest((bits + 7) / 8);

      // remaining arguments are for format
      format("o", location, &args, &dest, false);

      copy_back(target, bits, &dest);
      dest.handle_errors();
    }
  }

  va_end(ap);
}

// $swriteh
void dollar_swritehAV(tSimStateHdl simHdl,
		      Module* location, const char* size_str ...)
{
  va_list ap;
  va_start(ap,size_str);

  if (!bk_finished(simHdl))
  {
    ArgList args(size_str, &ap);

    // first argument is destination
    if (args.isDone() || !args.isPointer())
    {
      // this is an error
    }
    else
    {
      unsigned int bits = args.argSize();
      void* target = args.getPointer();
      BufferTarget dest((bits + 7) / 8);

      // remaining arguments are for format
      format("h", location, &args, &dest, false);

      copy_back(target, bits, &dest);
      dest.handle_errors();
    }
  }

  va_end(ap);
}


// $sformat
void dollar_sformatAV(tSimStateHdl simHdl,
		      Module* location, const char* size_str ...)
{
  va_list ap;
  va_start(ap,size_str);

  if (!bk_finished(simHdl))
  {
    ArgList args(size_str, &ap);

    // first argument is destination
    if (args.isDone() || !args.isPointer())
    {
      // this is an error
    }
    else
    {
      unsigned int bits = args.argSize();
      void* target = args.getPointer();
      BufferTarget dest((bits + 7) / 8);

      // remaining arguments are for format
      format("d", location, &args, &dest, true);

      copy_back(target, bits, &dest);
      dest.handle_errors();
    }
  }

  va_end(ap);
}

// $info
void dollar_info(tSimStateHdl simHdl,
		 Module* location, const char* size_str, ...)
{
  va_list ap;
  va_start(ap,size_str);

  if (!bk_finished(simHdl))
  {
    ArgList args(size_str, &ap);
    FileTarget dest(stdout);
    format("d", location, &args, &dest, false);
    dest.write_char('\n');
    dest.handle_errors();
  }

  va_end(ap);
}

// $info with no arguments
void dollar_info(tSimStateHdl simHdl, Module* location)
{
  dollar_display(simHdl, location);
}

// $warning
void dollar_warning(tSimStateHdl simHdl,
		    Module* location, const char* size_str, ...)
{
  va_list ap;
  va_start(ap,size_str);

  if (!bk_finished(simHdl))
  {
    ArgList args(size_str, &ap);
    FileTarget dest(stdout);
    format("d", location, &args, &dest, false);
    dest.write_char('\n');
    dest.handle_errors();
  }

  va_end(ap);
}

// $warning with no arguments
void dollar_warning(tSimStateHdl simHdl, Module* location)
{
  dollar_display(simHdl, location);
}

// $error
void dollar_error(tSimStateHdl simHdl,
		  Module* location, const char* size_str, ...)
{
  va_list ap;
  va_start(ap,size_str);

  if (!bk_finished(simHdl))
  {
    ArgList args(size_str, &ap);
    FileTarget dest(stdout);
    format("d", location, &args, &dest, false);
    dest.write_char('\n');
    dest.handle_errors();
  }

  va_end(ap);
}

// $error with no arguments
void dollar_error(tSimStateHdl simHdl, Module* location)
{
  dollar_display(simHdl, location);
}

// $fatal
void dollar_fatal(tSimStateHdl simHdl,
		  Module* location, const char* size_str, ...)
{
  va_list ap;
  va_start(ap,size_str);

  if (!bk_finished(simHdl))
  {
    ArgList args(size_str, &ap);
    FileTarget dest(stdout);

    // first argument is the exit status
    tValue v;
    fill_tValue(v, &args, &dest);

    int status = 0;
    if (v.usingWideVal)
      status = v.data.wideVal->extract32(31,0);
    else if (v.bits == 1)
      status = v.data.bitVal ? 1 : 0;
    else
      status = v.data.sVal;

    // Display message and then finish simulation
    format("d", location, &args, &dest, false);
    dest.write_char('\n');
    dest.handle_errors();
    bk_finish_now(simHdl, status);

    discard_tValue(v);
  }

  va_end(ap);
}

// $fatal must always have an argument (the status)

/*
 * Utility class for dealing with file-related system tasks.
 */

// Verilog has 2 concepts of file pointer: file handle, similar to C and mcd,
// multi-channel descriptors, which can represent multiple files.
// Here we define 2 containers for holding these files, and some functions
// to access them.
class VLFiles {
private:
  std::vector<FILE*> mcdfiles ;
  std::vector<FILE*> fdfiles ;

  const static tUInt32 fdbase = 0x80000000 ;
public:
  VLFiles() {
    // preopend and registered files.
    registerFile( true, stdout ) ;
    registerFile( false, stdin ) ;
    registerFile( false, stdout ) ;
    registerFile( false, stderr ) ;
  }
  ~VLFiles() {
    // We can close any files, but the system does that for us.
  }

  // After a call to fopen, store the FILE pointer
  tUInt32 registerFile ( bool mcd, FILE* file )
  {
    tUInt32 key = 0 ;
    if ( file == 0 ) {
      key = 0 ;
    } else if ( mcd && (mcdfiles.size() < 31 )) {
      mcdfiles.push_back( file );
      key = 0x01 << (mcdfiles.size() - 1)  ;
    } else if ( mcd ) {
      tUInt32 size = mcdfiles.size() ;
      for( tUInt32 i = 0 ; i <  size ; i = i + 1 ) {
        if ( mcdfiles[i] == 0 ){
          mcdfiles[i] = file ;
          key = 0x01 << i;
          break ;
        }
      }
    } else {
      fdfiles.push_back( file ) ;
      key = fdbase + (fdfiles.size () - 1);
    }
    return key ;
  }

  // MCD can cause multiple files to be specified.
  void findFiles( std::vector<FILE*> & result, tUInt32 key )
  {
    result.clear() ;
    if ( key >= fdbase ) {     // fd type
      if ( fdfiles[key - fdbase] != 0 )
        result.push_back( fdfiles[key - fdbase] ) ;
      // XXX check for valid index done by stl?
    } else { // mcd type
      tUInt32 position = 0  ;
      while (key != 0 ) {
        if ( (key & 0x01) && mcdfiles[position] ) {
          result.push_back( mcdfiles[position] ) ;
        }
        key = key >> 1 ;
        position = position + 1 ;
      }

    }
  }
  void findAllFiles( std::vector<FILE*> & result )
  {
    result.clear() ;
    result.insert( result.end(), fdfiles.begin(), fdfiles.end() ) ;
    result.insert( result.end(), mcdfiles.begin(), mcdfiles.end() ) ;
  }
  void closeFiles( tUInt32 key )
  {
    // Don't close stdin, stdout or stderr
    if ( key > 0x80000002 ) {     // fd type
      if ( fdfiles[key - fdbase] != 0 )
        {
          fclose( fdfiles[key - fdbase] ) ;
          fdfiles[key - fdbase] = 0 ;
        }
      // XXX check for valid index done by stl?
    } else if ( key < 0x8000000 ) { // mcd type
      tUInt32 position = 1  ;
      key = key >> 1 ;          // remove stdout
      while (key != 0 ) {
        if ( (key & 0x01) && mcdfiles[position] )
          {
            fclose( mcdfiles[position] ) ;
            mcdfiles[position] = 0 ;
          }
        key = key >> 1 ;
        position = position + 1 ;
      }
    }
  }

  FILE* getFD( tUInt32 key )
  {
    FILE *res =  0 ;
      if (( key >= fdbase ) && (fdfiles[key - fdbase] != 0 ))  {
        res = fdfiles[key - fdbase]  ;
      }
      return res ;
  }

} ; // end class

// Now create a global VLFiles
static VLFiles vlfile ;

/*
 * These are the "file" based system tasks
 */

// $fopen( filename,mode ) ;
tUInt32 dollar_fopen(const char* /*unused*/, const std::string* filename,
                                             const std::string* mode)
{
  FILE* nowopened = fopen(filename->c_str(), mode->c_str());
  tUInt32 key = vlfile.registerFile(false, nowopened);
  return key ;
}

// $fopen ( filename )
// MCD file type
tUInt32 dollar_fopen(const char* /*unused*/ , const std::string* filename)
{
  FILE* nowopened = fopen(filename->c_str(), "w");
  tUInt32 key = vlfile.registerFile(true, nowopened);
  return key ;
}

// $fclose(filehandle)
void dollar_fclose(const char* /*unused*/, tUInt32 filehandle)
{
  vlfile.closeFiles( filehandle ) ;
}

// $fflush( filehandle )
void dollar_fflush(const char* /*unused*/, tUInt32 filehandle)
{
  std::vector<FILE*> files ;
  vlfile.findFiles( files, filehandle ) ;
  for ( unsigned int i = 0 ; i < files.size(); i ++ )
    fflush( files[i] );
}


// $fflush()
void dollar_fflush()
{
  std::vector<FILE*> files ;
  vlfile.findAllFiles(files) ;
  for (unsigned int i = 0 ; i < files.size(); i ++)
    fflush(files[i]);
}


// $fdisplay
void dollar_fdisplay(tSimStateHdl simHdl,
		     Module* location, const char* size_str ...)
{
  if (!bk_finished(simHdl))
  {
    va_list ap;
    va_start(ap,size_str);
    ArgList args(size_str, &ap);

    std::vector<FILE*> files ;
    tUInt32 filehandle = args.getUInt() ;

    va_end(ap) ;

    vlfile.findFiles( files, filehandle ) ;

    for( unsigned int i = 0 ; i < files.size() ; i ++ )
    {
      // Reset the arg and continue
      va_start( ap, size_str) ;
      ArgList * local_args = new ArgList(size_str, &ap);
      local_args->getUInt() ;

      FileTarget dest(files[i]);
      format("d", location, local_args, &dest, false);
      dest.write_char('\n');
      dest.handle_errors();

      delete local_args ;
      va_end(ap);
    }
  }
}


// $fdisplayb
void dollar_fdisplayb(tSimStateHdl simHdl,
		      Module* location, const char* size_str ...)
{
  if (!bk_finished(simHdl))
  {
    va_list ap;
    va_start(ap,size_str);
    ArgList args(size_str, &ap);

    std::vector<FILE*> files ;
    tUInt32 filehandle = args.getUInt() ;

    va_end(ap) ;

    vlfile.findFiles( files, filehandle ) ;

    for( unsigned int i = 0 ; i < files.size() ; i ++ )
    {
      // Reset the arg and continue
      va_start( ap, size_str) ;
      ArgList * local_args = new ArgList(size_str, &ap);
      local_args->getUInt() ;

      FileTarget dest(files[i]);
      format("b", location, local_args, &dest, false);
      dest.write_char('\n');
      dest.handle_errors();

      delete local_args ;
      va_end(ap);
    }
  }
}


// $fdisplayo
void dollar_fdisplayo(tSimStateHdl simHdl,
		      Module* location, const char* size_str ...)
{
  if (!bk_finished(simHdl))
  {
    va_list ap;
    va_start(ap,size_str);
    ArgList args(size_str, &ap);

    std::vector<FILE*> files ;
    tUInt32 filehandle = args.getUInt() ;

    va_end(ap) ;

    vlfile.findFiles( files, filehandle ) ;

    for( unsigned int i = 0 ; i < files.size() ; i ++ )
    {
      // Reset the arg and continue
      va_start( ap, size_str) ;
      ArgList * local_args = new ArgList(size_str, &ap);
      local_args->getUInt() ;

      FileTarget dest(files[i]);
      format("o", location, local_args, &dest, false);
      dest.write_char('\n');
      dest.handle_errors();

      delete local_args ;
      va_end(ap);
    }
  }
}

// $fdisplayh
void dollar_fdisplayh(tSimStateHdl simHdl,
		      Module* location, const char* size_str ...)
{
  if (!bk_finished(simHdl))
  {
    va_list ap;
    va_start(ap,size_str);
    ArgList args(size_str, &ap);

    std::vector<FILE*> files ;
    tUInt32 filehandle = args.getUInt() ;

    va_end(ap) ;

    vlfile.findFiles( files, filehandle ) ;

    for( unsigned int i = 0 ; i < files.size() ; i ++ )
    {
      // Reset the arg and continue
      va_start( ap, size_str) ;
      ArgList * local_args = new ArgList(size_str, &ap);
      local_args->getUInt() ;

      FileTarget dest(files[i]);
      format("h", location, local_args, &dest, false);
      dest.write_char('\n');
      dest.handle_errors();

      delete local_args ;
      va_end(ap);
    }
  }
}

// $fwrite
void dollar_fwrite(tSimStateHdl simHdl,
		   Module* location, /*tUInt32 filehandle, */ const char* size_str ...)
{
  if (!bk_finished(simHdl))
  {
    va_list ap;
    va_start(ap,size_str);
    ArgList args(size_str, &ap);

    std::vector<FILE*> files ;
    tUInt32 filehandle = args.getUInt() ;

    va_end(ap) ;

    vlfile.findFiles( files, filehandle ) ;

    for( unsigned int i = 0 ; i < files.size() ; i ++ )
    {
      // Reset the arg and continue
      va_start( ap, size_str) ;
      ArgList * local_args = new ArgList(size_str, &ap);
      local_args->getUInt() ;

      FileTarget dest(files[i]);
      format("d", location, local_args, &dest, false);
      dest.handle_errors();

      delete local_args ;
      va_end(ap);
    }
  }
}

// $fwriteb
void dollar_fwriteb(tSimStateHdl simHdl,
		    Module* location, const char* size_str ...)
{
  if (!bk_finished(simHdl))
  {
    va_list ap;
    va_start(ap,size_str);
    ArgList args(size_str, &ap);

    std::vector<FILE*> files ;
    tUInt32 filehandle = args.getUInt() ;

    va_end(ap) ;

    vlfile.findFiles( files, filehandle ) ;

    for( unsigned int i = 0 ; i < files.size() ; i ++ )
    {
      // Reset the arg and continue
      va_start( ap, size_str) ;
      ArgList * local_args = new ArgList(size_str, &ap);
      local_args->getUInt() ;

      FileTarget dest(files[i]);
      format("b", location, local_args, &dest, false);
      dest.handle_errors();

      delete local_args ;
      va_end(ap);
    }
  }
}

// $fwriteo
void dollar_fwriteo(tSimStateHdl simHdl,
		    Module* location, const char* size_str ...)
{
  if (!bk_finished(simHdl))
  {
    va_list ap;
    va_start(ap,size_str);
    ArgList args(size_str, &ap);

    std::vector<FILE*> files ;
    tUInt32 filehandle = args.getUInt() ;

    va_end(ap) ;

    vlfile.findFiles( files, filehandle ) ;

    for( unsigned int i = 0 ; i < files.size() ; i ++ )
    {
      // Reset the arg and continue
      va_start( ap, size_str) ;
      ArgList * local_args = new ArgList(size_str, &ap);
      local_args->getUInt() ;

      FileTarget dest(files[i]);
      format("o", location, local_args, &dest, false);
      dest.handle_errors();

      delete local_args ;
      va_end(ap);
    }
  }
}

// $fwriteh
void dollar_fwriteh(tSimStateHdl simHdl,
		    Module* location, const char* size_str ...)
{
  if (!bk_finished(simHdl))
  {
    va_list ap;
    va_start(ap,size_str);
    ArgList args(size_str, &ap);

    std::vector<FILE*> files ;
    tUInt32 filehandle = args.getUInt() ;

    va_end(ap) ;

    vlfile.findFiles( files, filehandle ) ;

    for( unsigned int i = 0 ; i < files.size() ; i ++ )
    {
      // Reset the arg and continue
      va_start( ap, size_str) ;
      ArgList * local_args = new ArgList(size_str, &ap);
      local_args->getUInt() ;

      FileTarget dest(files[i]);
      format("h", location, local_args, &dest, false);
      dest.handle_errors();

      delete local_args ;
      va_end(ap);
    }
  }
}

tSInt32 dollar_fgetc ( const char* /*Unused*/, const tUInt32 filehandle )
{
  FILE * infile = vlfile.getFD( filehandle ) ;
  int res = -1 ;
  if ( infile )
    res = fgetc( infile ) ;

  return res ;
}

// $ungetc( char, file )
tSInt32 dollar_ungetc(  const char* size_str, const char back, const tUInt32 filehandle )
{
  FILE * infile = vlfile.getFD( filehandle ) ;
  int res = -1 ;
  if ( infile )
    res = ungetc( back, infile ) ;

  return res ;
}
