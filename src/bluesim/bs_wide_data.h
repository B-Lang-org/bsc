#ifndef __BS_WIDE_DATA_H__
#define __BS_WIDE_DATA_H__

/* NOTE: The WideData class is a C++-only feature, used internally
 * but not part of the external C API.
 *
 * C code uses arrays of unsigned ints and must account for
 * bit widths in an ad-hoc manner.
 */
#include "bs_target.h"
#include "bs_mem_defines.h"

#define NUM_WORDS(b) (unsigned int)((b+WORD_SIZE-1)/WORD_SIZE)

// forward declarations
class WideData;
extern void init_val(WideData& v, unsigned int width);
extern void init_val(unsigned long long /* unused */,
                     unsigned int /* unused */);
extern void dump_val(unsigned long long v, unsigned int width);
extern void dump_val(const WideData& v, unsigned int /* unused */);
extern void write_undet(bool* pValue, unsigned int width);
extern void write_undet(unsigned char* pValue, unsigned int width);
extern void write_undet(unsigned int* pValue, unsigned int width);
extern void write_undet(unsigned long long* pValue, unsigned int width);
extern void write_undet(WideData* pValue, unsigned int /* unused */);
extern void mask_high_bits(bool* pValue, unsigned int width);
extern void mask_high_bits(unsigned char* pValue, unsigned int width);
extern void mask_high_bits(unsigned int* pValue, unsigned int width);
extern void mask_high_bits(unsigned long long* pValue, unsigned int width);
extern void mask_high_bits(WideData* pValue, unsigned int /* unused */);
extern bool is_zero(unsigned char  v);
extern bool is_zero(unsigned int v);
extern bool is_zero(unsigned long long  v);
extern bool is_zero(const WideData& v);
extern bool is_bit_set(unsigned char v, unsigned int n);
extern bool is_bit_set(unsigned int v, unsigned int n);
extern bool is_bit_set(unsigned long long v, unsigned int n);
extern bool is_bit_set(const WideData& v, unsigned int n);
extern bool chunks_eq(unsigned char x, unsigned char y, unsigned int n, unsigned int width);
extern bool chunks_eq(unsigned int x, unsigned int y, unsigned int n, unsigned int width);
extern bool chunks_eq(unsigned long long x, unsigned long long y, unsigned int n, unsigned int width);
extern bool chunks_eq(const WideData& x, const WideData& y, unsigned int n, unsigned int width);
extern void xfer_chunk(unsigned char* pDest, unsigned char src, unsigned int n, unsigned int width);
extern void xfer_chunk(unsigned int* pDest, unsigned int src, unsigned int n, unsigned int width);
extern void xfer_chunk(unsigned long long* pDest, unsigned long long src, unsigned int n, unsigned int width);
extern void xfer_chunk(const WideData* pDest, const WideData& src, unsigned int n, unsigned int width);
extern WideData bs_wide_tmp(unsigned int width);

// The actual wide data implementation

class WideData
{
 private:
  unsigned int  nBits;
  unsigned int  nWords;

 // This is public only for the purpose of passing values to foreign C functions.
 // Please don't abuse it!
 public:
  unsigned int* data;

 public:
  // default constructor used when making arrays of WideData values.
  // The object is constructed with no data, use setSize() to allocate.
  WideData();

  // basic sized constructor -- initializes to 0xAAA...AAA if init is set
  explicit WideData(unsigned int bits, bool init = true);

  // special constructor used for literal values
  WideData(unsigned int bits, const unsigned int array[]);

  // special constructor for static-wide-data -- no initialization
  //  WideData(unsigned int * data, unsigned int bits);

  // special constructors used to promote non-wide values
  WideData(unsigned int bits, unsigned int value);
  WideData(unsigned int bits, unsigned long long value);

  // special constructor used to represent strings
  WideData(unsigned int bits, const char* str);

  // copy constructor
  WideData(const WideData& v);

  // copy assignment
  WideData& operator=(const WideData& v);

  // destructor
  ~WideData();

 public:
  void setSize(unsigned int width);
  unsigned int size() const { return nBits; }
  unsigned int numWords() const { return nWords; }
  unsigned int& operator[](unsigned int idx) const { return data[idx]; }
  unsigned char getByte(unsigned int byte_num) const;
  void setByte(unsigned int byte_num, unsigned char val);
  bool extract1(unsigned int idx) const;
  unsigned char extract8(unsigned int hi, unsigned int lo) const;
  unsigned int extract32(unsigned int hi, unsigned int lo) const;
  unsigned long long extract64(unsigned int hi, unsigned int lo) const;
  WideData extractWide(unsigned int hi, unsigned int lo) const;
  void wop_extractWide(unsigned int hi, unsigned int lo, WideData& result) const;
  void clear(unsigned int from = 0);
  void clear(unsigned int from, unsigned int to);
  void set(unsigned int from = 0);
  void set(unsigned int from, unsigned int to);
  void copy(const WideData& src);
  void copy(const WideData& src, unsigned int to);
  void write(unsigned int* buf, unsigned int size, unsigned int to);
  bool is_clear(unsigned int from = 0) const;
  bool is_clear(unsigned int from, unsigned int to) const;
  WideData& set_whole_word(unsigned int value, unsigned int word_idx);
  WideData& set_bits_in_word(unsigned char value, unsigned int word_idx, unsigned int offset, unsigned int nbits);
  WideData& set_bits_in_word(int value, unsigned int word_idx, unsigned int offset, unsigned int nbits);
  WideData& set_bits_in_word(unsigned int value, unsigned int word_idx, unsigned int offset, unsigned int nbits);
  WideData& build_concat(bool src, unsigned int loc, unsigned int nbits);
  WideData& build_concat(unsigned char src, unsigned int loc, unsigned int nbits);
  WideData& build_concat(int src, unsigned int loc, unsigned int nbits);
  WideData& build_concat(unsigned int src, unsigned int loc, unsigned int nbits);
  WideData& build_concat(unsigned long long src, unsigned int loc, unsigned int nbits);
  WideData& build_concat(const WideData& src, unsigned int loc, unsigned int nbits);
  unsigned int get_whole_word(unsigned int word_idx) const;
  unsigned char get_bits_in_word8(unsigned int word_idx, unsigned int offset, unsigned int nbits) const;
  unsigned int get_bits_in_word32(unsigned int word_idx, unsigned int offset, unsigned int nbits) const;

 public:
  void print_binary(Target* dest, unsigned int field_width=0) const;
  void print_hex(Target* dest, unsigned int field_width=0) const;
  void print_octal(Target* dest, unsigned int field_width=0) const;
  static unsigned int max_decimal_digits(unsigned int bits, bool is_signed);
  void print_decimal(Target* dest, unsigned int field_width, bool is_signed) const;

 public:
  friend void write_undet(WideData* pValue, unsigned int width);

  friend WideData operator&(const WideData&, const WideData&);
  friend WideData operator|(const WideData&, const WideData&);
  friend WideData operator^(const WideData&, const WideData&);
  friend WideData operator~(const WideData&);

  friend WideData operator>>(const WideData&, unsigned int);
  friend WideData operator<<(const WideData&, unsigned int);

  friend WideData operator-(const WideData&);

  friend WideData operator+(const WideData&, const WideData&);
  friend WideData operator-(const WideData&, const WideData&);
  friend WideData operator*(const WideData&, const WideData&);
  friend WideData operator/(const WideData&, const WideData&);
  friend WideData operator%(const WideData&, const WideData&);

  friend bool operator==(const WideData&, const WideData&);
  friend bool operator!=(const WideData&, const WideData&);
  friend bool operator<(const WideData&, const WideData&);
  friend bool operator>(const WideData&, const WideData&);
  friend bool operator<=(const WideData&, const WideData&);
  friend bool operator>=(const WideData&, const WideData&);
};

// inline-able class methods

inline WideData& WideData::set_whole_word(unsigned int value, unsigned int word_idx)
{
  data[word_idx] = value;
  return (*this);
}

inline WideData& WideData::set_bits_in_word(unsigned char value, unsigned int word_idx, unsigned int offset, unsigned int nbits)
{
  unsigned int mask = ((1 << nbits) - 1) << offset;
  data[word_idx] = (data[word_idx] & ~mask) | (((unsigned int)value << offset) & mask);
  return (*this);
}

inline WideData& WideData::set_bits_in_word(int value, unsigned int word_idx, unsigned int offset, unsigned int nbits)
{
  unsigned int mask = ((1 << nbits) - 1) << offset;
  data[word_idx] = (data[word_idx] & ~mask) | ((value << offset) & mask);
  return (*this);
}

inline WideData& WideData::set_bits_in_word(unsigned int value, unsigned int word_idx, unsigned int offset, unsigned int nbits)
{
  unsigned int mask = ((1 << nbits) - 1) << offset;
  data[word_idx] = (data[word_idx] & ~mask) | ((value << offset) & mask);
  return (*this);
}

inline unsigned int WideData::get_whole_word(unsigned int word_idx) const
{
  return data[word_idx];
}

inline unsigned char WideData::get_bits_in_word8(unsigned int word_idx, unsigned int offset, unsigned int nbits) const
{
  unsigned int mask = (1 << nbits) - 1;
  return (unsigned char)((data[word_idx] >> offset) & mask);
}

inline unsigned int WideData::get_bits_in_word32(unsigned int word_idx, unsigned int offset, unsigned int nbits) const
{
  unsigned int mask = (1 << nbits) - 1;
  return ((data[word_idx] >> offset) & mask);
}

// convenience typedef
typedef WideData tUWide;

// operators overloaded to work with WideData
WideData operator&(const WideData& v1, const WideData& v2);
WideData operator|(const WideData& v1, const WideData& v2);
WideData operator^(const WideData& v1, const WideData& v2);
WideData operator~(const WideData& v);

WideData operator>>(const WideData& value, unsigned int shift);
WideData operator<<(const WideData& value, unsigned int shift);

WideData operator-(const WideData& v);

WideData operator+(const WideData& v1, const WideData& v2);
WideData operator-(const WideData& v1, const WideData& v2);
WideData operator*(const WideData& v1, const WideData& v2);
WideData operator/(const WideData& v1, const WideData& v2);
WideData operator%(const WideData& v1, const WideData& v2);

bool operator==(const WideData& v1, const WideData& v2);
bool operator!=(const WideData& v1, const WideData& v2);
bool operator<(const WideData& v1, const WideData& v2);
bool operator>(const WideData& v1, const WideData& v2);
bool operator<=(const WideData& v1, const WideData& v2);
bool operator>=(const WideData& v1, const WideData& v2);

//operators for wide-data
void wop_and(const WideData& a, const WideData& b, WideData& c);// c = a & b
void wop_or(const WideData& a, const WideData& b, WideData& c); // c = a | b
void wop_xor(const WideData& a, const WideData& b, WideData& c);// c = a ^ b
void wop_inv(const WideData& a, WideData& c);                   // c = ~a
void wop_neg(const WideData& v, WideData& result);              // c = -a
void wop_srl(const WideData& a, unsigned int x, WideData& c);   // c = a >> x
void wop_sl(const WideData& a, unsigned int x, WideData& c);    // c = a << x
void wop_add(const WideData& a, const WideData& b, WideData& c);//c = a + b
void wop_sub(const WideData& a, const WideData& b, WideData& c);//c = a - b
void wop_mul(const WideData& a, const WideData& b, WideData& c);//c = a * b
void wop_quot(const WideData& a, const WideData& b, WideData& c);// c = a / b
void wop_rem(const WideData& a, const WideData& b, WideData& c);// c = a % b

//may-useless function calls
void wop_maskWide(unsigned int n, const WideData& val, WideData& result);

#endif /* __BS_WIDE_DATA_H__ */
