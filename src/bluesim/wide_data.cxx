#include <cstdlib>
#include <cstring>
#include <csignal>

#include "bs_wide_data.h"
#include "bs_mem_defines.h"
#include "mem_alloc.h"

#define uint unsigned int

/* static inline functions */

// Which word is this bit in?
static inline unsigned int word_idx(unsigned int bit)
{
  return (bit / WORD_SIZE);
}

// What offset within the word is the bit at?
static inline unsigned int word_offset(unsigned int bit)
{
  return (bit % WORD_SIZE);
}

// Get a pointer to the word containing this bit
static inline unsigned int* word_ptr(unsigned int* buf, unsigned int bit)
{
  return buf + (bit / WORD_SIZE);
}

static inline char* byte_ptr(unsigned int* buf, unsigned int bit)
{
  return ((char*) buf) + (bit / BYTE_SIZE);
}

// Produce an n-bit (out of 8) mask
static inline unsigned char mask8(unsigned int bits)
{
  return (bits == 8) ? ~0 : ((1 << bits) - 1);
}

// Produce an n-bit (out of 32) mask
static inline unsigned int mask(unsigned int bits)
{
  return (bits == 32) ? ~0 : ((1 << bits) - 1);
}

// Produce an n-bit (out of 64) mask
static inline unsigned long long mask64(unsigned int bits)
{
  return (bits == 64) ? ~0llu : ((1llu << bits) - 1llu);
}

// Copy "size" bits from src starting at position srcBit into
// dst starting at position dstBit.
// Note: src and dst must not overlap.
static void copy_bits(unsigned int* dst, unsigned int dstBit,
                      unsigned int* src, unsigned int srcBit,
                      unsigned int size)
{
  unsigned int soff = word_offset(srcBit);
  unsigned int doff = word_offset(dstBit);
  unsigned int* dptr = word_ptr(dst,dstBit);
  unsigned int* sptr = word_ptr(src,srcBit);
  unsigned int remaining = size;
  unsigned int msk;

  if (soff == doff)     // handle the aligned copy case
  {
    // copy first part-word
    msk = ~mask(soff);
    if (soff + size < WORD_SIZE)
    {
      msk &= mask(word_offset(srcBit + size));
      remaining = 0;
    }
    else
      remaining -= (WORD_SIZE - soff);

    *dptr = (*dptr & ~msk) | (*sptr & msk);
    ++dptr;
    ++sptr;

    // copy interior words
    if (remaining > 0)
    {
      unsigned int n = remaining / WORD_SIZE;
      remaining -= n * WORD_SIZE;
      while (n-- > 0)
        *(dptr++) = *(sptr++);
    }

    // copy final part-word
    if (remaining > 0)
    {
      msk = mask(remaining);
      *dptr = (*dptr & ~msk) | (*sptr & msk);
    }

    return;
  }
  else if (doff > soff)   // handle one non-aligned copy case
  {
    // abits is the number of upper bits of the source word which form
    // low bits of the next destination word.  It is > 0.
    unsigned int abits = doff - soff;

    // bbits is the number of lower bits of the source word which form
    // upper bits of the current destination word.
    unsigned int bbits = WORD_SIZE - abits;

    if (remaining <= WORD_SIZE - doff)
    {
      // all of the bits fit into the first destination word
      unsigned int tmp = *sptr << abits;
      msk = mask(remaining) << doff;
      *dptr = (*dptr & ~msk) | (tmp & msk);
      return;
    }
    else if (remaining <= WORD_SIZE - soff)
    {
      // the bits are in the first source word, but do not fill an
      // entire carry_over frame.
      unsigned int tmp = *sptr << abits;
      msk = mask(remaining) << doff;
      *dptr = (*dptr & ~msk) | (tmp & msk);
      ++dptr;
      remaining -= WORD_SIZE - doff;
      msk = mask(remaining);
      tmp = *sptr >> bbits;
      *dptr = (*dptr & ~msk) | (tmp & msk);
      return;
    }

    // copy the first part-word
    msk = mask(WORD_SIZE - doff) << doff;
    *dptr = (*dptr & ~msk) | ((*sptr << abits) & msk);
    unsigned int carry_over = *(sptr++) >> bbits;
    dptr++;
    remaining -= WORD_SIZE - doff;

    // copy intermediate words
    while (remaining >= WORD_SIZE)
    {
      *(dptr++) = carry_over | (*sptr << abits);
      carry_over = *(sptr++) >> bbits;
      remaining -= WORD_SIZE;
    }

    // copy the final part-word
    msk = mask(remaining);
    if (remaining > abits)
    {
      *dptr = (*dptr & ~msk) | ((carry_over | (*sptr << abits)) & msk);
    }
    else if (remaining > 0)
    {
      *dptr = (*dptr & ~msk) | (carry_over & msk);
    }

    return;
  }
  else if (doff < soff)   // handle the other non-aligned copy case
  {
    // abits is the number of lower bits of the next source word which form
    // upper bits of the current destination word.  It is > 0.
    unsigned int abits = soff - doff;

    // bbits is the number of upper bits of the source word which form
    // lower bits of the current destination word.
    unsigned int bbits = WORD_SIZE - abits;

    unsigned int tmp;
    if (remaining <= WORD_SIZE - soff)
    {
      // the bits are contained within the first source word
      tmp = (*sptr >> soff) << doff;
      msk = mask(remaining) << doff;
      *dptr = (*dptr & ~msk) | (tmp & msk);
      return;
    }
    else if (remaining <= WORD_SIZE - doff)
    {
      // the bits are split across two source words but fit into
      // one destination word.
      tmp = *(sptr++) >> abits;
      tmp |= (*sptr & mask(abits)) << bbits;
      msk = mask(remaining) << doff;
      *dptr = (*dptr & ~msk) | (tmp & msk);
      return;
    }

    // copy the first part-word
    msk = mask(doff);
    tmp = *(sptr++) >> abits;
    tmp |= (*sptr & mask(abits)) << bbits;
    *dptr = (*dptr & msk) | (tmp & ~msk);
    ++dptr;
    remaining -= WORD_SIZE - doff;

    msk = mask(abits);
    // copy intermediate words
    while (remaining >= WORD_SIZE)
    {
      tmp = *(sptr++) >> abits;
      *(dptr++) = tmp | ((*sptr & msk) << bbits);
      remaining -= WORD_SIZE;
    }

    // copy the final part-word
    msk = mask(remaining);
    if (remaining > bbits)
    {
      tmp = (*sptr++) >> abits;
      tmp |= (*sptr & mask(abits)) << bbits;
      *dptr = (*dptr & ~msk) | (tmp & msk);
    }
    else if (remaining > 0)
    {
      tmp = *sptr >> abits;
      *dptr = (*dptr & ~msk) | (tmp & msk);
    }

    return;
  }
}

// Copy "size" bits from src starting at position srcBit into
// dst starting at position 0. This is an optimized routine
// equivalent to copy_bits(dst, 0, src, srcBit, size).
// Note: src and dst must not overlap.
static inline void copy_bits_to_0(unsigned int* dst,
                                  unsigned int* src, unsigned int srcBit,
                                  unsigned int size)
{
  unsigned int remaining = size;
  const unsigned int word_bits = 8 * sizeof(unsigned int);
  unsigned int soff = word_offset(srcBit);
  unsigned int* dptr = word_ptr(dst,0);
  unsigned int* sptr = word_ptr(src,srcBit);
  unsigned int lo_sz = soff;
  unsigned int lo_mask = (1 << lo_sz) - 1;
  unsigned int hi_sz = word_bits - lo_sz;
  unsigned int hi_mask = (hi_sz == word_bits) ? (~0) : ((1 << hi_sz) - 1);
  unsigned int mask;

  while (1) {
    mask = (remaining < hi_sz) ? ((1 << remaining) - 1) : hi_mask;
    *dptr = (*dptr & ~mask) | ((*sptr >> lo_sz) & mask);
    if (remaining > hi_sz)
      remaining -= hi_sz;
    else
      return;
    ++sptr;
    if (lo_sz != 0) {
      mask = (remaining < lo_sz) ? ((1 << remaining) - 1) : lo_mask;
      *dptr = (*dptr & ~(mask << hi_sz)) | ((*sptr & mask) << hi_sz);
      if (remaining > lo_sz)
        remaining -= lo_sz;
      else
        return;
    }
    ++dptr;
  }
}

// Copy "size" bits from src starting at position 0 into
// dst starting at position dstBit. This is an optimized routine
// equivalent to copy_bits(dst, dstBit, src, 0, size).
// Note: src and dst must not overlap.
static inline void copy_bits_from_0(unsigned int* dst, unsigned int dstBit,
                                    unsigned int* src,
                                    unsigned int size)
{
  unsigned int remaining = size;
  const unsigned int word_bits = 8 * sizeof(unsigned int);
  unsigned int doff = word_offset(dstBit);
  unsigned int* dptr = word_ptr(dst,dstBit);
  unsigned int* sptr = word_ptr(src,0);
  unsigned int lo_sz = doff;
  unsigned int lo_mask = (1 << lo_sz) - 1;
  unsigned int hi_sz = word_bits - lo_sz;
  unsigned int hi_mask = (hi_sz == word_bits) ? (~0) : ((1 << hi_sz) - 1);
  unsigned int mask;

  while (1) {
    mask = (remaining < hi_sz) ? ((1 << remaining) - 1) : hi_mask;
    *dptr = (*dptr & ~(mask << lo_sz)) | ((*sptr & mask) << lo_sz);
    if (remaining > hi_sz)
      remaining -= hi_sz;
    else
      return;
    ++dptr;
    if (lo_sz != 0) {
      mask = (remaining < lo_sz) ? ((1 << remaining) - 1) : lo_mask;
      *dptr = (*dptr & ~mask) | ((*sptr >> hi_sz) & mask);
      if (remaining > lo_sz)
        remaining -= lo_sz;
      else
        return;
    }
    ++sptr;
  }
}

// Clear all of the bits in data between start and end, inclusive.
static inline void clear_bits(unsigned int* data, unsigned int start,
                              unsigned int end)
{
  if (start > end)
    return;

  unsigned int msk = ~0;
  unsigned int lo = word_idx(start);
  unsigned int hi = word_idx(end);
  msk <<= word_offset(start);
  if (hi == lo)
    msk &= mask(word_offset(end)+1);
  data[lo++] &= ~msk;
  while (lo < hi)
    data[lo++] = 0;
  if (lo <= hi)
    data[lo] &= ~mask(word_offset(end)+1);
}

// Set all of the bits in data between start and end, inclusive.
static inline void set_bits(unsigned int* data, unsigned int start,
                            unsigned int end)
{
  if (start > end)
    return;

  unsigned int msk = ~0;
  unsigned int lo = word_idx(start);
  unsigned int hi = word_idx(end);
  msk <<= word_offset(start);
  if (hi == lo)
    msk &= mask(word_offset(end)+1);
  data[lo++] |= msk;
  while (lo < hi)
    data[lo++] = ~0;
  if (lo <= hi)
    data[lo] |= mask(word_offset(end)+1);
}

// Whether all of the bits in data are clear between start and end, inclusive
static inline bool bits_are_clear(unsigned int* data, unsigned int start,
                                  unsigned int end)
{
  if (start > end)
    return true;

  unsigned int msk = ~0;
  unsigned int lo = word_idx(start);
  unsigned int hi = word_idx(end);
  msk <<= word_offset(start);
  if (hi == lo)
    msk &= mask(word_offset(end)+1);
  if ((data[lo++] & msk) != 0)
    return false;
  while (lo < hi)
    if (data[lo++] != 0)
      return false;
  if (lo <= hi)
    if ((data[lo] & mask(word_offset(end)+1)) != 0)
      return false;
  return true;
}

// default constructor used when allocating arrays of WideData
WideData::WideData()
{
  nBits = 0;    // creates 0-bit values, use setSize to initialize
  nWords = 0;
  data = NULL;
}

// basic sized constructor
WideData::WideData(unsigned int bits, bool init)
{
  nBits = bits;
  nWords = NUM_WORDS(bits);
  if (nWords == 0)
  {
    data = NULL;
  }
  else
  {
    data = (unsigned int*) alloc_mem(nWords);
    if (init)
      write_undet(this,nBits);
  }
}

// special constructor used for literal values
WideData::WideData(unsigned int bits, const unsigned int array[])
{
  nBits = bits;
  nWords = NUM_WORDS(bits);
  if (nWords == 0)
  {
    data = NULL;
  }
  else
  {
    data = (unsigned int*) alloc_mem(nWords);
    for (unsigned int i = 0; i < nWords; ++i)
      data[i] = array[i];
  }
}

// special constructors used to promote non-wide values
WideData::WideData(unsigned int bits, unsigned int value)
{
  nBits = bits;
  nWords = NUM_WORDS(bits);
  if (nWords == 0)
  {
    data = NULL;
  }
  else
  {
    data = (unsigned int*) alloc_mem(nWords);
    data[0] = value;
    clear(nBits);
  }
}

WideData::WideData(unsigned int bits, unsigned long long value)
{
  nBits = bits;
  nWords = NUM_WORDS(bits);
  if (nWords == 0)
  {
    data = NULL;
  }
  else
  {
    data = (unsigned int*) alloc_mem(nWords);
    data[0] = (unsigned int) (value & mask(WORD_SIZE));
    data[1] = (unsigned int) (value >> WORD_SIZE);
    clear(nBits);
  }
}

// special constructor used to represent strings
WideData::WideData(unsigned int bits, const char* str)
{
  nBits = bits;
  nWords = NUM_WORDS(bits);
  if (nWords == 0)
  {
    data = NULL;
  }
  else
  {
    data = (unsigned int*) alloc_mem(nWords);
    clear();
    const char* cptr = str;
    for (unsigned int i = nBits; i > 0; i -= BYTE_SIZE)
      *(byte_ptr(data, i-1)) = *(cptr++);
  }
}


// copy constructor
WideData::WideData(const WideData& v)
{
  nBits  = v.nBits;
  nWords = v.nWords;
  if (nWords == 0)
  {
    data = NULL;
  }
  else
  {
    data = (unsigned int*) alloc_mem(nWords);
    for (unsigned int i = 0; i < nWords; ++i)
      data[i] = v.data[i];
  }
}

// copy assignment
WideData& WideData::operator=(const WideData& v)
{

  // assumes that sizes match
  for (unsigned int i = 0; i < nWords; ++i)
    data[i] = v.data[i];
  return (*this);
}

// destructor
WideData::~WideData()
{
  free_mem(data, nWords);
  data = NULL;
  nBits = 0;
  nWords = 0;
}


void WideData::setSize(unsigned int width)
{
  free_mem(data, nWords);
  nBits  = width;
  nWords = NUM_WORDS(width);
  if (nWords == 0)
    data = NULL;
  else
    data = (unsigned int*) alloc_mem(nWords);
}

unsigned char WideData::getByte(unsigned int byte_num) const
{
  return ((data[byte_num/BYTES_PER_WORD] >> (8 * (byte_num % BYTES_PER_WORD))) & 0xFF);
}

void WideData::setByte(unsigned int byte_num, unsigned char val)
{
  unsigned int idx = byte_num / BYTES_PER_WORD;
  unsigned int offset = 8 * (byte_num % BYTES_PER_WORD);
  data[idx] = (data[idx] & (~(0xFF << offset))) | (val << offset);
}

/* operations on wide data */


void WideData::clear(unsigned int from)
{
  clear(from, (nWords * WORD_SIZE) - 1);
}

void WideData::clear(unsigned int from, unsigned int to)
{
  clear_bits(data, from, to);
}

void WideData::set(unsigned int from)
{
  set(from, (nWords * WORD_SIZE) - 1);
}

void WideData::set(unsigned int from, unsigned int to)
{
  set_bits(data, from, to);
}

void WideData::copy(const WideData& src)
{
  copy(src,0);
}

void WideData::copy(const WideData& src, unsigned int to)
{
  copy_bits_from_0(data, to, src.data, src.nBits);
}

void WideData::write(unsigned int* buf, unsigned int sze,
                     unsigned int to)
{
  copy_bits_from_0(data, to, buf, sze);
}

bool WideData::is_clear(unsigned int from) const
{
  return is_clear(from, nBits - 1);
}

bool WideData::is_clear(unsigned int from, unsigned int to) const
{
  return bits_are_clear(data, from, to);
}

WideData& WideData::build_concat(bool src, unsigned int loc, unsigned int nbits)
{
  unsigned int buf[1];
  buf[0] = src ? 1 : 0;
  copy_bits_from_0(data, loc, buf, nbits);
  return (*this);
}

WideData& WideData::build_concat(unsigned char src, unsigned int loc, unsigned int nbits)
{
  unsigned int buf[1];
  buf[0] = (unsigned int) src;
  copy_bits_from_0(data, loc, buf, nbits);
  return (*this);
}

WideData& WideData::build_concat(int src, unsigned int loc, unsigned int nbits)
{
  copy_bits_from_0(data, loc, (unsigned int*) (&src), nbits);
  return (*this);
}

WideData& WideData::build_concat(unsigned int src, unsigned int loc, unsigned int nbits)
{
  copy_bits_from_0(data, loc, &src, nbits);
  return (*this);
}

WideData& WideData::build_concat(unsigned long long src, unsigned int loc, unsigned int nbits)
{
  unsigned int buf[2];
  buf[0] = (unsigned int) src;
  buf[1] = (unsigned int) (src >> WORD_SIZE);
  copy_bits_from_0(data, loc, buf, nbits);
  return (*this);
}

WideData& WideData::build_concat(const WideData& src, unsigned int loc, unsigned int nbits)
{
  copy_bits_from_0(data, loc, src.data, nbits);
  return (*this);
}

bool WideData::extract1(unsigned int idx) const
{
  return ((data[word_idx(idx)] >> word_offset(idx)) & 0x1) ;
}

unsigned char WideData::extract8(unsigned int hi, unsigned int lo) const
{
  unsigned int idx = word_idx(lo);
  unsigned long long val = data[idx++];
  if (idx < nWords)
    val |= (((unsigned long long)data[idx]) << WORD_SIZE);
  unsigned int mask_sz = std::min(8u, hi-lo+1);
  unsigned char result = mask8(mask_sz) & (val >> word_offset(lo));
  return result;
}

unsigned int WideData::extract32(unsigned int hi, unsigned int lo) const
{
  unsigned int idx = word_idx(lo);
  unsigned long long val = data[idx++];
  if (idx < nWords)
    val |= (((unsigned long long)data[idx]) << WORD_SIZE);
  unsigned int mask_sz = std::min(32u, hi-lo+1);
  unsigned int result = mask(mask_sz) & (val >> word_offset(lo));
  return result;
}

unsigned long long WideData::extract64(unsigned int hi, unsigned int lo) const
{
  unsigned int buffer[2];
  copy_bits_to_0(buffer, data, lo, std::min(64u,(hi-lo+1)));
  clear_bits(buffer, (hi-lo+1), 63);
  unsigned long long result = ((unsigned long long) buffer[0]) |
                              (((unsigned long long)buffer[1]) << WORD_SIZE);
  return result;
}

WideData WideData::extractWide(unsigned int hi, unsigned int lo) const
{
  WideData result((hi-lo+1), NUM_WORDS(hi-lo+1));
  copy_bits_to_0(result.data, data, lo, (hi-lo+1));
  clear_bits(result.data, (hi-lo+1), (result.nWords * WORD_SIZE) - 1);
  return result;
}

/* output routines */

void WideData::print_binary(Target* dest, unsigned int field_width) const
{
  unsigned int sz = nWords * WORD_SIZE;
  if (sz < field_width)
    sz = field_width;
  unsigned int digits = 0;
  unsigned int non_zero_digits = 0;
  char buf[sz+1];
  char* str = buf + sz;
  *str = '\0';

  // generate digits by shifting & masking
  unsigned int remaining = nBits;
  unsigned int* dptr = data;
  while (remaining > 0)
  {
    unsigned int val = *(dptr++);
    unsigned int n = std::min(remaining,WORD_SIZE);
    remaining -= n;
    while (n-- > 0)
    {
      *(--str) = (val & 0x1) ? '1' : '0';
      ++digits;
      if (val & 0x1)
        non_zero_digits = digits;
      val >>= 1;
    }
  }

  // include only enough leading zeros to satisfy field_width
  unsigned int digits_shown;
  if (field_width < non_zero_digits)
    digits_shown = non_zero_digits;
  else
    digits_shown = std::min(field_width, digits);
  str = buf + sz - digits_shown;

  // handle zero value
  if (digits_shown == 0)
  {
    *(--str) = '0';
    ++digits_shown;
  }

  // pad to minimum field width with spaces
  while (digits_shown < field_width)
  {
    *(--str) = ' ';
    ++digits_shown;
  }

  dest->write_data(str,digits_shown,sizeof(char));
}

static inline unsigned char hexChar(unsigned int v)
{
  unsigned char c = (unsigned char) (v & mask(4));
  if (c > 9)
    c += 'a' - 10;
  else
    c += '0';
  return c;
}

void WideData::print_hex(Target*dest, unsigned int field_width) const
{
  unsigned int sz = 2 * nWords * BYTES_PER_WORD;
  if (sz < field_width)
    sz = field_width;
  unsigned int digits = 0;
  unsigned int non_zero_digits = 0;
  char buf[sz+1];
  char* str = buf + sz;
  *str = '\0';

  // generate digits by shifting & masking
  unsigned int remaining = nBits;
  unsigned int* dptr = data;
  while (remaining > 0)
  {
    unsigned int val = *(dptr++);
    unsigned int n = std::min(remaining,WORD_SIZE);
    remaining -= n;
    while (n > 0)
    {
      char c = hexChar(val);
      *(--str) = c;
      val >>= 4;
      if (n < 4)
        n = 0;
      else
        n -= 4;
      ++digits;
      if (c != '0')
        non_zero_digits = digits;
    }
  }

  // include only enough leading zeros to satisfy field_width
  unsigned int digits_shown;
  if (field_width < non_zero_digits)
    digits_shown = non_zero_digits;
  else
    digits_shown = std::min(field_width, digits);
  str = buf + sz - digits_shown;

  // handle zero value
  if (digits_shown == 0)
  {
    *(--str) = '0';
    ++digits_shown;
  }

  // pad to minimum field width with spaces
  while (digits_shown < field_width)
  {
    *(--str) = ' ';
    ++digits_shown;
  }

  dest->write_data(str,digits_shown,sizeof(char));
}


static inline unsigned char octalChar(unsigned long long v)
{
  return ('0' + (unsigned char) (v & mask(3)));
}

void WideData::print_octal(Target* dest, unsigned int field_width) const
{
  unsigned int sz = 3 * nWords * BYTES_PER_WORD;
  if (sz < field_width)
    sz = field_width;
  unsigned int digits = 0;
  unsigned int non_zero_digits = 0;
  char buf[sz+1];
  char* str = buf + sz;
  *str = '\0';

  // generate digits by extracting 3-bit chunks
  unsigned int remaining = nBits;
  unsigned int* dptr = data;
  unsigned long long val = 0llu;
  unsigned int n = 0;
  while (remaining > 0)
  {
    val |= (((unsigned long long)*(dptr++)) << n);
    n = std::min(remaining,n+WORD_SIZE);
    while (n >= 3)
    {
      char c = octalChar(val);
      *(--str) = c;
      val >>= 3;
      remaining -= 3;
      n -= 3;
      ++digits;
      if (c != '0')
        non_zero_digits = digits;
    }
    if (remaining < 3 && remaining > 0 && remaining == n)
    {
      char c = octalChar(val);
      *(--str) = c;
      ++digits;
      if (c != '0')
        non_zero_digits = digits;
      remaining = 0;
    }
  }

  // include only enough leading zeros to satisfy field_width
  unsigned int digits_shown;
  if (field_width < non_zero_digits)
    digits_shown = non_zero_digits;
  else
    digits_shown = std::min(field_width, digits);
  str = buf + sz - digits_shown;

  // handle zero value
  if (digits_shown == 0)
  {
    *(--str) = '0';
    ++digits_shown;
  }

  // pad to minimum field width with spaces
  while (digits_shown < field_width)
  {
    *(--str) = ' ';
    ++digits_shown;
  }

  dest->write_data(str,digits_shown,sizeof(char));
}


static inline unsigned char div10(unsigned int* dividend,
                                  unsigned int* quotient,
                                  signed int first_non_zero)
{
  unsigned long long remainder = 0llu;
  for (signed int i = first_non_zero; i >= 0; --i)
  {
    remainder = (remainder << WORD_SIZE) + dividend[i];
    quotient[i] = (unsigned int) (remainder / 10llu);
    remainder %= 10llu;
  }
  return (unsigned char) remainder;
}

unsigned int WideData::max_decimal_digits(unsigned int bits, bool is_signed)
{
  if (bits == 0)
    return 0;

  // count digits by repeated division by 10
  unsigned int digits = 0;
  unsigned int nWords = NUM_WORDS(bits);
  unsigned int quotient[nWords];
  signed int first_non_zero = nWords-1;

  // setup quotient as n 1's (for unsigned) or 2^(n-1) (for signed)
  if (is_signed)
  {
    quotient[nWords-1] = 1 << word_offset(bits-1);
    if (nWords > 1)
    {
      for (signed int i = nWords - 2; i >=0; --i)
        quotient[i] = 0;
    }
  }
  else
  {
    quotient[nWords-1] = mask(word_offset(bits-1)+1);
    if (nWords > 1)
    {
      for (signed int i = nWords - 2; i >= 0; --i)
        quotient[i] = ~0;
    }
  }

  while (first_non_zero >= 0)
  {
    div10(quotient, quotient, first_non_zero);
    ++digits;

    while ((first_non_zero >= 0) && (quotient[first_non_zero] == 0))
      --first_non_zero;
  }

  // handle zero value
  if (digits == 0) ++digits;

  return digits;
}

void WideData::print_decimal(Target* dest,
                             unsigned int field_width, bool is_signed) const
{
  unsigned int sz = nWords * 10;
  if (sz < field_width)
    sz = field_width;
  unsigned int digits = 0;
  char buf[sz+1];
  char* str = buf + sz;
  *str = '\0';

  bool is_negative = false;
  if (is_signed)
    is_negative = ((data[nWords-1] >> ((nBits-1) % WORD_SIZE)) & 0x1) != 0;

  // generate digits by repeated division by 10
  unsigned int quotient[nWords];
  unsigned int* dividend = data; // first iteration reads from data
  signed int first_non_zero = nWords-1;

  // for negative values, we negate the value before printing
  if (is_negative)
  {
    unsigned int borrow = 0;
    unsigned int x,y;
    for (unsigned int i = 0; i < nWords; ++i)
    {
      x = (i == word_idx(nBits)) ? (1 << word_offset(nBits)) : 0;
      y = data[i];
      quotient[i] = x - y - borrow;
      // borrow if y is greater than x
      borrow = (y > x) ? 1 : 0;
    }
    quotient[nWords-1] &= mask(word_offset(nBits-1)+1);
    dividend = quotient;
  }

  while ((first_non_zero >= 0) && (dividend[first_non_zero] == 0))
    --first_non_zero;

  while (first_non_zero >= 0)
  {
    *(--str) = '0' + div10(dividend, quotient, first_non_zero);
    ++digits;

    dividend = quotient; // subsequent iterations read previous result

    while ((first_non_zero >= 0) && (dividend[first_non_zero] == 0))
      --first_non_zero;
  }

  // handle zero value
  if (digits == 0)
  {
    *(--str) = '0';
    ++digits;
  }

  // handle negative values
  if (is_negative)
  {
    *(--str) = '-';
    ++digits;
  }

  // pad to minimum field width
  while (digits < field_width)
  {
    *(--str) = ' ';
    ++digits;
  }

  dest->write_data(str,digits,sizeof(char));
}

/* overloaded operators for use with WideData */

WideData operator&(const WideData& v1, const WideData& v2)
{
  WideData result(v1.nBits, v1.nWords);
  for (unsigned int idx = 0; idx < v1.nWords; ++idx)
    result.data[idx] = v1.data[idx] & v2.data[idx];
  return result;
}

WideData operator|(const WideData& v1, const WideData& v2)
{
  WideData result(v1.nBits, v1.nWords);
  for (unsigned int idx = 0; idx < v1.nWords; ++idx)
    result.data[idx] = v1.data[idx] | v2.data[idx];
  return result;
}

WideData operator^(const WideData& v1, const WideData& v2)
{
  WideData result(v1.nBits, v1.nWords);
  for (unsigned int idx = 0; idx < v1.nWords; ++idx)
    result.data[idx] = v1.data[idx] ^ v2.data[idx];
  return result;
}

WideData operator~(const WideData& v)
{
  WideData result(v.nBits, v.nWords);
  for (unsigned int idx = 0; idx < v.nWords; ++idx)
    result.data[idx] = ~v.data[idx];
  clear_bits(result.data, result.nBits, (result.nWords * WORD_SIZE) - 1);
  return result;
}

WideData operator>>(const WideData& value, unsigned int shift)
{
  if (shift == 0)
  {
    return value;
  }
  else
  {
    WideData result(value.nBits, value.nWords);
    if (shift > value.nBits)
    {
      // the result is all zeros
      for (unsigned int i = 0; i < value.nWords; ++i)
        result.data[i] = 0;
    }
    else
    {
      // copy the bits we need and clear the rest
      copy_bits_to_0(result.data, value.data, shift, value.nBits - shift);
      clear_bits(result.data, value.nBits - shift, (result.nWords * WORD_SIZE) - 1);
    }
    return result;
  }
}

WideData operator<<(const WideData& value, unsigned int shift)
{
  if (shift == 0)
  {
    return value;
  }
  else
  {
    WideData result(value.nBits, value.nWords);
    if (shift > value.nBits)
    {
      // the result is all zeros
      for (unsigned int i = 0; i < value.nWords; ++i)
        result.data[i] = 0;
    }
    else
    {
      // copy the bits we need and clear the rest
      copy_bits_from_0(result.data, shift, value.data, value.nBits - shift);
      clear_bits(result.data, 0, shift - 1);
      clear_bits(result.data, result.nBits, (result.nWords * WORD_SIZE) - 1);
    }
    return result;
  }
}

WideData operator-(const WideData& v)
{
  WideData result(v.nBits, v.nWords);

  bool borrow = false;
  unsigned int y;
  for (unsigned int i = 0; i < v.nWords; ++i)
  {
    y = v.data[i];
    result.data[i] = -y - (borrow ? 1 : 0);
    // borrow if (y > 0) or (y == 0) and we borrowed before
    borrow |= (y > 0);
  }
  // prevent underflow into the unused bits
  result.data[result.nWords-1] &= mask(word_offset(result.nBits-1)+1);

  return result;
}

WideData operator+(const WideData& v1, const WideData& v2)
{
  WideData result(v1.nBits, v1.nWords);

  bool carry = 0;
  unsigned int x,y,z;
  for (unsigned int i = 0; i < v1.nWords; ++i)
  {
    x = v1.data[i];
    y = v2.data[i];
    z = x + y;
    result.data[i] = z + (carry ? 1 : 0);
    // carry if z is less than either of the arguments or
    // if the result is less than z;
    carry = (z < x || z < y || result.data[i] < z);
  }
  // prevent overflow into the unused bits
  result.data[result.nWords-1] &= mask(word_offset(result.nBits-1)+1);

  return result;
}

WideData operator-(const WideData& v1, const WideData& v2)
{
  WideData result(v1.nBits, v1.nWords);

  bool borrow = false;
  unsigned int x,y;
  for (unsigned int i = 0; i < v1.nWords; ++i)
  {
    x = v1.data[i];
    y = v2.data[i];
    result.data[i] = x - y - (borrow ? 1 : 0);
    // borrow if (y > x) or (y == x) and we borrowed before
    borrow = (y > x) || ((y == x) && borrow);
  }
  // prevent underflow into the unused bits
  result.data[result.nWords-1] &= mask(word_offset(result.nBits-1)+1);

  return result;
}

// Add a 64-bit value into a data array, propagating carries as far as needed
static void incr(unsigned int* data, unsigned int words,
                 unsigned long long value)
{
  unsigned long long sum = value & (unsigned long long) mask(WORD_SIZE);
  sum += ((unsigned long long) (data[0]));
  data[0] = (unsigned int) (sum & (unsigned long long) mask(WORD_SIZE));
  sum >>= WORD_SIZE;
  sum += value >> WORD_SIZE;
  unsigned int i = 0;
  while ((++i < words) && (sum != 0llu))
  {
    sum += ((unsigned long long) (data[i]));
    data[i] = (unsigned int) (sum & (unsigned long long) mask(WORD_SIZE));
    sum >>= WORD_SIZE;
  }
}

WideData operator*(const WideData& v1, const WideData& v2)
{
  WideData result(v1.nBits + v2.nBits, NUM_WORDS(v1.nBits + v2.nBits));

  result.clear();

  unsigned int i,j;
  for (unsigned int idx = 0; idx < result.nWords; ++idx)
  {
    // the value of a word in the result is made up of
    // a value carried from the previous word plus the
    // sum of the products of source word pairs whose
    // indices sum to the destination index.
    // eg. z[0] = 0 + (x[0] * y[0]);
    //     z[1] = carry + (x[0] * y[1]) + (x[1] * y[0]);
    //     z[2] = carry + (x[0] * y[2]) + (x[1] * y[1]) + (x[2] * y[0]);
    i = std::min(v1.nWords,idx+1);
    while (i > 0)
    {
      --i;
      j = idx - i;
      if (i < v1.nWords && j < v2.nWords)
      {
        incr(result.data + idx, result.nWords - idx,
             ((unsigned long long) v1.data[i]) *
             ((unsigned long long) v2.data[j]));
      }
    }
  }

  // prevent overflow into the unused bits
  result.data[result.nWords-1] &= mask(word_offset(result.nBits-1)+1);

  return result;
}

// Perform division on the wide values, writing the quotient and
// remainder into their respective buffers.
void wide_quot_rem(const WideData& v1, const WideData& v2,
                   unsigned int* quot, unsigned int* rem)
{
  WideData dividend = v1;
  WideData divisor = v2;

  // start with quotient = 0 & remainder = 0
  memset(quot, 0, BYTES_PER_WORD * dividend.numWords());
  memset(rem,  0, BYTES_PER_WORD * divisor.numWords());

  // find the most significant bit set in the divisor
  int first_divisor_bit = divisor.size() - 1;
  while (first_divisor_bit >= 0)
  {
    if (divisor.extract1(first_divisor_bit))
      break;
    --first_divisor_bit;
  }

  // handle division by zero
  if (first_divisor_bit < 0)
    raise(SIGFPE);

  // find the most significant bit set in the dividend
  int first_dividend_bit = dividend.size() - 1;
  while (first_dividend_bit >= 0)
  {
    if (dividend.extract1(first_dividend_bit))
      break;
    --first_dividend_bit;
  }

  // handle the zero dividend case
  if (first_dividend_bit < 0)
    return;

  // align the first bit of the divisor with the first bit of the dividend
  // subtract the divisor from the dividend and set the bit of the quotient
  // corresponding to the shift amount
  unsigned int shift = first_dividend_bit - first_divisor_bit;
  while (first_dividend_bit >= first_divisor_bit)
  {
    WideData tmp = divisor << shift;

    if (dividend < tmp)
    {
      if (shift == 0)
        break;
      --shift;
      continue;
    }

    quot[word_idx(shift)] |= 1 << word_offset(shift);
    dividend = dividend - tmp;
    while (first_dividend_bit >= 0)
    {
      if (dividend.extract1(first_dividend_bit))
        break;
      --first_dividend_bit;
    }
    shift = first_dividend_bit - first_divisor_bit;
  }

  // the remaining dividend is the remainder
  memcpy(rem, dividend.data, BYTES_PER_WORD * divisor.numWords());

  return;
}

WideData operator/(const WideData& v1, const WideData& v2)
{
  WideData result(v1.nBits, v1.nWords);
  unsigned int ignore[v2.nWords];

  result.clear();
  wide_quot_rem(v1, v2, result.data, ignore);

  return result;
}

WideData operator%(const WideData& v1, const WideData& v2)
{
  WideData result(v2.nBits, v2.nWords);
  unsigned int ignore[v1.nWords];

  result.clear();
  wide_quot_rem(v1, v2, ignore, result.data);

  return result;
}

bool operator==(const WideData& v1, const WideData& v2)
{
  unsigned int idx = v1.nWords;
  while (idx > 0)
  {
    --idx;
    if (v1.data[idx] != v2.data[idx])
      return false;
  }
  return true;
}

bool operator!=(const WideData& v1, const WideData& v2)
{
  return !(v1 == v2);
}

bool operator<(const WideData& v1, const WideData& v2)
{
  unsigned int idx = v1.nWords;
  while (idx > 0)
  {
    --idx;
    if (v1.data[idx] < v2.data[idx])
      return true;
    if (v1.data[idx] > v2.data[idx])
      return false;
  }
  return false; // exactly equal
}

bool operator>(const WideData& v1, const WideData& v2)
{
  unsigned int idx = v1.nWords;
  while (idx > 0)
  {
    --idx;
    if (v1.data[idx] > v2.data[idx])
      return true;
    if (v1.data[idx] < v2.data[idx])
      return false;
  }
  return false; // exactly equal
}

bool operator<=(const WideData& v1, const WideData& v2)
{
  return !(v1 > v2);
}

bool operator>=(const WideData& v1, const WideData& v2)
{
  return !(v1 < v2);
}

// Utility functions that use overloading to handle wide and narrow
// data uniformly.

void init_val(WideData& v, unsigned int width)
{
  v.setSize(width);
}

void init_val(unsigned long long /* unused */, unsigned int /* unused */)
{
  return;
}

void dump_val(unsigned long long v, unsigned int width)
{
  FileTarget dest(stdout);
  if (width == 0)
    dest.write_string("()");
  else if (width == 1)
    dest.write_string("%s", (v ? "True" : "False"));
  else
    dest.write_string("0x%0*llx", ((width+3)/4), v);
}

void dump_val(const WideData& v, unsigned int /* unused */)
{
  FileTarget dest(stdout);
  dest.write_string("0x");
  v.print_hex(&dest);
}

void write_undet(bool* pValue, unsigned int width)
{
  *pValue = false;
}

void write_undet(unsigned char* pValue, unsigned int width)
{
  *pValue = 0xAAAAAAAA & mask(width);
}

void write_undet(unsigned int* pValue, unsigned int width)
{
  *pValue = 0xAAAAAAAA & mask(width);
}

void write_undet(unsigned long long* pValue, unsigned int width)
{
  if (width <= 32)
    *pValue = 0xAAAAAAAAllu & mask(width);
  else
    *pValue = 0xAAAAAAAAAAAAAAAAllu &
         ((((unsigned long long)mask(width - 32)) << 32) | 0xFFFFFFFFllu);
}

void write_undet(WideData* pValue, unsigned int /* unused */)
{
  unsigned int n = pValue->nBits;
  unsigned int* dptr = pValue->data;
  unsigned int sz;
  while (n > 0)
  {
    sz = std::min(n,32u);
    write_undet(dptr++, sz);
    n -= sz;
  }
}


void mask_high_bits(bool* pValue, unsigned int width)
{
  if (width == 0)
    *pValue = false;
}

void mask_high_bits(unsigned char* pValue, unsigned int width)
{
  *pValue &= mask(width);
}

void mask_high_bits(unsigned int* pValue, unsigned int width)
{
  *pValue &= mask(width);
}

void mask_high_bits(unsigned long long* pValue, unsigned int width)
{
  if (width <= 32)
    *pValue &= (unsigned long long) mask(width);
  else
    *pValue &= ((((unsigned long long)mask(width - 32)) << 32) | 0xFFFFFFFFllu);
}

void mask_high_bits(WideData* pValue, unsigned int width)
{
  pValue->clear(width+1);
}


bool is_zero(unsigned char  v)
{
  return (v == 0);
}

bool is_zero(unsigned int v)
{
  return (v == 0);
}

bool is_zero(unsigned long long  v)
{
  return (v == 0llu);
}

bool is_zero(const WideData& v)
{
  for (unsigned int n = 0; n < v.numWords(); ++n)
    if (v[n] != 0)
      return false;

  return true;
}


bool is_bit_set(unsigned char v, unsigned int n)
{
  return (((v >> n) & 1) != 0);
}

bool is_bit_set(unsigned int v, unsigned int n)
{
  return (((v >> n) & 1) != 0);
}

bool is_bit_set(unsigned long long v, unsigned int n)
{
  return (((v >> n) & 1llu) != 0llu);
}

bool is_bit_set(const WideData& v, unsigned int n)
{
  return v.extract1(n);
}


bool chunks_eq(unsigned char x, unsigned char y, unsigned int n, unsigned int width)
{
  unsigned char x2 = (x >> (n * width)) & mask8(width);
  unsigned char y2 = (y >> (n * width)) & mask8(width);
  return (x2 == y2);
}

bool chunks_eq(unsigned int x, unsigned int y, unsigned int n, unsigned int width)
{
  unsigned int x2 = (x >> (n * width)) & mask(width);
  unsigned int y2 = (y >> (n * width)) & mask(width);
  return (x2 == y2);
}

bool chunks_eq(unsigned long long x, unsigned long long y, unsigned int n, unsigned int width)
{
  unsigned long long x2 = (x >> (n * width)) & mask64(width);
  unsigned long long y2 = (y >> (n * width)) & mask64(width);
  return (x2 == y2);
}

bool chunks_eq(const WideData& x, const WideData& y, unsigned int n, unsigned int width)
{
  if (width == 1)
  {
    return (x.extract1(n) == y.extract1(n));
  }
  else if (width <= 8)
  {
    return (x.extract8((n+1)*width - 1, n*width) == y.extract8((n+1)*width - 1, n*width));
  }
  else if (width <= 32)
  {
    return (x.extract32((n+1)*width - 1, n*width) == y.extract32((n+1)*width - 1, n*width));
  }
  else if (width <= 64)
  {
    return (x.extract64((n+1)*width - 1, n*width) == y.extract64((n+1)*width - 1, n*width));
  }
  else if (width < x.size())
  {
    WideData chunk1;
    WideData chunk2;
    chunk1 = x.extractWide((n+1)*width - 1, n*width);
    chunk2 = y.extractWide((n+1)*width - 1, n*width);
    return (chunk1 == chunk2);
  }
  else
  {
    return (x == y);
  }
}

void xfer_chunk(unsigned char* pDest, unsigned char src, unsigned int n, unsigned int width)
{
  unsigned char m = mask8(width) << (n * width);
  *pDest = (*pDest & ~m) | (src & m);
}

void xfer_chunk(unsigned int* pDest, unsigned int src, unsigned int n, unsigned int width)
{
  unsigned int m = mask(width) << (n * width);
  *pDest = (*pDest & ~m) | (src & m);
}

void xfer_chunk(unsigned long long* pDest, unsigned long long src, unsigned int n, unsigned int width)
{
  unsigned long long m = mask64(width) << (n * width);
  *pDest = (*pDest & ~m) | (src & m);
}

void xfer_chunk(const WideData* pDest, const WideData& src, unsigned int n, unsigned int width)
{
  copy_bits(pDest->data, n*width, src.data, n*width, width);
}

WideData bs_wide_tmp(unsigned int width)
{
  WideData tmp(width,false);
  return tmp;
}

/********************************************
 Functions for wide-data manipulation
 without return value. The last argument of
 these functions is the real return address.
 Most of the implementations are copied from
 the original ones with return value.
*********************************************/

/*** operators ***/

// c = a & b
void wop_and(const WideData& v1, const WideData& v2, WideData& result)
{
  for (unsigned int idx = 0; idx < v1.numWords(); ++idx)
    result.data[idx] = v1.data[idx] & v2.data[idx];
}

// c = a | b
void wop_or(const WideData& v1, const WideData& v2, WideData& result)
{
  for (unsigned int idx = 0; idx < v1.numWords(); ++idx)
    result.data[idx] = v1.data[idx] | v2.data[idx];
}

// c = a ^ b
void wop_xor(const WideData& v1, const WideData& v2, WideData& result)
{
  for (unsigned int idx = 0; idx < v1.numWords(); ++idx)
    result.data[idx] = v1.data[idx] ^ v2.data[idx];
}

// c = ~a
void wop_inv(const WideData& v, WideData& result)
{
  for (uint idx = 0; idx < v.numWords(); ++idx)
    result.data[idx] = ~v.data[idx];
  clear_bits(result.data, result.size(), (result.numWords() * WORD_SIZE) - 1);
}

void wop_neg(const WideData& v, WideData& result)
{
  bool borrow = false;
  unsigned int y;
  for (unsigned int i = 0; i < v.numWords(); ++i)
  {
    y = v.data[i];
    result.data[i] = -y - (borrow ? 1 : 0);
    // borrow if (y > 0) or (y == 0) and we borrowed before
    borrow |= (y > 0);
  }
  // prevent underflow into the unused bits
  result.data[result.numWords()-1] &= mask(word_offset(result.size()-1)+1);
}

// c = a >> x
void wop_srl(const WideData& value, uint shift, WideData& result)
{
  if (shift == 0)
  {
    result = value; //FIXME: double check if this is an address-passing
  }
  else
  {
    if (shift > value.size())
    {
      // the result is all zeros
      for (uint i = 0; i < value.numWords(); ++i)
        result.data[i] = 0;
    }
    else
    {
      // copy the bits we need and clear the rest
      copy_bits_to_0(result.data, value.data, shift, value.size() - shift);
      clear_bits(result.data, value.size() - shift,
                 (result.numWords() * WORD_SIZE) - 1);
    }
  }
}

// c = a << x
void wop_sl(const WideData& value, uint shift, WideData& result)
{
  if (shift == 0)
  {
    result = value; //FIXME: double check
  }
  else
  {
    if (shift > value.size())
    {
      // the result is all zeros
      for (uint i = 0; i < value.numWords(); ++i)
        result.data[i] = 0;
    }
    else
    {
      // copy the bits we need and clear the rest
      copy_bits_from_0(result.data, shift, value.data, value.size() - shift);
      clear_bits(result.data, 0, shift - 1);
      clear_bits(result.data, result.size(),
                 (result.numWords() * WORD_SIZE) - 1);
    }
  }
}

//c = a + b
void wop_add(const WideData &a, const WideData &b, WideData &c){

  bool carry = 0;
  uint x,y,z;

  for (uint i = 0; i < a.numWords(); ++i)
  {
    x = a.data[i];
    y = b.data[i];
    z = x + y;
    c.data[i] = z + (carry ? 1 : 0);
    carry = (z < x || z < y || c.data[i] < z);
  }

  c.data[c.numWords()-1] &= mask(word_offset(c.size()-1)+1);
}

//c = a - b
void wop_sub(const WideData &a, const WideData &b, WideData &c){

  bool borrow = false;
  uint x,y;

  for (uint i = 0; i < a.numWords(); ++i)
  {
    x = a.data[i];
    y = b.data[i];
    c.data[i] = x - y - (borrow ? 1 : 0);
    borrow = (y > x) || ((y == x) && borrow);
  }

  c.data[c.numWords()-1] &= mask(word_offset(c.size()-1)+1);

}

// c = a * b
void wop_mul(const WideData &a, const WideData &b, WideData &c){

  uint i,j;

  c.clear();

  for (uint idx = 0; idx < c.numWords(); ++idx)
  {
    i = std::min(a.numWords(),idx+1);
    while (i > 0)
    {
      --i;
      j = idx - i;
      if (i < a.numWords() && j < b.numWords())
      {
        incr(c.data + idx, c.numWords() - idx, ((unsigned long long) a.data[i])
             * ((unsigned long long) b.data[j]));
      }
    }
  }

  c.data[c.numWords()-1] &= mask(word_offset(c.size()-1)+1);
}

// c = a / b
void wop_quot(const WideData& v1, const WideData& v2, WideData &result)
{
  uint ignore[v2.numWords()];
  result.clear();
  wide_quot_rem(v1, v2, result.data, ignore);
}

// c = a % b
void wop_rem(const WideData& v1, const WideData& v2, WideData &result)
{
  uint ignore[v1.numWords()];
  result.clear();
  wide_quot_rem(v1, v2, ignore, result.data);
}

/*** function calls ***/

/* maybe useful */
void WideData::wop_extractWide(uint hi, uint lo, WideData& result) const
{
  copy_bits_to_0(result.data, data, lo, (hi-lo+1));
  clear_bits(result.data, (hi-lo+1), (result.numWords() * WORD_SIZE) - 1);
}

void wop_maskWide(uint n, WideData& val, WideData& result)
{
  val.wop_extractWide(n-1,0,result);
}
/* or useless - these two above */
