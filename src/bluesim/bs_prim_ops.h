#ifndef __BS_PRIM_OPS_H__
#define __BS_PRIM_OPS_H__

#include <string>

#include "bluesim_types.h"
#include "bs_wide_data.h"

/* These are utility functions used when implementing
 * bit-granularity primitives on top of coarse C/C++
 * primitives.
 */

/* The organizing principle behind these routines is
 * determined by the interactions of C++ function overloading
 * and integral promotion.
 *
 * - Overloading works on the function name and argument types,
 *   but not on the return type.  Therefore, the return type
 *   is encoded in the function name as 8 (for bool or tUInt8),
 *   32 (for tUInt32), 64 (for tUInt64) or Wide (for tUWide).
 *
 * - For some operators, the return type size is not related to
 *   the argument type size.  In this case, you may have several
 *   implementations for the same return size with different
 *   argument sizes (which can be larger or smaller than the
 *   return size).
 *
 * - If there is not an exact match for the argument types
 *   in a function call, an approximate match is chosen and the
 *   arguments which are no the correct type undergo integral
 *   promotion to a larger value.  This allows us to use one
 *   function with two larger types instead of creating multiple
 *   functions to handle each possible combination of argument
 *   sizes.
 *
 * - An ambiguity in overload resolution generates a compiler
 *   error, so it is better to NOT create lots of implementations
 *   when fewer implementations + function overloading will do.
 */

/* Note: The C/C++ standard says that shifting a value by an
 * amount greater than the width of the datatype yields an
 * undefined value, and compiler optimizations *do* take advantage
 * of this.  In Bluespec, a zero value is expected in these
 * cases, so we have to use a guarded shift operation in situations
 * where the value is not guaranteed to be in range.
 * For efficiency, we want to use unguarded shifts when we know
 * it is safe.
 */


/* The caller of the mask operations is responsible for ensuring that
 * the number of bits requested is less than or equal to the result size.
 */

// This case handles promoted values
static inline tUInt8 mask8(tUInt32 n, tSInt32 val)
{
  return (tUInt8)(((1 << n) - 1) & val);
}

static inline tUInt8 mask8(tUInt32 n, tUInt32 val)
{
  return (tUInt8)(((1 << n) - 1) & val);
}

static inline tUInt8 mask8(tUInt32 n, tUInt64 val)
{
  return (tUInt8)(((1 << n) - 1) & val);
}

static inline tUInt8 mask8(tUInt32 n, const tUWide& val)
{
  return val.extract8(n-1,0);
}

// This case handles promoted values
static inline tUInt32 mask32(tUInt32 n, tSInt32 val)
{
  return (tUInt32)((n == 32) ? val : (((1 << n) - 1) & val));
}

static inline tUInt32 mask32(tUInt32 n, tUInt32 val)
{
  return (n == 32) ? val : (((1 << n) - 1) & val);
}

static inline tUInt32 mask32(tUInt32 n, tUInt64 val)
{
  return (tUInt32)(((1llu << n) - 1llu) & val);
}

static inline tUInt32 mask32(tUInt32 n, const tUWide& val)
{
  return val.extract32(n-1,0);
}

static inline tUInt64 mask64(tUInt32 n, tUInt64 val)
{
  return (n == 64) ? val : (((1llu << n) - 1llu) & val);
}

static inline tUInt64 mask64(tUInt32 n, const tUWide& val)
{
  return val.extract64(n-1,0);
}

static inline tUWide maskWide(tUInt32 n, const tUWide& val)
{
  return val.extractWide(n-1,0);
}

/* Sign testing operations used for signed relational primitives */

// This case handles promoted values
static inline bool sign_bit_set(tUInt32 data_sz, tSInt32 data)
{
  return ((data & (1 << (data_sz - 1))) != 0);
}

static inline bool sign_bit_set(tUInt32 data_sz, tUInt32 data)
{
  return ((data & (1 << (data_sz - 1))) != 0);
}

static inline bool sign_bit_set(tUInt32 data_sz, tUInt64 data)
{
  return ((data & (1llu << (data_sz - 1))) != 0llu);
}

static inline bool sign_bit_set(tUInt32 data_sz, const tUWide& data)
{
  return data.extract1(data_sz - 1);
}

/*
 * Definitions of primitive operators that
 * do not have corresponding C primitives.
 */

// forward declarations
static inline tUInt32 primShiftR32( tUInt32 result_sz
                                  , tUInt32 data_sz
                                  , tUInt32 data
                                  , tUInt32 shift_sz
                                  , tUInt32 shift
                                  );

static inline tUInt64 primShiftR64( tUInt32 result_sz
                                  , tUInt32 data_sz
                                  , tUInt64 data
                                  , tUInt32 shift_sz
                                  , tUInt32 shift
                                  );


// 8-bit primitives

static inline tUInt8 primSignExt8( tUInt32 result_sz
                                 , tUInt32 data_sz
                                 , tUInt8 data
                                 )
{
  if (sign_bit_set(data_sz, data))
  {
    /* the data is signed, so fill the upper bits with 1 */
    return mask8(result_sz, ((~0u) << data_sz) | data);
  } else {
    /* the value is unsigned, so just return it */
    return data;
  }
}

static inline tUInt8 primZeroExt8( tUInt32 result_sz
                                 , tUInt32 data_sz
                                 , tUInt8 data
                                 )
{
  return data;
}

static inline tUInt8 primShiftR8( tUInt32 result_sz
                                , tUInt32 data_sz
                                , tUInt8 data
                                , tUInt32 shift_sz
                                , tUInt8 shift
                                )
{
  if (shift < 8)
    return (data >> shift);
  else
    return 0;
}

static inline tUInt8 primShiftR8( tUInt32 result_sz
                                , tUInt32 data_sz
                                , tUInt8 data
                                , tUInt32 shift_sz
                                , tUInt32 shift
                                )
{
  if (shift < 8)
    return (data >> shift);
  else
    return 0;
}

static inline tUInt8 primShiftR8( tUInt32 result_sz
                                , tUInt32 data_sz
                                , tUInt8 data
                                , tUInt32 shift_sz
                                , tUInt64 shift
                                )
{
  if (shift < 8)
    return (data >> shift);
  else
    return 0;
}

static inline tUInt8 primShiftR8( tUInt32 result_sz
                                , tUInt32 data_sz
                                , tUInt8 data
                                , tUInt32 shift_sz
                                , const tUWide& shift
                                )
{
  tUInt32 shift32 = shift.extract32(std::min(32u,shift.size()), 0);
  if (shift.is_clear(33u) && (shift32 < 8))
    return (data >> shift32);
  else
    return 0;
}

static inline tUInt8 primShiftL8( tUInt32 result_sz
                                , tUInt32 data_sz
                                , tUInt8 data
                                , tUInt32 shift_sz
                                , tUInt8 shift
                                )
{
  if (shift < 8)
    return mask8(result_sz, data << shift);
  else
    return 0;
}

static inline tUInt8 primShiftL8( tUInt32 result_sz
                                , tUInt32 data_sz
                                , tUInt8 data
                                , tUInt32 shift_sz
                                , tUInt32 shift
                                )
{
  if (shift < 8)
    return mask8(result_sz, data << shift);
  else
    return 0;
}

static inline tUInt8 primShiftL8( tUInt32 result_sz
                                , tUInt32 data_sz
                                , tUInt8 data
                                , tUInt32 shift_sz
                                , tUInt64 shift
                                )
{
  if (shift < 8)
    return mask8(result_sz, data << shift);
  else
    return 0;
}

static inline tUInt8 primShiftL8( tUInt32 result_sz
                                , tUInt32 data_sz
                                , tUInt8 data
                                , tUInt32 shift_sz
                                , const tUWide& shift
                                )
{
  tUInt32 shift32 = shift.extract32(std::min(32u,shift.size()), 0);
  if (shift.is_clear(33u) && (shift32 < 8))
    return mask8(result_sz, data << shift32);
  else
    return 0;
}

static inline tUInt8 primShiftRA8( tUInt32 result_sz
                                 , tUInt32 data_sz
                                 , tUInt8 data
                                 , tUInt32 shift_sz
                                 , tUInt8 shift
                                 )
{
  tUInt8 tmp = 0;

  if (shift < data_sz)
  {
    tmp = primShiftR8(data_sz, data_sz, data, shift_sz, shift);
    tmp = primSignExt8(result_sz, data_sz - shift, tmp);
  }
  else if (sign_bit_set(data_sz,data))
  {
    tmp = mask8(result_sz, ~0u); // result should be all 1's
  }

  return tmp;
}

static inline tUInt8 primShiftRA8( tUInt32 result_sz
                                 , tUInt32 data_sz
                                 , tUInt8 data
                                 , tUInt32 shift_sz
                                 , tUInt32 shift
                                 )
{
  tUInt8 tmp = 0;

  if (shift < data_sz)
  {
    tmp = primShiftR8(data_sz, data_sz, data, shift_sz, shift);
    tmp = primSignExt8(result_sz, data_sz - shift, tmp);
  }
  else if (sign_bit_set(data_sz,data))
  {
    tmp = mask8(result_sz, ~0u); // result should be all 1's
  }

  return tmp;
}

static inline tUInt8 primShiftRA8( tUInt32 result_sz
                                 , tUInt32 data_sz
                                 , tUInt8 data
                                 , tUInt32 shift_sz
                                 , tUInt64 shift
                                 )
{
  tUInt8 tmp = 0;

  if (shift < data_sz)
  {
    tmp = primShiftR8(data_sz, data_sz, data, shift_sz, shift);
    tmp = primSignExt8(result_sz, data_sz - shift, tmp);
  }
  else if (sign_bit_set(data_sz,data))
  {
    tmp = mask8(result_sz, ~0u); // result should be all 1's
  }

  return tmp;
}

static inline tUInt8 primShiftRA8( tUInt32 result_sz
                                 , tUInt32 data_sz
                                 , tUInt8 data
                                 , tUInt32 shift_sz
                                 , const tUWide& shift
                                 )
{
  tUInt8 tmp = 0;

  tUInt32 shift32 = shift.extract32(std::min(32u,shift.size()), 0);
  if (shift.is_clear(33u) && (shift32 < data_sz))
  {
    tmp = primShiftR8(data_sz, data_sz, data, 32u, shift32);
    tmp = primSignExt8(result_sz, data_sz - shift32, tmp);
  }
  else if (sign_bit_set(data_sz,data))
  {
    tmp = mask8(result_sz, ~0u); // result should be all 1's
  }

  return tmp;
}

static inline tUInt8 primTrunc8( tUInt32 result_sz
                               , tUInt32 data_sz
                               , tUInt32 data
                               )
{
  return mask8(result_sz, data);
}

static inline tUInt8 primTrunc8( tUInt32 result_sz
                               , tUInt32 data_sz
                               , tUInt64 data
                               )
{
  return mask8(result_sz, data);
}

static inline tUInt8 primExtract8( tUInt32 result_sz
                                 , tUInt32 data_sz
                                 , tUInt8 data
                                 , tUInt32 high_sz
                                 , tUInt32 high
                                 , tUInt32 low_sz
                                 , tUInt32 low
                                 )
{
  tUInt8 tmp = primShiftR8(data_sz, data_sz, data, low_sz, low);
  tUInt32 mask_sz = std::min(result_sz, (high-low+1));
  return mask8(mask_sz, tmp);
}

static inline tUInt8 primExtract8( tUInt32 result_sz
                                 , tUInt32 data_sz
                                 , tUInt32 data
                                 , tUInt32 high_sz
                                 , tUInt32 high
                                 , tUInt32 low_sz
                                 , tUInt32 low
                                 )
{
  tUInt32 tmp = primShiftR32(data_sz, data_sz, data, low_sz, low);
  tUInt32 mask_sz = std::min(result_sz, (high-low+1));
  return mask8(mask_sz, tmp);
}

static inline tUInt8 primExtract8( tUInt32 result_sz
                                 , tUInt32 data_sz
                                 , tUInt64 data
                                 , tUInt32 high_sz
                                 , tUInt32 high
                                 , tUInt32 low_sz
                                 , tUInt32 low
                                 )
{
  tUInt64 tmp = primShiftR64(data_sz, data_sz, data, low_sz, low);
  tUInt32 mask_sz = std::min(result_sz, (high-low+1));
  return mask8(mask_sz, tmp);
}

static inline tUInt8 primExtract8( tUInt32 result_sz
                                 , tUInt32 data_sz
                                 , const tUWide& data
                                 , tUInt32 high_sz
                                 , tUInt32 high
                                 , tUInt32 low_sz
                                 , tUInt32 low
                                 )
{
  tUInt8 tmp = data.extract8(high,low);
  return mask8(result_sz, tmp);
}

// 32-bit primitives

static inline tUInt32 primSignExt32( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , tUInt32 data
                                   )
{
  if (sign_bit_set(data_sz, data))
  {
    /* the data is signed, so fill the upper bits with 1 */
    return mask32(result_sz, ((~0u) << (data_sz - 1)) | data);
  } else {
    /* the value is unsigned, so just return it */
    return data;
  }
}

static inline tUInt32 primZeroExt32( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , tUInt32 data
                                   )
{
  return data;
}

static inline tUInt32 primShiftR32( tUInt32 result_sz
                                  , tUInt32 data_sz
                                  , tUInt32 data
                                  , tUInt32 shift_sz
                                  , tUInt8 shift
                                  )
{
  if (shift < 32)
    return (data >> shift);
  else
    return 0;
}

static inline tUInt32 primShiftR32( tUInt32 result_sz
                                  , tUInt32 data_sz
                                  , tUInt32 data
                                  , tUInt32 shift_sz
                                  , tUInt32 shift
                                  )
{
  if (shift < 32)
    return (data >> shift);
  else
    return 0;
}

static inline tUInt32 primShiftR32( tUInt32 result_sz
                                  , tUInt32 data_sz
                                  , tUInt32 data
                                  , tUInt32 shift_sz
                                  , tUInt64 shift
                                  )
{
  if (shift < 32)
    return (data >> shift);
  else
    return 0;
}

static inline tUInt32 primShiftR32( tUInt32 result_sz
                                  , tUInt32 data_sz
                                  , tUInt32 data
                                  , tUInt32 shift_sz
                                  , const tUWide& shift
                                  )
{
  tUInt32 shift32 = shift.extract32(std::min(32u,shift.size()), 0);
  if (shift.is_clear(33u) && (shift32 < 32))
    return (data >> shift32);
  else
    return 0;
}

static inline tUInt32 primShiftL32( tUInt32 result_sz
                                  , tUInt32 data_sz
                                  , tUInt32 data
                                  , tUInt32 shift_sz
                                  , tUInt8 shift
                                  )
{
  if (shift < 32)
    return mask32(result_sz, data << shift);
  else
    return 0;
}


static inline tUInt32 primShiftL32( tUInt32 result_sz
                                  , tUInt32 data_sz
                                  , tUInt32 data
                                  , tUInt32 shift_sz
                                  , tUInt32 shift
                                  )
{
  if (shift < 32)
    return mask32(result_sz, data << shift);
  else
    return 0;
}


static inline tUInt32 primShiftL32( tUInt32 result_sz
                                  , tUInt32 data_sz
                                  , tUInt32 data
                                  , tUInt32 shift_sz
                                  , tUInt64 shift
                                  )
{
  if (shift < 32)
    return mask32(result_sz, data << shift);
  else
    return 0;
}


static inline tUInt32 primShiftL32( tUInt32 result_sz
                                  , tUInt32 data_sz
                                  , tUInt32 data
                                  , tUInt32 shift_sz
                                  , const tUWide& shift
                                  )
{
  tUInt32 shift32 = shift.extract32(std::min(32u,shift.size()), 0);
  if (shift.is_clear(33u) && (shift32 < 32))
    return mask32(result_sz, data << shift32);
  else
    return 0;
}


static inline tUInt32 primShiftRA32( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , tUInt32 data
                                   , tUInt32 shift_sz
                                   , tUInt8 shift
                                   )
{
  tUInt32 tmp = 0u;

  if (shift < data_sz)
  {
    tmp = primShiftR32(data_sz, data_sz, data, shift_sz, shift);
    tmp = primSignExt32(result_sz, data_sz - shift, tmp);
  }
  else if (sign_bit_set(data_sz,data))
  {
    tmp = mask32(result_sz, ~0u); // result should be all 1's
  }

  return tmp;
}

static inline tUInt32 primShiftRA32( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , tUInt32 data
                                   , tUInt32 shift_sz
                                   , tUInt32 shift
                                   )
{
  tUInt32 tmp = 0u;

  if (shift < data_sz)
  {
    tmp = primShiftR32(data_sz, data_sz, data, shift_sz, shift);
    tmp = primSignExt32(result_sz, data_sz - shift, tmp);
  }
  else if (sign_bit_set(data_sz,data))
  {
    tmp = mask32(result_sz, ~0u); // result should be all 1's
  }

  return tmp;
}

static inline tUInt32 primShiftRA32( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , tUInt32 data
                                   , tUInt32 shift_sz
                                   , tUInt64 shift
                                   )
{
  tUInt32 tmp = 0u;

  if (shift < data_sz)
  {
    tmp = primShiftR32(data_sz, data_sz, data, shift_sz, shift);
    tmp = primSignExt32(result_sz, data_sz - shift, tmp);
  }
  else if (sign_bit_set(data_sz,data))
  {
    tmp = mask32(result_sz, ~0u); // result should be all 1's
  }

  return tmp;
}

static inline tUInt32 primShiftRA32( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , tUInt32 data
                                   , tUInt32 shift_sz
                                   , const tUWide& shift
                                   )
{
  tUInt32 tmp = 0u;

  tUInt32 shift32 = shift.extract32(std::min(32u,shift.size()), 0);
  if (shift.is_clear(33u) && (shift32 < data_sz))
  {
    tmp = primShiftR32(data_sz, data_sz, data, 32u, shift32);
    tmp = primSignExt32(result_sz, data_sz - shift32, tmp);
  }
  else if (sign_bit_set(data_sz,data))
  {
    tmp = mask32(result_sz, ~0u); // result should be all 1's
  }

  return tmp;
}

static inline tUInt32 primTrunc32( tUInt32 result_sz
                                 , tUInt32 data_sz
                                 , tUInt32 data
                                 )
{
  return mask32(result_sz, data);
}

static inline tUInt32 primExtract32( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , tUInt8 data
                                   , tUInt32 high_sz
                                   , tUInt32 high
                                   , tUInt32 low_sz
                                   , tUInt32 low
                                   )
{
  tUInt32 tmp = primShiftR32(data_sz, data_sz, (tUInt32)data, low_sz, low);
  tUInt32 mask_sz = std::min(result_sz, (high-low+1));
  return mask32(mask_sz, tmp);
}

static inline tUInt32 primExtract32( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , tUInt32 data
                                   , tUInt32 high_sz
                                   , tUInt32 high
                                   , tUInt32 low_sz
                                   , tUInt32 low
                                   )
{
  tUInt32 tmp = primShiftR32(data_sz, data_sz, data, low_sz, low);
  tUInt32 mask_sz = std::min(result_sz, (high-low+1));
  return mask32(mask_sz, tmp);
}

static inline tUInt32 primExtract32( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , tUInt64 data
                                   , tUInt32 high_sz
                                   , tUInt32 high
                                   , tUInt32 low_sz
                                   , tUInt32 low
                                   )
{
  tUInt64 tmp = primShiftR64(data_sz, data_sz, data, low_sz, low);
  tUInt32 mask_sz = std::min(result_sz, (high-low+1));
  return mask32(mask_sz, tmp);
}

static inline tUInt32 primExtract32( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , const tUWide& data
                                   , tUInt32 high_sz
                                   , tUInt32 high
                                   , tUInt32 low_sz
                                   , tUInt32 low
                                   )
{
  tUInt32 tmp = data.extract32(high,low);
  return mask32(result_sz, tmp);
}

// 64-bit primitives

static inline tUInt64 primSignExt64( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , tUInt64 data
                                   )
{
  if (sign_bit_set(data_sz, data))
  {
    /* the data is signed, so fill the upper bits with 1 */
    return mask64(result_sz, ((~0llu) << (data_sz - 1)) | data);
  } else {
    /* the value is unsigned, so just return it */
    return data;
  }
}

static inline tUInt64 primZeroExt64( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , tUInt64 data
                                   )
{
  return data;
}

static inline tUInt64 primShiftR64( tUInt32 result_sz
                                  , tUInt32 data_sz
                                  , tUInt64 data
                                  , tUInt32 shift_sz
                                  , tUInt8 shift
                                  )
{
  if (shift < 64)
    return (data >> shift);
  else
    return 0;
}

static inline tUInt64 primShiftR64( tUInt32 result_sz
                                  , tUInt32 data_sz
                                  , tUInt64 data
                                  , tUInt32 shift_sz
                                  , tUInt32 shift
                                  )
{
  if (shift < 64)
    return (data >> shift);
  else
    return 0;
}

static inline tUInt64 primShiftR64( tUInt32 result_sz
                                  , tUInt32 data_sz
                                  , tUInt64 data
                                  , tUInt32 shift_sz
                                  , tUInt64 shift
                                  )
{
  if (shift < 64)
    return (data >> shift);
  else
    return 0;
}

static inline tUInt64 primShiftR64( tUInt32 result_sz
                                  , tUInt32 data_sz
                                  , tUInt64 data
                                  , tUInt32 shift_sz
                                  , const tUWide& shift
                                  )
{
  tUInt32 shift32 = shift.extract32(std::min(32u,shift.size()), 0);
  if (shift.is_clear(33u) && (shift32 < 64))
    return (data >> shift32);
  else
    return 0;
}

static inline tUInt64 primShiftL64( tUInt32 result_sz
                                  , tUInt32 data_sz
                                  , tUInt64 data
                                  , tUInt32 shift_sz
                                  , tUInt8 shift
                                  )
{
  if (shift < 64)
    return mask64(result_sz, data << shift);
  else
    return 0;
}

static inline tUInt64 primShiftL64( tUInt32 result_sz
                                  , tUInt32 data_sz
                                  , tUInt64 data
                                  , tUInt32 shift_sz
                                  , tUInt32 shift
                                  )
{
  if (shift < 64)
    return mask64(result_sz, data << shift);
  else
    return 0;
}

static inline tUInt64 primShiftL64( tUInt32 result_sz
                                  , tUInt32 data_sz
                                  , tUInt64 data
                                  , tUInt32 shift_sz
                                  , tUInt64 shift
                                  )
{
  if (shift < 64)
    return mask64(result_sz, data << shift);
  else
    return 0;
}

static inline tUInt64 primShiftL64( tUInt32 result_sz
                                  , tUInt32 data_sz
                                  , tUInt64 data
                                  , tUInt32 shift_sz
                                  , const tUWide& shift
                                  )
{
  tUInt32 shift32 = shift.extract32(std::min(32u,shift.size()), 0);
  if (shift.is_clear(33u) && (shift32 < 64))
    return mask64(result_sz, data << shift32);
  else
    return 0;
}

static inline tUInt64 primShiftRA64( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , tUInt64 data
                                   , tUInt32 shift_sz
                                   , tUInt8 shift
                                   )
{
  tUInt64 tmp = 0llu;

  if (shift < data_sz)
  {
    tmp = primShiftR64(data_sz, data_sz, data, shift_sz, shift);
    tmp = primSignExt64(result_sz, data_sz - shift, tmp);
  }
  else if (sign_bit_set(data_sz,data))
  {
    tmp = mask64(result_sz, ~0llu); // result should be all 1's
  }

  return tmp;
}

static inline tUInt64 primShiftRA64( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , tUInt64 data
                                   , tUInt32 shift_sz
                                   , tUInt32 shift
                                   )
{
  tUInt64 tmp = 0llu;

  if (shift < data_sz)
  {
    tmp = primShiftR64(data_sz, data_sz, data, shift_sz, shift);
    tmp = primSignExt64(result_sz, data_sz - shift, tmp);
  }
  else if (sign_bit_set(data_sz,data))
  {
    tmp = mask64(result_sz, ~0llu); // result should be all 1's
  }

  return tmp;
}

static inline tUInt64 primShiftRA64( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , tUInt64 data
                                   , tUInt32 shift_sz
                                   , tUInt64 shift
                                   )
{
  tUInt64 tmp = 0llu;

  if (shift < data_sz)
  {
    tmp = primShiftR64(data_sz, data_sz, data, shift_sz, shift);
    tmp = primSignExt64(result_sz, data_sz - shift, tmp);
  }
  else if (sign_bit_set(data_sz,data))
  {
    tmp = mask64(result_sz, ~0llu); // result should be all 1's
  }

  return tmp;
}

static inline tUInt64 primShiftRA64( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , tUInt64 data
                                   , tUInt32 shift_sz
                                   , const tUWide& shift
                                   )
{
  tUInt64 tmp = 0llu;

  tUInt32 shift32 = shift.extract32(std::min(32u,shift.size()), 0);
  if (shift.is_clear(33u) && (shift32 < data_sz))
  {
    tmp = primShiftR64(data_sz, data_sz, data, 32u, shift32);
    tmp = primSignExt64(result_sz, data_sz - shift32, tmp);
  }
  else if (sign_bit_set(data_sz,data))
  {
    tmp = mask64(result_sz, ~0llu); // result should be all 1's
  }

  return tmp;
}

static inline tUInt64 primTrunc64( tUInt32 result_sz
                                 , tUInt32 data_sz
                                 , tUInt64 data
                                 )
{
  return mask64(result_sz, data);
}

static inline tUInt64 primExtract64( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , tUInt64 data
                                   , tUInt32 high_sz
                                   , tUInt32 high
                                   , tUInt32 low_sz
                                   , tUInt32 low
                                   )
{
  tUInt64 tmp = primShiftR64(data_sz, data_sz, data, low_sz, low);
  tUInt32 mask_sz = std::min(result_sz, (high-low+1));
  return mask64(mask_sz, tmp);
}

static inline tUInt64 primExtract64( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , const tUWide& data
                                   , tUInt32 high_sz
                                   , tUInt32 high
                                   , tUInt32 low_sz
                                   , tUInt32 low
                                   )
{
  tUInt64 tmp = data.extract64(high,low);
  return mask64(result_sz, tmp);
}

// Wide primitives


static inline tUWide primSignExtWide( tUInt32 result_sz
                                    , tUInt32 data_sz
                                    , const tUWide& data
                                    )
{
  tUWide result(result_sz, NUM_WORDS(result_sz));
  result.copy(data);

  if (sign_bit_set(data_sz, data))
    result.set(data_sz);
  else
    result.clear(data_sz);
  return result;
}

static inline tUWide primSignExtWide( tUInt32 result_sz
                                    , tUInt32 data_sz
                                    , tUInt64 data
                                    )
{
  tUWide result(result_sz, NUM_WORDS(result_sz));
  unsigned int buf[2];
  buf[0] = (unsigned int) data;
  buf[1] = (unsigned int) (data >> 32);
  result.write(buf, data_sz, 0);
  if (sign_bit_set(data_sz, data))
    result.set(data_sz);
  else
    result.clear(data_sz);
  return result;
}

static inline tUWide primZeroExtWide( tUInt32 result_sz
                                    , tUInt32 data_sz
                                    , const tUWide& data
                                    )
{
  tUWide result(result_sz, NUM_WORDS(result_sz));
  result.copy(data);
  result.clear(data_sz);
  return result;
}

static inline tUWide primZeroExtWide( tUInt32 result_sz
                                    , tUInt32 data_sz
                                    , tUInt64 data
                                    )
{
  tUWide result(result_sz, NUM_WORDS(result_sz));
  unsigned int buf[2];
  buf[0] = (unsigned int) data;
  buf[1] = (unsigned int) (data >> 32);
  result.write(buf, data_sz, 0);
  result.clear(data_sz);
  return result;
}

static inline tUWide primShiftRWide( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , const tUWide& data
                                   , tUInt32 shift_sz
                                   , tUInt8 shift
                                   )
{
  return data >> shift;  // wide data >> operator handles guarding
}

static inline tUWide primShiftRWide( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , const tUWide& data
                                   , tUInt32 shift_sz
                                   , tUInt32 shift
                                   )
{
  return data >> shift;  // wide data >> operator handles guarding
}

static inline tUWide primShiftRWide( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , const tUWide& data
                                   , tUInt32 shift_sz
                                   , tUInt64 shift
                                   )
{
  if (shift < data_sz) {
    return data >> shift;  // wide data >> operator handles guarding
  } else {
    WideData result(result_sz, NUM_WORDS(result_sz));
    result.clear();
    return result;
  }
}

static inline tUWide primShiftRWide( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , const tUWide& data
                                   , tUInt32 shift_sz
                                   , const tUWide& shift
                                   )
{
  tUInt32 shift32 = shift.extract32(std::min(32u,shift.size()), 0);
  if (shift.is_clear(33u) && (shift32 < data_sz)) {
    return data >> shift32;  // wide data >> operator handles guarding
  } else {
    WideData result(result_sz, NUM_WORDS(result_sz));
    result.clear();
    return result;
  }
}

static inline tUWide primShiftLWide( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , const tUWide& data
                                   , tUInt32 shift_sz
                                   , tUInt8 shift
                                   )
{
  // wide data << operator handles guarding
  return maskWide(result_sz, data << shift);
}

static inline tUWide primShiftLWide( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , const tUWide& data
                                   , tUInt32 shift_sz
                                   , tUInt32 shift
                                   )
{
  // wide data << operator handles guarding
  return maskWide(result_sz, data << shift);
}

static inline tUWide primShiftLWide( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , const tUWide& data
                                   , tUInt32 shift_sz
                                   , tUInt64 shift
                                   )
{
  if (shift < data_sz) {
    // wide data << operator handles guarding
    return maskWide(result_sz, data << shift);
  } else {
    WideData result(result_sz, NUM_WORDS(result_sz));
    result.clear();
    return result;
  }
}

static inline tUWide primShiftLWide( tUInt32 result_sz
                                   , tUInt32 data_sz
                                   , const tUWide& data
                                   , tUInt32 shift_sz
                                   , const tUWide& shift
                                   )
{
  tUInt32 shift32 = shift.extract32(std::min(32u,shift.size()), 0);
  if (shift.is_clear(33u) && (shift32 < data_sz)) {
    // wide data << operator handles guarding
    return maskWide(result_sz, data << shift32);
  } else {
    WideData result(result_sz, NUM_WORDS(result_sz));
    result.clear();
    return result;
  }
}

static inline tUWide primShiftRAWide( tUInt32 result_sz
                                    , tUInt32 data_sz
                                    , const tUWide& data
                                    , tUInt32 shift_sz
                                    , tUInt8 shift
                                    )
{
  if (shift < data_sz)
    return primSignExtWide(result_sz, data_sz - shift, data >> shift);
  else
  {
    tUWide tmp;
    tmp.setSize(result_sz);
    if (sign_bit_set(data_sz, data))
      tmp.set();
    else
      tmp.clear();
    return tmp;
  }
}

static inline tUWide primShiftRAWide( tUInt32 result_sz
                                    , tUInt32 data_sz
                                    , const tUWide& data
                                    , tUInt32 shift_sz
                                    , tUInt32 shift
                                    )
{
  if (shift < data_sz)
    return primSignExtWide(result_sz, data_sz - shift, data >> shift);
  else
  {
    tUWide tmp;
    tmp.setSize(result_sz);
    if (sign_bit_set(data_sz, data))
      tmp.set();
    else
      tmp.clear();
    return tmp;
  }
}

static inline tUWide primShiftRAWide( tUInt32 result_sz
                                    , tUInt32 data_sz
                                    , const tUWide& data
                                    , tUInt32 shift_sz
                                    , tUInt64 shift
                                    )
{
  if (shift < data_sz)
    return primSignExtWide(result_sz, data_sz - shift, data >> shift);
  else
  {
    tUWide tmp;
    tmp.setSize(result_sz);
    if (sign_bit_set(data_sz, data))
      tmp.set();
    else
      tmp.clear();
    return tmp;
  }
}

static inline tUWide primShiftRAWide( tUInt32 result_sz
                                    , tUInt32 data_sz
                                    , const tUWide& data
                                    , tUInt32 shift_sz
                                    , const tUWide& shift
                                    )
{
  tUInt32 shift32 = shift.extract32(std::min(32u,shift.size()), 0);
  if (shift.is_clear(33u) && (shift32 < data_sz))
    return primSignExtWide(result_sz, data_sz - shift32, data >> shift32);
  else
  {
    tUWide tmp;
    tmp.setSize(result_sz);
    if (sign_bit_set(data_sz, data))
      tmp.set();
    else
      tmp.clear();
    return tmp;
  }
}

static inline tUWide primTruncWide( tUInt32 result_sz
                                  , tUInt32 data_sz
                                  , const tUWide& data
                                  )
{
  return maskWide(result_sz, data);
}

static inline tUWide primExtractWide( tUInt32 result_sz
                                    , tUInt32 data_sz
                                    , tUInt8 data
                                    , tUInt32 high_sz
                                    , tUInt32 high
                                    , tUInt32 low_sz
                                    , tUInt32 low
                                    )
{
  WideData dataW(data_sz, (tUInt32)data);
  return dataW.extractWide(high,low);
}

static inline tUWide primExtractWide( tUInt32 result_sz
                                    , tUInt32 data_sz
                                    , tUInt32 data
                                    , tUInt32 high_sz
                                    , tUInt32 high
                                    , tUInt32 low_sz
                                    , tUInt32 low
                                    )
{
  WideData dataW(data_sz, data);
  return dataW.extractWide(high,low);
}

static inline tUWide primExtractWide( tUInt32 result_sz
                                    , tUInt32 data_sz
                                    , tUInt64 data
                                    , tUInt32 high_sz
                                    , tUInt32 high
                                    , tUInt32 low_sz
                                    , tUInt32 low
                                    )
{
  WideData dataW(data_sz, data);
  return dataW.extractWide(high,low);
}

static inline tUWide primExtractWide( tUInt32 result_sz
                                    , tUInt32 data_sz
                                    , const tUWide& data
                                    , tUInt32 high_sz
                                    , tUInt32 high
                                    , tUInt32 low_sz
                                    , tUInt32 low
                                    )
{
  return data.extractWide(high,low);
}

// Signed relational operators

static inline bool primSLT8( tUInt32 result_sz
                           , tUInt32 data1_sz
                           , tUInt8 data1
                           , tUInt32 data2_sz
                           , tUInt8 data2
                           )
{
  if (sign_bit_set(data1_sz, data1) == sign_bit_set(data2_sz, data2))
  {
    return (data1 < data2);
  } else {
    return sign_bit_set(data1_sz, data1);
  }
}

static inline bool primSLE8( tUInt32 result_sz
                           , tUInt32 data1_sz
                           , tUInt8 data1
                           , tUInt32 data2_sz
                           , tUInt8 data2
                           )
{
  if (sign_bit_set(data1_sz, data1) == sign_bit_set(data2_sz, data2))
  {
    return (data1 <= data2);
  } else {
    return sign_bit_set(data1_sz, data1);
  }
}

static inline bool primSLT8( tUInt32 result_sz
                           , tUInt32 data1_sz
                           , tUInt32 data1
                           , tUInt32 data2_sz
                           , tUInt32 data2
                           )
{
  if (sign_bit_set(data1_sz, data1) == sign_bit_set(data2_sz, data2))
  {
    return (data1 < data2);
  } else {
    return sign_bit_set(data1_sz, data1);
  }
}

static inline bool primSLE8( tUInt32 result_sz
                           , tUInt32 data1_sz
                           , tUInt32 data1
                           , tUInt32 data2_sz
                           , tUInt32 data2
                           )
{
  if (sign_bit_set(data1_sz, data1) == sign_bit_set(data2_sz, data2))
  {
    return (data1 <= data2);
  } else {
    return sign_bit_set(data1_sz, data1);
  }
}

static inline bool primSLT8( tUInt32 result_sz
                           , tUInt32 data1_sz
                           , tUInt64 data1
                           , tUInt32 data2_sz
                           , tUInt64 data2
                           )
{
  if (sign_bit_set(data1_sz, data1) == sign_bit_set(data2_sz, data2))
  {
    return (data1 < data2);
  } else {
    return sign_bit_set(data1_sz, data1);
  }
}

static inline bool primSLE8( tUInt32 result_sz
                           , tUInt32 data1_sz
                           , tUInt64 data1
                           , tUInt32 data2_sz
                           , tUInt64 data2
                           )
{
  if (sign_bit_set(data1_sz, data1) == sign_bit_set(data2_sz, data2))
  {
    return (data1 <= data2);
  } else {
    return sign_bit_set(data1_sz, data1);
  }
}

static inline bool primSLT8( tUInt32 result_sz
                           , tUInt32 data1_sz
                           , const tUWide& data1
                           , tUInt32 data2_sz
                           , const tUWide& data2
                           )
{
  if (sign_bit_set(data1_sz, data1) == sign_bit_set(data2_sz, data2))
  {
    return (data1 < data2);
  } else {
    return sign_bit_set(data1_sz, data1);
  }
}

static inline bool primSLE8( tUInt32 result_sz
                           , tUInt32 data1_sz
                           , const tUWide& data1
                           , tUInt32 data2_sz
                           , const tUWide& data2
                           )
{
  if (sign_bit_set(data1_sz, data1) == sign_bit_set(data2_sz, data2))
  {
    return (data1 <= data2);
  } else {
    return sign_bit_set(data1_sz, data1);
  }
}

/* prim function calls which originally return wide-data, now take the
   return address as the last parameter*/
static inline void wop_primSignExtWide( unsigned int result_sz,
                                        unsigned int data_sz,
                                        const tUWide& data, tUWide& result)
{
  result.copy(data);

  if (sign_bit_set(data_sz, data))
    result.set(data_sz);
  else
    result.clear(data_sz);
}

static inline void wop_primSignExtWide( unsigned int result_sz,
                                        unsigned int data_sz,
                                        unsigned long long data,
                                        tUWide& result)
{
  unsigned int buf[2];
  buf[0] = (unsigned int) data;
  buf[1] = (unsigned int) (data >> 32);
  result.write(buf, data_sz, 0);
  if (sign_bit_set(data_sz, data))
    result.set(data_sz);
  else
    result.clear(data_sz);
}

static inline void wop_primZeroExtWide( unsigned int result_sz,
                                   unsigned int data_sz,
                                   const tUWide& data, tUWide& result)
{
  result.copy(data);
  result.clear(data_sz);
}

static inline void wop_primZeroExtWide( unsigned int result_sz,
                                   unsigned int data_sz,
                                   unsigned long long data, tUWide& result)
{
  unsigned int buf[2];
  buf[0] = (unsigned int) data;
  buf[1] = (unsigned int) (data >> 32);
  result.write(buf, data_sz, 0);
  result.clear(data_sz);
}

static inline void wop_primShiftRWide( unsigned int result_sz, unsigned int data_sz,
                                  const tUWide& data, unsigned int shift_sz,
                                  unsigned char shift, tUWide& result)
{
  wop_srl(data, shift, result);
}

static inline void wop_primShiftRWide( unsigned int result_sz, unsigned int data_sz,
                                  const tUWide& data, unsigned int shift_sz,
                                  unsigned int shift, tUWide& result)
{
  wop_srl(data, shift, result);
}

static inline void wop_primShiftRWide( unsigned int result_sz, unsigned int data_sz,
                                  const tUWide& data, unsigned int shift_sz,
                                  unsigned long long shift, tUWide& result)
{
  if (shift < data_sz)
    wop_srl(data, shift, result);
  else
    result.clear();
}

static inline void wop_primShiftRWide( unsigned int result_sz, unsigned int data_sz,
                                  const tUWide& data, unsigned int shift_sz,
                                  const tUWide& shift, tUWide& result)
{
  tUInt32 shift32 = shift.extract32(std::min(32u,shift.size()), 0);
  if (shift.is_clear(33u) && (shift32 < data_sz))
    wop_srl(data, shift32, result);
  else
    result.clear();
}

static inline void wop_primShiftLWide( unsigned int result_sz,
                                       unsigned int data_sz,
                                       const tUWide& data,
                                       unsigned int shift_sz,
                                       unsigned char shift, tUWide& result)
{
  wop_sl(data, shift, result);
}

static inline void wop_primShiftLWide( unsigned int result_sz,
                                       unsigned int data_sz,
                                       const tUWide& data,
                                       unsigned int shift_sz,
                                       unsigned int shift, tUWide& result)
{
  wop_sl(data, shift, result);
}

static inline void wop_primShiftLWide( unsigned int result_sz,
                                       unsigned int data_sz,
                                       const tUWide& data,
                                       unsigned int shift_sz,
                                       unsigned long long shift, tUWide& result)
{
  if (shift < data_sz)
    wop_sl(data, shift, result);
  else
    result.clear();
}

static inline void wop_primShiftLWide( unsigned int result_sz,
                                       unsigned int data_sz,
                                       const tUWide& data,
                                       unsigned int shift_sz,
                                       const tUWide& shift, tUWide& result)
{
  tUInt32 shift32 = shift.extract32(std::min(32u,shift.size()), 0);
  if (shift.is_clear(33u) && (shift32 < data_sz))
    wop_sl(data, shift32, result);
  else
    result.clear();
}

static inline void wop_primShiftRAWide( unsigned int result_sz,
                                        unsigned int data_sz,
                                        const tUWide& data,
                                        unsigned int shift_sz,
                                        unsigned char shift, tUWide& result)
{
  if (shift < data_sz)
    wop_primSignExtWide(result_sz, data_sz - shift, data >> shift, result);
  else
  {
    if (sign_bit_set(data_sz, data))
      result.set();
    else
      result.clear();
  }
}

static inline void wop_primShiftRAWide( unsigned int result_sz,
                                        unsigned int data_sz,
                                        const tUWide& data,
                                        unsigned int shift_sz,
                                        unsigned int shift, tUWide& result)
{
  if (shift < data_sz)
    wop_primSignExtWide(result_sz, data_sz - shift, data >> shift, result);
  else
  {
    if (sign_bit_set(data_sz, data))
      result.set();
    else
      result.clear();
  }
}

static inline void wop_primShiftRAWide( unsigned int result_sz,
                                        unsigned int data_sz,
                                        const tUWide& data,
                                        unsigned int shift_sz,
                                        unsigned long long shift, tUWide& result)
{
  if (shift < data_sz)
    wop_primSignExtWide(result_sz, data_sz - shift, data >> shift, result);
  else
  {
    if (sign_bit_set(data_sz, data))
      result.set();
    else
      result.clear();
  }
}

static inline void wop_primShiftRAWide( unsigned int result_sz,
                                        unsigned int data_sz,
                                        const tUWide& data,
                                        unsigned int shift_sz,
                                        const tUWide& shift, tUWide& result)
{
  tUInt32 shift32 = shift.extract32(std::min(32u,shift.size()), 0);
  if (shift.is_clear(33u) && (shift32 < data_sz))
    wop_primSignExtWide(result_sz, data_sz - shift32, data >> shift32, result);
  else
  {
    if (sign_bit_set(data_sz, data))
      result.set();
    else
      result.clear();
  }
}

static inline void wop_primExtractWide(unsigned int dst_sz,
                                       unsigned int src_sz,
                                       tUInt8 src,
                                       unsigned int high_sz, unsigned int high,
                                       unsigned int low_sz, unsigned int low,
                                       tUWide &dst)
{
  WideData srcW(src_sz, (tUInt32)src);
  srcW.wop_extractWide(high, low, dst);
}

static inline void wop_primExtractWide(unsigned int dst_sz,
                                       unsigned int src_sz,
                                       tUInt32 src,
                                       unsigned int high_sz, unsigned int high,
                                       unsigned int low_sz, unsigned int low,
                                       tUWide &dst)
{
  WideData srcW(src_sz, src);
  srcW.wop_extractWide(high, low, dst);
}

static inline void wop_primExtractWide(unsigned int dst_sz,
                                       unsigned int src_sz,
                                       tUInt64 src,
                                       unsigned int high_sz, unsigned int high,
                                       unsigned int low_sz, unsigned int low,
                                       tUWide &dst)
{
  WideData srcW(src_sz, src);
  srcW.wop_extractWide(high, low, dst);
}

static inline void wop_primExtractWide(unsigned int dst_sz,
                                       unsigned int src_sz,
                                       const tUWide & src,
                                       unsigned int high_sz, unsigned int high,
                                       unsigned int low_sz, unsigned int low,
                                       tUWide &dst)
{
  src.wop_extractWide(high, low, dst);
}

/* Routines for managing copies of arguments to foreign functions */

// Copy a value into a temporary array
unsigned int* copy_arg(const tUInt8* data, unsigned int n = 1);
unsigned int* copy_arg(const tUInt32* data);
unsigned int* copy_arg(const tUInt64* data, unsigned int n = 2);
unsigned int* copy_arg(const unsigned int* data, unsigned int n);
char* copy_arg(const std::string& str);

// Allocate an uninitialized temporary array
unsigned int* ignore_arg(unsigned int n);
unsigned int* return_arg(unsigned int n);

// Copy data from a return_arg call into the return data location
tUInt8  write_return(unsigned int unused, tUInt8* data);
tUInt32 write_return(unsigned int unused, tUInt32* data);
tUInt64 write_return(unsigned int unused, tUInt64* data);

// Delete all of the currently allocated argument copies
void delete_arg_copies();


#endif /* __BS_PRIM_OPS__ */
