#ifndef __BLUESIM_TYPES_H__
#define __BLUESIM_TYPES_H__

#include <time.h>

/*
 * Definition of types used by the Bluesim API
 */

#if __cplusplus
extern "C" {
#endif

/* The type used to hold Bluesim version information
 */
typedef struct
{
  const char*  name;          /* release name */
  const char*  build;         /* build identifier */
  time_t       creation_time; /* time at which the model was generated */
} tBluesimVersionInfo;

/* Type used to represent a boolean value (0 = False, >0 = True) */
typedef unsigned char tBool;

/* Type used to represent status codes (<0 = error, >= 0 = success) */
typedef int tStatus;
#define BK_ERROR   (-1)
#define BK_SUCCESS   0

/* Types used for 32/64-bit portability */
typedef unsigned char      tUInt8;
typedef   signed char      tSInt8;
typedef unsigned int       tUInt32;
typedef   signed int       tSInt32;
typedef unsigned long long tUInt64;
typedef   signed long long tSInt64;

/* The type used to represent simulation time */
typedef tUInt64 tTime;

/* Handle type used to refer to clocks */
typedef unsigned int tClock;
#define BAD_CLOCK_HANDLE ((tClock)~0)

/* Type used to represent clock values */
typedef enum { CLK_LOW=0, CLK_HIGH=1 } tClockValue;

/* Type used to represent clock transitions */
typedef enum { NEGEDGE=0, POSEDGE=1 } tEdgeDirection;

/* Opaque symbol handle type */
struct tSym;
typedef struct tSym* tSymbol;
#define BAD_SYMBOL ((tSymbol)NULL)

/*
 * Opaque handle to the kernel state
 */
struct tSimState;
typedef struct tSimState * tSimStateHdl;

/*
 * Opaque handle to a design, for the kernel to manipulate the model
 */
typedef void* tModel;

/* A schedule function, an action executed on the edge
 * of a clock.  It takes handles to the kernel state and
 * to the top-level instance as arguments.
 */
typedef void (*tScheduleFn)(tSimStateHdl, void*);

/* A reset function is a function which is executed when a
 * reset is asserted or deasserted.
 */
typedef void (*tResetFn)(void*, tUInt8);

/* A user interface function is called when the kernel
 * wishes to yield to the user interface.
 */
typedef tTime (*tUIFn)(void*);

#if __cplusplus
} /* extern "C" */
#endif

#endif /* __BLUESIM_TYPES_H__ */
