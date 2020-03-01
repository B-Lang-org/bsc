#ifndef __BS_SYMBOL_H__
#define __BS_SYMBOL_H__

#include "bluesim_types.h"

/* Type used to tag a symbol's void* to indicate what it points at */
typedef unsigned char tSymTag;

#define SYM_UNKNOWN  0
#define SYM_MODULE   1
#define SYM_DEF      2
#define SYM_PARAM    3
#define SYM_PORT     4
#define SYM_RULE     5
#define SYM_RANGE    6
#define SYM_COMPUTED 7

/* Symbol information structure */
struct tSym
{
  const char*  key;
  unsigned int info;   /* contains tag and size */
  void*        value;
};

/* Range structure */
typedef struct
{
  tUInt64 lo;
  tUInt64 hi;
  void* base;
  const unsigned int* (*fetch)(void* base, tUInt64 addr);
} Range;

/* Internal functions */
void init_symbol(tSym* symptr, const char* key, tSymTag tag,
		 void* value = NULL, unsigned int sz = 0);
tSymTag get_symtag(tSymbol sym);
const unsigned int* symbol_value(void* ptr, unsigned int sz);

#endif /* __BS_SYMBOL_H__ */
