#include "bs_symbol.h"
#include "bs_wide_data.h"

/* API functions */
extern "C" const char* bk_get_key(tSymbol sym);
extern "C" tUInt32 bk_get_size(tSymbol sym);
extern "C" void* bk_get_ptr(tSymbol sym);

/* Get the key for a symbol */
const char* bk_get_key(tSymbol sym)
{
  if (sym != BAD_SYMBOL)
    return sym->key;
  else
    return NULL;
}

/* Get the size for a symbol */
tUInt32 bk_get_size(tSymbol sym)
{
  if (sym != BAD_SYMBOL)
    return (sym->info >> 4);
  else
    return 0;
}

/* Get the void* value for a symbol */
void* bk_get_ptr(tSymbol sym)
{
  if (sym != BAD_SYMBOL)
    return sym->value;
  else
    return NULL;
}

/* Get the tag for a symbol */
tSymTag get_symtag(tSymbol sym)
{
  if (sym != BAD_SYMBOL)
    return (tSymTag)(sym->info & 0xf);
  else
    return SYM_UNKNOWN;
}

/* Get a pointer to the data for a symbol value */
const unsigned int* symbol_value(void* ptr, unsigned int sz)
{
  if (sz <= 64)
    return (const unsigned int*) ptr;
  else
    return (const unsigned int*) (((WideData*)ptr)->data);
}

/* Initialize a tSym structure */
void init_symbol(tSym* symptr, const char* key, tSymTag tag,
		 void* value, unsigned int sz)
{
  symptr->key = key;
  symptr->info = tag | (sz << 4);
  symptr->value = value;
}
