#include <cstring>
#include <ctype.h>

#include "bs_module.h"
#include "kernel.h"

/* Utility functions used for dumping rule firings */

// save state needed to print label
void print_rule_label(tSimStateHdl simHdl,
		      unsigned int indent, const char* text)
{
  tLabel label;
  label.indent = indent;
  label.text = text;

  while ((! simHdl->labels.empty()) &&
	 (simHdl->labels.back().indent >= indent))
    simHdl->labels.pop_back();

  simHdl->labels.push_back(label);
  simHdl->rule_name_indent = indent + 2;
}

// print rule
// print labels only if this is the first one since the label was given
void print_rule(tSimStateHdl simHdl,
		const char* name, bool could_fire, bool did_fire)
{
  if (!could_fire)
    return;

  while (! simHdl->labels.empty())
  {
    const tLabel& label = simHdl->labels.front();
    printf("%*s%s:\n", label.indent, "", label.text);
    simHdl->labels.pop_front();
  }
  const char* msg = did_fire ? "fired" : "inhibited by more urgent rule";
  printf("%*s%s %s\n", simHdl->rule_name_indent, "", name, msg);  
}


/* Perform a binary search on a table of tSym structures, in sorted
 * order according to the key.  The return value is the index of 
 * the structure in the table, or -1 if it is not found.
 */

static int match_key(const char* key, const char* str, unsigned int len)
{
  char k,s;
  while (1)
  {    
    k = (len-- == 0) ? '\0' : *(key++);
    s = *(str++);
    if (k == '\0')
      return (s == '\0') ? 0 : -1;
    else if (s == '\0')
      return +1;
    else if (tolower(k) < tolower(s))
      return -1;
    else if (tolower(k) > tolower(s))
      return +1;
    else if (k < s)
      return -1;
    else if (k > s)
      return +1;
  }

  return 0;
}

static int bin_search(tSym table[], unsigned int size,
		      const char* key, unsigned int len)
{
  if ((table == NULL) || (size == 0))
    return -1;
  unsigned int lo = 0;
  unsigned int hi = size - 1;
  do {
    unsigned int mid = (lo + hi)/2;
    int cmp = match_key(key, table[mid].key, len);
    if (cmp < 0)
    {
      /* key is below mid */
      hi = mid;
    }
    else if (cmp > 0)
    {
      /* key is above mid */
      if (lo == mid)
      {
	/* hi is only remaining possibility */
	if (!match_key(key, table[hi].key, len))
	  return hi;  /* matched hi */
	else
	  return -1; /* no match */
      }
      lo = mid;      
    }
    else
    {
      /* exact match at mid */
      return mid; 
    }
  } while (hi != lo);
  return -1;  /* search terminated without finding key */
}

/* Module class method implementations */

Module::Module(tSimStateHdl hdl, const char* name, Module* parent_module)
  : parent(parent_module), inst_name(name), sim_hdl(hdl),
    vcd_num(0), symbol_count(0), symbols(NULL)
{  
}

Module::~Module()
{
  delete[] symbols;
}

void Module::write_name(Target* dest) const
{
  if (parent != NULL)
  {
    parent->write_name(dest);
    dest->write_char('.');
  }
  dest->write_data(inst_name,sizeof(char),strlen(inst_name));
}

/* Lookup a symbol in this module by name.  The name consists
 * of the first 'len' characters of 'key'.  If the named entry
 * is found a pointer to it is returned, otherwise BAD_SYMBOL
 * is returned.
 */
tSymbol Module::lookup(const char* key, unsigned int len) const
{
  int n = bin_search(symbols, symbol_count, key, len);
  if (n < 0)
    return BAD_SYMBOL;
  else
    return &(symbols[n]);
}

/* Get the number of symbols in this module */
unsigned int Module::num_symbols() const
{
  return symbol_count;
}

/* Get the nth symbol in the module, counting from 0 */
tSymbol Module::nth_symbol(unsigned int n) const
{
  if (n < symbol_count)
    return &(symbols[n]);
  else
    return BAD_SYMBOL;
}
