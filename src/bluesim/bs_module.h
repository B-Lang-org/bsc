#ifndef __BS_MODULE_H__
#define __BS_MODULE_H__

#include "bluesim_types.h"
#include "bs_symbol.h"
#include "bs_target.h"

/* Utility functions used for dumping rule firings */
void print_rule_label(unsigned int indent, const char* text);
void print_rule(const char* name, bool could_fire, bool did_fire);

/* This is the base class for all modules, including primitives.
 * It contains just a small amount of book-keeping information
 * that all modules need.  It is important that this base class
 * not get bloated and not contain any virtual functions.
 */

class Module
{
 public:
  Module(tSimStateHdl simHdl, const char* name, Module* parent_module);
  ~Module();

  void write_name(Target* dest) const;
  tSymbol lookup(const char* key, unsigned int len) const;
  unsigned int num_symbols() const;
  tSymbol nth_symbol(unsigned int n) const;

 public:
  Module*     parent;
  const char* inst_name;

  tSimStateHdl sim_hdl;

 protected:
  unsigned int vcd_num;
  unsigned int symbol_count;
  tSymbol      symbols;
};

#endif /* __BS_MODULE_H__ */
