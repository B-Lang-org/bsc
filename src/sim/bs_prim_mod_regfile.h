#ifndef __BS_PRIM_MOD_REGFILE_H__
#define __BS_PRIM_MOD_REGFILE_H__

#include <cstdio>
#include <string>

#include "bluesim_kernel_api.h"
#include "bluesim_probes.h"
#include "bs_mem_file.h"
#include "bs_module.h"
#include "bs_vcd.h"
#include "bs_range_tracker.h"

// forward declaration
template<typename AT, typename DT> class MOD_RegFile;

// Handler for binary mem files
template<typename AT, typename DT>
class BinFormatHandler : public FormatHandler
{
 public:
  BinFormatHandler(MOD_RegFile<AT,DT>* reg_file, bool check_ranges,
		   unsigned int addr_width, unsigned int data_width,
		   const AT& range_start, const AT& range_end)
    : FormatHandler(), rf(reg_file),
      addr_bits(addr_width), data_bits(data_width),
      start(range_start), end(range_end), check(check_ranges)
  {
    addr = start;
    decreasing = (start > end);
  }

  virtual ~BinFormatHandler() {}

  virtual tMemFileStatus updateAddress(const char* addr_str)
  {
    if (!parse_hex(&addr, addr_str, addr_bits))
      return MF_BAD_FORMAT;

    if (check && (addr < start || addr > end))
      return MF_OUT_OF_BOUNDS;

    return MF_ACCEPTED;
  }

  virtual tMemFileStatus setEntry(const char* data_str)
  {
    tMemFileStatus status;

    if (addr < start || addr > end)
    {
      status = MF_IGNORED;
    }
    else
    {
      DT value;
      init_val(value, data_bits);
      if (!parse_bin(&value, data_str, data_bits))
	status = MF_BAD_FORMAT;
      else
      {
	rf->METH_upd(addr, value, true);
	status = MF_ACCEPTED;
	rt.setAddr(addr);
      }
    }

    if (decreasing)
      --addr;
    else
      ++addr;

    return status;
  }

  virtual void checkRange(const char* filename, const char* memname)
  {
    rt.checkRange(filename, memname, start, end);
  }
 private:
  MOD_RegFile<AT,DT>* rf;
  unsigned int addr_bits;
  unsigned int data_bits;
  AT start;
  AT end;
  AT addr;
  bool check;
  bool decreasing;
  RangeTracker<AT> rt;
};

// Handler for hex mem files
template<typename AT, typename DT>
class HexFormatHandler : public FormatHandler
{
 public:
  HexFormatHandler(MOD_RegFile<AT,DT>* reg_file, bool check_ranges,
		   unsigned int addr_width, unsigned int data_width,
		   const AT& range_start, const AT& range_end)
    : FormatHandler(), rf(reg_file),
      addr_bits(addr_width), data_bits(data_width),
      start(range_start), end(range_end), check(check_ranges)
  {
    addr = start;
    decreasing = (start > end);
  }

  virtual ~HexFormatHandler() {}

  virtual tMemFileStatus updateAddress(const char* addr_str)
  {
    if (!parse_hex(&addr, addr_str, addr_bits))
      return MF_BAD_FORMAT;

    if (check && (addr < start || addr > end))
      return MF_OUT_OF_BOUNDS;
    else
      return MF_ACCEPTED;
  }

  virtual tMemFileStatus setEntry(const char* data_str)
  {
    tMemFileStatus status;

    if (addr < start || addr > end)
    {
      status = MF_IGNORED;
    }
    else
    {
      DT value;
      init_val(value, data_bits);
      if (!parse_hex(&value, data_str, data_bits))
	status = MF_BAD_FORMAT;
      else
      {
	rf->METH_upd(addr, value, true);
	status = MF_ACCEPTED;
	rt.setAddr(addr);
      }
    }

    if (decreasing)
      --addr;
    else
      ++addr;

    return status;
  }

  virtual void checkRange(const char* filename, const char* memname)
  {
    rt.checkRange(filename, memname, start, end);
  }
 private:
  MOD_RegFile<AT,DT>* rf;
  unsigned int addr_bits;
  unsigned int data_bits;
  AT start;
  AT end;
  AT addr;
  bool check;
  bool decreasing;
  RangeTracker<AT> rt;
};

template<typename AT, typename DT>
const unsigned int* index_rf_fn(void* base, tUInt64 addr);

// This is the definition of the RegFile primitive
template<typename AT, typename DT>
class MOD_RegFile : public Module
{
 public:
  MOD_RegFile<AT,DT>(tSimStateHdl simHdl, const char* name, Module* parent,
		     unsigned int addr_width, unsigned int data_width,
		     const AT& lo, const AT& hi)
    : Module(simHdl, name, parent), addr_bits(addr_width),
      data_bits(data_width), lo_addr(lo), hi_addr(hi),
      upd_at(~bk_now(sim_hdl)), proxy(NULL)
  {
    if (vcd_is_backing_instance(sim_hdl))
      return;  // do not allocate storage for backing instance

    init_storage();

    init_symbols();
  }
  MOD_RegFile<AT,DT>(tSimStateHdl simHdl, const char* name, Module* parent,
		     const std::string& memfile,
		     unsigned int addr_width, unsigned int data_width,
		     const AT& lo, const AT& hi, bool bin_format)
    : Module(simHdl, name, parent), addr_bits(addr_width),
      data_bits(data_width), lo_addr(lo), hi_addr(hi),
      upd_at(~bk_now(sim_hdl)), proxy(NULL)
  {
    if (vcd_is_backing_instance(sim_hdl))
      return; // do not allocate storage for backing instance

    init_storage();

    init_from_file(memfile, bin_format);

    init_symbols();
  }
  ~MOD_RegFile<AT,DT>() { delete_blocks(top_level,0); delete proxy; }

 // shared initialization routines
 private:
  void init_storage()
  {
    last_word = hi_addr - lo_addr;

    // partition address space for sparse storage
    num_levels = (addr_bits + 9) / 10;
    if ((num_levels > 1) && (addr_bits % 10 > 0) && (addr_bits % 10 < 5))
      --num_levels;
    level_bits = new unsigned char[num_levels];
    unsigned int bits_remaining = addr_bits;
    for (unsigned int i = num_levels; i > 0; --i)
    {
      if (bits_remaining < 15)
      {
	level_bits[i-1] = bits_remaining;
	bits_remaining = 0;
      }
      else if (bits_remaining > 16)
      {
	level_bits[i-1] = 10;
	bits_remaining -= 10;
      }
      else
      {
	level_bits[i-1] = 8;
	bits_remaining -= 8;
      }
    }

    // allocate top-level storage block
    top_level = new_block(0);

    // initialize address and data storage
    init_val(upd_addr, addr_bits);
    write_undet(&upd_addr, addr_bits);
    init_val(upd_prev, data_bits);
    write_undet(&upd_prev, data_bits);
  }

  void init_symbols()
  {
    // initialize symbols
    symbol_count = 3;
    symbols = new tSym[symbol_count];

    range.lo = (unsigned long long) lo_addr;
    range.hi = (unsigned long long) hi_addr;
    range.base = (void*) this;
    range.fetch = index_rf_fn<AT,DT>;

    symbols[0].key = "";
    symbols[0].info = SYM_RANGE | data_bits << 4;
    symbols[0].value = (void*)(&range);

    symbols[1].key = "high_addr";
    symbols[1].info = SYM_PARAM | addr_bits << 4;
    symbols[1].value = (void*)(&hi_addr);

    symbols[2].key = "low_addr";
    symbols[2].info = SYM_PARAM | addr_bits << 4;
    symbols[2].value = (void*)(&lo_addr);
  }

  void init_from_file(const std::string& memfile, bool bin_format)
  {
    FormatHandler* reader;
    if (bin_format)
      reader = new BinFormatHandler<AT,DT>(this, true,
					   addr_bits, data_bits,
					   lo_addr, hi_addr);
    else
      reader = new HexFormatHandler<AT,DT>(this, true,
					   addr_bits, data_bits,
					   lo_addr, hi_addr);
    read_mem_file(memfile.c_str(), inst_name, reader);
  }

  void* new_block(unsigned int level)
  {
    unsigned int nEntries = 1 << level_bits[level];
    if (level == (num_levels - 1))
    {
      DT* data = new DT[nEntries];
      for (unsigned int n = 0; n < nEntries; ++n)
      {
	init_val(data[n], data_bits);
	write_undet(&(data[n]), data_bits);
      }
      return (void*) data;
    }
    else
    {
      void** ptrs = new void*[nEntries];
      for (unsigned int n = 0; n < nEntries; ++n)
	ptrs[n] = NULL;
      return (void*) ptrs;
    }
  }

  void delete_blocks(void* ptr, unsigned int level)
  {
    if (level == (num_levels - 1))
    {
      DT* data = (DT*) ptr;
      delete[] data;
    }
    else
    {
      void** ptrs = (void**) ptr;
      unsigned int nEntries = 1 << level_bits[level];
      for (unsigned int n = 0; n < nEntries; ++n)
      {
	if (ptrs[n] != NULL)
	  delete_blocks(ptrs[n], level+1);
      }
      delete[] ptrs;
    }
  }

  DT* lookup_value(const AT& addr, bool alloc)
  {
    // figure out the target index and which bits of the address to use
    unsigned long long idx = addr - lo_addr;
    unsigned int shift = addr_bits;
    void* ptr = top_level;
    unsigned int level = 0;
    while (true)
    {
      shift -= level_bits[level];
      unsigned int mask = (1 << level_bits[level]) - 1;
      unsigned int n = (idx >> shift) & mask;
      if (level == (num_levels - 1))
      {
	DT* data = (DT*) ptr;
	return &(data[n]);
      }
      else
      {
	void** ptrs = (void**) ptr;
	++level;
	if (ptrs[n] == NULL)
	{
	  if (alloc) ptrs[n] = new_block(level);
	  else return NULL;
	}
	ptr = ptrs[n];
      }
    }
  }

 public:
  // Note: there is RegFileWCF variant of RegFile that
  // allows upd before sub, but sub should be able to read the
  // value from the beginning of the cycle.
  const DT METH_sub(const AT& addr)
  {
    if (addr < lo_addr || addr > hi_addr)
    {
      FileTarget dest(stdout);
      printf("Warning: RegFile '");
      write_name(&dest);
      printf("' -- Read address is out of bounds: ");
      dump_val(addr, addr_bits);
      putchar('\n');
      DT v;
      init_val(v, data_bits);
      write_undet(&v, data_bits);
      return v;
    }
    else if ((upd_addr == addr) && bk_is_same_time(sim_hdl, upd_at))
    {
      return upd_prev;
    }
    else
    {
      DT* value_ptr = lookup_value(addr, false);
      if (value_ptr != NULL)
      {
	return *value_ptr;
      }
      else
      {
	DT v;
	init_val(v, data_bits);
	write_undet(&v, data_bits);
	return v;
      }
    }
  }
  void METH_upd(const AT& addr, const DT& val, bool immediate = false)
  {
    DT* value_ptr = lookup_value(addr, true);
    if (value_ptr != NULL)
    {
      if (!immediate)
      {
	upd_at = bk_now(sim_hdl);
	upd_addr = addr;
	upd_prev = *value_ptr;
      }
      *value_ptr = val;
    }
    else
    {
      FileTarget dest(stdout);
      printf("Warning: RegFile '");
      write_name(&dest);
      printf("' -- Write address is out of bounds: ");
      dump_val(addr, addr_bits);
      putchar('\n');
    }
  }

 public:
  const unsigned int* data_index(tUInt64 addr)
  {
    DT* value_ptr = lookup_value(addr, true);
    if (value_ptr != NULL)
      return symbol_value(value_ptr, data_bits);
    else
      return NULL;
  }

  void dump_state(unsigned int indent)
  {
    printf("%*s%s = ", indent, "", inst_name);
    if (last_word < 16)
    {
      DT* data = (DT*) top_level;
      printf("{ ");
      for (unsigned long long n = 0llu; n <= last_word; ++n)
      {
	if (n > 0)
	  printf(", ");
	dump_val(lo_addr + n, addr_bits);
	printf(": ");
	dump_val(data[n], data_bits);
      }
      printf(" }");
    }
    else
    {
      printf("<RegFile with %llu entries>", (unsigned long long) last_word + 1);
    }

    // dump write address and data
    if (upd_at == bk_now(sim_hdl))
    {
      printf(" (Wrote ");
      dump_val(upd_addr, addr_bits);
      printf(": ");
      DT* value_ptr = lookup_value(upd_addr,true);
      dump_val(*value_ptr, data_bits);
      printf(")");
    }
    putchar('\n');
  }
  unsigned int dump_VCD_defs(unsigned int num)
  {
    // Memory contents are not dumped
    // Please update ../lib/tcllib/bluespec/Waves.tcl proc correct_regfile_names
    // when vcd dumping is enabled.
    return (num);
  }
  void dump_VCD(tVCDDumpType /* unused */,
		MOD_RegFile<AT,DT>& /* unused */)

  {
    // Memory contents are not dumped
  }

 // RegFile data members
 private:
  unsigned int addr_bits;
  unsigned int data_bits;
  AT lo_addr;
  AT hi_addr;
  AT last_word;
  unsigned int num_levels;
  unsigned char* level_bits;
  void* top_level;
  tTime upd_at;
  AT upd_addr;
  DT upd_prev;

  // range structure for symbolic access to RegFile data
  Range range;

 // proxy access facility
 private:
  BluespecProbe<DT,AT>* proxy;
 public:
  BluespecProbe<DT,AT>& getProbe()
  {
    if (proxy == NULL)
      proxy = new BluespecProbe<DT,AT>(this, bounds, has_elem, read_rf, write_rf);
    return (*proxy);
  }
 // static helper functions for probe implementation
 private:
  static AT bounds(void* obj, bool hi)
  {
    MOD_RegFile<AT,DT>* rf = (MOD_RegFile<AT,DT>*) obj;
    return (hi ? rf->hi_addr : rf->lo_addr);
  }
  static bool has_elem(void* obj, AT addr)
  {
    MOD_RegFile<AT,DT>* rf = (MOD_RegFile<AT,DT>*) obj;
    return ((addr >= rf->lo_addr) && (addr <= rf->hi_addr));
  }
  static const DT& read_rf(void* obj, AT addr)
  {
    MOD_RegFile<AT,DT>* rf = (MOD_RegFile<AT,DT>*) obj;
    DT* value_ptr = rf->lookup_value(addr, true);
    if (value_ptr != NULL)
      return *value_ptr;
    else
      return read_rf(obj, rf->lo_addr); // out-of-bounds
  }
  static bool write_rf(void* obj, AT addr, const DT& data)
  {
    MOD_RegFile<AT,DT>* rf = (MOD_RegFile<AT,DT>*) obj;
    rf->METH_upd(addr,data,true);
    return has_elem(obj,addr);
  }

 public:
  friend class BinFormatHandler<AT,DT>;
  friend class HexFormatHandler<AT,DT>;
};

// Function to index into RegFile data array
template<typename AT, typename DT>
const unsigned int* index_rf_fn(void* base, tUInt64 addr)
{
  MOD_RegFile<AT,DT>* rf = (MOD_RegFile<AT,DT>*) base;
  return rf->data_index(addr);
}

#endif /* __BS_PRIM_MOD_REGFILE_H__ */
