#ifndef __BS_PRIM_MOD_BRAM_H__
#define __BS_PRIM_MOD_BRAM_H__

#include <cstdio>
#include <string>

#include "bluesim_kernel_api.h"
#include "bluesim_probes.h"
#include "bs_mem_file.h"
#include "bs_module.h"
#include "bs_vcd.h"
#include "bs_range_tracker.h"

// forward declaration
template<typename AT, typename DT, typename ET> class MOD_BRAM;

// Handler for binary mem files
template<typename AT, typename DT, typename ET>
class BinFormatHandlerBRAM : public FormatHandler
{
 public:
 BinFormatHandlerBRAM(MOD_BRAM<AT,DT,ET>* block_ram, bool check_ranges,
                   unsigned int addr_width, unsigned int data_width,
                   const AT& range_start, const AT& range_end)
    : FormatHandler(), bram(block_ram),
      addr_bits(addr_width), data_bits(data_width),
      start(range_start), end(range_end), check(check_ranges)
  {
    addr = start;
    decreasing = (start > end);
  }

  virtual ~BinFormatHandlerBRAM() {}

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
        bram->METH_a_put(1, addr, value, true);
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
  MOD_BRAM<AT,DT,ET>* bram;
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
template<typename AT, typename DT, typename ET>
class HexFormatHandlerBRAM : public FormatHandler
{
 public:
 HexFormatHandlerBRAM(MOD_BRAM<AT,DT,ET>* block_ram, bool check_ranges,
                   unsigned int addr_width, unsigned int data_width,
                   const AT& range_start, const AT& range_end)
    : FormatHandler(), bram(block_ram),
      addr_bits(addr_width), data_bits(data_width),
      start(range_start), end(range_end), check(check_ranges)
  {
    addr = start;
    decreasing = (start > end);
  }

  virtual ~HexFormatHandlerBRAM() {}

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
        bram->METH_a_put(1, addr, value, true);
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
  MOD_BRAM<AT,DT,ET>* bram;
  unsigned int addr_bits;
  unsigned int data_bits;
  AT start;
  AT end;
  AT addr;
  bool check;
  bool decreasing;
  RangeTracker<AT> rt;
};

template<typename AT, typename DT, typename ET>
const unsigned int* index_bram_fn(void* base, tUInt64 addr);

// This is the definition of the BRAM primitive
template<typename AT, typename DT, typename ET>
class MOD_BRAM : public Module
{
 public:
 MOD_BRAM<AT,DT,ET>(tSimStateHdl simHdl, const char* name, Module* parent,
                    tUInt8 is_pipelined,
                    unsigned int addr_width, unsigned int data_width,
                    unsigned long long mem_size, unsigned int num_ports)
    : Module(simHdl, name, parent), pipelined(is_pipelined),
      addr_bits(addr_width), data_bits(data_width),
      lo_addr(0), hi_addr(mem_size-1),
      chunk_size(data_width), num_wens(1), dual_port(num_ports == 2),
      upd_a_at(~bk_now(sim_hdl)), written_a_at(~bk_now(sim_hdl)),
      upd_b_at(~bk_now(sim_hdl)), written_b_at(~bk_now(sim_hdl)),
      proxy(NULL)
  {
    init_storage();

    init_symbols();
  }
 MOD_BRAM<AT,DT,ET>(tSimStateHdl simHdl, const char* name, Module* parent,
                    tUInt8 is_pipelined,
                    unsigned int addr_width, unsigned int data_width,
                    unsigned int chunk_size, unsigned int num_wens,
                    unsigned long long mem_size, unsigned int num_ports)
    : Module(simHdl, name, parent), pipelined(is_pipelined),
      addr_bits(addr_width), data_bits(data_width),
      lo_addr(0), hi_addr(mem_size-1),
      chunk_size(chunk_size), num_wens(num_wens), dual_port(num_ports == 2),
      upd_a_at(~bk_now(sim_hdl)), written_a_at(~bk_now(sim_hdl)),
      upd_b_at(~bk_now(sim_hdl)), written_b_at(~bk_now(sim_hdl)),
      proxy(NULL)
  {
    init_storage();

    init_symbols();
  }
 MOD_BRAM<AT,DT,ET>(tSimStateHdl simHdl, const char* name, Module* parent,
                    const std::string& memfile,
                    tUInt8 is_pipelined,
                    unsigned int addr_width, unsigned int data_width,
                    unsigned long long mem_size,
                    bool bin_format, unsigned int num_ports)
    : Module(simHdl, name, parent), pipelined(is_pipelined),
      addr_bits(addr_width), data_bits(data_width),
      lo_addr(0), hi_addr(mem_size-1),
      chunk_size(data_width), num_wens(1), dual_port(num_ports == 2),
      upd_a_at(~bk_now(sim_hdl)), written_a_at(~bk_now(sim_hdl)),
      upd_b_at(~bk_now(sim_hdl)), written_b_at(~bk_now(sim_hdl)),
      proxy(NULL)
  {
    init_storage();

    init_from_file(memfile, bin_format);

    init_symbols();
  }
 MOD_BRAM<AT,DT,ET>(tSimStateHdl simHdl, const char* name, Module* parent,
                    const std::string& memfile,
                    tUInt8 is_pipelined,
                    unsigned int addr_width, unsigned int data_width,
                    unsigned int chunk_size, unsigned int num_wens,
                    unsigned long long mem_size,
                    bool bin_format, unsigned int num_ports)
    : Module(simHdl, name, parent), pipelined(is_pipelined),
      addr_bits(addr_width), data_bits(data_width),
      lo_addr(0), hi_addr(mem_size-1),
      chunk_size(chunk_size), num_wens(num_wens), dual_port(num_ports == 2),
      upd_a_at(~bk_now(sim_hdl)), written_a_at(~bk_now(sim_hdl)),
      upd_b_at(~bk_now(sim_hdl)), written_b_at(~bk_now(sim_hdl)),
      proxy(NULL)
  {
    init_storage();

    init_from_file(memfile, bin_format);

    init_symbols();
  }
 ~MOD_BRAM<AT,DT,ET>() { delete_blocks(top_level,0); delete proxy; }

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
    if (!vcd_is_backing_instance(sim_hdl))
      top_level = new_block(0);

    // initialize address and data storage

    init_val(upd_a_addr, addr_bits);
    init_val(upd_a_val,data_bits);
    write_undet(&upd_a_val, data_bits);
    init_val(out_reg_a,data_bits);
    write_undet(&out_reg_a, data_bits);
    init_val(out_reg2_a,data_bits);
    write_undet(&out_reg2_a, data_bits);
    init_val(upd_a_prev,data_bits);
    write_undet(&upd_a_prev, data_bits);
    init_val(upd_a_wens,num_wens);
    write_undet(&upd_a_wens, num_wens);

    init_val(upd_b_addr, addr_bits);
    init_val(upd_b_val,data_bits);
    write_undet(&upd_b_val, data_bits);
    init_val(out_reg_b,data_bits);
    write_undet(&out_reg_b, data_bits);
    init_val(out_reg2_b,data_bits);
    write_undet(&out_reg2_b, data_bits);
    init_val(upd_b_prev,data_bits);
    write_undet(&upd_b_prev, data_bits);
    init_val(upd_b_wens,num_wens);
    write_undet(&upd_b_wens, num_wens);
  }

  void init_symbols()
  {
    if (vcd_is_backing_instance(sim_hdl))
      return; // do not allocate symbols for backing instance

    // initialize symbols
    symbol_count = 3;
    symbols = new tSym[symbol_count];

    range.lo = (unsigned long long) lo_addr;
    range.hi = (unsigned long long) hi_addr;
    range.base = (void*) this;
    range.fetch = index_bram_fn<AT,DT,ET>;

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
    if (vcd_is_backing_instance(sim_hdl))
      return; // do not try to initialize the backing instance

    FormatHandler* reader;
    if (bin_format)
      reader = new BinFormatHandlerBRAM<AT,DT,ET>(this, true,
                                                  addr_bits, data_bits,
                                                  lo_addr, hi_addr);
    else
      reader = new HexFormatHandlerBRAM<AT,DT,ET>(this, true,
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
  // Note: BRAM has put CF read, plus has cross-port
  // issues, so we must take care to faithfully reproduce
  // the write-first memory semantics no matter what order
  // the methods are called in.

  void clkA(tUInt8 /* clock_value */, tUInt8 gate_value = 1)
  {
    DT* value_ptr = NULL;

    // update out_reg2_a
    out_reg2_a = out_reg_a;

    // check if a put method call needs to be handled
    if (bk_is_same_time(sim_hdl, upd_a_at))
    {
      bool is_write = !is_zero(upd_a_wens);
      if (upd_a_addr < lo_addr || upd_a_addr > hi_addr)
      {
        // this access is out-of-range
        write_undet(&out_reg_a, data_bits);
      }
      else if (is_write) {
        // perform a memory write and set out_reg_a to the new value
        value_ptr = lookup_value(upd_a_addr, true);
        if (value_ptr != NULL)
        {
          if ((upd_a_addr == upd_b_addr) &&
              bk_is_same_time(sim_hdl, upd_b_at) &&
              !is_zero(upd_b_wens))
          {
            // check if written values are incompatible
            bool collision = false;
            for (unsigned int n = 0; n < num_wens; ++n)
            {
              if (is_bit_set(upd_a_wens, n) && is_bit_set(upd_b_wens, n))
                collision |= chunks_eq(upd_a_val, upd_b_val, n, chunk_size);
            }
            if (collision)
            {
              FileTarget dest(stdout);
              printf("Warning: BRAM '");
              write_name(&dest);
              printf("' -- Write collision at address ");
              dump_val(upd_a_addr, addr_bits);
              putchar('\n');
            }
          }

          // determine the previous value at this address
          // if a simultaneous write has been handled on the other port,
          // we must use the value before that write
          written_a_at = upd_a_at;
          if (bk_is_same_time(sim_hdl, written_b_at) &&
              (upd_a_addr == upd_b_addr))
            upd_a_prev = upd_b_prev;
          else
            upd_a_prev = *value_ptr;
          for (unsigned int n = 0; n < num_wens; ++n)
          {
            if (is_bit_set(upd_a_wens, n))
              xfer_chunk(value_ptr,upd_a_val,n,chunk_size);
          }

          // set the out_reg_a value
          for (unsigned int n = 0; n < num_wens; ++n)
          {
            if (is_bit_set(upd_a_wens, n))
              xfer_chunk(&out_reg_a,upd_a_val,n,chunk_size);
            else
              xfer_chunk(&out_reg_a,upd_a_prev,n,chunk_size);
          }
        }
      }
      else
      {
        // perform a memory read and set out_reg_a to the retrieved value
        value_ptr = lookup_value(upd_a_addr, false);
        if (value_ptr == NULL)
          write_undet(&out_reg_a, data_bits);
        else {
          // if a simultaneous write has been handled on the other port,
          // we must use the value before that write
          if (bk_is_same_time(sim_hdl, written_b_at) &&
              (upd_a_addr == upd_b_addr))
            out_reg_a = upd_b_prev;
          else
            out_reg_a = *value_ptr;
        }
      }
    }
  }

  void clkB(tUInt8 /* clock_value */, tUInt8 gate_value = 1)
  {
    DT* value_ptr = NULL;

    // update out_reg2_b
    out_reg2_b = out_reg_b;

    // check if a put method call needs to be handled
    if (bk_is_same_time(sim_hdl, upd_b_at))
    {
      bool is_write = !is_zero(upd_b_wens);
      if (upd_b_addr < lo_addr || upd_b_addr > hi_addr)
      {
        // this access is out-of-range
        write_undet(&out_reg_b, data_bits);
      }
      else if (is_write) {
        // perform a memory write and set out_reg_a to the new value
        value_ptr = lookup_value(upd_b_addr, true);
        if (value_ptr != NULL)
        {
          if ((upd_a_addr == upd_b_addr) &&
              bk_is_same_time(sim_hdl, upd_a_at) &&
              !is_zero(upd_a_wens))
          {
            // check if written values are incompatible
            bool collision = false;
            for (unsigned int n = 0; n < num_wens; ++n)
            {
              if (is_bit_set(upd_a_wens, n) && is_bit_set(upd_b_wens, n))
                collision |= chunks_eq(upd_a_val, upd_b_val, n, chunk_size);
            }
            if (collision)
            {
              FileTarget dest(stdout);
              printf("Warning: BRAM '");
              write_name(&dest);
              printf("' -- Write collision at address ");
              dump_val(upd_b_addr, addr_bits);
              putchar('\n');
            }
          }

          // determine the previous value at this address
          // if a simultaneous write has been handled on the other port,
          // we must use the value before that write
          written_b_at = upd_b_at;
          if (bk_is_same_time(sim_hdl, written_a_at) &&
              (upd_a_addr == upd_b_addr))
            upd_b_prev = upd_a_prev;
          else
            upd_b_prev = *value_ptr;
          for (unsigned int n = 0; n < num_wens; ++n)
          {
            if (is_bit_set(upd_b_wens, n))
              xfer_chunk(value_ptr,upd_b_val,n,chunk_size);
          }

          // set the out_reg_b value
          for (unsigned int n = 0; n < num_wens; ++n)
          {
            if (is_bit_set(upd_b_wens, n))
              xfer_chunk(&out_reg_b,upd_b_val,n,chunk_size);
            else
              xfer_chunk(&out_reg_b,upd_b_prev,n,chunk_size);
          }
        }
      }
      else
      {
        // perform a memory read and set out_reg_b to the retrieved value
        value_ptr = lookup_value(upd_b_addr, false);
        if (value_ptr == NULL)
          write_undet(&out_reg_b, data_bits);
        else {
          // if a simultaneous write has been handled on the other port,
          // we must use the value before that write
          if (bk_is_same_time(sim_hdl, written_a_at) &&
              (upd_a_addr == upd_b_addr))
            out_reg_b = upd_a_prev;
          else
            out_reg_b = *value_ptr;
        }
      }
    }
  }

  void METH_a_put(const ET& write_ens, const AT& addr, const DT& val,
                  bool immediate = false)
  {
    // bounds check
    if (addr < lo_addr || addr > hi_addr)
    {
      FileTarget dest(stdout);
      printf("Warning: BRAM '");
      write_name(&dest);
      printf("' -- %s address on port A is out of bounds: ", (write_ens != 0) ? "Write" : "Read");
      dump_val(addr, addr_bits);
      putchar('\n');
    }

    bool is_write = !is_zero(write_ens);

    // handle an immediate write
    if (is_write && immediate)
    {
      DT* value_ptr = lookup_value(addr, true);
      if (value_ptr != NULL)
        *value_ptr = val;
    }
    else
    {
      // otherwise, we just record the request to be handled in clkA()
      upd_a_at   = bk_now(sim_hdl);
      upd_a_addr = addr;
      upd_a_wens = write_ens;
      upd_a_val  = val;
    }
  }

  const DT METH_a_read()
  {
    if (pipelined)
      return out_reg2_a;
    else
      return out_reg_a;
  }

 void METH_b_put(const ET& write_ens, const AT& addr, const DT& val,
                  bool immediate = false)
  {
    // bounds check
    if (addr < lo_addr || addr > hi_addr)
    {
      FileTarget dest(stdout);
      printf("Warning: BRAM '");
      write_name(&dest);
      printf("' -- %s address on port B is out of bounds: ", (write_ens != 0) ? "Write" : "Read");
      dump_val(addr, addr_bits);
      putchar('\n');
    }

    bool is_write = !is_zero(write_ens);

    // handle an immediate write
    if (is_write && immediate)
    {
      DT* value_ptr = lookup_value(addr, true);
      if (value_ptr != NULL)
        *value_ptr = val;
    }
    else
    {
      // otherwise, we just record the request to be handled in clkB()
      upd_b_at   = bk_now(sim_hdl);
      upd_b_addr = addr;
      upd_b_wens = write_ens;
      upd_b_val  = val;
    }
  }

  const DT METH_b_read()
  {
    if (pipelined)
      return out_reg2_b;
    else
      return out_reg_b;
  }

  // used for single-port BRAMs

  void clk(tUInt8 clock_value, tUInt8 gate_value)
  {
    clkA(clock_value, gate_value);
  }

  void METH_put(const ET& write_ens, const AT& addr, const DT& val,
                bool immediate = false)
  {
    METH_a_put(write_ens, addr, val, immediate);
  }

  const DT METH_read()
  {
    return METH_a_read();
  }

 public:

  // Setting the clocks

  void set_clk_0(const char* s)
  {
    __clk_handle_0 = bk_get_or_define_clock(sim_hdl, s);
  }

  void set_clk_1(const char* s)
  {
    __clk_handle_1 = bk_get_or_define_clock(sim_hdl, s);
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
      printf(" }\n");
    }
    else
    {
      printf("<BRAM with %llu entries>\n", (unsigned long long) last_word + 1);
    }
  }
  unsigned int dump_VCD_defs(unsigned int num)
  {
    // Memory contents are not dumped, only ports
    vcd_num = vcd_reserve_ids(sim_hdl, dual_port ? 10 : 5);
    unsigned int n = vcd_num;
    vcd_write_scope_start(sim_hdl, inst_name);
    if (dual_port) {
      vcd_write_def(sim_hdl, bk_clock_vcd_num(sim_hdl, __clk_handle_0), "CLKA", 1);
      vcd_set_clock(sim_hdl, n, __clk_handle_0);
      vcd_write_def(sim_hdl, n++, "ENA", 1);
      vcd_set_clock(sim_hdl, n, __clk_handle_0);
      vcd_write_def(sim_hdl, n++, "WEA", num_wens);
      vcd_set_clock(sim_hdl, n, __clk_handle_0);
      vcd_write_def(sim_hdl, n++, "ADDRA", addr_bits);
      vcd_set_clock(sim_hdl, n, __clk_handle_0);
      vcd_write_def(sim_hdl, n++, "DIA", data_bits);
      vcd_write_def(sim_hdl, n++, "DOA", data_bits);
      vcd_write_def(sim_hdl, bk_clock_vcd_num(sim_hdl, __clk_handle_1), "CLKB", 1);
      vcd_set_clock(sim_hdl, n, __clk_handle_1);
      vcd_write_def(sim_hdl, n++, "ENB", 1);
      vcd_set_clock(sim_hdl, n, __clk_handle_1);
      vcd_write_def(sim_hdl, n++, "WEB", num_wens);
      vcd_set_clock(sim_hdl, n, __clk_handle_1);
      vcd_write_def(sim_hdl, n++, "ADDRB", addr_bits);
      vcd_set_clock(sim_hdl, n, __clk_handle_1);
      vcd_write_def(sim_hdl, n++, "DIB", data_bits);
      vcd_write_def(sim_hdl, n++, "DOB", data_bits);
    } else {
      vcd_write_def(sim_hdl, bk_clock_vcd_num(sim_hdl, __clk_handle_0), "CLK", 1);
      vcd_set_clock(sim_hdl, n, __clk_handle_0);
      vcd_write_def(sim_hdl, n++, "EN", 1);
      vcd_set_clock(sim_hdl, n, __clk_handle_0);
      vcd_write_def(sim_hdl, n++, "WE", num_wens);
      vcd_set_clock(sim_hdl, n, __clk_handle_0);
      vcd_write_def(sim_hdl, n++, "ADDR", addr_bits);
      vcd_set_clock(sim_hdl, n, __clk_handle_0);
      vcd_write_def(sim_hdl, n++, "DI", data_bits);
      vcd_write_def(sim_hdl, n++, "DO", data_bits);
    }
    vcd_write_scope_end(sim_hdl);
    return n;
  }
  void dump_VCD(tVCDDumpType dt, MOD_BRAM<AT,DT,ET>& backing)
  {
    // Memory contents are not dumped, only ports
    unsigned int num = vcd_num;
    if (dt == VCD_DUMP_XS)
    {
      vcd_write_x(sim_hdl, num++, 1);
      vcd_write_x(sim_hdl, num++, num_wens);
      vcd_write_x(sim_hdl, num++, addr_bits);
      vcd_write_x(sim_hdl, num++, data_bits);
      vcd_write_x(sim_hdl, num++, data_bits);
      if (dual_port)
      {
        vcd_write_x(sim_hdl, num++, 1);
        vcd_write_x(sim_hdl, num++, num_wens);
        vcd_write_x(sim_hdl, num++, addr_bits);
        vcd_write_x(sim_hdl, num++, data_bits);
        vcd_write_x(sim_hdl, num++, data_bits);
      }
    }
    else if (dt == VCD_DUMP_CHANGES)
    {
      bool at_posedge_a =
               bk_clock_val(sim_hdl, __clk_handle_0) == CLK_HIGH &&
               bk_clock_last_edge(sim_hdl, __clk_handle_0) == bk_now(sim_hdl);
      if (at_posedge_a)
      {
        did_ena = bk_is_same_time(sim_hdl, upd_a_at);
        bool did_write = did_ena && !is_zero(upd_a_wens);
        bool backing_did_write = backing.did_ena && !is_zero(backing.upd_a_wens);
        if (did_ena != backing.did_ena)
        {
          vcd_write_val(sim_hdl, num++, did_ena, 1);
          backing.did_ena = did_ena;
        }
        else
          ++num;
        if ((did_write != backing_did_write) || (upd_a_wens != backing.upd_a_wens))
        {
          if (!did_ena)
            vcd_write_val(sim_hdl, num++, 0llu, num_wens); // it's OK that 0 may not be of type ET
          else
            vcd_write_val(sim_hdl, num++, upd_a_wens, num_wens);
        }
        else
          ++num;
        if (upd_a_addr != backing.upd_a_addr)
          vcd_write_val(sim_hdl, num++, upd_a_addr, addr_bits);
        else
          ++num;
        if (upd_a_val != backing.upd_a_val)
          vcd_write_val(sim_hdl, num++, upd_a_val, data_bits);
        else
          ++num;
        if (pipelined && (out_reg2_a != backing.out_reg2_a))
          vcd_write_val(sim_hdl, num++, out_reg2_a, data_bits);
        else if (!pipelined && (out_reg_a != backing.out_reg_a))
          vcd_write_val(sim_hdl, num++, out_reg_a, data_bits);
        else
          ++num;
      }
      else
        num += 5;
      if (dual_port)
      {
        bool at_posedge_b =
                 bk_clock_val(sim_hdl, __clk_handle_1) == CLK_HIGH &&
                 bk_clock_last_edge(sim_hdl, __clk_handle_1) == bk_now(sim_hdl);
        if (at_posedge_b)
        {
          did_enb = bk_is_same_time(sim_hdl, upd_b_at);
          bool did_write = did_enb && !is_zero(upd_b_wens);
          bool backing_did_write = backing.did_enb && !is_zero(backing.upd_b_wens);
          if (did_enb != backing.did_enb)
          {
            vcd_write_val(sim_hdl, num++, did_enb, 1);
            backing.did_enb = did_enb;
          }
          else
            ++num;
          if ((did_write != backing_did_write) || (upd_b_wens != backing.upd_b_wens))
          {
            if (!did_enb)
              vcd_write_val(sim_hdl, num++, 0llu, num_wens); // it's OK that 0 may not be of type ET
            else
              vcd_write_val(sim_hdl, num++, upd_b_wens, num_wens);
          }
          else
            ++num;
          if (upd_b_addr != backing.upd_b_addr)
            vcd_write_val(sim_hdl, num++, upd_b_addr, addr_bits);
          else
            ++num;
          if (upd_b_val != backing.upd_b_val)
            vcd_write_val(sim_hdl, num++, upd_b_val, data_bits);
          else
            ++num;
          if (pipelined && (out_reg2_b != backing.out_reg2_b))
            vcd_write_val(sim_hdl, num++, out_reg2_b, data_bits);
          else if (!pipelined && (out_reg_b != backing.out_reg_b))
            vcd_write_val(sim_hdl, num++, out_reg_b, data_bits);
          else
            ++num;
        }
        else
          num += 5;
      }
    }
    else
    {
      did_ena = bk_is_same_time(sim_hdl, upd_a_at);
      vcd_write_val(sim_hdl, num++, did_ena, 1);
      vcd_write_val(sim_hdl, num++, upd_a_wens, num_wens);
      vcd_write_val(sim_hdl, num++, upd_a_addr, addr_bits);
      vcd_write_val(sim_hdl, num++, upd_a_val, data_bits);
      if (pipelined)
        vcd_write_val(sim_hdl, num++, out_reg2_a, data_bits);
      else
        vcd_write_val(sim_hdl, num++, out_reg_a, data_bits);
      if (dual_port)
      {
        did_enb = bk_is_same_time(sim_hdl, upd_b_at);
        vcd_write_val(sim_hdl, num++, did_enb, 1);
        vcd_write_val(sim_hdl, num++, upd_b_wens, num_wens);
        vcd_write_val(sim_hdl, num++, upd_b_addr, addr_bits);
        vcd_write_val(sim_hdl, num++, upd_b_val, data_bits);
        if (pipelined)
          vcd_write_val(sim_hdl, num++, out_reg2_b, data_bits);
        else
          vcd_write_val(sim_hdl, num++, out_reg_b, data_bits);
      }
      backing.did_ena = did_ena;
      backing.did_enb = did_enb;
    }

    backing.upd_a_at   = upd_a_at;
    backing.upd_a_wens = upd_a_wens;
    backing.upd_a_addr = upd_a_addr;
    backing.upd_a_val  = upd_a_val;
    backing.out_reg_a  = out_reg_a;
    backing.out_reg2_a = out_reg2_a;
    if (dual_port)
    {
      backing.upd_b_at   = upd_b_at;
      backing.upd_b_wens = upd_b_wens;
      backing.upd_b_addr = upd_b_addr;
      backing.upd_b_val  = upd_b_val;
      backing.out_reg_b  = out_reg_b;
      backing.out_reg2_b = out_reg2_b;
    }
  }

 // BRAM data members
 private:
  bool           pipelined;
  unsigned int   addr_bits;
  unsigned int   data_bits;
  AT             lo_addr;
  AT             hi_addr;
  AT             last_word;
  unsigned int   chunk_size;
  unsigned int   num_wens;
  bool           dual_port;
  unsigned int   num_levels;
  unsigned char* level_bits;
  void*          top_level;
  tClock         __clk_handle_0;
  tClock         __clk_handle_1;
  tTime          upd_a_at;
  tTime          written_a_at;
  AT             upd_a_addr;
  DT             upd_a_val;
  DT             out_reg_a;
  DT             out_reg2_a;
  DT             upd_a_prev;
  ET             upd_a_wens;
  tTime          upd_b_at;
  tTime          written_b_at;
  AT             upd_b_addr;
  DT             upd_b_val;
  DT             out_reg_b;
  DT             out_reg2_b;
  DT             upd_b_prev;
  ET             upd_b_wens;

  // range structure for symbolic access to RegFile data
  Range range;

  // used for VCD dumping
  bool did_ena;
  bool did_enb;

 // proxy access facility
 private:
  BluespecProbe<DT,AT>* proxy;
 public:
  BluespecProbe<DT,AT>& getProbe()
  {
    if (proxy == NULL)
      proxy = new BluespecProbe<DT,AT>(this, bounds, has_elem, read_bram, write_bram);
    return (*proxy);
  }
 // static helper functions for probe implementation
 private:
  static AT bounds(void* obj, bool hi)
  {
    MOD_BRAM<AT,DT,ET>* bram = (MOD_BRAM<AT,DT,ET>*) obj;
    return (hi ? bram->hi_addr : bram->lo_addr);
  }
  static bool has_elem(void* obj, AT addr)
  {
    MOD_BRAM<AT,DT,ET>* bram = (MOD_BRAM<AT,DT,ET>*) obj;
    return ((addr >= bram->lo_addr) && (addr <= bram->hi_addr));
  }
  static const DT& read_bram(void* obj, AT addr)
  {
    MOD_BRAM<AT,DT,ET>* bram = (MOD_BRAM<AT,DT,ET>*) obj;
    DT* value_ptr = bram->lookup_value(addr, true);
    if (value_ptr != NULL)
      return *value_ptr;
    else
      return read_bram(obj, bram->lo_addr); // out-of-bounds
  }
  static bool write_bram(void* obj, AT addr, const DT& data)
  {
    MOD_BRAM<AT,DT,ET>* bram = (MOD_BRAM<AT,DT,ET>*) obj;
    bram->METH_a_put(1, addr,data,true);
    return has_elem(obj,addr);
  }

 public:
  friend class BinFormatHandlerBRAM<AT,DT,ET>;
  friend class HexFormatHandlerBRAM<AT,DT,ET>;
};

// Function to index into RegFile data array
template<typename AT, typename DT, typename ET>
const unsigned int* index_bram_fn(void* base, tUInt64 addr)
{
  MOD_BRAM<AT,DT,ET>* bram = (MOD_BRAM<AT,DT,ET>*) base;
  return bram->data_index(addr);
}

#endif /* __BS_PRIM_MOD_BRAM_H__ */
