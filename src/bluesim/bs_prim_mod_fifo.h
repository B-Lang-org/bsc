#ifndef __BS_PRIM_MOD_FIFO_H__
#define __BS_PRIM_MOD_FIFO_H__

#include <cstdio>
#include <cstring>
#include "bluesim_kernel_api.h"
#include "bluesim_probes.h"
#include "bs_module.h"
#include "bs_vcd.h"

typedef enum { FIFO_SIMPLE, FIFO_LOOPY, FIFO_BYPASS} tFifoType;

/*
 * Things to know about FIFOs:
 *
 * 1. deq() and first() can occur in either order,
 *    as can clear() and first().
 * 2. notFull() and notEmpty() can occur before or
 *    after enq(), deq(), and clear().
 * 3. For a FIFO_LOOPY, deq() then enq() is allowed
 *    even if the fifo was full at the start of the
 *    cycle, but it is not allowed for the non-loopy case.
 * 4. For a FIFO_BYPASS, enq() then deq() is allowed
 *    even if the fifo was empty at the start of the
 *    cycle, but it is not allowed for the non-bypass case.
 */

template<typename T>
const unsigned int* index_fn_fifo(void* base, tUInt64 addr);

// This is the definition of the Fifo primitive
template<typename T>
class MOD_Fifo : public Module
{
 public:
  MOD_Fifo<T>(tSimStateHdl simHdl, const char* name, Module* parent,
              unsigned int width, unsigned int depth,
              unsigned int guarded, unsigned int fifo_type)
    : Module(simHdl, name, parent), bits(width), size(depth),
      guard(guarded != 0), type((tFifoType) fifo_type),
      enq_at(~bk_now(sim_hdl)), deq_at(~bk_now(sim_hdl)),
      clear_at(~bk_now(sim_hdl)), proxy(NULL)
  {
    data = new T[depth];
    for (unsigned int n = 0; n < depth; ++n)
    {
      init_val(data[n], width);
      write_undet(&data[n], width);
    }
    fst   = 0;
    elems = 0;
    in_reset = false;
    suppress_writes = false;
    // for zero-width fifos and VCDs
    init_val(dummyval, width);
    write_undet(&dummyval, width);

    symbol_count = 3;
    symbols = new tSym[symbol_count];

    range.lo = 0;
    range.hi = depth - 1;
    range.base = (void*) this;
    range.fetch = index_fn_fifo<T>;

    symbols[0].key = "";
    symbols[0].info = SYM_RANGE | bits << 4;
    symbols[0].value = (void*)(&range);

    symbols[1].key = "depth";
    symbols[1].info = SYM_PARAM | (8*sizeof(unsigned int)) << 4;
    symbols[1].value = (void*)(&depth);

    symbols[2].key = "level";
    symbols[2].info = SYM_DEF | (8*sizeof(unsigned int)) << 4;
    symbols[2].value = (void*)(&size);
  }
  ~MOD_Fifo<T>() { delete[] data; delete proxy; }
 public:
  // Note: first < (deq, clear) so we do *not* need to preserve
  // the first element to achieve registered behavior.  first CF enq,
  // but first on a FIFO which was empty at the start of the cycle
  // is allowed to return invalid data.
  const T& METH_first() const { return data[fst]; }

  // Note: all FIFOs have deq < clear, and loopy FIFOs also have
  // deq < enq.  Bypass FIFOs have enq < deq.  The only troublesome
  // case is for regular FIFOs where the enq() can happen before the
  // deq(), but a deq() when the FIFO was empty at the start of
  // the cycle should still generate an error.
  void METH_deq()
  {
    if (suppress_writes)
      return;

    deq_at = bk_now(sim_hdl);
    if (enq_at != bk_now(sim_hdl))
      saved_elems = elems;

    if (elems == 0 ||
        (type != FIFO_BYPASS &&
         guard &&
         enq_at == bk_now(sim_hdl) &&
         saved_elems == 0))
    {
      FileTarget dest(stdout);
      printf("Warning: ");
      write_name(&dest);
      printf(" -- Dequeuing from empty fifo\n");
    }
    else if (elems != 0)
    {
      fst = (fst + 1) % size;
      --elems;
    }
  }

  // Note: normal FIFOs have enq CF deq, but loopy FIFOs have deq < enq
  // and bypass FIFOs have enq < deq.  The only troublesome case is for
  // regular FIFOs where the deq() can happen before a subsequent enq() --
  // if this happens when the FIFO is full, it is an error.
  void METH_enq(const T& x)
  {
    dummyval = x;  // save for VCD display

    if (suppress_writes)
      return;

    enq_at = bk_now(sim_hdl);
    if (deq_at != bk_now(sim_hdl))
      saved_elems = elems;

    if (elems == size ||
        (type != FIFO_LOOPY &&
         guard &&
         deq_at == bk_now(sim_hdl) &&
         saved_elems == size))
    {
      FileTarget dest(stdout);
      printf("Warning: ");
      write_name(&dest);
      printf(" -- Enqueuing to a full fifo\n");
    }
    else if (elems < size)
    {
      data[(fst + elems) % size] = x;
      ++elems;
    }
  }
  // for zero-width fifos
  void METH_enq() { METH_enq(dummyval); }

  // Note: for all FIFOs, enq, deq, first < clear.
  void METH_clear()
  {
    if (suppress_writes)
      return;

    clear_at = bk_now(sim_hdl);
    if (enq_at != bk_now(sim_hdl) && deq_at != bk_now(sim_hdl))
      saved_elems = elems;

    fst = 0;
    elems = 0;
  }

  // Note: for all FIFOs, notFull < (enq, clear)
  // For non-loopy FIFOs, notFull < deq but for loopy FIFOs
  // deq < notFull.  Since we want the deq to be reflected
  // in the notFull value for loopy FIFOs, using the size
  // directly gives the correct result.
  bool METH_notFull() const  { return (elems < size); }

  // Note: for all FIFOs, notEmpty < (enq, deq, clear)
  bool METH_notEmpty() const { return (elems != 0); }

  // Note: for non-loopy FIFOs, i_notFull CF (enq, deq, clear),
  // so we need to compensate for any previous FIFO manipulations.
  // For loopy FIFOs, deq < i_notFull < (enq, clear) and we want to
  // reflect the deq in the i_notFull value.
  bool METH_i_notFull() const
  {
    if (type != FIFO_LOOPY &&
        (bk_is_same_time(sim_hdl, enq_at) ||
         bk_is_same_time(sim_hdl, deq_at) ||
         bk_is_same_time(sim_hdl, clear_at)))
      return (saved_elems < size);
    else
      return (elems < size);
  }

  // Note: for non-loopy FIFOs, i_notEmpty CF (enq, deq, clear),
  // so we need to compensate for any previous FIFO manipulations.
  // For loopy FIFOs, i_notEmpty < (enq, deq, clear).
  bool METH_i_notEmpty() const
  {
    if (type != FIFO_LOOPY &&
        (bk_is_same_time(sim_hdl, enq_at) ||
         bk_is_same_time(sim_hdl, deq_at) ||
         bk_is_same_time(sim_hdl, clear_at)))
      return (saved_elems != 0);
    else
      return (elems != 0);
  }

 public:
  // Setting the clock
  void set_clk_0(const char* s)
  {
    __clk_handle_0 = bk_get_or_define_clock(sim_hdl, s);
  }

  // Handle reset
  void reset_RST(tUInt8 rst_in)
  {
    in_reset = (rst_in == 0);
    if (in_reset)
    {
      start_reset_ticks(sim_hdl); /* request rst_tick() on the next clock edge */
    }
    else
    {
      suppress_writes = false;
      stop_reset_ticks(sim_hdl); /* stop rst_tick() when reset is not asserted */
    }
  }
  void rst_tick_clk(tUInt8 clock_gate)
  {
    if (in_reset && (clock_gate != 0) && !suppress_writes)
    {
      METH_clear();
      suppress_writes = true;
    }
  }

 public:
  const unsigned int* data_index(tUInt64 addr) const
  {
    if (addr < ((tUInt64) size))
      return symbol_value(&(data[addr]),bits);
    else
      return NULL;
  }

  void dump_state(unsigned int indent)
  {
    printf("%*s%s = ", indent, "", inst_name);
    if (elems == 0)
      printf("EMPTY");
    else
    {
      printf("{ ");
      for (unsigned int n = 0; n < elems; ++n)
      {
	if (n > 0)
	  printf(", ");
	dump_val(data[(fst + n) % size], bits);
      }
      printf(" }");
    }
    putchar('\n');
  }
  unsigned int dump_VCD_defs(unsigned int num)
  {
    vcd_num = vcd_reserve_ids(sim_hdl, size + 6 + (bits > 0 ? 1 : 0));
    unsigned int n = vcd_num;
    char buf[16];
    vcd_write_scope_start(sim_hdl, inst_name);
    vcd_write_def(sim_hdl, bk_clock_vcd_num(sim_hdl, __clk_handle_0), "CLK", 1);
    vcd_write_def(sim_hdl, n++, "RST", 1);
    vcd_write_def(sim_hdl, n++, "FULL_N", 1);
    vcd_write_def(sim_hdl, n++, "EMPTY_N", 1);
    vcd_set_clock(sim_hdl, n, __clk_handle_0);
    vcd_write_def(sim_hdl, n++, "ENQ", 1);
    if (bits > 0)
    {
      vcd_set_clock(sim_hdl, n, __clk_handle_0);
      vcd_write_def(sim_hdl, n++, "D_IN", bits);
    }
    vcd_set_clock(sim_hdl, n, __clk_handle_0);
    vcd_write_def(sim_hdl, n++, "DEQ", 1);
    vcd_set_clock(sim_hdl, n, __clk_handle_0);
    vcd_write_def(sim_hdl, n++, "CLR", 1);
    if (bits > 0)
      vcd_write_def(sim_hdl, n,"D_OUT", bits);  // alias of arr_0
    for (unsigned int i = 0; i < size; ++i)
    {
      sprintf(buf, "arr_%d", i);
      vcd_write_def(sim_hdl, n++, buf, bits);
    }
    vcd_write_scope_end(sim_hdl);
    return n;
  }
  void dump_VCD(tVCDDumpType dt, MOD_Fifo<T>& backing)
  {
    unsigned int num = vcd_num;
    if (dt == VCD_DUMP_XS)
    {
      vcd_write_x(sim_hdl, num++, 1);
      vcd_write_x(sim_hdl, num++, 1);
      vcd_write_x(sim_hdl, num++, 1);
      vcd_write_x(sim_hdl, num++, 1);
      if (bits > 0)
	vcd_write_x(sim_hdl, num++, bits);
      vcd_write_x(sim_hdl, num++, 1);
      vcd_write_x(sim_hdl, num++, 1);
      for (unsigned int i = 0; i < size; ++i)
	vcd_write_x(sim_hdl, num++, bits);
    }
    else if (dt == VCD_DUMP_CHANGES)
    {
      if (in_reset != backing.in_reset)
	vcd_write_val(sim_hdl, num++, !in_reset, 1);
      else
	++num;
      if (METH_notFull() != backing.METH_notFull())
	vcd_write_val(sim_hdl, num++, METH_notFull(), 1);
      else
	++num;
      if (METH_notEmpty() != backing.METH_notEmpty())
	vcd_write_val(sim_hdl, num++, METH_notEmpty(), 1);
      else
	++num;
      bool at_posedge =
	       bk_clock_val(sim_hdl, __clk_handle_0) == CLK_HIGH &&
	       bk_clock_last_edge(sim_hdl, __clk_handle_0) == bk_now(sim_hdl);
      if (at_posedge)
      {
	did_enq = bk_is_same_time(sim_hdl, enq_at);
	if (did_enq != backing.did_enq)
	{
	  vcd_write_val(sim_hdl, num++, did_enq, 1);
	  backing.did_enq = did_enq;
	}
	else
	  ++num;
      }
      else
	++num;
      if (bits > 0)
      {
	if (dummyval != backing.dummyval)
	  vcd_write_val(sim_hdl, num++, dummyval, bits);
	else
	  ++num;
      }
      if (at_posedge)
      {
	did_deq = bk_is_same_time(sim_hdl, deq_at);
	if (did_deq != backing.did_deq)
	{
	  vcd_write_val(sim_hdl, num++, did_deq, 1);
	  backing.did_deq = did_deq;
	}
	else
	  ++num;
      }
      else
	++num;
      if (at_posedge)
      {
	did_clear = bk_is_same_time(sim_hdl, clear_at);
	if (did_clear != backing.did_clear)
	{
	  vcd_write_val(sim_hdl, num++, did_clear, 1);
	  backing.did_clear = did_clear;
	}
	else
	  ++num;
      }
      else
	++num;
      for (unsigned int i = 0; i < size; ++i)
      {
	unsigned int idx = (fst + i) % size;
	unsigned int b_idx = (backing.fst + i) % size;
	if ((i < elems) &&
	    ((i >= backing.elems) || (data[idx] != backing.data[b_idx])))
	  vcd_write_val(sim_hdl, num++, data[idx], bits);
	else if ((i >= elems) && (i < backing.elems))
	  vcd_write_x(sim_hdl, num++, bits);
	else
	  ++num;
      }
    }
    else
    {
      vcd_write_val(sim_hdl, num++, !in_reset, 1);
      vcd_write_val(sim_hdl, num++, METH_notFull(), 1);
      vcd_write_val(sim_hdl, num++, METH_notEmpty(), 1);
      did_enq = bk_is_same_time(sim_hdl, enq_at);
      did_deq = bk_is_same_time(sim_hdl, deq_at);
      did_clear = bk_is_same_time(sim_hdl, clear_at);
      vcd_write_val(sim_hdl, num++, did_enq, 1);
      if (bits > 0)
	vcd_write_val(sim_hdl, num++, dummyval, bits);
      vcd_write_val(sim_hdl, num++, did_deq, 1);
      vcd_write_val(sim_hdl, num++, did_clear, 1);
      for (unsigned int i = 0; i < size; ++i)
      {
	unsigned int idx = (fst + i) % size;
	if (i < elems)
	  vcd_write_val(sim_hdl, num++, data[idx], bits);
	else
	  vcd_write_x(sim_hdl, num++, bits);
      }
      backing.did_enq = did_enq;
      backing.did_deq = did_deq;
      backing.did_clear = did_clear;
    }

    backing.fst = fst;
    backing.elems = elems;
    for (unsigned int i = 0; i < size; ++i)
      backing.data[i] = data[i];
    backing.in_reset = in_reset;
    backing.dummyval = dummyval;
  }

  // FIFO data members
 private:
  T*                 data;
  const unsigned int bits;
  const unsigned int size;
  const bool         guard;
  const tFifoType    type;
  unsigned int       fst;
  unsigned int       elems;
  tClock             __clk_handle_0;
  tTime              enq_at;
  tTime              deq_at;
  tTime              clear_at;
  unsigned int       saved_elems;
  bool               in_reset;
  bool               suppress_writes;

  // for zero-width fifos (also used for VCD data)
  T dummyval;

  // range structure for symbolic access to FIFO data
  Range range;

  // used for VCD dumping
  bool did_enq;
  bool did_deq;
  bool did_clear;

 // proxy access facility
 private:
  BluespecProbe<T>* proxy;
 public:
  BluespecProbe<T>& getProbe()
  {
    if (proxy == NULL)
      proxy = new BluespecProbe<T>(this, bounds, has_elem, read_fifo, write_fifo);
    return (*proxy);
  }
 private:
  static unsigned int bounds(void* obj, bool hi)
  {
    MOD_Fifo<T>* fifo = (MOD_Fifo<T>*) obj;
    if (hi)
      return fifo->elems;
    else
      return 1;
  }
  static bool has_elem(void* obj, unsigned int addr)
  {
    MOD_Fifo<T>* fifo = (MOD_Fifo<T>*) obj;
    return ((addr > 0) && (addr <= fifo->elems));
  }
  static const T& read_fifo(void* obj, unsigned int addr)
  {
    MOD_Fifo<T>* fifo = (MOD_Fifo<T>*) obj;
    return (fifo->data[(fifo->fst + addr - 1) % fifo->size]);
  }
  static bool write_fifo(void* obj, unsigned int addr, const T& data)
  {
    MOD_Fifo<T>* fifo = (MOD_Fifo<T>*) obj;
    if ((addr > 0) && (addr <= fifo->elems))
    {
      // overwrite fifo contents
      fifo->data[(fifo->fst + addr - 1) % fifo->size] = data;
      return true;
    }
    else if (fifo->elems < fifo->size)
    {
      // add to fifo contents
      fifo->data[(fifo->fst + fifo->elems) % fifo->size] = data;
      fifo->elems += 1;
      return true;
    }
    else
      return false; // indicates enq to full fifo
  }
};


// Function to index into FIFO data array
template<typename T>
const unsigned int* index_fn_fifo(void* base, tUInt64 addr)
{
  MOD_Fifo<T>* fifo = (MOD_Fifo<T>*) base;
  return fifo->data_index(addr);
}

#endif /* __BS_PRIM_MOD_FIFO_H__ */
