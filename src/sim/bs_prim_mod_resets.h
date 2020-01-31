#ifndef __BS_PRIM_MOD_RESETS_H__
#define __BS_PRIM_MOD_RESETS_H__

#include "bluesim_kernel_api.h"
#include "bs_module.h"
#include "bs_vcd.h"
#include "bs_reset.h"

/* Notes on reset handling
 *
 * Each module, including primitives, has a reset function associated
 * with each reset input to the module.  The reset function is
 * responsible for calling the reset functions of subinstances of the
 * module.  The reset function is called when the reset is asserted
 * and when the reset is deasserted.  The argument to the function is
 * a tUInt8 that is 0 for an asserted reset and 1 for a deasserted
 * reset.
 *
 * Primitive modules are responsible for recording the reset
 * conditions when their reset functions are called and behaving
 * accordingly.
 *
 * When any reset condition is asserted, all primitives with reset tick
 * methods have those methods called in addition to any regular tick
 * methods.
 *
 * Reset generation primitives are passed a pointer to a static
 * function that forwards to a module reset function.  Since
 * primitives often test reset conditions in their tick methods, reset
 * generation primitives should defer asserting and deasserting
 * synchronous resets until the end of the schedule, after the
 * primitives' tick methods have executed.
 */

// This is the definition used for synchronizer primitives
// with a 2-destination-clock-cycle delay.
class MOD_SyncReset: public Module
{
 public:
  MOD_SyncReset(tSimStateHdl simHdl, const char* name, Module* parent_mod,
		unsigned int cycles, tUInt8 async)
    : Module(simHdl, name, parent_mod), reset_hold(cycles),
      is_async(async != 0), __clk_handle_0(BAD_CLOCK_HANDLE)
  {
    reset_fn = NULL;
    count = 0;
    in_reset = false;
    call_reset_fn = false;
  }
 public:
  void set_reset_fn_gen_rst(tResetFn fn) {
    reset_fn = fn;
    //reset_init(sim_hdl, reset_fn, parent, (count == 0) ? 1 : 0);
  }
  void reset_IN_RST(tUInt8 rst_in)
  {
    in_reset = (rst_in == 0);
    if (in_reset)
    {
      count = reset_hold + 1;
      if (reset_fn)
      {
	if (is_async)
	{
	  reset_fn(parent, rst_in);  // async reset generation
	  start_reset_ticks(sim_hdl);
	}
	else
	  call_reset_fn = true;
      }
    }
  }

  void set_clk_0(const char* s)
  {
    __clk_handle_0 = bk_get_or_define_clock(sim_hdl, s);
  }

  void clk(tUInt8 /* clock_value */, tUInt8 gate_value = 1)
  {
    if (gate_value == 0)
      return;

    // handle synchronous reset generation
    if (call_reset_fn)
    {
      if (in_reset)
	reset_at_end_of_timeslice(sim_hdl, reset_fn, parent, 0);
      call_reset_fn = false;
    }

    // once our incoming reset is deasserted, we count down the hold
    // cycles for our outgoing reset.
    if (!in_reset && (count > 0))
    {
      if ((count == 1) && reset_fn)
	reset_at_end_of_timeslice(sim_hdl, reset_fn, parent, 1);
      --count;
    }
  }
  void rst_tick_rst(tUInt8 /* clock_gate */) { /* nothing required */ }
 public:
  void dump_state(unsigned int indent)
  {
    printf("%*s%s:\n", indent, "", inst_name);
  }
  unsigned int dump_VCD_defs(unsigned int /* num */)
  {
    vcd_num = vcd_reserve_ids(sim_hdl, 2);
    unsigned int n = vcd_num;
    vcd_write_scope_start(sim_hdl, inst_name);
    vcd_write_def(sim_hdl, bk_clock_vcd_num(sim_hdl, __clk_handle_0), "CLK", 1);
    vcd_write_def(sim_hdl, n++, "IN_RST", 1);
    vcd_write_def(sim_hdl, n++, "OUT_RST", 1);
    vcd_write_scope_end(sim_hdl);
    return (n);
  }
  void dump_VCD(tVCDDumpType dt, MOD_SyncReset& backing)
  {
    unsigned int num = vcd_num;
    if (dt == VCD_DUMP_XS)
    {
      vcd_write_x(sim_hdl, num++, 1);
      vcd_write_x(sim_hdl, num++, 1);
    }
    else if (dt == VCD_DUMP_CHANGES)
    {
      if (in_reset != backing.in_reset)
	vcd_write_val(sim_hdl, num++, !in_reset, 1);
      else
	num++;
      bool rst_out = in_reset || (count > 1);
      bool backing_rst_out = backing.in_reset || (backing.count > 1);
      if (rst_out != backing_rst_out)
	vcd_write_val(sim_hdl, num++, !rst_out, 1);
      else
	num++;
    }
    else
    {
      vcd_write_val(sim_hdl, num++, !in_reset, 1);
      vcd_write_val(sim_hdl, num++, !(in_reset || (count > 1)), 1);
    }
    backing.in_reset = in_reset;
    backing.count    = count;
  }

 private:
  unsigned int reset_hold;
  unsigned int count;
  bool         is_async;
  bool         in_reset;
  bool         call_reset_fn;
  tResetFn     reset_fn;

  // used for VCD dumping
  tClock __clk_handle_0;
};


class MOD_SyncReset0: public Module
{
 public:
  MOD_SyncReset0(tSimStateHdl simHdl, const char* name, Module* parent_mod)
    : Module(simHdl, name, parent_mod), reset_fn(NULL), in_reset(false)
  {
  }
 public:
  void set_reset_fn_gen_rst(tResetFn fn) { reset_fn = fn; }
  void reset_IN_RST(tUInt8 rst_in)
  {
    if (reset_fn)
      reset_fn(parent, rst_in);  // async reset generation
    // update the ticks
    bool new_in_reset = (rst_in == 0);
    if (!in_reset) {
      if (new_in_reset)
	start_reset_ticks(sim_hdl);
    } else {
      if (!new_in_reset)
	stop_reset_ticks(sim_hdl);
    }
    in_reset = new_in_reset;
  }
  void rst_tick_rst(tUInt8 /* clock_gate */) { /* nothing required */ }
 public:
  void dump_state(unsigned int /* indent */)
  {
    // no state dump
  }
  unsigned int dump_VCD_defs(unsigned int num )
  {
    // no VCD output
    return num;
  }
  void dump_VCD(tVCDDumpType /* dt */, MOD_SyncReset0& /* backing */)
  {
    // no VCD output
  }

 private:
  tResetFn     reset_fn;
  bool         in_reset;
};


class MOD_InitialReset: public Module
{
 public:
  MOD_InitialReset(tSimStateHdl simHdl, const char* name, Module* parent_mod,
		   unsigned int cycles)
    : Module(simHdl, name, parent_mod), reset_hold(cycles)
  {
    reset_fn = NULL;
    count = 0;
  }
 public:
  void set_reset_fn_gen_rst(tResetFn fn)
  {
    reset_fn = fn;
    count = reset_hold;
    
    // add initial reset assertion at time 0
    reset_init(sim_hdl, reset_fn, parent, 0);
  }
  void clk(tUInt8 /* clock_value */, tUInt8 gate_value = 1)
  {
    if (gate_value == 0 || count == 0)
      return;
    if (count-- == 1)
    {
      if (reset_fn != NULL)
	reset_at_end_of_timeslice(sim_hdl, reset_fn, parent, 1);
    }
  }
 public:
  void dump_state(unsigned int indent)
  {
    printf("%*s%s:\n", indent, "", inst_name);
  }
  unsigned int dump_VCD_defs(unsigned int /* num */)
  {
    vcd_num = vcd_reserve_ids(sim_hdl, 3);
    vcd_write_scope_start(sim_hdl, inst_name);
    vcd_write_scope_end(sim_hdl);
    return (vcd_num + 3);
  }
  void dump_VCD(tVCDDumpType dt, MOD_InitialReset& backing)
  {
  }

 private:
  unsigned int reset_hold;
  unsigned int count;
  tResetFn     reset_fn;
};


class MOD_MakeReset: public Module
{
 public:
  MOD_MakeReset(tSimStateHdl simHdl, const char* name, Module* parent,
		unsigned int cycles, tUInt8 init, tUInt8 async);

 public:
  // the following four member functions are based on RegA
  tUInt8 METH_isAsserted()
  {
    return (rst == 0);
  }
  void METH_assertReset()
  {
    // asynchronous reset
    if (!in_reset) {  // if (!suppress_write)
      old_rst = rst;
      rst = 0;
      written = bk_now(sim_hdl);
    }
  }
  void reset_RST(tUInt8 rst_in)
  {
    in_reset = (rst_in == 0);
    if (in_reset) {
      old_rst = rst;
      rst = rst_reset_value;
      if (old_rst != rst)
	sync.reset_IN_RST(rst);  // reset_syncRst$rst(rst);
    }
  }
  void rst_tick_clk(tUInt8 /* clock_gate */) { /* nothing required */ }
  void clk(tUInt8 /* clock_value */, tUInt8 gate_value = 1)
  {
    if (gate_value == 0)
      return;

    if (!in_reset) {  // if (!suppress_write)
      if (written != bk_now(sim_hdl)) {
	old_rst = rst;
	rst = 1;
      }
      if (rst != old_rst) {
	reset_at_end_of_timeslice(sim_hdl, static_reset_syncRst$rst, this, rst);
      }
    }
  }

  // Since the clk and dst_clk edges can coincide, we schedule this after
  // the clock ticks, to call the reset on the submodule
  void reset_syncRst$rst(tUInt8 rst_in)
  {
    sync.reset_IN_RST(rst_in);
  }
  static void static_reset_syncRst$rst(void *my_this, tUInt8 rst_in);

  void reset_syncRst$gen_rst(tUInt8 rst_in)
  {
    if (reset_fn)
      reset_fn(parent, rst_in);
  }
  static void static_reset_syncRst$gen_rst(void *my_this, tUInt8 rst_in);

  void set_reset_fn_new_rst(tResetFn fn) {
    reset_fn = fn;
    sync.set_reset_fn_gen_rst(static_reset_syncRst$gen_rst);
    //reset_init(sim_hdl, static_reset_syncRst$rst, this, rst);
  }

  void dst_clk(tUInt8 clock_value, tUInt8 gate_value = 1)
  {
    sync.clk(clock_value, gate_value);
  }
 public:
  void dump_state(unsigned int indent)
  {
    printf("%*s%s:\n", indent, "", inst_name);
    printf("%*srst = ", indent+2, "");
    dump_val(rst, 1);
    putchar('\n');
  }
  unsigned int dump_VCD_defs(unsigned int /* num */)
  {
    vcd_num = vcd_reserve_ids(sim_hdl, 1);
    vcd_write_scope_start(sim_hdl, inst_name);
    vcd_write_def(sim_hdl, vcd_num, "rst", 1);
    vcd_write_scope_end(sim_hdl);
    return (vcd_num + 1);
  }
  void dump_VCD(tVCDDumpType dt, MOD_MakeReset& backing)
  {
    if (dt == VCD_DUMP_XS)
      vcd_write_x(sim_hdl, vcd_num, 1);
    else if ((dt != VCD_DUMP_CHANGES) || (backing.rst != rst))
    {
      vcd_write_val(sim_hdl, vcd_num, rst, 1);
      backing.rst = rst;
    }
  }

 private:
  MOD_SyncReset sync;
  tResetFn     reset_fn;
  // to support the internal RegA
  tUInt8       rst;
  tUInt8       rst_reset_value;
  bool         in_reset;
  // to support clearing the rst when not written
  tTime        written;
  // to support detection of the edges
  tUInt8       old_rst;
};


class MOD_MakeReset0: public Module
{
 public:
  MOD_MakeReset0(tSimStateHdl simHdl, const char* name, Module* parent_mod,
		 tUInt8 init)
    : Module(simHdl, name, parent_mod), rst_reset_value(init),
      written(~bk_now(sim_hdl))
  {
    reset_fn = NULL;
    rst = 1;
    old_rst = rst;
    in_reset = false;
  }
 public:
  // the following four member functions are based on RegA
  tUInt8 METH_isAsserted()
  {
    return (rst == 0);
  }
  void METH_assertReset()
  {
    // asynchronous reset
    if (!in_reset) {  // if (!suppress_write)
      old_rst = rst;
      rst = 0;
      written = bk_now(sim_hdl);
    }
  }
  void reset_RST(tUInt8 rst_in)
  {
    in_reset = (rst_in == 0);
    if (in_reset) {
      old_rst = rst;
      rst = rst_reset_value;
      if (old_rst != rst)
	if (reset_fn)
	  reset_fn(parent, rst);
    }
  }
  void rst_tick_clk(tUInt8 /* clock_gate */) { /* nothing required */ }
  void clk(tUInt8 /* clock_value */, tUInt8 gate_value = 1)
  {
    if (gate_value == 0)
      return;

    if (!in_reset) {  // if (!suppress_write)
      if (written != bk_now(sim_hdl)) {
	old_rst = rst;
	rst = 1;
      }
      if (rst != old_rst) {
	if (reset_fn)
	  reset_at_end_of_timeslice(sim_hdl, reset_fn, parent, rst);
      }
    }
  }

  void set_reset_fn_new_rst(tResetFn fn) {
    reset_fn = fn;
    //if (reset_fn)
    //  reset_init(sim_hdl, reset_fn, parent, rst);
  }

 public:
  void dump_state(unsigned int indent)
  {
    printf("%*s%s:\n", indent, "", inst_name);
    printf("%*srst = ", indent+2, "");
    dump_val(rst, 1);
    putchar('\n');
  }
  unsigned int dump_VCD_defs(unsigned int /* num */)
  {
    vcd_num = vcd_reserve_ids(sim_hdl, 1);
    vcd_write_scope_start(sim_hdl, inst_name);
    vcd_write_def(sim_hdl, vcd_num, "rst", 1);
    vcd_write_scope_end(sim_hdl);
    return (vcd_num + 1);
  }
  void dump_VCD(tVCDDumpType dt, MOD_MakeReset0& backing)
  {
    if (dt == VCD_DUMP_XS)
      vcd_write_x(sim_hdl, vcd_num, 1);
    else if ((dt != VCD_DUMP_CHANGES) || (backing.rst != rst))
    {
      vcd_write_val(sim_hdl, vcd_num, rst, 1);
      backing.rst = rst;
    }
  }

 private:
  tResetFn     reset_fn;
  // to support the internal RegA
  tUInt8       rst;
  tUInt8       rst_reset_value;
  bool         in_reset;
  // to support clearing the rst when not written
  tTime        written;
  // to support detection of the edges
  tUInt8       old_rst;
};


// This is the definition of the ResetMux primitive,
// used to implement mkResetMux.
class MOD_ResetMux : public Module
{
 public:
  MOD_ResetMux(tSimStateHdl simHdl, const char* name, Module* parent_mod)
    : Module(simHdl, name, parent_mod)
  {
    reset_fn = NULL;
    select_out = false;
    new_select_out = false;
    a_rst_in = 0;
    b_rst_in = 0;
  }

  void set_reset_fn_reset_out(tResetFn fn) {
    reset_fn = fn;
  }

  void reset_A_RST(tUInt8 rst_in)
  {
    // record the value, in case the selector changes
    a_rst_in = rst_in;
    // if this reset is selected, pass it along
    if (select_out) {
      if (reset_fn) {
	reset_fn(parent, rst_in);
      }
    }
  }

  void reset_B_RST(tUInt8 rst_in)
  {
    // record the value, in case the selector changes
    b_rst_in = rst_in;
    // if this reset is selected, pass it along
    if (!select_out) {
      if (reset_fn) {
	reset_fn(parent, rst_in);
      }
    }
  }

  void METH_select(tUInt8 use_a)
  {
    new_select_out = (use_a != 0);
  }

 private:
  // This should only be called at the end of timeslice
  void do_select()
  {
    // update the selector
    select_out = new_select_out;
    // if the resets have different values
    if (a_rst_in != b_rst_in) {
      // then trigger the value of the newly selected reset
      tUInt8 new_rst = (select_out ? a_rst_in : b_rst_in);
      reset_fn(parent, new_rst);
    }
  }
  static void static_do_select(void *my_this, tUInt8 /* rst_in */);

 public:
  void rst_tick_xclk(tUInt8 /* clock_gate */) { /* nothing required */ }
  void xclk(tUInt8 /* clock_value */, tUInt8 gate_value = 1)
  {
    // if the selector has changed
    if (new_select_out != select_out) {
      reset_at_end_of_timeslice(sim_hdl, &static_do_select, this, 0);
    }
  }
 public:
  void dump_state(unsigned int /* indent */) const
  {
    // no state dump
  }

  unsigned int dump_VCD_defs(unsigned int num) const
  {
    // no VCD output
    return (num);
  }

  void dump_VCD(tVCDDumpType /* dt */, MOD_ResetMux& /* backing */)
  {
    // no VCD output
  }

 private:
  tResetFn     reset_fn;
  bool         select_out;
  // to detect when the selector register has changed
  bool         new_select_out;
  // the last value of each reset
  // (to know if changing the selector changes the output)
  tUInt8       a_rst_in;
  tUInt8       b_rst_in;
};


// This is the definition of the ResetEither primitive,
// used to implement mkResetEither.
class MOD_ResetEither : public Module
{
 public:
  MOD_ResetEither(tSimStateHdl simHdl, const char* name, Module* parent_mod)
    : Module(simHdl, name, parent_mod)
  {
    reset_fn = NULL;
    a_rst_in = 1;
    b_rst_in = 1;
  }

  void set_reset_fn_reset_out(tResetFn fn) {
    reset_fn = fn;
  }

  void reset_A_RST(tUInt8 rst_in)
  {
    // propagate change on A_RST when B_RST is 1
    if ((rst_in != a_rst_in) && (b_rst_in != 0)) {
      if (reset_fn) {
	reset_fn(parent, rst_in);
      }
    }
    a_rst_in = rst_in;
  }

  void reset_B_RST(tUInt8 rst_in)
  {
    // propagate change on B_RST when A_RST is 1
    if ((rst_in != b_rst_in) && (a_rst_in != 0)) {
      if (reset_fn) {
	reset_fn(parent, rst_in);
      }
    }
    b_rst_in = rst_in;
  }

 public:
  void rst_tick_xclk(tUInt8 /* clock_gate */) { /* nothing required */ }

 public:
  void dump_state(unsigned int /* indent */) const
  {
    // no state dump
  }

  unsigned int dump_VCD_defs(unsigned int num) const
  {
    // no VCD output
    return (num);
  }

  void dump_VCD(tVCDDumpType /* dt */, MOD_ResetEither& /* backing */)
  {
    // no VCD output
  }

 private:
  tResetFn     reset_fn;
  // the last value of each reset
  // (to detect when it is necessary to propagate changes)
  tUInt8       a_rst_in;
  tUInt8       b_rst_in;
};


// This is the definition of the ResetToBool primitive,
// used to implement isResetAsserted.
class MOD_ResetToBool : public Module
{
 public:
  MOD_ResetToBool(tSimStateHdl simHdl, const char* name, Module* parent_mod)
    : Module(simHdl, name, parent_mod)
  {
    in_reset = 0;
  }

  void reset_RST(tUInt8 rst_in)
  {
    in_reset = (rst_in == 0);
  }

 public:
  tUInt8 METH__read() const { return in_reset; }


 public:
  void rst_tick_clk(tUInt8 /* clock_gate */) { /* nothing required */ }

 public:
  void dump_state(unsigned int /* indent */) const
  {
    // no state dump
  }

  unsigned int dump_VCD_defs(unsigned int num) const
  {
    // no VCD output
    return (num);
  }

  void dump_VCD(tVCDDumpType /* dt */, MOD_ResetToBool& /* backing */)
  {
    // no VCD output
  }

 private:
  tUInt8 in_reset;
};

#endif /* __BS_PRIM_MOD_RESETS_H__ */
