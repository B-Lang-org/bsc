#ifndef __BS_PRIM_MOD_CLOCKMUX_H__
#define __BS_PRIM_MOD_CLOCKMUX_H__

#include <string>

#include "bluesim_kernel_api.h"
#include "bs_module.h"
#include "bs_vcd.h"
#include "bs_reset.h"

// This is the definition of the ClockMux primitive,
// used to implement mkClockMux.
class MOD_ClockMux : public Module
{
 public:
  MOD_ClockMux(tSimStateHdl simHdl, const char* name, Module* parent)
    : Module(simHdl, name, parent), __clk_handle_0(BAD_CLOCK_HANDLE)
  {
    select_out = false;
    a_clk  = b_clk  = 0;
    a_gate = b_gate = 0;
    new_clk = 0;
    PORT_CLK_GATE_OUT = 1;
  }

 private:
  
  void do_clock()
  {
    tUInt8 old_clk = new_clk;
    new_clk  = select_out ? a_clk  : b_clk;
    PORT_CLK_GATE_OUT = select_out ? a_gate : b_gate;

    // trigger clock edge when new_clk changes
    if (new_clk != old_clk)
      bk_trigger_clock_edge(sim_hdl, __clk_handle_0,
			    (new_clk != 0) ? POSEDGE : NEGEDGE,
			    bk_now(sim_hdl));
  }

 public:
  void set_clk_0(const char* s)
  {
    __clk_handle_0 = bk_get_or_define_clock(sim_hdl, s);
    bk_alter_clock(sim_hdl, __clk_handle_0,
		   CLK_LOW, true,
		   0, 0, 0); // no predefined waveform
  }

  void METH_select(tUInt8 use_a)
  {
    select_out = (use_a != 0);
  }

  void aClk(tUInt8 clock_value, tUInt8 gate_value = 1)
  {
    a_clk  = clock_value;
    a_gate = gate_value;
    do_clock();
  }

  void bClk(tUInt8 clock_value, tUInt8 gate_value = 1)
  {
    b_clk  = clock_value;
    b_gate = gate_value;
    do_clock();
  }

  void xclk(tUInt8 /* clock_value */, tUInt8 gate_value = 1)
  {
    do_clock();
  }

  void dump_state(unsigned int /* unused */, bool with_label=true) const
  {
  }

  unsigned int dump_VCD_defs(unsigned int num) const
  {
    return (num);
  }

  void dump_VCD(tVCDDumpType /* unused */, MOD_ClockMux& /* unused */) const
  {
  }

 public:
  tUInt8 PORT_CLK_GATE_OUT;

 private:
  tClock __clk_handle_0;
  bool   select_out;
  tUInt8 a_clk;
  tUInt8 a_gate;
  tUInt8 b_clk;
  tUInt8 b_gate;
  tUInt8 new_clk;
};


// This is the definition of the ClockSelect primitive,
// used to implement mkClockSelect.
class MOD_ClockSelect : public Module
{
 public:
  MOD_ClockSelect(tSimStateHdl simHdl, const char* name, Module* parent,
		  unsigned int stages)
    : Module(simHdl, name, parent), __clk_handle_0(BAD_CLOCK_HANDLE),
      reset_delay(stages), reset_hold(stages + 1), reset_fn(NULL)
  {
    select_out = select_out2 = false;
    written = ~bk_now(sim_hdl);
    in_reset = false;
    a_clk  = b_clk  = 0;
    a_gate = b_gate = 1;
    new_clk = 0;
    changed = false;
    changed_negedge = ~bk_now(sim_hdl);
    PORT_CLK_GATE_OUT = 1;
  }

 private:
  
  void do_clock_and_reset()
  {
    tUInt8 old_clk = new_clk;
    new_clk = select_out ? a_clk : b_clk;
    PORT_CLK_GATE_OUT = select_out ? a_gate : b_gate;

    bool prev_changed = changed;
    changed = (select_out != select_out2) || in_reset;
    // "changed" is assigned non-blocking in the Verilog, so its new value
    // is only observed after this cycle; to simulate that in Bluesim,
    // we record the time of the negedge and don't use the new value
    // if that time is now (in case an output clock edge occurs coincident
    // with the selector clock edge which reset "changed")
    if (!changed && prev_changed)
      changed_negedge = bk_now(sim_hdl);

    // trigger clock edge when new_clk changes
    if (new_clk != old_clk)
      bk_trigger_clock_edge(sim_hdl, __clk_handle_0,
			    (new_clk != 0) ? POSEDGE : NEGEDGE,
			    bk_now(sim_hdl));

    // handle reset logic on new_clk edges or transitions of changed
    if (((new_clk == 1) && (old_clk == 0)) || (changed && !prev_changed))
    {
      if (changed || (changed_negedge == bk_now(sim_hdl)))
      {
	if ((reset_hold > reset_delay) && (reset_fn != NULL))
	  reset_at_end_of_timeslice(sim_hdl, reset_fn, parent, 0);
	reset_hold = 0;
      }
      else
      {
	if (reset_hold <= reset_delay)
	  ++reset_hold;
	if ((reset_hold > reset_delay) && (reset_fn != NULL))
	  reset_at_end_of_timeslice(sim_hdl, reset_fn, parent, 1);
      }
    }
  }

 public:
  void set_clk_0(const char* s)
  {
    __clk_handle_0 = bk_get_or_define_clock(sim_hdl, s);
    bk_alter_clock(sim_hdl, __clk_handle_0,
		   CLK_LOW, true,
		   0, 0, 0); // no predefined waveform
  }

  void METH_select(tUInt8 use_a)
  {
    if (!in_reset)
    {
      written = bk_now(sim_hdl);
      // this update could be delayed until the xclk() tick function
      select_out2 = select_out;
      select_out = (use_a != 0);
      do_clock_and_reset();
    }
  }

  void set_reset_fn_reset_out(tResetFn fn) { reset_fn = fn; }

  void reset_RST(tUInt8 rst_in)
  {
    in_reset = (rst_in == 0);
    if (!in_reset)
    {
      select_out = select_out2 = 0;
    }
    do_clock_and_reset();
  }

  void rst_tick_xclk(tUInt8 /* clock_gate */)
  {
    // nothing to do
  }

  void aClk(tUInt8 clock_value, tUInt8 gate_value = 1)
  {
    a_clk  = clock_value;
    a_gate = gate_value;
    do_clock_and_reset();
  }

  void bClk(tUInt8 clock_value, tUInt8 gate_value = 1)
  {
    b_clk  = clock_value;
    b_gate = gate_value;
    do_clock_and_reset();
  }

  void xclk(tUInt8 /* clock_value */, tUInt8 gate_value = 1)
  {
    if (!in_reset)
    {
      // if the select method was called, then we've already updated
      // the state/outputs this cycle
      if (written != bk_now(sim_hdl)) {
	select_out2 = select_out;
	do_clock_and_reset();
      }
    }
  }

  void dump_state(unsigned int /* unused */, bool with_label=true) const
  {
  }

  unsigned int dump_VCD_defs(unsigned int num) const
  {
    return (num);
  }
  void dump_VCD(tVCDDumpType /* unused */,
		MOD_ClockSelect& /* unused */) const
  {
  }

 public:
  tUInt8 PORT_CLK_GATE_OUT;

 private:
  tClock       __clk_handle_0;
  unsigned int reset_delay;
  unsigned int reset_hold;
  tResetFn     reset_fn;
  bool         select_out;
  bool         select_out2;
  tTime        written;
  bool         in_reset;
  tUInt8       a_clk;
  tUInt8       a_gate;
  tUInt8       b_clk;
  tUInt8       b_gate;
  tUInt8       new_clk;
  bool         changed;
  tTime        changed_negedge;
};

#endif /* __BS_PRIM_MOD_CLOCKMUX_H__ */
