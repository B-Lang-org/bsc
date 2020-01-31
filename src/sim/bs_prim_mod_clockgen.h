#ifndef __BS_PRIM_MOD_CLOCKGEN_H__
#define __BS_PRIM_MOD_CLOCKGEN_H__

#include <string>

#include "bluesim_kernel_api.h"
#include "bs_module.h"
#include "bs_vcd.h"

// This is the definition of the ClockGen primitive,
// used to implement mkAbsoluteClock, etc.
class MOD_ClockGen : public Module
{
 public:
  MOD_ClockGen(tSimStateHdl simHdl, const char* name, Module* parent,
	       tTime v1Width, tTime v2Width, tTime initDelay,
	       unsigned int initValue, unsigned int /* otherValue */)
    : Module(simHdl, name, parent), __clk_handle_0(BAD_CLOCK_HANDLE),
      v1Width(v1Width), v2Width(v2Width),
      initDelay(initDelay), initValue(initValue)
  {
  }

 public:
  void set_clk_0(const char* s)
  {
    __clk_handle_0 = bk_get_or_define_clock(sim_hdl, s);
    bk_alter_clock(sim_hdl,
		   __clk_handle_0,
		   initValue ? CLK_HIGH : CLK_LOW,
		   true,
		   initDelay,
		   initValue ? v2Width : v1Width,   // high duration
		   initValue ? v1Width : v2Width);  // low duration
  }

  void dump_state(unsigned int /* unused */, bool with_label=true) const
  {
  }
  unsigned int dump_VCD_defs(unsigned int num) const
  {
    vcd_write_scope_start(sim_hdl, inst_name);
    vcd_write_def(sim_hdl, bk_clock_vcd_num(sim_hdl, __clk_handle_0), "CLK_OUT", 1);
    vcd_write_scope_end(sim_hdl);
    return (num);
  }
  void dump_VCD(tVCDDumpType /* unused */,
		MOD_ClockGen& /* unused */) const
  {
  }

 private:
  tClock __clk_handle_0;
  tTime v1Width;
  tTime v2Width;
  tTime initDelay;
  unsigned int initValue;
};

// This is the definition of the MakeClock primitive,
// used to implement mkClock.
class MOD_MakeClock : public Module
{
 public:
  MOD_MakeClock(tSimStateHdl simHdl, const char* name, Module* parent,
		tUInt8 initClock, tUInt8 initCond)
    : Module(simHdl, name, parent), __clk_handle_0(BAD_CLOCK_HANDLE),
      initValue(initClock ? CLK_HIGH : CLK_LOW), initGate(initCond),
      in_reset(false)
  {
    current_clk       = initValue;
    old_out_clk       = initValue;
    PORT_CLK_GATE_OUT = initGate;
    new_gate          = initGate;
  }

 public:
  void set_clk_0(const char* s)
  {
    __clk_handle_0 = bk_get_or_define_clock(sim_hdl, s);
    bk_alter_clock(sim_hdl, __clk_handle_0,
		   initValue, true,
		   0, 0, 0); // no pre-defined waveform
    if (initValue == CLK_HIGH)
      bk_enqueue_initial_clock_edge(sim_hdl, __clk_handle_0, POSEDGE);
    else
      bk_enqueue_initial_clock_edge(sim_hdl, __clk_handle_0, NEGEDGE);
  }

  void METH_setClockValue(tUInt8 v)
  {
    if (in_reset) return;
    current_clk = v ? CLK_HIGH : CLK_LOW;
  }

  tUInt8 METH_getClockValue() const
  {
    return ((current_clk == CLK_HIGH) ? 1 : 0);
  }

  void METH_setGateCond(tUInt8 v)
  {
    if (in_reset) return;
    new_gate = v;
  }

  tUInt8 METH_getGateCond() const
  {
    return new_gate;
  }

  void reset_RST(tUInt8 rst)
  {
    in_reset = (rst == 0);
    if (in_reset)
    {
      current_clk       = initValue;
      PORT_CLK_GATE_OUT = initGate;
      new_gate          = initGate;
    }
  }

  // this is called on pos edge of CLK -- modeling latch and clock out
  void clk (tUInt8 /* clock_value */, tUInt8 gate_value = 1)
  {
    if (in_reset) return;
    if (old_out_clk == CLK_LOW && current_clk == CLK_HIGH && PORT_CLK_GATE_OUT != 0)
    {
      // schedule posedge
      bk_trigger_clock_edge(sim_hdl, __clk_handle_0, POSEDGE, bk_now(sim_hdl));
      old_out_clk = CLK_HIGH;
    }
    else if (old_out_clk == CLK_HIGH && current_clk == CLK_LOW)
    {
      // schedule negedge
      bk_trigger_clock_edge(sim_hdl, __clk_handle_0, NEGEDGE, bk_now(sim_hdl));
      old_out_clk = CLK_LOW;
    }

    // Latch -- yes a race condition when clk /^ and gate \_
    if (current_clk == CLK_LOW) {
      PORT_CLK_GATE_OUT = new_gate;
    }
  }

  void rst_tick_clk(tUInt8 /* clock_gate */) const
  {
    // nothing to do
  }

  void dump_state(unsigned int /* unused */, bool with_label=true) const
  {
  }
  unsigned int dump_VCD_defs(unsigned int num)
  {
    vcd_num = vcd_reserve_ids(sim_hdl, 2);
    unsigned int n = vcd_num;
    vcd_write_scope_start(sim_hdl, inst_name);
    vcd_write_def(sim_hdl, bk_clock_vcd_num(sim_hdl, __clk_handle_0), "CLK_OUT", 1);
    vcd_write_def(sim_hdl, n++, "CLK_GATE_OUT", 1);
    vcd_write_def(sim_hdl, n++, "CLK_VAL_OUT", 1);
    vcd_write_scope_end(sim_hdl);
    return (n);
  }
  void dump_VCD(tVCDDumpType dt, MOD_MakeClock& backing)
  {
    unsigned int num = vcd_num;
    if (dt == VCD_DUMP_XS)
    {
      vcd_write_x(sim_hdl, num++, 1);
      vcd_write_x(sim_hdl, num++, 1);
    }
    else if (dt == VCD_DUMP_CHANGES)
    {
      if (PORT_CLK_GATE_OUT != backing.PORT_CLK_GATE_OUT)
	vcd_write_val(sim_hdl, num++, PORT_CLK_GATE_OUT, 1);
      else
	++num;
      if (current_clk != backing.current_clk)
	vcd_write_val(sim_hdl, num++, current_clk, 1);
      else
	++num;
    }
    else
    {
      vcd_write_val(sim_hdl, num++, PORT_CLK_GATE_OUT, 1);
      vcd_write_val(sim_hdl, num++, current_clk, 1);
    }
    backing.current_clk       = current_clk;
    backing.PORT_CLK_GATE_OUT = PORT_CLK_GATE_OUT;
  }

 public:
  tUInt8 PORT_CLK_GATE_OUT;

 private:
  tClock      __clk_handle_0;
  tClockValue initValue;
  tClockValue current_clk;      // register out
  tClockValue old_out_clk;      // module out
  tUInt8      initGate;
  tUInt8      new_gate;
  bool        in_reset;
};


// This is the definition of the ClockInverter primitive,
// used to implement mkClockInverter and mkGatedClockInverter.
class MOD_ClockInverter : public Module
{
 public:
  MOD_ClockInverter(tSimStateHdl simHdl, const char* name, Module* parent)
    : Module(simHdl, name, parent), __clk_handle_0(BAD_CLOCK_HANDLE)
  {
    current_clk = CLK_LOW;
    PORT_CLK_GATE_OUT = 1;
    preedge = false;
  }

 public:
  void set_clk_0(const char* s)
  {
    __clk_handle_0 = bk_get_or_define_clock(sim_hdl, s);
    bk_alter_clock(sim_hdl, __clk_handle_0,
		   CLK_LOW, true,
		   0, 0, 0); // no pre-defined waveform
  }

  tUInt8 METH_clockReady() const
  {
    return 1;
  }

  void clk(tUInt8 clk_value, tUInt8 gate_value = 1)
  {
    tClockValue new_clk = ((clk_value & gate_value) != 0) ? CLK_LOW : CLK_HIGH;
    if (PORT_CLK_GATE_OUT == 0)
      new_clk = CLK_LOW;
    if (new_clk != current_clk)
      bk_trigger_clock_edge(sim_hdl, __clk_handle_0,
			    (new_clk == CLK_HIGH) ? POSEDGE : NEGEDGE,
			    bk_now(sim_hdl));
    current_clk = new_clk;
    if (new_clk == CLK_LOW)
      PORT_CLK_GATE_OUT = gate_value;

    // record for VCD dumping
    clk_in = clk_value;
    clk_gate_in = gate_value;
  }

  void dump_state(unsigned int /* unused */, bool with_label=true) const
  {
  }
  unsigned int dump_VCD_defs(unsigned int num)
  {
    vcd_num = vcd_reserve_ids(sim_hdl, 4);
    unsigned int n = vcd_num;
    vcd_write_scope_start(sim_hdl, inst_name);
    vcd_write_def(sim_hdl, n++, "CLK_IN", 1);
    vcd_write_def(sim_hdl, n++, "CLK_GATE_IN", 1);
    vcd_write_def(sim_hdl, n++, "PREEDGE", 1);
    vcd_write_def(sim_hdl, bk_clock_vcd_num(sim_hdl, __clk_handle_0), "CLK_OUT", 1);
    vcd_write_def(sim_hdl, n++, "CLK_GATE_OUT", 1);
    vcd_write_scope_end(sim_hdl);
    return (n);
  }
  void dump_VCD(tVCDDumpType dt, MOD_ClockInverter& backing)
  {
    unsigned int num = vcd_num;
    if (dt == VCD_DUMP_XS)
    {
      vcd_write_x(sim_hdl, num++, 1);
      vcd_write_x(sim_hdl, num++, 1);
      vcd_write_x(sim_hdl, num++, 1);
      vcd_write_x(sim_hdl, num++, 1);
      preedge = false;
    }
    else if (dt == VCD_DUMP_CHANGES)
    {
      if (clk_in != backing.clk_in)
	vcd_write_val(sim_hdl, num++, clk_in, 1);
      else
	++num;
      if (clk_gate_in != backing.clk_gate_in)
	vcd_write_val(sim_hdl, num++, clk_gate_in, 1);
      else
	++num;
      preedge = true;
      if (preedge != backing.preedge)
	vcd_write_val(sim_hdl, num++, preedge, 1);
      else
	++num;
      if (PORT_CLK_GATE_OUT != backing.PORT_CLK_GATE_OUT)
	vcd_write_val(sim_hdl, num++, PORT_CLK_GATE_OUT, 1);
      else
	++num;
    }
    else
    {
      vcd_write_val(sim_hdl, num++, clk_in, 1);
      vcd_write_val(sim_hdl, num++, clk_gate_in, 1);
      preedge = true;
      vcd_write_val(sim_hdl, num++, preedge, 1);
      vcd_write_val(sim_hdl, num++, PORT_CLK_GATE_OUT, 1);
    }
    backing.clk_in            = clk_in;
    backing.clk_gate_in       = clk_gate_in;
    backing.preedge           = preedge;
    backing.PORT_CLK_GATE_OUT = PORT_CLK_GATE_OUT;
  }

 public:
  tUInt8 PORT_CLK_GATE_OUT;

 private:
  tClock __clk_handle_0;
  tClockValue current_clk;

  // used for VCD dumping
  tUInt8 clk_in;
  tUInt8 clk_gate_in;
  bool   preedge;
};

// This is the definition of the ClockDivider primitive,
// used to implement mkClockDivider, mkClockDividerOffset
// and mkGatedClockDivider.
class MOD_ClockDivider : public Module
{
 public:
  MOD_ClockDivider(tSimStateHdl simHdl, const char* name, Module* parent,
		   unsigned int width,
		   unsigned int lower, unsigned int upper,
		   unsigned int offset)
    : Module(simHdl, name, parent), __clk_handle_0(BAD_CLOCK_HANDLE),
      width(width), lower(lower), upper(upper), offset(offset),
      __clk_handle_1(BAD_CLOCK_HANDLE)
  {
    cntr = upper - offset;
    transition = 1 << (width - 1);
    in_reset = false;
    PORT_CLK_GATE_OUT = 0;
  }

 public:
  void set_clk_0(const char* s)
  {
    tClockValue initValue = (cntr >= transition) ? CLK_HIGH : CLK_LOW;
    __clk_handle_0 = bk_get_or_define_clock(sim_hdl, s);
    bk_alter_clock(sim_hdl, __clk_handle_0,
		   initValue, true,
		   0, 0, 0); // no pre-defined waveform
    if (initValue == CLK_HIGH)
      bk_enqueue_initial_clock_edge(sim_hdl, __clk_handle_0, POSEDGE);
    else
      bk_enqueue_initial_clock_edge(sim_hdl, __clk_handle_0, NEGEDGE);
  }
  void set_clk_1(const char* s)
  {
    __clk_handle_1 = bk_get_or_define_clock(sim_hdl, s);
  }

  tUInt8 METH_clockReady() const
  {
    return (cntr == (transition - 1));
  }

  void clk(tUInt8 /* clk_value */, tUInt8 gate_value = 1)
  {
    if (!in_reset)
    {
      if (cntr < transition)
	PORT_CLK_GATE_OUT = gate_value;
      if (cntr == upper)
      {
	cntr = lower;
	if (PORT_CLK_GATE_OUT != 0)
	{
	  bk_trigger_clock_edge(sim_hdl, __clk_handle_0, NEGEDGE, bk_now(sim_hdl));
	  PORT_CLK_GATE_OUT = gate_value;
	}
      }
      else
      {
	++cntr;
	if ((cntr == transition) && (PORT_CLK_GATE_OUT != 0))
	  bk_trigger_clock_edge(sim_hdl, __clk_handle_0, POSEDGE, bk_now(sim_hdl));
      }
    }
  }

  void reset_RST(tUInt8 rst_in)
  {
    in_reset = (rst_in == 0);
    if (in_reset)
    {
      unsigned int prev_cntr = cntr;
      cntr = upper - offset;
      if ((prev_cntr >= transition) && (cntr < transition))
	bk_trigger_clock_edge(sim_hdl, __clk_handle_0, NEGEDGE, bk_now(sim_hdl));
      else if ((prev_cntr < transition) && (cntr >= transition))
	bk_trigger_clock_edge(sim_hdl, __clk_handle_0, POSEDGE, bk_now(sim_hdl));
      PORT_CLK_GATE_OUT = 0;
    }
  }

  void rst_tick_clk(tUInt8 /* clock_gate */) const
  {
    // nothing to do
  }

  void dump_state(unsigned int /* unused */, bool with_label=true) const
  {
  }
  unsigned int dump_VCD_defs(unsigned int num)
  {
    vcd_num = vcd_reserve_ids(sim_hdl, 2);
    unsigned int n = vcd_num;
    vcd_write_scope_start(sim_hdl, inst_name);
    vcd_write_def(sim_hdl, bk_clock_vcd_num(sim_hdl, __clk_handle_1), "CLK_IN", 1);
    vcd_write_def(sim_hdl, bk_clock_vcd_num(sim_hdl, __clk_handle_0), "CLK_OUT", 1);
    vcd_write_def(sim_hdl, n++, "RST", 1);
    vcd_write_def(sim_hdl, n++, "PREEDGE", 1);
    vcd_write_scope_end(sim_hdl);
    return (n);
  }
  void dump_VCD(tVCDDumpType dt, MOD_ClockDivider& backing)
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
	++num;
      if ((cntr != backing.cntr) &&
	  (cntr == (transition-1) || backing.cntr != (transition - 1)))
	vcd_write_val(sim_hdl, num++, cntr == (transition - 1), 1);
      else
	++num;
    }
    else
    {
      vcd_write_val(sim_hdl, num++, !in_reset, 1);
      vcd_write_val(sim_hdl, num++, cntr == (transition - 1), 1);
    }
    backing.in_reset = in_reset;
    backing.cntr     = cntr;
  }

 public:
  tUInt8 PORT_CLK_GATE_OUT;

 private:
  tClock       __clk_handle_0;
  unsigned int width;
  unsigned int lower;
  unsigned int upper;
  unsigned int offset;
  unsigned int cntr;
  unsigned int transition;
  bool         in_reset;

  // used for VCD dumping
  tClock __clk_handle_1;
};

#endif /* __BS_PRIM_MOD_CLOCKGEN_H__ */
