#ifndef __BS_PRIM_MOD_GATEDCLOCK_H__
#define __BS_PRIM_MOD_GATEDCLOCK_H__

#include "bluesim_kernel_api.h"
#include "bs_module.h"
#include "bs_vcd.h"

// This is the definition of the GatedClock primitive.
// It has an internal register, to delay the gate change by a cycle.
// The implementation here is similar to ConfigReg, so that the new_clk
// method (for reading the output gate) is always the old value of the
// internal register, even if setGateCond has been called in this cycle.
class MOD_GatedClock : public Module
{
 public:
  MOD_GatedClock(tSimStateHdl simHdl, const char* name, Module* parent,
		 tUInt8 v)
    : Module(simHdl, name, parent), written(~bk_now(sim_hdl)),
      clk_in_hdl(BAD_CLOCK_HANDLE), clk_in_gate(0), reg_reset_value(v)
  {
    PORT_CLK_GATE_OUT = 0;
    write_undet(&reg, 1);
    in_reset = false;
    suppress_write = false;
  }

 private:

  // this represents the latch, and it should be called when on falling
  // edges of the clock, or when the reg or gate value changes while the
  // clock is low.
  void update_new_gate()
  {
    if ((clk_in_hdl != BAD_CLOCK_HANDLE) &&
	(bk_clock_val(sim_hdl, clk_in_hdl) == CLK_LOW))
      PORT_CLK_GATE_OUT = clk_in_gate & reg;
  }

 public:
  // record clock handle
  void set_clk_0(const char* s)
  {
    clk_in_hdl = bk_get_clock_by_name(sim_hdl, s);
  }

  // the following four member functions are based on RegA
  tUInt8 METH_getGateCond()
  {
    return reg;
  }

  void METH_setGateCond(tUInt8 gate)
  {
    // asynchronous reset
    if (!suppress_write)
    {
      reg = gate;
      update_new_gate();
    }
  }

  void reset_RST(tUInt8 rst_in)
  {
    in_reset = (rst_in == 0);
    if (in_reset) {
      // reset is asynchronous
      suppress_write = true;
      reg = reg_reset_value;
      update_new_gate();
    } else {
      suppress_write = false;
    }
  }

  void rst_tick_clk(tUInt8 /* clock_gate */) { /* nothing to do */ }

  // this is called on both edges of CLK
  void clk_in (tUInt8 clock_value, tUInt8 gate_value = 1)
  {
    clk_in_gate = gate_value;
    update_new_gate();
  }

 public:
  void dump_state(unsigned int indent)
  {
    printf("%*s%s:\n", indent, "", inst_name);
    printf("%*snew_gate = ", indent+2, "");
    dump_val(PORT_CLK_GATE_OUT, 1);
    putchar('\n');
  }
  unsigned int dump_VCD_defs(unsigned int /* num */)
  {
    vcd_num = vcd_reserve_ids(sim_hdl, 1);
    vcd_write_scope_start(sim_hdl, inst_name);
    vcd_write_def(sim_hdl, vcd_num, "new_gate", 1);
    vcd_write_scope_end(sim_hdl);
    return (vcd_num + 1);
  }
  void dump_VCD(tVCDDumpType dt, MOD_GatedClock& backing)
  {
    if (dt == VCD_DUMP_XS)
      vcd_write_x(sim_hdl, vcd_num, 1);
    else if ((dt != VCD_DUMP_CHANGES) ||
	     (backing.PORT_CLK_GATE_OUT != PORT_CLK_GATE_OUT))
    {
      vcd_write_val(sim_hdl, vcd_num, PORT_CLK_GATE_OUT, 1);
      backing.PORT_CLK_GATE_OUT = PORT_CLK_GATE_OUT;
    }
  }

 public:
  tUInt8 PORT_CLK_GATE_OUT;

 private:
  tTime written;
  // simulate the latch
  tClock clk_in_hdl;
  tUInt8 clk_in_gate;
  // to support the internal RegA
  tUInt8 reg;
  tUInt8 reg_reset_value;
  bool suppress_write;
  bool in_reset;
};

#endif /* __BS_PRIM_MOD_GATEDCLOCK_H__ */
