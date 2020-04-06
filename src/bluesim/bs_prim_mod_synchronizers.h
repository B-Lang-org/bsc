#ifndef __BS_PRIM_MOD_SYNCHRONIZERS_H__
#define __BS_PRIM_MOD_SYNCHRONIZERS_H__

#include "bluesim_kernel_api.h"
#include "bs_module.h"
#include "bs_vcd.h"

// This is a helper class we use manage race conditions at
// clock domain crossings.  A SyncVar allows us to read a
// variable in one domain that was written from a different
// domain at the same time, and see the previous value.
// This mimics the Verilog behavior of a non-blocking write
// that updates at the of the simulation cycle.
template<typename T>
class SyncVar
{
 public:
  SyncVar(tSimStateHdl simHdl, unsigned int width)
    : sim_hdl(simHdl), bits(width)
  {
    init_val(prev_value, bits);
    write_undet(&prev_value, bits);
    init_val(value, bits);
    write_undet(&value, bits);
    written_at = ~bk_now(sim_hdl);
  }
 public:
  const T& read() const
  {
    if (bk_is_same_time(sim_hdl, written_at))
      return prev_value;
    else
      return value;
  }
  const T& probe() const { return value; }
  void write(const T& x)
  {
    prev_value = value;
    value = x;
    written_at = bk_now(sim_hdl);
  }
  void force(const T& x)
  {
    prev_value = x;
    value = x;
  }
 public:
  SyncVar<T>& operator=(const SyncVar<T>& sv)
  {
    prev_value = sv.prev_value;
    value = sv.value;
    written_at = sv.written_at;
    return (*this);
  }
 private:
  tSimStateHdl sim_hdl;
  const unsigned int bits;
  T prev_value;
  T value;
  tTime written_at;
};

// Simple uni-directional synchronizers

// This is the definition used for 1-bit synchronizer primitives
// with a 2-destination-clock-cycle delay.
class MOD_Sync2 : public Module
{
 public:
  MOD_Sync2(tSimStateHdl simHdl, const char* name, Module* parent, tUInt8 v)
    : Module(simHdl, name, parent), sSyncReg(simHdl, 1), reset_value(v)
  {
    init_val(dSyncReg1, 1);
    write_undet(&dSyncReg1, 1);
    init_val(dSyncReg2, 1);
    write_undet(&dSyncReg2, 1);
    in_reset = false;
  }
 public:
  const tUInt8 METH_read() const  { return dSyncReg2; }

  void METH_send(tUInt8 x) { if (!in_reset) sSyncReg.write(x); }

  void clk_dst(tUInt8 /* clock_value */, tUInt8 gate_value = 1)
  {
    if (gate_value == 0) return;

    dSyncReg2 = dSyncReg1;
    dSyncReg1 = sSyncReg.read();
  }

  void reset_sRST(tUInt8 rst_in)
  {
    in_reset = (rst_in == 0);
    if (in_reset)
    {
      dSyncReg1 = dSyncReg2 = reset_value;
      sSyncReg.force(reset_value);
    }
  }
  void rst_tick_clk_src(tUInt8 /* clock_gate */) { /* unused */ }
 public:
  void dump_state(unsigned int indent)
  {
    printf("%*s%s:\n", indent, "", inst_name);
    printf("%*sdSyncReg1 = ", indent+2, "");
    dump_val(dSyncReg1, 1);
    putchar('\n');
    printf("%*sdSyncReg2 = ", indent+2, "");
    dump_val(dSyncReg2, 1);
    putchar('\n');
    printf("%*ssSyncReg = ", indent+2, "");
    dump_val(sSyncReg.read(), 1);
    putchar('\n');
  }
  unsigned int dump_VCD_defs(unsigned int /* num */)
  {
    vcd_num = vcd_reserve_ids(sim_hdl, 3);
    vcd_write_scope_start(sim_hdl, inst_name);
    vcd_write_def(sim_hdl, vcd_num,   "dSyncReg1", 1);
    vcd_write_def(sim_hdl, vcd_num+1, "dSyncReg2", 1);
    vcd_write_def(sim_hdl, vcd_num+2, "sSyncReg",  1);
    vcd_write_scope_end(sim_hdl);
    return (vcd_num + 3);
  }
  void dump_VCD(tVCDDumpType dt, MOD_Sync2& backing)
  {
    if (dt == VCD_DUMP_XS)
    {
      vcd_write_x(sim_hdl, vcd_num,   1);
      vcd_write_x(sim_hdl, vcd_num+1, 1);
      vcd_write_x(sim_hdl, vcd_num+2, 1);
    }
    else
    {
      if ((dt != VCD_DUMP_CHANGES) || (backing.dSyncReg1 != dSyncReg1))
      {
	vcd_write_val(sim_hdl, vcd_num, dSyncReg1, 1);
	backing.dSyncReg1 = dSyncReg1;
      }
      if ((dt != VCD_DUMP_CHANGES) || (backing.dSyncReg2 != dSyncReg2))
      {
	vcd_write_val(sim_hdl, vcd_num+1, dSyncReg2, 1);
	backing.dSyncReg2 = dSyncReg2;
      }
      if ((dt != VCD_DUMP_CHANGES) ||
	  (backing.sSyncReg.read() != sSyncReg.read()))
      {
	vcd_write_val(sim_hdl, vcd_num+2, sSyncReg.read(),  1);
	backing.sSyncReg = sSyncReg;
      }
    }
  }

 private:
  tUInt8 dSyncReg1;
  tUInt8 dSyncReg2;
  SyncVar<tUInt8> sSyncReg;
  tUInt8 reset_value;
  bool in_reset;
};

// This is the definition used for synchronizer primitives
// with a 1.5-destination-clock-cycle delay.
class MOD_Sync15 : public Module
{
 public:
  MOD_Sync15(tSimStateHdl simHdl, const char* name, Module* parent, tUInt8 v)
    : Module(simHdl, name, parent), sSyncReg(simHdl, 1), reset_value(v)
  {
    init_val(dSyncReg1, 1);
    write_undet(&dSyncReg1, 1);
    init_val(dSyncReg2, 1);
    write_undet(&dSyncReg2, 1);
    in_reset = false;
  }
 public:
  const tUInt8 METH_read() const  { return dSyncReg2; }
  void METH_send(tUInt8 x) { if (!in_reset) sSyncReg.write(x); }
  void clk_dst(tUInt8 clock_value, tUInt8 gate_value = 1)
  {
    if (gate_value == 0) return;

    if (clock_value != 0)
      dSyncReg2 = dSyncReg1;
    else
      dSyncReg1 = sSyncReg.read();
  }
  void reset_sRST(tUInt8 rst_in)
  {
    in_reset = (rst_in == 0);
    if (in_reset)
    {
      dSyncReg2 = dSyncReg1 = reset_value;
      sSyncReg.force(reset_value);
    }
  }
  void rst_tick_clk_src(tUInt8 /* clock_gate */) { /* unused */ }
 public:
  void dump_state(unsigned int indent)
  {
    printf("%*s%s:\n", indent, "", inst_name);
    printf("%*sdSyncReg1 = ", indent+2, "");
    dump_val(dSyncReg1, 1);
    putchar('\n');
    printf("%*sdSyncReg2 = ", indent+2, "");
    dump_val(dSyncReg2, 1);
    putchar('\n');
    printf("%*ssSyncReg = ", indent+2, "");
    dump_val(sSyncReg.read(), 1);
    putchar('\n');
  }
  unsigned int dump_VCD_defs(unsigned int /* num */)
  {
    vcd_num = vcd_reserve_ids(sim_hdl, 3);
    vcd_write_scope_start(sim_hdl, inst_name);
    vcd_write_def(sim_hdl, vcd_num,   "dSyncReg1", 1);
    vcd_write_def(sim_hdl, vcd_num+1, "dSyncReg2", 1);
    vcd_write_def(sim_hdl, vcd_num+2, "sSyncReg",  1);
    vcd_write_scope_end(sim_hdl);
    return (vcd_num + 3);
  }
  void dump_VCD(tVCDDumpType dt, MOD_Sync15& backing)
  {
    if (dt == VCD_DUMP_XS)
    {
      vcd_write_x(sim_hdl, vcd_num,   1);
      vcd_write_x(sim_hdl, vcd_num+1, 1);
      vcd_write_x(sim_hdl, vcd_num+2, 1);
    }
    else
    {
      if ((dt != VCD_DUMP_CHANGES) || (backing.dSyncReg1 != dSyncReg1))
      {
	vcd_write_val(sim_hdl, vcd_num, dSyncReg1, 1);
	backing.dSyncReg1 = dSyncReg1;
      }
      if ((dt != VCD_DUMP_CHANGES) || (backing.dSyncReg2 != dSyncReg2))
      {
	vcd_write_val(sim_hdl, vcd_num+1, dSyncReg2, 1);
	backing.dSyncReg2 = dSyncReg2;
      }
      if ((dt != VCD_DUMP_CHANGES) ||
	  (backing.sSyncReg.read() != sSyncReg.read()))
      {
	vcd_write_val(sim_hdl, vcd_num+2, sSyncReg.read(), 1);
	backing.sSyncReg = sSyncReg;
      }
    }
  }

 private:
  tUInt8 dSyncReg1;
  tUInt8 dSyncReg2;
  SyncVar<tUInt8> sSyncReg;
  tUInt8 reset_value;
  bool in_reset;
};

// This is the definition used for synchronizer primitives
// with a 1-destination-clock-cycle delay.  It is also used
// for 0.5-destination-clock-cycle delay, since the only difference
// is whether clk_dst() is called on posedge or negedge.
class MOD_Sync1 : public Module
{
 public:
  MOD_Sync1(tSimStateHdl simHdl, const char* name, Module* parent, tUInt8 v)
    : Module(simHdl, name, parent), sSyncReg(simHdl, 1), reset_value(v)
  {
    init_val(dSyncReg1, 1);
    write_undet(&dSyncReg1, 1);
    in_reset = false;
  }
 public:
  const tUInt8 METH_read() const  { return dSyncReg1; }

  void METH_send(tUInt8 x) { if (!in_reset) sSyncReg.write(x); }

  void clk_dst(tUInt8 /* clock_value */, tUInt8 gate_value = 1)
  {
    if (gate_value == 0) return;

    dSyncReg1 = sSyncReg.read();
  }

  void reset_sRST(tUInt8 rst_in)
  {
    in_reset = (rst_in == 0);
    if (in_reset)
    {
      dSyncReg1 = reset_value;
      sSyncReg.force(reset_value);
    }
  }
  void rst_tick_clk_src(tUInt8 /* clock_gate */) { /* unused */ }
 public:
  void dump_state(unsigned int indent)
  {
    printf("%*s%s:\n", indent, "", inst_name);
    printf("%*sdSyncReg1 = ", indent+2, "");
    dump_val(dSyncReg1, 1);
    putchar('\n');
    printf("%*ssSyncReg = ", indent+2, "");
    dump_val(sSyncReg.read(), 1);
    putchar('\n');
  }
  unsigned int dump_VCD_defs(unsigned int /* num */)
  {
    vcd_num = vcd_reserve_ids(sim_hdl, 2);
    vcd_write_scope_start(sim_hdl, inst_name);
    vcd_write_def(sim_hdl, vcd_num,   "dSyncReg1", 1);
    vcd_write_def(sim_hdl, vcd_num+1, "sSyncReg",  1);
    vcd_write_scope_end(sim_hdl);
    return (vcd_num + 2);
  }
  void dump_VCD(tVCDDumpType dt, MOD_Sync1& backing)
  {
    if (dt == VCD_DUMP_XS)
    {
      vcd_write_x(sim_hdl, vcd_num,   1);
      vcd_write_x(sim_hdl, vcd_num+1, 1);
    }
    else
    {
      if ((dt != VCD_DUMP_CHANGES) || (backing.dSyncReg1 != dSyncReg1))
      {
	vcd_write_val(sim_hdl, vcd_num, dSyncReg1, 1);
	backing.dSyncReg1 = dSyncReg1;
      }
      if ((dt != VCD_DUMP_CHANGES) ||
	  (backing.sSyncReg.read() != sSyncReg.read()))
      {
	vcd_write_val(sim_hdl, vcd_num+1, sSyncReg.read(), 1);
	backing.sSyncReg = sSyncReg;
      }
    }
  }

 private:
  tUInt8 dSyncReg1;
  SyncVar<tUInt8> sSyncReg;
  tUInt8 reset_value;
  bool in_reset;
};

// Pulse synchronizers

// A pulse synchronizer is a uni-directional synchronizer
// based on transmitting a pulse across clock domains.
class MOD_SyncPulse : public Module
{
 public:
  MOD_SyncPulse(tSimStateHdl simHdl, const char* name, Module* parent)
    : Module(simHdl, name, parent), sSyncReg(simHdl, 1)
  {
    init_val(dSyncReg1, 1);
    write_undet(&dSyncReg1, 1);
    init_val(dSyncReg2, 1);
    write_undet(&dSyncReg2, 1);
    init_val(dSyncPulse, 1);
    write_undet(&dSyncPulse, 1);
    in_reset = false;
  }
 public:
  tUInt8 METH_pulse() const  { return (dSyncReg2 ^ dSyncPulse) ? 0x1 : 0x0; }
  void METH_send()
  {
    if (!in_reset)
      sSyncReg.write((sSyncReg.read() == 0) ? 0x1 : 0x0);
  }
  void clk_dst(tUInt8 /* clock_value */, tUInt8 gate_value = 1)
  {
    if (gate_value == 0) return;

    dSyncPulse = dSyncReg2;
    dSyncReg2 = dSyncReg1;
    dSyncReg1 = sSyncReg.read();
  }
  void reset_sRST(tUInt8 rst_in)
  {
    in_reset = (rst_in == 0);
    if (in_reset)
    {
      dSyncPulse = dSyncReg2 = dSyncReg1 = 0;
      sSyncReg.force(0);
    }
  }
  void rst_tick_clk_src(tUInt8 /* clock_gate */) { /* unused */ }
 public:
  void dump_state(unsigned int indent)
  {
    printf("%*s%s:\n", indent, "", inst_name);
    printf("%*sdSyncReg1 = ", indent+2, "");
    dump_val(dSyncReg1, 1);
    putchar('\n');
    printf("%*sdSyncReg2 = ", indent+2, "");
    dump_val(dSyncReg2, 1);
    putchar('\n');
    printf("%*sdSyncPulse = ", indent+2, "");
    dump_val(dSyncPulse, 1);
    putchar('\n');
    printf("%*ssSyncReg = ", indent+2, "");
    dump_val(sSyncReg.read(), 1);
    putchar('\n');
  }
  unsigned int dump_VCD_defs(unsigned int /* num */)
  {
    vcd_num = vcd_reserve_ids(sim_hdl, 4);
    vcd_write_scope_start(sim_hdl, inst_name);
    vcd_write_def(sim_hdl, vcd_num,   "dSyncReg1", 1);
    vcd_write_def(sim_hdl, vcd_num+1, "dSyncReg2", 1);
    vcd_write_def(sim_hdl, vcd_num+2, "dSyncPulse", 1);
    vcd_write_def(sim_hdl, vcd_num+3, "sSyncReg",  1);
    vcd_write_scope_end(sim_hdl);
    return (vcd_num + 4);
  }
  void dump_VCD(tVCDDumpType dt, MOD_SyncPulse& backing)
  {
    if (dt == VCD_DUMP_XS)
    {
      vcd_write_x(sim_hdl, vcd_num,   1);
      vcd_write_x(sim_hdl, vcd_num+1, 1);
      vcd_write_x(sim_hdl, vcd_num+2, 1);
      vcd_write_x(sim_hdl, vcd_num+3, 1);
    }
    else
    {
      if ((dt != VCD_DUMP_CHANGES) || (backing.dSyncReg1 != dSyncReg1))
      {
	vcd_write_val(sim_hdl, vcd_num, dSyncReg1, 1);
	backing.dSyncReg1 = dSyncReg1;
      }
      if ((dt != VCD_DUMP_CHANGES) || (backing.dSyncReg2 != dSyncReg2))
      {
	vcd_write_val(sim_hdl, vcd_num+1, dSyncReg2, 1);
	backing.dSyncReg2 = dSyncReg2;
      }
      if ((dt != VCD_DUMP_CHANGES) || (backing.dSyncPulse != dSyncPulse))
      {
	vcd_write_val(sim_hdl, vcd_num+2, dSyncPulse, 1);
	backing.dSyncPulse = dSyncPulse;
      }
      if ((dt != VCD_DUMP_CHANGES) ||
	  (backing.sSyncReg.read() != sSyncReg.read()))
      {
	vcd_write_val(sim_hdl, vcd_num+3, sSyncReg.read(),  1);
	backing.sSyncReg = sSyncReg;
      }
    }
  }

 private:
  tUInt8 dSyncReg1;
  tUInt8 dSyncReg2;
  tUInt8 dSyncPulse;
  SyncVar<tUInt8> sSyncReg;
  bool in_reset;
};

// Handshaking synchronizers

// A handshake synchronizer is a pulse synchronizer which feeds
// synchronization information back from the destination domain
// to ensure that the next pulse cannot be transmitted until the
// previous pulse has become visible in the destination domain.
class MOD_SyncHandshake : public Module
{
 public:
  MOD_SyncHandshake(tSimStateHdl simHdl, const char* name, Module* parent
                    ,bool init = 0, bool delayreturn = false)
    : Module(simHdl, name, parent),
      dSyncReg2(simHdl, 1)
    , dLastState(simHdl, 1)
    , sToggleReg(simHdl, 1)
    , param_init(init)
    , param_delayreturn(delayreturn)
    , __clk_handle_0(BAD_CLOCK_HANDLE)
    , __clk_handle_1(BAD_CLOCK_HANDLE)
  {
    init_val(sSyncReg1, 1);
    write_undet(&sSyncReg1, 1);
    init_val(sSyncReg2, 1);
    write_undet(&sSyncReg2, 1);
    init_val(sRDY, 0);
    sRDY = 0;

    init_val(dSyncReg1, 1);
    write_undet(&dSyncReg1, 1);

    sSyncReg1 = 1;
    sSyncReg2 = 1;

    en = false;
    did_send = false;
    pulsing = false;

    in_reset = false;
  }
 public:
  tUInt8 METH_pulse() const  { return (dSyncReg2.read() != dLastState.read()) ? 0x1 : 0x0; }
  void METH_send() { en = true; }
  bool METH_RDY_send() const { return (!in_reset && (sRDY != 0)); }
  void clk_src(tUInt8 /* clock_value */, tUInt8 gate_value = 1)
  {
    if (gate_value == 0) return;

    if (!in_reset) {
      sSyncReg2 = sSyncReg1;
      sSyncReg1 = param_delayreturn ? dLastState.read() : dSyncReg2.read();
    }

    if (en)
    {
      sToggleReg.write((sToggleReg.read() == 0) ? 0x1 : 0x0);
      sRDY = 0;
    }
    else
      sRDY = (sSyncReg2 == sToggleReg.read());

    did_send = en;
    en = false;
  }
  void clk_dst(tUInt8 /* clock_value */, tUInt8 gate_value = 1)
  {
    if (gate_value == 0) return;

    dLastState.write (dSyncReg2.read());
    dSyncReg2.write(dSyncReg1);
    dSyncReg1 = sToggleReg.read();
    pulsing = dLastState.probe() != dSyncReg2.probe();
  }

  void set_clk_0(const char* s)
  {
    __clk_handle_0 = bk_get_or_define_clock(sim_hdl, s);
  }

  void set_clk_1(const char* s)
  {
    __clk_handle_1 = bk_get_or_define_clock(sim_hdl, s);
  }

  void reset_sRST(tUInt8 rst_in)
  {
    in_reset = (rst_in == 0);
    if (in_reset)
    {
      dSyncReg2.force(param_init ? 1 : 0);
      sToggleReg.force(param_init ? 1 : 0);
      dSyncReg1 = param_init ? 1 : 0;
      dLastState.force (param_init ? 1 : 0);
      sSyncReg1 = param_init ? 0 : 1; /* ! init */
      sSyncReg2 = param_init ? 0 : 1; /* ! init */
      sRDY = 0;
      en = false;
      pulsing = false;
    }
  }
  void rst_tick_clk_src(tUInt8 /* clock_gate */) { /* unused */ }
 public:
  void dump_state(unsigned int indent)
  {
    printf("%*s%s:\n", indent, "", inst_name);
    printf("%*sdSyncReg1 = ", indent+2, "");
    dump_val(dSyncReg1, 1);
    putchar('\n');
    printf("%*sdSyncReg2 = ", indent+2, "");
    dump_val(dSyncReg2.read(), 1);
    putchar('\n');
    printf("%*sdLastState = ", indent+2, "");
    dump_val(dLastState.read(), 1);
    putchar('\n');
    printf("%*ssToggleReg = ", indent+2, "");
    dump_val(sToggleReg.read(), 1);
    putchar('\n');
    printf("%*ssSyncReg1 = ", indent+2, "");
    dump_val(sSyncReg1, 1);
    putchar('\n');
    printf("%*ssSyncReg2 = ", indent+2, "");
    dump_val(sSyncReg2, 1);
    putchar('\n');
    printf("%*ssRDY = ", indent+2, "");
    dump_val(sRDY, 1);
    putchar('\n');
  }
  unsigned int dump_VCD_defs(unsigned int /* num */)
  {
    vcd_num = vcd_reserve_ids(sim_hdl, 12);
    unsigned int n = vcd_num;
    vcd_write_scope_start(sim_hdl, inst_name);
    vcd_write_def(sim_hdl, n++, "dSyncReg1", 1);
    vcd_write_def(sim_hdl, n++, "dSyncReg2", 1);
    vcd_write_def(sim_hdl, n++, "dLastState", 1);
    vcd_write_def(sim_hdl, n++, "sToggleReg", 1);
    vcd_write_def(sim_hdl, n++, "sSyncReg1", 1);
    vcd_write_def(sim_hdl, n++, "sSyncReg2", 1);
    vcd_write_def(sim_hdl, n++, "sRDY", 1);
    vcd_set_clock(sim_hdl, n, __clk_handle_0);
    vcd_write_def(sim_hdl, n++, "sEN", 1);
    vcd_write_def(sim_hdl, bk_clock_vcd_num(sim_hdl, __clk_handle_0), "sCLK", 1);
    vcd_write_def(sim_hdl, bk_clock_vcd_num(sim_hdl, __clk_handle_1), "dCLK", 1);
    vcd_write_def(sim_hdl, n++, "sRST", 1);
    vcd_write_def(sim_hdl, n++, "dPulse", 1);
    vcd_write_scope_end(sim_hdl);
    return (n);
  }
  void dump_VCD(tVCDDumpType dt, MOD_SyncHandshake& backing)
  {
    unsigned int num = vcd_num;
    if (dt == VCD_DUMP_XS)
    {
      vcd_write_x(sim_hdl, num++, 1);
      vcd_write_x(sim_hdl, num++, 1);
      vcd_write_x(sim_hdl, num++, 1);
      vcd_write_x(sim_hdl, num++, 1);
      vcd_write_x(sim_hdl, num++, 1);
      vcd_write_x(sim_hdl, num++, 1);
      vcd_write_x(sim_hdl, num++, 1);
      vcd_write_x(sim_hdl, num++, 1);
      vcd_write_x(sim_hdl, num++, 1);
      vcd_write_x(sim_hdl, num++, 1);
    }
    else if (dt == VCD_DUMP_CHANGES)
    {
      if (backing.dSyncReg1 != dSyncReg1)
	vcd_write_val(sim_hdl, num++, dSyncReg1, 1);
      else
	num++;
      if (backing.dSyncReg2.probe() != dSyncReg2.probe())
	vcd_write_val(sim_hdl, num++, dSyncReg2.probe(), 1);
      else
	num++;
      if (backing.dLastState.probe() != dLastState.probe())
	vcd_write_val(sim_hdl, num++, dLastState.probe(), 1);
      else
	num++;
      if (backing.sToggleReg.probe() != sToggleReg.probe())
	vcd_write_val(sim_hdl, num++, sToggleReg.probe(), 1);
      else
	num++;
      if (backing.sSyncReg1 != sSyncReg1)
	vcd_write_val(sim_hdl, num++, sSyncReg1, 1);
      else
	num++;
      if (backing.sSyncReg2 != sSyncReg2)
	vcd_write_val(sim_hdl, num++, sSyncReg2, 1);
      else
	num++;
      if (backing.sRDY != sRDY)
	vcd_write_val(sim_hdl, num++, sRDY, 1);
      else
	num++;
      if (backing.did_send != did_send)
      {
	vcd_write_val(sim_hdl, num++, did_send, 1);
	backing.did_send = did_send;
      }
      else
	num++;
      if (backing.in_reset != in_reset)
	vcd_write_val(sim_hdl, num++, !in_reset, 1);
      else
	num++;
      if (backing.pulsing != pulsing)
	vcd_write_val(sim_hdl, num++, pulsing, 1);
      else
	num++;
    }
    else
    {
      vcd_write_val(sim_hdl, num++, dSyncReg1, 1);
      vcd_write_val(sim_hdl, num++, dSyncReg2.probe(), 1);
      vcd_write_val(sim_hdl, num++, dLastState.probe(), 1);
      vcd_write_val(sim_hdl, num++, sToggleReg.probe(), 1);
      vcd_write_val(sim_hdl, num++, sSyncReg1, 1);
      vcd_write_val(sim_hdl, num++, sSyncReg2, 1);
      vcd_write_val(sim_hdl, num++, sRDY, 1);
      vcd_write_val(sim_hdl, num++, did_send, 1);
      backing.did_send = did_send;
      vcd_write_val(sim_hdl, num++, !in_reset, 1);
      vcd_write_val(sim_hdl, num++, pulsing, 1);
    }
    backing.dSyncReg1 = dSyncReg1;
    backing.dSyncReg2 = dSyncReg2;
    backing.dLastState = dLastState;
    backing.sToggleReg = sToggleReg;
    backing.sSyncReg1 = sSyncReg1;
    backing.sSyncReg2 = sSyncReg2;
    backing.sRDY = sRDY;
    backing.pulsing = pulsing;
  }

 private:
  tUInt8 dSyncReg1;
  SyncVar<tUInt8> dSyncReg2;
  SyncVar<tUInt8> dLastState;
  SyncVar<tUInt8> sToggleReg;
  tUInt8 sSyncReg1;
  tUInt8 sSyncReg2;
  tUInt8 sRDY;
  bool en;
  bool in_reset;
  bool pulsing;
  bool param_init;
  bool param_delayreturn;

  // used for VCD dumping
  tClock __clk_handle_0; // sCLK
  tClock __clk_handle_1; // dCLK
  bool did_send;
};

// Synchronized registers

template<typename T>
class MOD_SyncReg : public Module
{
 public:
  MOD_SyncReg(tSimStateHdl simHdl, const char* name, Module* parent,
	      unsigned int width, const T& v)
    : Module(simHdl, name, parent), sDataSyncIn(simHdl, width), reset_value(v),
    sync(simHdl, "sync", this, false, true), bits(width)
  {
    init_val(dD_OUT, bits);
    write_undet(&dD_OUT, bits);
    in_reset = false;
  }
  MOD_SyncReg(tSimStateHdl simHdl, const char* name, Module* parent,
	      unsigned int width)
    : Module(simHdl, name, parent), sync(simHdl, "sync", this),
      sDataSyncIn(simHdl, width), bits(width)
  {
    init_val(dD_OUT, bits);
    write_undet(&dD_OUT, bits);
    init_val(reset_value, bits);
    write_undet(reset_value, bits);
    in_reset = false;
  }
 public:
  const T& METH_read() const  { return dD_OUT; }
  bool METH_RDY_write() const { return sync.METH_RDY_send(); }
  void METH_write(const T& x)
  {
    sDataSyncIn.write(x);
    sync.METH_send();
  }
  void clk_src(tUInt8 clock_value, tUInt8 gate_value = 1)
  {
    if (gate_value == 0) return;

    sync.clk_src(clock_value, gate_value);
  }
  void clk_dst(tUInt8 clock_value, tUInt8 gate_value = 1)
  {
    if (gate_value == 0) return;

    if (sync.METH_pulse())
      dD_OUT = sDataSyncIn.read();
    sync.clk_dst(clock_value, gate_value);
  }
  void reset_sRST(tUInt8 rst_in)
  {
    in_reset = (rst_in == 0);
    sync.reset_sRST(rst_in);
    if (in_reset)
    {
      sDataSyncIn.force(reset_value);
      dD_OUT = reset_value;
    }
  }
  void rst_tick_clk_src(tUInt8 /* clock_gate */) { /* unused */ }
 public:
  void dump_state(unsigned int indent)
  {
    printf("%*s%s:\n", indent, "", inst_name);
    printf("%*sdD_OUT = ", indent+2, "");
    dump_val(dD_OUT, bits);
    putchar('\n');
    printf("%*ssDataSyncIn = ", indent+2, "");
    dump_val(sDataSyncIn.read(), bits);
    putchar('\n');
    sync.dump_state(indent + 2);
  }
  unsigned int dump_VCD_defs(unsigned int /* num */)
  {
    vcd_num = vcd_reserve_ids(sim_hdl, 2);
    vcd_write_scope_start(sim_hdl, inst_name);
    vcd_write_def(sim_hdl, vcd_num,   "dD_OUT", bits);
    vcd_write_def(sim_hdl, vcd_num+1, "sDataSyncIn", bits);
    unsigned int n = sync.dump_VCD_defs(vcd_num + 2);
    vcd_write_scope_end(sim_hdl);
    return (n);
  }
  void dump_VCD(tVCDDumpType dt, MOD_SyncReg<T>& backing)
  {
    if (dt == VCD_DUMP_XS)
    {
      vcd_write_x(sim_hdl, vcd_num,   bits);
      vcd_write_x(sim_hdl, vcd_num+1, bits);
    }
    else
    {
      if ((dt != VCD_DUMP_CHANGES) || (backing.dD_OUT != dD_OUT))
      {
	vcd_write_val(sim_hdl, vcd_num, dD_OUT, bits);
	backing.dD_OUT = dD_OUT;
      }
      if ((dt != VCD_DUMP_CHANGES) ||
	  (backing.sDataSyncIn.read() != sDataSyncIn.read()))
      {
	vcd_write_val(sim_hdl, vcd_num+1, sDataSyncIn.read(), bits);
	backing.sDataSyncIn = sDataSyncIn;
      }
    }
    sync.dump_VCD(dt, backing.sync);
  }

 private:
  SyncVar<T> sDataSyncIn;
  T dD_OUT;
  T reset_value;
  MOD_SyncHandshake sync;
  bool in_reset;
  const unsigned int bits;
};


// Synchronized FIFOs

template<typename T, typename I>
const unsigned int* index_fn_syncfifo(void* base, tUInt64 addr);

static unsigned int index_size(unsigned int d)
{
    unsigned int sz = 0;
    while (d != 0)
    {
      ++sz;
      d = d >> 1;
    }
    return sz;
}

template<typename T, typename I>
class MOD_SyncFIFO : public Module
{
 public:
  MOD_SyncFIFO<T,I>(tSimStateHdl simHdl, const char* name, Module* parent,
		    unsigned int width, unsigned int depth, unsigned int hasClr)
    : Module(simHdl, name, parent), width(width), depth(depth),
      src_hi(simHdl, index_size(depth)+1), dst_lo(simHdl, index_size(depth)+1),
      hasClear(hasClr),
      sClrSync(simHdl, "sClrSync", this), dClrSync(simHdl, "dClrSync", this)
  {
    data = new T[depth];
    for (unsigned int n = 0; n < depth; ++n)
      init_val(data[n], width);
    init_val(dDoutReg, width);

    idx_bits = index_size(depth);
    mask = (1 << idx_bits) - 1;

    src_lo = 0;
    dst_hi = 0;
    src_hi_plus_1 = 1;
    dst_lo_plus_1 = 1;
    dSyncReg1 = 0;
    sSyncReg1 = 0;

    init_val(sCountReg, idx_bits);
    sCountReg = 0;
    init_val(dCountReg, idx_bits);
    dCountReg = 0;

    not_empty = false;
    not_full = true;
    in_reset = false;
    s_reset = false;
    d_reset = false;
    did_enq = false;
    did_deq = false;
    did_sclear = false;
    did_dclear = false;

    symbol_count = 3;
    symbols = new tSym[symbol_count];

    range.lo = 0;
    range.hi = depth - 1;
    range.base = (void*) this;
    range.fetch = index_fn_syncfifo<T,I>;

    symbols[0].key = "";
    symbols[0].info = SYM_RANGE | width << 4;
    symbols[0].value = (void*)(&range);

    symbols[1].key = "depth";
    symbols[1].info = SYM_PARAM | (8*sizeof(unsigned int)) << 4;
    symbols[1].value = (void*)(&depth);

    symbols[2].key = "level";
    symbols[2].info = SYM_DEF | idx_bits << 4;
    symbols[2].value = (void*)(&dCountReg);
  }
  ~MOD_SyncFIFO<T,I>() { delete[] data; }
 public:
  bool METH_notEmpty()
  {
    // true when non-empty and not in reset
    return (!d_reset && ((depth != 1) ? not_empty : dst_hi != dst_lo.probe()));
    //    return (!d_reset && not_empty);
  }
  // support the alternate naming used by the SyncFIFOLevel import-BVI
  bool METH_dNotEmpty()
  {
    return METH_notEmpty();
  }
  bool METH_RDY_first()
  {
    return METH_notEmpty();
  }
  T METH_first()
  {
    return dDoutReg;
  }
  bool METH_RDY_deq()
  {
    return METH_notEmpty();
  }
  void METH_deq()
  {
    did_deq = true;
  }
  bool METH_notFull()
  {
    // true when non-full and not in reset
    // (note: depth assumed to be power of 2)
    return (!s_reset && not_full);
  }
  // support the alternate naming used by the SyncFIFOLevel import-BVI
  bool METH_sNotFull()
  {
    return METH_notFull();
  }
  bool METH_RDY_enq()
  {
    return METH_notFull();
  }
  void METH_enq(const T& x)
  {
    if (depth == 1)
      dDoutReg = x;
    data[src_hi.read() % depth] = x;
    did_enq = true;
  }
  // For zero-width variants
  void METH_enq()
  {
    did_enq = true;
  }
  I METH_sCount()
  {
    return sCountReg;
  }
  I METH_dCount()
  {
    return dCountReg;
  }
  bool METH_RDY_sClear()
  {
    return sClrSync.METH_RDY_send();
  }
  void METH_sClear()
  {
    sClrSync.METH_send();
    did_sclear = true;
  }
  bool METH_RDY_dClear()
  {
    return dClrSync.METH_RDY_send();
  }
  void METH_dClear()
  {
    dClrSync.METH_send();
    did_dclear = true;
  }

  void clk_src(tUInt8 clock_value, tUInt8 gate_value = 1)
  {
    if (gate_value == 0) return;

    // update source-side reset
    s_reset = in_reset;

    // update not full reg and count
    if (s_reset ||
        (hasClear && (did_sclear || !sClrSync.METH_RDY_send() || dClrSync.METH_pulse())))
    {
      src_hi.force(0);
      src_hi_plus_1 = 1;
      not_full = false;
      sCountReg = 0;
    }
    else if (did_enq)
    {
      not_full = ((src_hi_plus_1 ^ depth) != src_lo);
      if (src_hi_plus_1 > src_lo)
	sCountReg = src_hi_plus_1 - src_lo;
      else
	sCountReg = (src_hi_plus_1 + (2*depth) - src_lo) & mask;
      src_hi.write(src_hi_plus_1);
      src_hi_plus_1 = (src_hi_plus_1 + 1) % (2*depth);
    }
    else
    {
      not_full = ((src_hi.read() ^ depth) != src_lo);
      if (src_hi.read() > src_lo)
	sCountReg = src_hi.read() - src_lo;
      else
	sCountReg = (src_hi.read() + (2*depth) - src_lo) & mask;
    }
    did_sclear = false;
    did_enq = false;

    // synchronize index from destination side
    src_lo = sSyncReg1;
    sSyncReg1 = dst_lo.read();

    if (depth == 1) {
      not_full = src_hi.probe() == src_lo;
      sCountReg = not_full ? 0 : 1;
    }

    sClrSync.clk_src(clock_value, gate_value);
    dClrSync.clk_dst(clock_value, gate_value);
  }
  void clk_dst(tUInt8 clock_value, tUInt8 gate_value = 1)
  {
    if (gate_value == 0) return;

    // update destination-side reset
    d_reset = in_reset;

    // update not empty reg and count
    if (d_reset ||
        (hasClear && (did_dclear || !dClrSync.METH_RDY_send() || sClrSync.METH_pulse())))
    {
      dst_lo.force(0);
      dst_lo_plus_1 = 1;
      not_empty = false;
      dCountReg = 0;
    }
    else if (did_deq)
    {
      not_empty = (dst_hi != dst_lo.read());
      if (dst_hi > dst_lo_plus_1)
	dCountReg = dst_hi - dst_lo.read();
      else
	dCountReg = (dst_hi + (2*depth) - dst_lo.read()) & mask;
      //not_empty = dCountReg != 0;
      if (not_empty) {
        if (depth != 1)
          dDoutReg = data[dst_lo.read() % depth];
        dst_lo.write(dst_lo_plus_1);
        dst_lo_plus_1 = (dst_lo_plus_1 + 1) % (2*depth);
      }
    }
    else
    {
      if (dst_hi > dst_lo.read())
	dCountReg = dst_hi - dst_lo.read();
      else
	dCountReg = (dst_hi + (2*depth) - dst_lo.read()) & mask;

      if ((depth != 1) && !not_empty && (dst_hi != dst_lo.read())) {
        dDoutReg = data[dst_lo.read() % depth];
        dst_lo.write(dst_lo_plus_1);
        dst_lo_plus_1 = (dst_lo_plus_1 + 1) % (2*depth);
        not_empty = true;
      }

    }
    did_dclear = false;
    did_deq = false;

    // synchronize index from source side
    dst_hi = dSyncReg1;
    dSyncReg1 = src_hi.read();

    if (depth == 1) {
      not_empty = dst_lo.probe() == dst_hi;
      dCountReg = not_empty ? 1 : 0;
    }

    sClrSync.clk_dst(clock_value, gate_value);
    dClrSync.clk_src(clock_value, gate_value);
  }
  void reset_sRST(tUInt8 rst_in)
  {
    in_reset = (rst_in == 0);
    sClrSync.reset_sRST(rst_in);
    dClrSync.reset_sRST(rst_in);
    if (in_reset)
    {
      src_lo = dst_hi = 0;
      src_hi.force(0);
      dst_lo.force(0);
      src_hi_plus_1 = dst_lo_plus_1 = 1;
      dSyncReg1 = sSyncReg1 = 0;
      sCountReg = dCountReg = 0;
      s_reset = d_reset = true;
      did_enq = did_deq = false;
      did_sclear = did_dclear = false;
    }
  }
  void rst_tick_clk_src(tUInt8 /* clock_gate */) { /* unused */ }
 private:
  bool occupied(unsigned int idx)
  {
    unsigned int l = dst_lo.probe();
    unsigned int h = src_hi.probe();
    // when l == h the FIFO is empty
    if (l == h)
      return false;
    // map l and h onto data array indexes
    l = l % depth;
    h = h % depth;
    return (l < h) ? (idx >= l && idx < h) : (idx >= l || idx < h);
  }
 public:
  const unsigned int* data_index(tUInt64 addr) const
  {
    if (addr < ((tUInt64) dCountReg))
      return symbol_value(&(data[(dst_lo.read() + addr) % depth]),width);
    else
      return NULL;
  }

  void dump_state(unsigned int indent)
  {
    printf("%*s%s = ", indent, "", inst_name);
    if (src_hi.read() == dst_lo.read())
      printf("EMPTY");
    else
    {
      printf("{ ");
      for (unsigned int n = 0; (dst_lo.read() + n) % (2*depth) != src_hi.read(); ++n)
      {
	if (n > 0)
	  printf(", ");
	dump_val(data[(dst_lo.read() + n) % depth], width);
      }
      printf(" }");
    }
    putchar('\n');
    if (hasClear) {
      sClrSync.dump_state(indent + 2);
      dClrSync.dump_state(indent + 2);
    }
  }
  unsigned int dump_VCD_defs(unsigned int num)
  {
    vcd_num = vcd_reserve_ids(sim_hdl, depth + 13);
    unsigned int n = vcd_num;
    char buf[16];
    vcd_write_scope_start(sim_hdl, inst_name);
    vcd_write_def(sim_hdl, n++, "FULL_N", 1);
    vcd_write_def(sim_hdl, n++, "EMPTY_N", 1);
    vcd_write_def(sim_hdl, n++, "dEnqPtr", idx_bits+1);
    vcd_write_def(sim_hdl, n++, "dGDeqPtr", idx_bits+1);
    vcd_write_def(sim_hdl, n++, "dGDeqPtr1", idx_bits+1);
    vcd_write_def(sim_hdl, n++, "dSyncReg1", idx_bits+1);
    vcd_write_def(sim_hdl, n++, "sDeqPtr", idx_bits+1);
    vcd_write_def(sim_hdl, n++, "sGEnqPtr", idx_bits+1);
    vcd_write_def(sim_hdl, n++, "sGEnqPtr1", idx_bits+1);
    vcd_write_def(sim_hdl, n++, "sSyncReg1", idx_bits+1);
    vcd_write_def(sim_hdl, n++, "sCount", idx_bits);
    vcd_write_def(sim_hdl, n++, "dCount", idx_bits);
    vcd_write_def(sim_hdl, n++, "dDoutReg", width);
    for (unsigned int i = 0; i < depth; ++i)
    {
      sprintf(buf, "arr_%d", i);
      vcd_write_def(sim_hdl, n++, buf, width);
    }
    unsigned int n2 = sClrSync.dump_VCD_defs(n);
    unsigned int n3 = dClrSync.dump_VCD_defs(n2);
    vcd_write_scope_end(sim_hdl);
    return n3;
  }
  void dump_VCD(tVCDDumpType dt, MOD_SyncFIFO<T,I>& backing)
  {
    unsigned int num = vcd_num;
    if (dt == VCD_DUMP_XS)
    {
      vcd_write_x(sim_hdl, num++, 1);
      vcd_write_x(sim_hdl, num++, 1);
      vcd_write_x(sim_hdl, num++, idx_bits+1);
      vcd_write_x(sim_hdl, num++, idx_bits+1);
      vcd_write_x(sim_hdl, num++, idx_bits+1);
      vcd_write_x(sim_hdl, num++, idx_bits+1);
      vcd_write_x(sim_hdl, num++, idx_bits+1);
      vcd_write_x(sim_hdl, num++, idx_bits+1);
      vcd_write_x(sim_hdl, num++, idx_bits+1);
      vcd_write_x(sim_hdl, num++, idx_bits+1);
      vcd_write_x(sim_hdl, num++, idx_bits);
      vcd_write_x(sim_hdl, num++, idx_bits);
      vcd_write_x(sim_hdl, num++, width);
      for (unsigned int i = 0; i < depth; ++i)
	vcd_write_x(sim_hdl, num++, width);
    }
    else if (dt == VCD_DUMP_CHANGES)
    {
      if (not_full != backing.not_full)
	vcd_write_val(sim_hdl, num++, not_full, 1);
      else
	++num;
      if (METH_RDY_first() != backing.METH_RDY_first())
	vcd_write_val(sim_hdl, num++, METH_RDY_first(), 1);
      else
	++num;
      if (dst_hi != backing.dst_hi)
	vcd_write_val(sim_hdl, num++, dst_hi, idx_bits+1);
      else
	++num;
      if (dst_lo.probe() != backing.dst_lo.read())
        vcd_write_val(sim_hdl, num++, dst_lo.probe(), idx_bits+1);
      else
	++num;
      if (dst_lo_plus_1 != backing.dst_lo_plus_1)
	vcd_write_val(sim_hdl, num++, dst_lo_plus_1, idx_bits+1);
      else
	++num;
      if (dSyncReg1 != backing.dSyncReg1)
	vcd_write_val(sim_hdl, num++, dSyncReg1, idx_bits+1);
      else
	++num;
      if (src_lo != backing.src_lo)
	vcd_write_val(sim_hdl, num++, src_lo, idx_bits+1);
      else
	++num;
      if (src_hi.probe() != backing.src_hi.read())
        vcd_write_val(sim_hdl, num++, src_hi.probe(), idx_bits+1);
      else
	++num;
      if (src_hi_plus_1 != backing.src_hi_plus_1)
	vcd_write_val(sim_hdl, num++, src_hi_plus_1, idx_bits+1);
      else
	++num;
      if (sSyncReg1 != backing.sSyncReg1)
	vcd_write_val(sim_hdl, num++, sSyncReg1, idx_bits+1);
      else
	++num;
      if (sCountReg != backing.sCountReg)
	vcd_write_val(sim_hdl, num++, sCountReg, idx_bits);
      else
	++num;
      if (dCountReg != backing.dCountReg)
	vcd_write_val(sim_hdl, num++, dCountReg, idx_bits);
      else
	++num;
      if (METH_RDY_first() && !backing.METH_RDY_first())
	vcd_write_val(sim_hdl, num++, dDoutReg, width);
      else if (!METH_RDY_first() && backing.METH_RDY_first())
        vcd_write_x(sim_hdl, num++, width);
      else if (METH_RDY_first() && (dDoutReg != backing.dDoutReg))
	vcd_write_val(sim_hdl, num++, dDoutReg, width);
      else
	++num;
      for (unsigned int i = 0; i < depth; ++i)
      {
	unsigned int idx = (dst_lo.probe() + i) % depth;
	unsigned int b_idx = (backing.dst_lo.read() + i) % depth;
	// handle value which has been added
	if (occupied(idx) && !backing.occupied(b_idx))
	  vcd_write_val(sim_hdl, num++, data[idx], width);
	// handle value which is removed
	else if (!occupied(idx) && backing.occupied(b_idx))
	  vcd_write_x(sim_hdl, num++, width);
	// handle value which is changed
	else if (occupied(idx) && backing.occupied(b_idx) &&
		 (data[idx] != backing.data[b_idx]))
	  vcd_write_val(sim_hdl, num++, data[idx], width);
	// handle value which is unchanged
	else
	  ++num;
      }
    }
    else
    {
      vcd_write_val(sim_hdl, num++, METH_RDY_enq(), 1);
      vcd_write_val(sim_hdl, num++, METH_RDY_first(), 1);
      vcd_write_val(sim_hdl, num++, dst_hi, idx_bits+1);
      vcd_write_val(sim_hdl, num++, dst_lo.probe(), idx_bits+1);
      vcd_write_val(sim_hdl, num++, dst_lo_plus_1, idx_bits+1);
      vcd_write_val(sim_hdl, num++, dSyncReg1, idx_bits+1);
      vcd_write_val(sim_hdl, num++, src_lo, idx_bits+1);
      vcd_write_val(sim_hdl, num++, src_hi.probe(), idx_bits+1);
      vcd_write_val(sim_hdl, num++, src_hi_plus_1, idx_bits+1);
      vcd_write_val(sim_hdl, num++, sSyncReg1, idx_bits+1);
      vcd_write_val(sim_hdl, num++, sCountReg, idx_bits);
      vcd_write_val(sim_hdl, num++, dCountReg, idx_bits);
      if (METH_RDY_first()) 
        vcd_write_val(sim_hdl, num++, dDoutReg, width);
      else
	  vcd_write_x(sim_hdl, num++, width);
      for (unsigned int i = 0; i < depth; ++i)
      {
	unsigned int idx = (dst_lo.read() + i) % depth;
	if (occupied(idx))
	  vcd_write_val(sim_hdl, num++, data[idx], width);
	else
	  vcd_write_x(sim_hdl, num++, width);
      }
    }

    backing.src_lo = src_lo;
    backing.src_hi = src_hi;
    backing.dst_lo = dst_lo;
    backing.dst_hi = dst_hi;
    backing.src_hi_plus_1 = src_hi_plus_1;
    backing.dst_lo_plus_1 = dst_lo_plus_1;
    backing.sSyncReg1 = sSyncReg1;
    backing.dSyncReg1 = dSyncReg1;
    backing.sCountReg = sCountReg;
    backing.dCountReg = dCountReg;
    backing.not_empty = not_empty;
    backing.not_full  = not_full;
    backing.s_reset = s_reset;
    backing.d_reset = d_reset;
    backing.dDoutReg = dDoutReg;
    for (unsigned int i = 0; i < depth; ++i)
      backing.data[i] = data[i];

    sClrSync.dump_VCD(dt, backing.sClrSync);
    dClrSync.dump_VCD(dt, backing.dClrSync);
  }

 private:
  const unsigned int width;
  const unsigned int depth;

  unsigned int idx_bits;
  unsigned int mask;

  T* data;
  T  dDoutReg;
  unsigned int src_lo;
  SyncVar<unsigned int> src_hi;
  SyncVar<unsigned int> dst_lo;
  unsigned int dst_hi;
  unsigned int dSyncReg1;
  unsigned int sSyncReg1;
  unsigned int src_hi_plus_1;
  unsigned int dst_lo_plus_1;
  I sCountReg;
  I dCountReg;
  bool not_empty;
  bool not_full;
  bool in_reset;
  bool s_reset;
  bool d_reset;
  bool did_enq;
  bool did_deq;
  bool did_sclear;
  bool did_dclear;
  bool hasClear;
  MOD_SyncHandshake sClrSync;
  MOD_SyncHandshake dClrSync;

  // range structure for symbolic access to FIFO data
  Range range;
};

// Function to index into FIFO data array
template<typename T, typename I>
const unsigned int* index_fn_syncfifo(void* base, tUInt64 addr)
{
  MOD_SyncFIFO<T,I>* fifo = (MOD_SyncFIFO<T,I>*) base;
  return fifo->data_index(addr);
}

// Synchronized RAM Model

template<typename AT, typename DT>
class MOD_DualPortRam : public Module
{
 public:
  MOD_DualPortRam<AT,DT>(tSimStateHdl simHdl, const char* name, Module* parent,
			 unsigned int addr_width, unsigned int data_width)
    : Module(simHdl, name, parent), addr_bits(addr_width),
      data_bits(data_width), written_at(~bk_now(sim_hdl))
  {
    if (vcd_is_backing_instance(sim_hdl))
      return;  // do not allocate storage for backing instance
    nWords = 1llu << addr_width;
    data = new DT[nWords];
    for (unsigned long long n = 0llu; n < nWords; ++n)
    {
      init_val(data[n], data_bits);
      write_undet(&(data[n]), data_bits);
    }
    init_val(write_addr, addr_bits);
    init_val(prev_value, data_bits);
  }
  ~MOD_DualPortRam<AT,DT>() { delete[] data; }
 public:
  // Note: the read and write methods of a DualPortRam are
  // conflict free.  When the edges coincide and a simultaneous
  // read and write occur the same address, we want the read to
  // return the value from the beginning of the cycle.
  const DT METH_read(const AT& addr) const
  {
    if ((write_addr == addr) && bk_is_same_time(sim_hdl, written_at))
      return prev_value;
    else
      return data[addr];
  }
  void METH_write(const AT& addr, const DT& val)
  {
    written_at = bk_now(sim_hdl);
    write_addr = addr;
    prev_value = data[addr];
    data[addr] = val;
  }

 public:
  void dump_state(unsigned int indent)
  {
    // Memory contents are not dumped
  }
  unsigned int dump_VCD_defs(unsigned int num)
  {
    // Memory contents are not dumped
    return (num);
  }
  void dump_VCD(tVCDDumpType /* unused */,
		MOD_DualPortRam<AT,DT>& /* unused */)

  {
    // Memory contents are not dumped
  }

 private:
  DT* data;
  unsigned int addr_bits;
  unsigned int data_bits;
  unsigned long long nWords;
  tTime written_at;
  AT write_addr;
  DT prev_value;
};


// This is a synchronization primitive that combines a register
// with a latch. The register is written and read in the source
// domain, and its output is latched to be read in the destination
// domain.  The purpose of this primitive is to align data to a shifted
// clock domain.
template<typename T>
class MOD_LatchCrossingReg : public Module
{
 public:
  MOD_LatchCrossingReg(tSimStateHdl simHdl, const char* name, Module* parent,
		       unsigned int width, const T& v)
    : Module(simHdl, name, parent), reset_value(v), bits(width)
  {
    init_val(dLatch, width);
    write_undet(&dLatch, width);
    init_val(sFlop, width);
    write_undet(&sFlop, width);
    init_val(prev_value, width);
    write_undet(&prev_value, width);
    writtenAt = ~bk_now(sim_hdl);
    in_reset = false;
    prev_transparent = false;
    transparent = false;
  }
 public:
  const T& METH__read() const { return sFlop; }

  void METH__write(const T& x) {
    if (!in_reset) {
      prev_value = sFlop;
      sFlop = x;
      writtenAt = bk_now(sim_hdl);
      if (transparent) dLatch = x;
    }
  }

  const T& METH_crossed() const {
    if (transparent) {
      if (writtenAt == bk_now(sim_hdl))
	return prev_value;
      else
	return sFlop;
    } else {
      return dLatch;
    }
  }

  void dstClk(tUInt8 clock_value, tUInt8 gate_value = 1)
  {
    prev_transparent = transparent;
    transparent = (gate_value != 0 && clock_value != 0);

    if (transparent) {
      dLatch = sFlop;
    } else if (prev_transparent) {
      if (writtenAt == bk_now(sim_hdl))
	dLatch = prev_value;
      else
	dLatch = sFlop;
    }
  }

  void reset_SRST(tUInt8 rst_in)
  {
    in_reset = (rst_in == 0);
    if (in_reset)
    {
      dLatch = reset_value;
      sFlop = reset_value;
      prev_value = reset_value;
      prev_transparent = false;
      transparent = false;
    }
  }

  void rst_tick_clk(tUInt8 /* clock_gate */) { /* unused */ }
 public:
  void dump_state(unsigned int indent)
  {
    printf("%*s%s:\n", indent, "", inst_name);
    printf("%*sdLatch = ", indent+2, "");
    dump_val(dLatch, bits);
    putchar('\n');
    printf("%*ssFlop = ", indent+2, "");
    dump_val(sFlop, bits);
    putchar('\n');
  }
  unsigned int dump_VCD_defs(unsigned int /* num */)
  {
    char buf[128];
    vcd_num = vcd_reserve_ids(sim_hdl, 2);
    snprintf(buf,128,"%s$L_OUT",inst_name);
    vcd_write_def(sim_hdl, vcd_num,   buf, bits);
    snprintf(buf,128,"%s$Q_OUT",inst_name);
    vcd_write_def(sim_hdl, vcd_num+1, buf, bits);
    return (vcd_num + 2);
  }
  void dump_VCD(tVCDDumpType dt, MOD_LatchCrossingReg& backing)
  {
    if (dt == VCD_DUMP_XS)
    {
      vcd_write_x(sim_hdl, vcd_num,   bits);
      vcd_write_x(sim_hdl, vcd_num+1, bits);
    }
    else
    {
      if ((dt != VCD_DUMP_CHANGES) || (backing.dLatch != dLatch))
      {
	vcd_write_val(sim_hdl, vcd_num, dLatch, bits);
	backing.dLatch = dLatch;
      }
      if ((dt != VCD_DUMP_CHANGES) || (backing.sFlop != sFlop))
      {
	vcd_write_val(sim_hdl, vcd_num+1, sFlop, bits);
	backing.sFlop = sFlop;
      }
    }
  }

 private:
  T dLatch;
  T sFlop;
  T prev_value;
  T reset_value;
  unsigned int bits;
  tTime writtenAt;
  bool in_reset;
  bool prev_transparent;
  bool transparent;
};


#endif /* __BS_PRIM_MOD_SYNCHRONIZERS_H__ */
