#ifndef __BS_PRIM_MOD_REG_H__
#define __BS_PRIM_MOD_REG_H__

#include "bluesim_kernel_api.h"
#include "bluesim_probes.h"
#include "bs_module.h"
#include "bs_vcd.h"
#include "bs_reset.h"

#define NO_RESET_REG    0
#define SYNC_RESET_REG  1
#define ASYNC_RESET_REG 2

// This is the definition of the Reg register primitive.  It is used for both
// normal register and clock-crossing registers (so it has duplicate methods
// to cover all the required names and behaviors).
template<typename T>
class MOD_Reg : public Module
{
 public:
  // RegN, RegA, CrossingRegN, CrossingRegA
  MOD_Reg<T>(tSimStateHdl simHdl, const char* name, Module* parent,
	     unsigned int width, const T& v, unsigned int async)
    : Module(simHdl, name, parent), bits(width), reset_value(v),
      reset_type(async ? ASYNC_RESET_REG : SYNC_RESET_REG),
      proxy(NULL)
  {
    init_val(prev_value, bits);
    write_undet(&prev_value, bits);
    init_val(value, bits);
    write_undet(&value, bits);
    written_at = ~bk_now(sim_hdl);

    in_reset = false;
    suppress_write = false;

    symbol_count = 1;
    symbols = new tSym[symbol_count];

    symbols[0].key = "";
    symbols[0].info = SYM_DEF | bits << 4;
    symbols[0].value = (void*)(&value);
  }
  // RevertReg
  MOD_Reg<T>(tSimStateHdl simHdl, const char* name, Module* parent,
	     unsigned int width, const T& v)
    : Module(simHdl, name, parent), value(v), bits(width),
      reset_type(NO_RESET_REG), proxy(NULL)
  {
    in_reset = false;
    suppress_write = false;

    symbol_count = 1;
    symbols = new tSym[symbol_count];

    symbols[0].key = "";
    symbols[0].info = SYM_DEF | bits << 4;
    symbols[0].value = (void*)(&value);
  }
  // RegUN, CrossingRegUN
  MOD_Reg<T>(tSimStateHdl simHdl, const char* name, Module* parent,
	     unsigned int width)
    : Module(simHdl, name, parent), bits(width), reset_type(NO_RESET_REG),
      proxy(NULL)
  {
    init_val(prev_value, bits);
    write_undet(&prev_value, bits);
    init_val(value, bits);
    write_undet(&value, bits);
    init_val(reset_value, bits);
    write_undet(&reset_value, bits);
    written_at = ~bk_now(sim_hdl);

    in_reset = false;
    suppress_write = false;

    symbol_count = 1;
    symbols = new tSym[symbol_count];

    symbols[0].key = "";
    symbols[0].info = SYM_DEF | bits << 4;
    symbols[0].value = (void*)(&value);
  }
  ~MOD_Reg<T>() { delete proxy; }
 public:
  // read method for single-domain register
  const T& METH_read()    const { return value; }
  // read methods for clock-crossing register
  const T& METH__read()   const { return value; }
  const T& METH_crossed() const
  {
    if (bk_is_same_time(sim_hdl, written_at) && !bk_is_combo_sched(sim_hdl))
      return prev_value;
    else
      return value;
  }
  // write method for single-domain register
  void METH_write(const T& x)
  {
    if ((reset_type != ASYNC_RESET_REG) || !suppress_write)
      value = x;
  }
  // write method for clock-crossing register
  void METH__write(const T& x)
  {
    if ((reset_type != ASYNC_RESET_REG) || !suppress_write)
    {
      prev_value = value;
      value = x;
      written_at = bk_now(sim_hdl);
    }
  }
  // clock and reset infrastructure
  void reset_RST(tUInt8 rst_in)
  {
    in_reset = (rst_in == 0);
    if (in_reset)
    {
      if (reset_type == ASYNC_RESET_REG)
	rst_tick__clk__1(1);
      else if (reset_type == SYNC_RESET_REG)
	start_reset_ticks(sim_hdl); /* request rst_tick() on the next clock edge */
    }
    else
    {
      suppress_write = false;
      if (reset_type == SYNC_RESET_REG)
	stop_reset_ticks(sim_hdl); /* stop rst_tick() when reset is not asserted */
    }
  }
  void rst_tick__clk__1(tUInt8 clock_gate)
  {
    if (in_reset && (clock_gate != 0))
    {
      value = reset_value;
      suppress_write = true;
    }
  }
  void rst_tick_sClk(tUInt8 clock_gate)
  {
    if (in_reset && (clock_gate != 0))
    {
      prev_value = value;
      value = reset_value;
      written_at = bk_now(sim_hdl);
      suppress_write = true;
    }
  }
 public:
  void dump_state(unsigned int indent)
  {
    printf("%*s%s = ", indent, "", inst_name);
    dump_val(value, bits);
    putchar('\n');
  }
  unsigned int dump_VCD_defs(unsigned int /* num */)
  {
    vcd_num = vcd_reserve_ids(sim_hdl, 1);
    vcd_write_def(sim_hdl, vcd_num, inst_name, bits);
    return (vcd_num + 1);
  }
  void dump_VCD(tVCDDumpType dt, MOD_Reg<T>& backing)
  {
    unsigned int num = vcd_num;
    if (dt == VCD_DUMP_XS)
      vcd_write_x(sim_hdl, num++, bits);
    else if (dt == VCD_DUMP_CHANGES)
    {
      if (value != backing.value)
	vcd_write_val(sim_hdl, num++, value, bits);
      else
	++num;
    }
    else
    {
      vcd_write_val(sim_hdl, num++, value, bits);
    }
    backing.value = value;
  }

 // register data members
 private:
  T prev_value;
  T value;
  const unsigned int bits;
  T reset_value;
  const unsigned int reset_type;
  tTime written_at;
  bool suppress_write;
  bool in_reset;

 // proxy access facility
 private:
  BluespecProbe<T>* proxy;
 public:
  BluespecProbe<T>& getProbe()
  {
    if (proxy == NULL)
      proxy = new BluespecProbe<T>(this, one, eq_one, read_reg, write_reg);
    return (*proxy);
  }
 private:
  static unsigned int one(void* /*obj */, bool /* hi */)
  {
    return 1;
  }
  static bool eq_one(void* /* obj */, unsigned int addr)
  {
    return (addr == 1);
  }
  static const T& read_reg(void* obj, unsigned int /* addr */)
  {
    MOD_Reg<T>* reg = (MOD_Reg<T>*) obj;
    return reg->value;
  }
  static bool write_reg(void* obj, unsigned int addr, const T& data)
  {
    if (addr == 1)
    {
      MOD_Reg<T>* reg = (MOD_Reg<T>*) obj;
      reg->value = data;
      return true;
    }
    else
      return false; // indicates write to invalid address
  }
};


// This is the definition of the RegAligned register primitive.
// It is the same as Reg, but has different module, clock, etc.
// names, because it is imported differently.
template<typename T>
class MOD_RegAligned : public Module
{
 public:
  MOD_RegAligned<T>(tSimStateHdl simHdl, const char* name, Module* parent,
                unsigned int width, const T& v, unsigned int async)
    : Module(simHdl, name, parent), bits(width), reset_value(v),
      reset_type(async ? ASYNC_RESET_REG : SYNC_RESET_REG),
      __clk_handle_0(BAD_CLOCK_HANDLE), __clk_handle_1(BAD_CLOCK_HANDLE),
      written_at(~bk_now(sim_hdl)), proxy(NULL)
  {
    init_val(value, bits);
    write_undet(&value, bits);
    init_val(next_value, bits);
    write_undet(&next_value, bits);
    in_reset = false;
    suppress_write = false;
    did_write = false;

    symbol_count = 1;
    symbols = new tSym[symbol_count];

    symbols[0].key = "";
    symbols[0].info = SYM_DEF | bits << 4;
    symbols[0].value = (void*)(&value);
  }
  MOD_RegAligned<T>(tSimStateHdl simHdl, const char* name, Module* parent,
		    unsigned int width)
    : Module(simHdl, name, parent), bits(width), tick_at(~bk_now(sim_hdl)),
      reset_type(NO_RESET_REG), __clk_handle_0(BAD_CLOCK_HANDLE),
      __clk_handle_1(BAD_CLOCK_HANDLE), written_at(~bk_now(sim_hdl)),
      proxy(NULL)
  {
    init_val(value, bits);
    write_undet(&value, bits);
    init_val(reset_value, bits);
    write_undet(&reset_value, bits);
    in_reset = false;
    suppress_write = false;
    did_write = false;

    symbol_count = 1;
    symbols = new tSym[symbol_count];

    symbols[0].key = "";
    symbols[0].info = SYM_DEF | bits << 4;
    symbols[0].value = (void*)(&value);
  }
  ~MOD_RegAligned<T>() { delete proxy; }
 public:
  const T& METH__read() const  { return value; }
  void METH__write(const T& x)
  {
    if ((reset_type != ASYNC_RESET_REG) || !suppress_write)
    {
      next_value = x;
      if (tick_at == bk_now(sim_hdl))
      {
	value = next_value;
	written_at = bk_now(sim_hdl);
      }
    }
  }

  void realClock(tUInt8 /* clk */, tUInt8 gate = true )
  {
    tick_at = bk_now(sim_hdl);
    if ((reset_type != ASYNC_RESET_REG) || !suppress_write)
      value = next_value;
  }

  void set_clk_0(const char* s)
  {
    __clk_handle_0 = bk_get_or_define_clock(sim_hdl, s);
  }

  void set_clk_1(const char* s)
  {
    __clk_handle_1 = bk_get_or_define_clock(sim_hdl, s);
  }

  void reset_RST(tUInt8 rst_in)
  {
    in_reset = (rst_in == 0);
    if (in_reset)
    {
      if (reset_type == ASYNC_RESET_REG)
	rst_tick_realClock(1);
      else if (reset_type == SYNC_RESET_REG)
	start_reset_ticks(sim_hdl); /* request rst_tick() on the next clock edge */
    }
    else
    {
      suppress_write = false;
      if (reset_type == SYNC_RESET_REG)
	stop_reset_ticks(sim_hdl); /* stop rst_tick() when reset is not asserted */
    }
  }
  void rst_tick_realClock(tUInt8 clock_gate)
  {
    if (in_reset && (clock_gate != 0))
    {
      value = reset_value;
      next_value = reset_value;
      suppress_write = true;
    }
  }
 public:
  void dump_state(unsigned int indent)
  {
    printf("%*s%s = ", indent, "", inst_name);
    dump_val(value, bits);
    putchar('\n');
  }
  unsigned int dump_VCD_defs(unsigned int /* num */)
  {
    vcd_num = vcd_reserve_ids(sim_hdl, 4);
    unsigned int n = vcd_num;
    vcd_write_def(sim_hdl, n++, inst_name, bits);
    vcd_write_scope_start(sim_hdl, inst_name);
    vcd_write_def(sim_hdl, bk_clock_vcd_num(sim_hdl, __clk_handle_0), "CLK", 1);
    vcd_write_def(sim_hdl, n++, "RST", 1);
    vcd_set_clock(sim_hdl, n, __clk_handle_1);
    vcd_write_def(sim_hdl, n++, "EN", 1);
    vcd_set_clock(sim_hdl, n, __clk_handle_1);
    vcd_write_def(sim_hdl, n++, "D_IN", bits);
    vcd_write_def(sim_hdl, vcd_num, "Q_OUT", bits); // alias
    vcd_write_scope_end(sim_hdl);
    return (n);
  }
  void dump_VCD(tVCDDumpType dt, MOD_RegAligned<T>& backing)
  {
    unsigned int num = vcd_num;
    if (dt == VCD_DUMP_XS)
    {
      vcd_write_x(sim_hdl, num++, bits);
      vcd_write_x(sim_hdl, num++, 1);
      vcd_write_x(sim_hdl, num++, 1);
      vcd_write_x(sim_hdl, num++, bits);
    }
    else if (dt == VCD_DUMP_CHANGES)
    {
      if (backing.value != value)
	vcd_write_val(sim_hdl, num++, value, bits);
      else
	++num;
      if (in_reset != backing.in_reset)
	vcd_write_val(sim_hdl, num++, !in_reset, 1);
      else
	++num;
      bool at_input_posedge =
	       bk_clock_val(sim_hdl, __clk_handle_1) == CLK_HIGH &&
	       bk_clock_last_edge(sim_hdl, __clk_handle_1) == bk_now(sim_hdl);
      if (at_input_posedge)
      {
	did_write = bk_is_same_time(sim_hdl, written_at);
	if (did_write != backing.did_write)
	{
	  vcd_write_val(sim_hdl, num++, did_write, 1);
	  backing.did_write = did_write;
	}
	else
	  ++num;
      }
      else
	++num;
      if (next_value != backing.next_value)
	vcd_write_val(sim_hdl, num++, next_value, bits);
      else
	++num;
    }
    else
    {
      did_write = bk_is_same_time(sim_hdl, written_at);
      vcd_write_val(sim_hdl, num++, value, bits);
      vcd_write_val(sim_hdl, num++, !in_reset, 1);
      vcd_write_val(sim_hdl, num++, did_write, 1);
      vcd_write_val(sim_hdl, num++, next_value, bits);
      backing.did_write = did_write;
    }
    backing.value = value;
    backing.next_value = next_value;
  }

 // RegAligned data members
 private:
  T value;
  const unsigned int bits;
  T reset_value;
  T next_value;
  tTime tick_at;
  const unsigned int reset_type;
  bool suppress_write;
  bool in_reset;

  // used for VCD dumping
  tClock __clk_handle_0;  // clock for reg updates (realClock)
  tClock __clk_handle_1;  // clock for inputs      (sClkIn)
  bool did_write;
  tTime written_at;

 // proxy access facility
 private:
  BluespecProbe<T>* proxy;
 public:
  BluespecProbe<T>& getProbe()
  {
    if (proxy == NULL)
      proxy = new BluespecProbe<T>(this, one, eq_one, read_reg, write_reg);
    return (*proxy);
  }
 private:
  static unsigned int one(void* /*obj */, bool /* hi */)
  {
    return 1;
  }
  static bool eq_one(void* /* obj */, unsigned int addr)
  {
    return (addr == 1);
  }
  static const T& read_reg(void* obj, unsigned int /* addr */)
  {
    MOD_Reg<T>* reg = (MOD_Reg<T>*) obj;
    return reg->value;
  }
  static bool write_reg(void* obj, unsigned int addr, const T& data)
  {
    if (addr == 1)
    {
      MOD_Reg<T>* reg = (MOD_Reg<T>*) obj;
      reg->value = data;
      return true;
    }
    else
      return false; // indicates write to invalid address
  }
};


// This is the definition of the ConfigReg register primitive.
// It differs from Reg by always returning the value at the beginning
// of the simulation cycle.
template<typename T>
class MOD_ConfigReg : public Module
{
 public:
  MOD_ConfigReg<T>(tSimStateHdl simHdl, const char* name, Module* parent,
		   unsigned int width, const T& v, unsigned int async)
    : Module(simHdl, name, parent), bits(width), written(~bk_now(sim_hdl)),
      reset_value(v),
      reset_type(async ? ASYNC_RESET_REG : SYNC_RESET_REG),
      proxy(NULL)
  {
    init_val(value, bits);
    write_undet(&value, bits);
    init_val(old_value, bits);
    write_undet(&old_value, bits);
    in_reset = false;
    suppress_write = false;

    symbol_count = 1;
    symbols = new tSym[symbol_count];

    symbols[0].key = "";
    symbols[0].info = SYM_DEF | bits << 4;
    symbols[0].value = (void*)(&value);
  }
  MOD_ConfigReg<T>(tSimStateHdl simHdl, const char* name, Module* parent,
		   unsigned int width)
    : Module(simHdl, name, parent), bits(width), written(~bk_now(sim_hdl)),
      reset_type(NO_RESET_REG), proxy(NULL)
  {
    init_val(value, bits);
    write_undet(&value, bits);
    init_val(old_value, bits);
    write_undet(&old_value, bits);
    init_val(reset_value, bits);
    write_undet(&reset_value, bits);
    in_reset = false;
    suppress_write = false;

    symbol_count = 1;
    symbols = new tSym[symbol_count];

    symbols[0].key = "";
    symbols[0].info = SYM_DEF | bits << 4;
    symbols[0].value = (void*)(&value);
  }
  ~MOD_ConfigReg<T>() { delete proxy; }
 public:
  const T& METH_read() const
  {
    if (bk_is_same_time(sim_hdl, written))
      return old_value;
    else
      return value;
  }
  void METH_write(const T& x)
  {
    // suppress writes when async reset is active
    if ((reset_type == ASYNC_RESET_REG) && suppress_write)
      return;

    // only the first write in a cycle should update old_value
    if (written != bk_now(sim_hdl))
    {
      old_value = value;
      written = bk_now(sim_hdl);
    }
    value = x;
  }
  void reset_RST(tUInt8 rst_in)
  {
    in_reset = (rst_in == 0);
    if (in_reset)
    {
      if (reset_type == ASYNC_RESET_REG)
	rst_tick__clk__1(1);
      else if (reset_type == SYNC_RESET_REG)
	start_reset_ticks(sim_hdl); /* request rst_tick() on the next clock edge */
    }
    else
    {
      suppress_write = false;
      if (reset_type == SYNC_RESET_REG)
	stop_reset_ticks(sim_hdl); /* stop rst_tick() when reset is not asserted */
    }
  }
  void rst_tick__clk__1(tUInt8 clock_gate)
  {
    if (in_reset && (clock_gate != 0))
    {
      value = reset_value;
      old_value = reset_value;
      suppress_write = true;
    }
  }

 public:
  void dump_state(unsigned int indent)
  {
    printf("%*s%s = ", indent, "", inst_name);
    dump_val(value, bits);
    putchar('\n');
  }
  unsigned int dump_VCD_defs(unsigned int /* num */)
  {
    vcd_num = vcd_reserve_ids(sim_hdl, 1);
    vcd_write_def(sim_hdl, vcd_num, inst_name, bits);
    return (vcd_num + 1);
  }
  void dump_VCD(tVCDDumpType dt, MOD_ConfigReg<T>& backing)
  {
    if (dt == VCD_DUMP_XS)
      vcd_write_x(sim_hdl, vcd_num, bits);
    else if ((dt != VCD_DUMP_CHANGES) || (backing.value != value))
    {
      vcd_write_val(sim_hdl, vcd_num, value, bits);
      backing.value = value;
    }
  }

 // ConfigReg data members
 private:
  T value;
  unsigned int bits;
  tTime written;
  T old_value;
  T reset_value;
  const unsigned int reset_type;
  bool suppress_write;
  bool in_reset;

 // proxy access facility
 private:
  BluespecProbe<T>* proxy;
 public:
  BluespecProbe<T>& getProbe()
  {
    if (proxy == NULL)
      proxy = new BluespecProbe<T>(this, one, eq_one, read_reg, write_reg);
    return (*proxy);
  }
 private:
  static unsigned int one(void* /*obj */, bool /* hi */)
  {
    return 1;
  }
  static bool eq_one(void* /* obj */, unsigned int addr)
  {
    return (addr == 1);
  }
  static const T& read_reg(void* obj, unsigned int /* addr */)
  {
    MOD_Reg<T>* reg = (MOD_Reg<T>*) obj;
    return reg->value;
  }
  static bool write_reg(void* obj, unsigned int addr, const T& data)
  {
    if (addr == 1)
    {
      MOD_Reg<T>* reg = (MOD_Reg<T>*) obj;
      reg->value = data;
      return true;
    }
    else
      return false; // indicates write to invalid address
  }
};

// This is the definition of the RegTwo register primitive.
// It has two set methods, where setA has priority over setB.
// Like ConfigReg, the get method can occur after the sets but
// should return the original value.
template<typename T>
class MOD_RegTwo : public Module
{
 public:
  MOD_RegTwo<T>(tSimStateHdl simHdl, const char* name, Module* parent,
		unsigned int width, const T& v, unsigned int async)
    : Module(simHdl, name, parent), bits(width), written(~bk_now(sim_hdl)),
      a_at(~bk_now(sim_hdl)), reset_value(v),
      reset_type(async ? ASYNC_RESET_REG : SYNC_RESET_REG),
      proxy(NULL)
  {
    init_val(value, bits);
    write_undet(&value, bits);

    init_val(old_value, bits);

    in_reset = false;
    suppress_write = false;
  }
  MOD_RegTwo<T>(tSimStateHdl simHdl, const char* name, Module* parent,
		unsigned int width)
    : Module(simHdl, name, parent), bits(width), written(~bk_now(sim_hdl)),
      a_at(~bk_now(sim_hdl)), reset_type(NO_RESET_REG), proxy(NULL)
  {
    init_val(value, bits);
    write_undet(&value, bits);

    init_val(old_value, bits);

    init_val(reset_value, bits);
    write_undet(&reset_value, bits);
    in_reset = false;
    suppress_write = false;
  }
  ~MOD_RegTwo<T>() { delete proxy; }
 public:
  const T& METH_get() const
  {
    if (bk_is_same_time(sim_hdl, written))
      return old_value;
    else
      return value;
  }
  void METH_setA(const T& x)
  {
    if ((reset_type != ASYNC_RESET_REG) || !suppress_write)
    {
      if (written != bk_now(sim_hdl))
      {
        old_value = value;
        written = bk_now(sim_hdl);
      }
      a_at = bk_now(sim_hdl);
      value = x;
    }
  }
  void METH_setB(const T& x)
  {
    if ((reset_type != ASYNC_RESET_REG) || !suppress_write)
    {
      if (written != bk_now(sim_hdl))
      {
        old_value = value;
        written = bk_now(sim_hdl);
      }
      if (a_at != bk_now(sim_hdl))
        value = x;
    }
  }
  void reset_RST(tUInt8 rst_in)
  {
    in_reset = (rst_in == 0);
    if (in_reset)
    {
      if (reset_type == ASYNC_RESET_REG)
	rst_tick__clk__1(1);
      else if (reset_type == SYNC_RESET_REG)
	start_reset_ticks(sim_hdl); /* request rst_tick() on the next clock edge */
    }
    else
    {
      suppress_write = false;
      if (reset_type == SYNC_RESET_REG)
	stop_reset_ticks(sim_hdl); /* stop rst_tick() when reset is not asserted */
    }
  }
  void rst_tick__clk__1(tUInt8 clock_gate)
  {
    if (in_reset && (clock_gate != 0))
    {
      value = reset_value;
      suppress_write = true;
    }
  }
 public:
  void dump_state(unsigned int indent)
  {
    printf("%*s%s = ", indent, "", inst_name);
    dump_val(value, bits);
    putchar('\n');
  }
  unsigned int dump_VCD_defs(unsigned int /* num */)
  {
    vcd_num = vcd_reserve_ids(sim_hdl, 1);
    vcd_write_def(sim_hdl, vcd_num, inst_name, bits);
    return (vcd_num + 1);
  }
  void dump_VCD(tVCDDumpType dt, MOD_RegTwo<T>& backing)
  {
    if (dt == VCD_DUMP_XS)
      vcd_write_x(sim_hdl, vcd_num, bits);
    else if ((dt != VCD_DUMP_CHANGES) || (backing.value != value))
    {
      vcd_write_val(sim_hdl, vcd_num, value, bits);
      backing.value = value;
    }
  }

 // RegTwo data members
 private:
  T value;
  const unsigned int bits;
  tTime written;
  tTime a_at;
  T old_value;
  T reset_value;
  const unsigned int reset_type;
  bool suppress_write;
  bool in_reset;

 // proxy access facility
 private:
  BluespecProbe<T>* proxy;
 public:
  BluespecProbe<T>& getProbe()
  {
    if (proxy == NULL)
      proxy = new BluespecProbe<T>(this, one, eq_one, read_reg, write_reg);
    return (*proxy);
  }
 private:
  static unsigned int one(void* /*obj */, bool /* hi */)
  {
    return 1;
  }
  static bool eq_one(void* /* obj */, unsigned int addr)
  {
    return (addr == 1);
  }
  static const T& read_reg(void* obj, unsigned int /* addr */)
  {
    MOD_Reg<T>* reg = (MOD_Reg<T>*) obj;
    return reg->value;
  }
  static bool write_reg(void* obj, unsigned int addr, const T& data)
  {
    if (addr == 1)
    {
      MOD_Reg<T>* reg = (MOD_Reg<T>*) obj;
      reg->value = data;
      return true;
    }
    else
      return false; // indicates write to invalid address
  }
};

// This is the definition of the CReg concurrent register primitive.
// It has multiple Reg interfaces that schedule in sequence.
template<typename T>
class MOD_CReg : public Module
{
 public:
  // CRegN, CRegA
  MOD_CReg<T>(tSimStateHdl simHdl, const char* name, Module* parent,
	      unsigned int width, const T& v, unsigned int async)
    : Module(simHdl, name, parent),
      ports(max_ports), // this should eventually be a parameter
      __clk_handle_0(BAD_CLOCK_HANDLE),
      bits(width), reset_value(v),
      reset_type(async ? ASYNC_RESET_REG : SYNC_RESET_REG),
      proxy(NULL)
  {
    init_val(value, bits);
    write_undet(&value, bits);

    in_reset = false;
    suppress_write = false;

    init_val(value_rec, bits);
    write_undet(&value_rec, bits);

    for (unsigned int i = 0; i < max_ports; i++) {
      init_val(read_val[i], bits);
      write_undet(&(read_val[i]), bits);
      did_write[i] = false;
      did_write_rec[i] = false;
      init_val(write_val[i], bits);
      write_undet(&(write_val[i]), bits);
    }

    symbol_count = 1;
    symbols = new tSym[symbol_count];

    symbols[0].key = "";
    symbols[0].info = SYM_DEF | bits << 4;
    symbols[0].value = (void*)(&value);
  }
  // CRegUN
  MOD_CReg<T>(tSimStateHdl simHdl, const char* name, Module* parent,
	      unsigned int width)
    : Module(simHdl, name, parent),
      ports(max_ports), // this should eventually be a parameter
      __clk_handle_0(BAD_CLOCK_HANDLE),
      bits(width), reset_type(NO_RESET_REG),
      proxy(NULL)
  {
    init_val(value, bits);
    write_undet(&value, bits);
    init_val(reset_value, bits);
    write_undet(&reset_value, bits);

    in_reset = false;
    suppress_write = false;

    init_val(value_rec, bits);
    write_undet(&value_rec, bits);

    for (unsigned int i = 0; i < max_ports; i++) {
      init_val(read_val[i], bits);
      write_undet(&(read_val[i]), bits);
      did_write[i] = false;
      did_write_rec[i] = false;
      init_val(write_val[i], bits);
      write_undet(&(write_val[i]), bits);
    }

    symbol_count = 1;
    symbols = new tSym[symbol_count];

    symbols[0].key = "";
    symbols[0].info = SYM_DEF | bits << 4;
    symbols[0].value = (void*)(&value);
  }
  ~MOD_CReg<T>() { delete proxy; }
 public:
  const T& METH_port0__read()    const { return value; }
  const T& METH_port1__read()    const { return value; }
  const T& METH_port2__read()    const { return value; }
  const T& METH_port3__read()    const { return value; }
  const T& METH_port4__read()    const { return value; }
  void METH_port0__write(const T& x)
  {
    if ((reset_type != ASYNC_RESET_REG) || !suppress_write) {
      value = x;
      did_write[0] = true;
      write_val[0] = x;
    }
  }
  void METH_port1__write(const T& x)
  {
    if ((reset_type != ASYNC_RESET_REG) || !suppress_write) {
      value = x;
      did_write[1] = true;
      write_val[1] = x;
    }
  }
  void METH_port2__write(const T& x)
  {
    if ((reset_type != ASYNC_RESET_REG) || !suppress_write) {
      value = x;
      did_write[2] = true;
      write_val[2] = x;
    }
  }
  void METH_port3__write(const T& x)
  {
    if ((reset_type != ASYNC_RESET_REG) || !suppress_write) {
      value = x;
      did_write[3] = true;
      write_val[3] = x;
    }
  }
  void METH_port4__write(const T& x)
  {
    if ((reset_type != ASYNC_RESET_REG) || !suppress_write) {
      value = x;
      did_write[4] = true;
      write_val[4] = x;
    }
  }
 public:
  void set_clk_0(const char* s)
  {
    __clk_handle_0 = bk_get_or_define_clock(sim_hdl, s);
  }
  void clk(tUInt8 /* clock_value */, tUInt8 gate_value = 1)
  {
    // compute Q_OUTs starting with the registered value
    // (before the writes to "value" this cycle)
    read_val[0] = value_rec;
    // record the registered value for the next clock cycle
    value_rec = value;
    // record the EN signals and clear them for the next clock cycle
    for (unsigned int i = 0; i < ports; i++) {
      did_write_rec[i] = did_write[i];
      did_write[i] = false;
    }
  }
  void reset_RST(tUInt8 rst_in)
  {
    in_reset = (rst_in == 0);
    if (in_reset)
    {
      if (reset_type == ASYNC_RESET_REG)
	rst_tick_clk(1);
      else if (reset_type == SYNC_RESET_REG)
	start_reset_ticks(sim_hdl); /* request rst_tick() on the next clock edge */
    }
    else
    {
      suppress_write = false;
      if (reset_type == SYNC_RESET_REG)
	stop_reset_ticks(sim_hdl); /* stop rst_tick() when reset is not asserted */
    }
  }
  void rst_tick_clk(tUInt8 clock_gate)
  {
    if (in_reset && (clock_gate != 0))
    {
      value = reset_value;
      value_rec = reset_value;
      suppress_write = true;
    }
  }
 public:
  void dump_state(unsigned int indent)
  {
    printf("%*s%s = ", indent, "", inst_name);
    dump_val(value, bits);
    putchar('\n');
  }
  unsigned int dump_VCD_defs(unsigned int /* num */)
  {
    // There are 3*ports signals the submodule scope (Q_OUT, EN, D_IN)
    // and one signal in the parent scope (alias for Q_OUT)
    // but aliases re-use the same number, so we reserve 3*ports
    vcd_num = vcd_reserve_ids(sim_hdl, 3 * ports);
    unsigned int num = vcd_num;

    // don't increment the num, we'll reuse it for the alias
    vcd_write_def(sim_hdl, num, inst_name, bits);

    // buffer for auto-generating the signal names
    // (longest name is Q_OUT_# plus room for null terminator)
    char* buf = (char*) malloc(8);

    vcd_write_scope_start(sim_hdl, inst_name);
    for (unsigned int i = 0; i < ports; i++) {
      // start with Q_OUT, so that the alias' number is reused
      sprintf(buf, "Q_OUT_%u", i);
      vcd_set_clock(sim_hdl, num, __clk_handle_0);
      vcd_write_def(sim_hdl, num++, buf, bits);

      sprintf(buf, "EN_%u", i);
      vcd_set_clock(sim_hdl, num, __clk_handle_0);
      vcd_write_def(sim_hdl, num++, buf, 1);

      sprintf(buf, "D_IN_%u", i);
      vcd_set_clock(sim_hdl, num, __clk_handle_0);
      vcd_write_def(sim_hdl, num++, buf, bits);
    }
    vcd_write_scope_end(sim_hdl);

    free(buf);
    return num;
  }
  void dump_VCD(tVCDDumpType dt, MOD_CReg<T>& backing)
  {
    unsigned int num = vcd_num;
    if (dt == VCD_DUMP_XS)
    {
      for (unsigned int i = 0; i < ports; i++) {
	vcd_write_x(sim_hdl, num++, bits); // Q_OUT (including alias)
	vcd_write_x(sim_hdl, num++, 1);    // EN
	vcd_write_x(sim_hdl, num++, bits); // D_IN
      }
    }
    else if (dt == VCD_DUMP_CHANGES)
    {
      // compute the q_out value as we go
      T tmp_q_out = read_val[0];
      for (unsigned int i = 0; i < ports; i++) {
	if (tmp_q_out != backing.read_val[i])
	  vcd_write_val(sim_hdl, num, tmp_q_out, bits);
	num++;
	// record the value, so we can dump if it changes
	// (this is unnecessary when i==0)
	read_val[i] = tmp_q_out;
	if (did_write_rec[i] != backing.did_write_rec[i])
	  vcd_write_val(sim_hdl, num, did_write_rec[i], 1);
	num++;
	if (write_val[i] != backing.write_val[i])
	  vcd_write_val(sim_hdl, num, write_val[i], bits);
	num++;
	if (did_write_rec[i])
	  tmp_q_out = write_val[i];
      }
    }
    else
    {
      // compute the q_out value as we go
      T tmp_q_out = read_val[0];
      for (unsigned int i = 0; i < ports; i++) {
	vcd_write_val(sim_hdl, num++, tmp_q_out, bits);
	// record the value, so we can dump if it changes
	// (this is unnecessary when i==0)
	read_val[i] = tmp_q_out;
	vcd_write_val(sim_hdl, num++, did_write_rec[i], 1);
	vcd_write_val(sim_hdl, num++, write_val[i], bits);
	if (did_write_rec[i])
	  tmp_q_out = write_val[i];
      }
    }

    for (unsigned int i = 0; i < ports; i++) {
      backing.read_val[i] = read_val[i];
      backing.did_write_rec[i] = did_write_rec[i];
      backing.write_val[i] = write_val[i];
    }
  }

 // register data members
 private:
  static const unsigned int max_ports = 5;
  const unsigned int ports;
  tClock __clk_handle_0;
  T value;
  const unsigned int bits;
  T reset_value;
  const unsigned int reset_type;
  bool suppress_write;
  bool in_reset;
  // for VCD dumping of the methods
  T value_rec;
  T read_val[max_ports];
  bool did_write[max_ports];
  bool did_write_rec[max_ports];
  T write_val[max_ports];

 // proxy access facility
 private:
  BluespecProbe<T>* proxy;
 public:
  BluespecProbe<T>& getProbe()
  {
    if (proxy == NULL)
      proxy = new BluespecProbe<T>(this, one, eq_one, read_reg, write_reg);
    return (*proxy);
  }
 private:
  static unsigned int one(void* /*obj */, bool /* hi */)
  {
    return 1;
  }
  static bool eq_one(void* /* obj */, unsigned int addr)
  {
    return (addr == 1);
  }
  static const T& read_reg(void* obj, unsigned int /* addr */)
  {
    MOD_CReg<T>* reg = (MOD_CReg<T>*) obj;
    return reg->value;
  }
  static bool write_reg(void* obj, unsigned int addr, const T& data)
  {
    if (addr == 1)
    {
      MOD_CReg<T>* reg = (MOD_CReg<T>*) obj;
      reg->value = data;
      return true;
    }
    else
      return false; // indicates write to invalid address
  }
};

#endif /* __BS_PRIM_MOD_REG_H__ */
