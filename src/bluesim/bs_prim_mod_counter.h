#ifndef __BS_PRIM_MOD_COUNTER_H__
#define __BS_PRIM_MOD_COUNTER_H__

#include "bluesim_kernel_api.h"
#include "bs_module.h"
#include "bs_reset.h"
#include "bs_vcd.h"

// This is the definition of the Probe primitive.
template<typename T>
class MOD_Counter : public Module
{
 public:
  MOD_Counter<T>(tSimStateHdl simHdl, const char* name, Module* parent,
                 unsigned int width, const T& init)
    : Module(simHdl, name, parent),
      saved_at(~bk_now(sim_hdl)),
      a_at(~bk_now(sim_hdl)), b_at(~bk_now(sim_hdl)),
      c_at(~bk_now(sim_hdl)), f_at(~bk_now(sim_hdl)),

      bits(width), reset_val(init)
  {
    init_val(val, bits);
    write_undet(&val, bits);
    init_val(a, bits);
    init_val(b, bits);
    init_val(c, bits);
    init_val(f, bits);
    init_val(saved_val, bits);
    in_reset = false;
    suppress_write = false;
  }

 public:
  const T& METH_value() const
  {
    if (bk_is_same_time(sim_hdl, saved_at))
      return saved_val;
    else
      return val;
  }
  void METH_setC(const T& x)
  {
    if (!suppress_write)
    {
      if (saved_at != bk_now(sim_hdl))
      {
        saved_at = bk_now(sim_hdl);
        saved_val = val;
      }
      c_at = bk_now(sim_hdl);
      c    = x;
      val  = x;
      if (a_at == bk_now(sim_hdl))
        val += a;
      if (b_at == bk_now(sim_hdl))
        val += b;
      mask_high_bits(&val,bits);
    }
  }
  void METH_addA(const T& x)
  {
    if (!suppress_write)
    {
      if (saved_at != bk_now(sim_hdl))
      {
        saved_at = bk_now(sim_hdl);
        saved_val = val;
      }
      a_at = bk_now(sim_hdl);
      a    = x;
      val += x;
      mask_high_bits(&val,bits);
    }
  }
  void METH_addB(const T& x)
  {
    if (!suppress_write)
    {
      if (saved_at != bk_now(sim_hdl))
      {
        saved_at = bk_now(sim_hdl);
        saved_val = val;
      }
      b_at = bk_now(sim_hdl);
      b    = x;
      val += x;
      mask_high_bits(&val,bits);
    }
  }
  // Note: addA, addB, setC < setF
  void METH_setF(const T& x)
  {
    if (!suppress_write)
    {
      if (saved_at != bk_now(sim_hdl))
      {
        saved_at = bk_now(sim_hdl);
        saved_val = val;
      }
      f_at = bk_now(sim_hdl);
      f    = x;
      val  = x;
    }
  }
  const T& METH__read() const
  {
    return METH_value();
  }
  void METH_incrA (const T& x)
  {
    METH_addA(x);
  }
  void METH_incrB (const T& x)
  {
    METH_addB(x);
  }
  void METH_update (const T& x)
  {
    METH_setC(x);
  }
  void METH__write (const T& x)
  {
    METH_setF(x);
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
      suppress_write = false;
      stop_reset_ticks(sim_hdl); /* stop rst_tick() when reset is not asserted */
    }
  }
  void rst_tick__clk__1(tUInt8 clock_gate)
  {
    if (in_reset && (clock_gate != 0))
    {
      val = reset_val;
      suppress_write = true;
    }
  }
  void rst_tick__clk__(tUInt8 clock_gate)
  {
    rst_tick__clk__1(clock_gate);
  }

 public:
  void dump_state(unsigned int indent)
  {
    printf("%*s%s = ", indent, "", inst_name);
    dump_val(val, bits);
    putchar('\n');
  }
  unsigned int dump_VCD_defs(unsigned int /* num */)
  {
    vcd_num = vcd_reserve_ids(sim_hdl, 9);
    unsigned int n = vcd_num;
    vcd_write_def(sim_hdl, n++, inst_name, bits);
    vcd_write_scope_start(sim_hdl, inst_name);
    vcd_set_clock(sim_hdl, n, __clk_handle_0);
    vcd_write_def(sim_hdl, n++, "ADDA", 1);
    vcd_set_clock(sim_hdl, n, __clk_handle_0);
    vcd_write_def(sim_hdl, n++, "DATA_A", bits);
    vcd_set_clock(sim_hdl, n, __clk_handle_0);
    vcd_write_def(sim_hdl, n++, "ADDB", 1);
    vcd_set_clock(sim_hdl, n, __clk_handle_0);
    vcd_write_def(sim_hdl, n++, "DATA_B", bits);
    vcd_set_clock(sim_hdl, n, __clk_handle_0);
    vcd_write_def(sim_hdl, n++, "SETC", 1);
    vcd_set_clock(sim_hdl, n, __clk_handle_0);
    vcd_write_def(sim_hdl, n++, "DATA_C", bits);
    vcd_set_clock(sim_hdl, n, __clk_handle_0);
    vcd_write_def(sim_hdl, n++, "SETF", 1);
    vcd_set_clock(sim_hdl, n, __clk_handle_0);
    vcd_write_def(sim_hdl, n++, "DATA_F", bits);
    vcd_write_def(sim_hdl, vcd_num, "q_state", bits); // alias
    vcd_write_def(sim_hdl, vcd_num, "Q_OUT", bits); // alias
    vcd_write_scope_end(sim_hdl);
    return (vcd_num + 9);
  }
  void dump_VCD(tVCDDumpType dt, MOD_Counter<T>& backing)
  {
    unsigned int num = vcd_num;
    if (dt == VCD_DUMP_XS) {
      vcd_write_x(sim_hdl, num++, bits); // inst, q_state, Q_OUT
      vcd_write_x(sim_hdl, num++, 1);    // ADDA
      vcd_write_x(sim_hdl, num++, bits); // DATA_A
      vcd_write_x(sim_hdl, num++, 1);    // ADDB
      vcd_write_x(sim_hdl, num++, bits); // DATA_B
      vcd_write_x(sim_hdl, num++, 1);    // SETC
      vcd_write_x(sim_hdl, num++, bits); // DATA_C
      vcd_write_x(sim_hdl, num++, 1);    // SETF
      vcd_write_x(sim_hdl, num++, bits); // DATA_F
    }
    else if (dt == VCD_DUMP_CHANGES)
    {
      if (backing.val != val) vcd_write_val(sim_hdl, num++, val, bits);
      else ++num;
      bool at_posedge =
               bk_clock_val(sim_hdl, __clk_handle_0) == CLK_HIGH &&
               bk_clock_last_edge(sim_hdl, __clk_handle_0) == bk_now(sim_hdl);
      if (at_posedge)
      {
        did_adda = bk_is_same_time(sim_hdl, a_at);
        if (backing.did_adda != did_adda) {
          vcd_write_val(sim_hdl, num++, did_adda, 1);
          backing.did_adda = did_adda;
        }
        else
          ++num;
        if (backing.a != a) vcd_write_val(sim_hdl, num++, a, bits);
        else ++num;

        did_addb = bk_is_same_time(sim_hdl, b_at);
        if (backing.did_addb != did_addb) {
          vcd_write_val(sim_hdl, num++, did_addb, 1);
          backing.did_addb = did_addb;
        }
        else
          ++num;
        if (backing.b != b) vcd_write_val(sim_hdl, num++, b, bits);
        else ++num;

        did_setc = bk_is_same_time(sim_hdl, c_at);
        if (backing.did_setc != did_setc) {
          vcd_write_val(sim_hdl, num++, did_setc, 1);
          backing.did_setc = did_setc;
        }
        else
          ++num;
        if (backing.c != c) vcd_write_val(sim_hdl, num++, c, bits);
        else ++num;

        did_setf = bk_is_same_time(sim_hdl, f_at);
        if (backing.did_setf != did_setf) {
          vcd_write_val(sim_hdl, num++, did_setf, 1);
          backing.did_setf = did_setf;
        }
        else
          ++num;
        if (backing.f != f) vcd_write_val(sim_hdl, num++, f, bits);
        else ++num;
      }
    }
    else
    {
      vcd_write_val(sim_hdl, num++, val, bits);
      did_adda = bk_is_same_time(sim_hdl, a_at);
      vcd_write_val(sim_hdl, num++, did_adda, 1);
      vcd_write_val(sim_hdl, num++, a, bits);
      did_addb = bk_is_same_time(sim_hdl, b_at);
      vcd_write_val(sim_hdl, num++, did_addb, 1);
      vcd_write_val(sim_hdl, num++, b, bits);
      did_setc = bk_is_same_time(sim_hdl, c_at);
      vcd_write_val(sim_hdl, num++, did_setc, 1);
      vcd_write_val(sim_hdl, num++, c, bits);
      did_setf = bk_is_same_time(sim_hdl, f_at);
      vcd_write_val(sim_hdl, num++, did_setf, 1);
      vcd_write_val(sim_hdl, num++, f, bits);

      backing.did_adda = did_adda;
      backing.did_addb = did_addb;
      backing.did_setc = did_setc;
      backing.did_setf = did_setf;
    }

    if (backing.val != val) backing.val = val;
    if (backing.a != a)     backing.a = a;
    if (backing.b != b)     backing.b = b;
    if (backing.c != c)     backing.c = c;
    if (backing.f != f)     backing.f = f;
  }

 private:
  T val;
  T saved_val;
  T a;
  T b;
  T c;
  T f;
  tTime saved_at;
  tTime a_at;
  tTime b_at;
  tTime c_at;
  tTime f_at;
  const unsigned int bits;
  T reset_val;
  bool suppress_write;
  bool in_reset;

  // used for VCD dumping
  tClock __clk_handle_0;
  bool did_adda;
  bool did_addb;
  bool did_setc;
  bool did_setf;
};

#endif /* __BS_PRIM_MOD_COUNTER_H__ */
