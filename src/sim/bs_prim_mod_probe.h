#ifndef __BS_PRIM_MOD_PROBE_H__
#define __BS_PRIM_MOD_PROBE_H__

#include "bluesim_kernel_api.h"
#include "bluesim_probes.h"
#include "bs_module.h"
#include "bs_vcd.h"

// This is the definition of the Probe primitive.
template<typename T>
class MOD_Probe : public Module
{
 public:
  MOD_Probe<T>(tSimStateHdl simHdl, const char* name, Module* parent,
               unsigned int width)
    : Module(simHdl, name, parent), __clk_handle_0(BAD_CLOCK_HANDLE),
      bits(width), proxy(NULL)
  {
    init_val(value, bits);
    write_undet(&value, bits);

    symbol_count = 1;
    symbols = new tSym[symbol_count];

    symbols[0].key = "";
    symbols[0].info = SYM_DEF | bits << 4;
    symbols[0].value = (void*)(&value);
  }
 public:
  void METH__write(const T& x) { value = x; }
 public:
  void set_clk_0(const char* s)
  {
    __clk_handle_0 = bk_get_or_define_clock(sim_hdl, s);
  }
  void dump_state(unsigned int indent)
  {
    printf("%*s%s = ", indent, "", inst_name);
    dump_val(value, bits);
    putchar('\n');
  }
  unsigned int dump_VCD_defs(unsigned int /* num */)
  {
    char* buf = (char*) malloc(strlen(inst_name) + 7);
    sprintf(buf,"%s$PROBE", inst_name);
    vcd_num = vcd_reserve_ids(sim_hdl, 1);
    vcd_set_clock(sim_hdl, vcd_num, __clk_handle_0);
    vcd_write_def(sim_hdl, vcd_num, buf, bits);
    free(buf);
    return (vcd_num + 1);
  }
  void dump_VCD(tVCDDumpType dt, MOD_Probe<T>& backing)
  {
    if (dt == VCD_DUMP_XS)
      vcd_write_x(sim_hdl, vcd_num, bits);
    else if ((dt != VCD_DUMP_CHANGES) || (backing.value != value))
    {
      vcd_write_val(sim_hdl, vcd_num, value, bits);
      backing.value = value;
    }
  }

 // Probe data members
 private:
  tClock __clk_handle_0;
  T value;
  unsigned int bits;

 // proxy access facility 
 private:
  BluespecProbe<T>* proxy;
 public:
  BluespecProbe<T>& getProbe()
  {
    if (proxy == NULL)
      proxy = new BluespecProbe<T>(this, one, eq_one, read_probe, write_probe);
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
  static const T& read_probe(void* obj, unsigned int /* addr */)
  {
    MOD_Probe<T>* probe = (MOD_Probe<T>*) obj;
    return probe->value;
  }
  static bool write_probe(void* /* obj */, unsigned int /* addr */, const T& /* data */)
  {
    return false; // MOD_Probe<T> instances are read-only
  }
};

// This is the definition of the ProbeWire primitive.
template<typename T>
class MOD_ProbeWire : public Module
{
 public:
  MOD_ProbeWire<T>(tSimStateHdl simHdl, const char* name, Module* parent,
                   unsigned int width)
    : Module(simHdl, name, parent)
  {
    symbol_count = 0;
    symbols = NULL;
  }
 public:
  const T& METH_id(const T& x) const { return x; }
 public:
  void set_clk_0(const char* s)
  {
    //__clk_handle_0 = bk_get_or_define_clock(sim_hdl, s);
  }
  void dump_state(unsigned int indent)
  {
  }
  unsigned int dump_VCD_defs(unsigned int /* num */)
  {
    return vcd_num;
  }
  void dump_VCD(tVCDDumpType dt, MOD_ProbeWire<T>& backing)
  {
  }

 // ProbeWire data members
 private:
};

#endif /* __BS_PRIM_MOD_PROBE_H__ */
