#ifndef __TBGETPUT_SCH__
#define __TBGETPUT_SCH__

SC_MODULE(mkTbGetPut)
{
  // clock & reset inputs
  sc_in<bool> CLK;
  sc_in<bool> RST_N;

  // in_put method call ports
  sc_in<bool>       dut_RDY_in_put;
  sc_out<bool>      dut_EN_in_put;
  sc_out<sc_bv<8> > dut_in_put;

  // out_get method call ports
  sc_in<bool>      dut_RDY_out_get;
  sc_in<sc_bv<8> > dut_out_get;

  // sub-modules

  // constructor
  SC_CTOR(mkTbGetPut)
    : CLK("CLK"), RST_N("RST_N"),
      dut_RDY_in_put("dut_RDY_in_put"), dut_EN_in_put("dut_EN_in_put"),
      dut_in_put("dut_in_put"),
      dut_RDY_out_get("dut_RDY_out_get"), dut_out_get("dut_out_get"),
      count(0xaa), in_reset(false)
  {
    SC_METHOD(posedge_clk);
    sensitive << CLK.pos();
    dont_initialize();

    SC_METHOD(combinational_paths);
    sensitive << dut_RDY_in_put.value_changed() << count_sig.default_event();
    dont_initialize();

    SC_METHOD(handle_reset);
    sensitive << RST_N.value_changed();
    dont_initialize();
  }

 private:
  // local state
  sc_uint<8> count;
  sc_signal<sc_uint<8> > count_sig;
  bool in_reset;

  // rules
  void RL_send_input();
  void RL_get_output();
  void RL_done();

  // posedge clock
  void posedge_clk();

  // combinational logic
  void combinational_paths();   

  // reset
  void handle_reset();
};

#endif // __TBGETPUT_SCH__
