#ifndef __TBGCD_SCH__
#define __TBGCD_SCH__

SC_MODULE(mkTbGCD)
{
  // clock & reset inputs
  sc_in<bool> CLK;
  sc_in<bool> RST_N;

  // start method call ports
  sc_in<bool>        gcd_RDY_start;
  sc_out<bool>       gcd_EN_start;
  sc_out<sc_bv<16> > gcd_start_num1;
  sc_out<sc_bv<16> > gcd_start_num2;

  // result method call ports
  sc_in<bool>       gcd_RDY_result;
  sc_in<sc_bv<16> > gcd_result;

  // sub-modules

  // constructor
  SC_CTOR(mkTbGCD)
    : CLK("CLK"), RST_N("RST_N"),
      gcd_RDY_start("gcd_RDY_start"), gcd_EN_start("gcd_EN_start"),
      gcd_start_num1("gcd_start_num1"), gcd_start_num2("gcd_start_num2"),
      gcd_RDY_result("gcd_RDY_result"), gcd_result("gcd_result"),
      count1(0xaaaa), count2(0xaaaa), tbresult(0xaaaa), in_reset(false)
  {
    SC_METHOD(posedge_clk);
    sensitive << CLK.pos();
    dont_initialize();

    SC_METHOD(combinational_paths);
    sensitive << gcd_RDY_start.value_changed();
    dont_initialize();

    SC_METHOD(handle_reset);
    sensitive << RST_N.value_changed();
    dont_initialize();
  }

 private:
  // local state
  sc_uint<16> count1;
  sc_uint<16> count2;
  sc_uint<16> tbresult;
  bool in_reset;

  // rules
  void RL_send_input();
  void RL_get_result();
  void RL_done();

  // posedge clock
  void posedge_clk();

  // combinational logic
  void combinational_paths();   

  // reset
  void handle_reset();
};

#endif // __TBGCD_SCH__
