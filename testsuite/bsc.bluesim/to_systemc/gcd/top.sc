#include <systemc.h>

#include "TbGCD.sch"
#include DUT_INCLUDE

SC_MODULE(mkMain)
{
  // clock and reset output ports
  sc_out<bool> CLK;
  sc_out<bool> RST_N;

  // constructor
  SC_CTOR(mkMain)
    : CLK("CLK"), RST_N("RST_N")
  {
    // generate the clock
    CLK.initialize(false);
    SC_THREAD(gen_clock);

    // generate reset
    RST_N.initialize(true);
    SC_THREAD(gen_reset);
  }

  void gen_clock()
  {
    wait(1,SC_NS);
    CLK.write(true);
    wait(4,SC_NS);
    while (true)
    {
      CLK.write(false);
      wait(5,SC_NS);
      CLK.write(true);
      wait(5,SC_NS);
    }
  }

  void gen_reset()
  {
    RST_N.write(false);
    wait(2,SC_NS);
    RST_N.write(true);
  } 
};

int sc_main(int argc, char* argv[])
{
  // Make the clock and reset generator
  mkMain top("top");

  // Make the testbench
  mkTbGCD tb("tb");

  // Make the DUT
  mkGCD gcd("gcd");

  // connect the clock and reset to the testbench and DUT
  sc_signal<bool> clk;
  sc_signal<bool> rstn;
  top.CLK.bind(clk);
  top.RST_N.bind(rstn);
  tb.CLK.bind(clk);
  tb.RST_N.bind(rstn);
  gcd.CLK.bind(clk);
  gcd.RST_N.bind(rstn);

  // connect the ports for the start methood
  sc_signal<bool>       gcd_RDY_start;
  sc_signal<bool>       gcd_EN_start;
  sc_signal<sc_bv<16> > gcd_start_num1;
  sc_signal<sc_bv<16> > gcd_start_num2;
  gcd.RDY_start.bind(gcd_RDY_start);
  tb.gcd_RDY_start.bind(gcd_RDY_start);
  gcd.EN_start.bind(gcd_EN_start);
  tb.gcd_EN_start.bind(gcd_EN_start);
  gcd.start_num1.bind(gcd_start_num1);
  tb.gcd_start_num1.bind(gcd_start_num1);
  gcd.start_num2.bind(gcd_start_num2);
  tb.gcd_start_num2.bind(gcd_start_num2);

  // connect the ports for the result methood
  sc_signal<bool>       gcd_RDY_result;
  sc_signal<sc_bv<16> > gcd_result;
  gcd.RDY_result.bind(gcd_RDY_result);
  tb.gcd_RDY_result.bind(gcd_RDY_result);
  gcd.result.bind(gcd_result);
  tb.gcd_result.bind(gcd_result);

  sc_start();

  return 0;
}
