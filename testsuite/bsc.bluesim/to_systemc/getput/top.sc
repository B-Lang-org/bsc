#include <systemc.h>

#include "TbGetPut.sch"
#include "mkGetPutTest_systemc.h"

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
  mkTbGetPut tb("tb");

  // Make the DUT
  mkGetPutTest dut("dut");

  // connect the clock and reset to the testbench and DUT
  sc_signal<bool> clk;
  sc_signal<bool> rstn;
  top.CLK.bind(clk);
  top.RST_N.bind(rstn);
  tb.CLK.bind(clk);
  tb.RST_N.bind(rstn);
  dut.CLK.bind(clk);
  dut.RST_N.bind(rstn);

  // connect the ports for the in_put methood
  sc_signal<bool>      dut_RDY_in_put;
  sc_signal<bool>      dut_EN_in_put;
  sc_signal<sc_bv<8> > dut_in_put;
  dut.RDY_in_put(dut_RDY_in_put);
  tb.dut_RDY_in_put.bind(dut_RDY_in_put);
  dut.EN_in_put.bind(dut_EN_in_put);
  tb.dut_EN_in_put.bind(dut_EN_in_put);
  dut.in_put.bind(dut_in_put);
  tb.dut_in_put.bind(dut_in_put);

  // connect the ports for the result methood
  sc_signal<bool>      dut_RDY_out_get;
  sc_signal<sc_bv<8> > dut_out_get;
  dut.RDY_out_get.bind(dut_RDY_out_get);
  tb.dut_RDY_out_get.bind(dut_RDY_out_get);
  dut.out_get.bind(dut_out_get);
  tb.dut_out_get.bind(dut_out_get);

  sc_start();

  return 0;
}
