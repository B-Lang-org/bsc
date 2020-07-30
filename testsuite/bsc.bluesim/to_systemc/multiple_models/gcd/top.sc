#include <systemc.h>

#include "mkTbGCD_systemc.h"
#include "mkGCD_systemc.h"

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

SC_MODULE(mkTestTop)
{
  // clock and reset output ports
  sc_in<bool> CLK;
  sc_in<bool> RST_N;

  mkTbGCD   tb;
  mkGCD     gcd;

  sc_signal<bool> gcd_EN_start;
  sc_signal<sc_bv<16> > gcd_start_num1;
  sc_signal<sc_bv<16> > gcd_start_num2;

  sc_signal<bool> tb_EN_start;
  sc_signal<bool> tb_EN_result;
  sc_signal<sc_bv<16> > tb_result_r;

  // placate the systemc analysis

  sc_signal<bool> gcd_RDY_start;
  sc_signal<bool> gcd_RDY_result;
  sc_signal<sc_bv<16> > gcd_result;

  sc_signal<bool> tb_RDY_start;
  sc_signal<bool> tb_RDY_result;
  sc_signal<sc_bv<16> > tb_num1;
  sc_signal<sc_bv<16> > tb_num2;

  // constructor
  SC_CTOR(mkTestTop)
    : CLK("CLK"), RST_N("RST_N")
    , tb("tb")
    , gcd("gcd")
  {
    gcd_EN_start = false;
    gcd_start_num1 = 0;
    gcd_start_num2 = 0;

    tb_EN_start = false;
    tb_EN_result = false;
    tb_result_r = 0;

    gcd.CLK.bind(CLK);
    gcd.RST_N.bind(RST_N);

    gcd.EN_start.bind(gcd_EN_start);
    gcd.start_num1.bind(gcd_start_num1);
    gcd.start_num2.bind(gcd_start_num2);

    gcd.RDY_start.bind(gcd_RDY_start);
    gcd.RDY_result.bind(gcd_RDY_result);
    gcd.result.bind(gcd_result);

    tb.CLK.bind(CLK);
    tb.RST_N.bind(RST_N);

    tb.EN_start.bind(tb_EN_start);
    tb.EN_result.bind(tb_EN_result);
    tb.result_r.bind(tb_result_r);

    tb.RDY_start.bind(tb_RDY_start);
    tb.RDY_result.bind(tb_RDY_result);
    tb.num1.bind(tb_num1);
    tb.num2.bind(tb_num2);

    SC_METHOD(handle_start);
      sensitive << tb.RDY_start.value_changed();
      sensitive << gcd.RDY_start.value_changed();
      sensitive << tb.num1.value_changed();
      sensitive << tb.num2.value_changed();

    SC_METHOD(handle_result);
      sensitive << tb.RDY_result.value_changed();
      sensitive << gcd.RDY_result.value_changed();
      sensitive << gcd.result.value_changed();
  }

  void handle_start() {
    if (tb.RDY_start.read() && gcd.RDY_start.read()) {
      sc_bv<16> n1 = tb.num1.read();
      sc_bv<16> n2 = tb.num2.read();
      // cout << "connect_start: " << n1 << ", " << n2 << endl;
      gcd_start_num1.write(n1);
      gcd_start_num2.write(n2);
      tb_EN_start.write(true);
      gcd_EN_start.write(true);
    } else {
      tb_EN_start.write(false);
      gcd_EN_start.write(false);
    }
  }

  void handle_result() {
    if (tb.RDY_result.read() && gcd.RDY_result.read()) {
      sc_bv<16> r = gcd.result.read();
      // cout << "connect_result: " << r << endl;
      tb_result_r.write(r);
      tb_EN_result.write(true);
    } else {
      tb_EN_result.write(false);
    }
  }

};

int sc_main(int argc, char* argv[])
{
  // Make the clock and reset generator
  mkMain main("main");
  mkTestTop top("top");

  // connect the clock and reset
  sc_signal<bool> clk;
  main.CLK.bind(clk);
  top.CLK.bind(clk);

  sc_signal<bool> rstn;
  main.RST_N.bind(rstn);
  top.RST_N.bind(rstn);

  sc_start();

  return 0;
}
