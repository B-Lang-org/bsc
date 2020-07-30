
#include "systemc.h"
#include "mkGCD_systemc.h"

// This just generates the clock and reset signals
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

  // Clock's first posedge is at time 1 -- thereafter it has a
  // posedge on every multiple of 10.
  // So the edges are at 1,10,20,30,...
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

  // Reset is asserted low until time 2, so that the first clock edge
  // (at time 1) occurs during reset.
  void gen_reset()
  {
    RST_N.write(false);
    wait(2,SC_NS);
    RST_N.write(true);
  } 
};

// This is the main testbench module
SC_MODULE(mkTb)
{
 public:
  // clock and reset input ports
  sc_in<bool> CLK;
  sc_in<bool> RST_N;

  // start method ports
  sc_in<bool>        gcd_RDY_start;
  sc_out<bool>       gcd_EN_start;
  sc_out<sc_bv<16> > gcd_start_num1;
  sc_out<sc_bv<16> > gcd_start_num2;

  // result method ports
  sc_in<bool>       gcd_RDY_result;
  sc_in<sc_bv<16> > gcd_result;

  // constructor
  SC_CTOR(mkTb)
    : CLK("CLK"), RST_N("RST_N"),
      gcd_RDY_start("gcd_RDY_start"), gcd_EN_start("gcd_EN_start"),
      gcd_start_num1("gcd_start_num1"), gcd_start_num2("gcd_start_num2"),
      gcd_RDY_result("gcd_RDY_result"), gcd_result("gcd_result")
  {
    SC_THREAD(stimulate);  // uses dynamic sensitivity
  }

 private:
  // This is the stimulus generator
  void stimulate()
  {
    // wait to come out of reset
    if (RST_N == 0) wait(RST_N.posedge_event());

    // Setup our local counter variables
    count1 = 3;
    count2 = 7;

    // Loop generating test stimulus
    while (count1 < 100)
    {
      // call the do_gcd helper routine that twiddles the signals
      do_gcd(count1,count2);
      
      // increment the counts
      count1 += 3;
      count2 += 2;
    }

    // Test done, we can exit
    sc_stop();
  }

  void do_gcd(unsigned int num1, unsigned int num2)
  {
    // wait for the start method to become ready
    if (!gcd_RDY_start) wait(gcd_RDY_start.posedge_event());
    
    // trigger the start method
    gcd_EN_start.write(true);
    gcd_start_num1.write(num1);
    gcd_start_num2.write(num2);

    // return EN to false after the clock edge and then wait
    // for the result method to become ready again
    wait(CLK.posedge_event());
    gcd_EN_start.write(false);
    wait(1.0, SC_PS);
    while (!gcd_RDY_result) wait(gcd_RDY_result.posedge_event());

    // read and report the result value
    wait(1.0, SC_PS);
    std::cout << "gcd(" << num1 << "," << num2 << ") = " << gcd_result.read().to_uint() << std::endl;    
  }

 private:
  // local testbench state
  unsigned int count1;
  unsigned int count2;

  // local testbench routines
};

// This is the top-level SystemC function which is responsible
// for setting up the system and kicking it off with sc_start().
int sc_main(int argc, char* argv[])
{
  // Make the clock and reset generator
  mkMain top("top");

  // Make the testbench
  mkTb tb("tb");

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

  // kick off simulation
  sc_start();

  return 0;
}
