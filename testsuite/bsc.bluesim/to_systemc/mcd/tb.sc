#include <cstdio>

#include "systemc.h"
#include "mkMCD_systemc.h"

#define TRACE(x) sc_trace(tf,x,#x)

SC_MODULE(mkMain)
{
  // clock and reset output ports
  sc_out<bool> CLK;
  sc_out<bool> RST_N;
  sc_out<bool> CLK_clk_a;
  sc_out<bool> RST_N_rstn_a;
  sc_out<bool> CLK_clk_b;
  sc_out<bool> RST_N_rstn_b;
  sc_out<bool> CLK_clk_out;

  // constructor
  SC_CTOR(mkMain)
    : CLK("CLK"),       RST_N("RST_N")
    , CLK_clk_a("CLK_clk_a"), RST_N_rstn_a("RST_N_rstn_a")
    , CLK_clk_b("CLK_clk_b"), RST_N_rstn_b("RST_N_rstn_b")
    , CLK_clk_out("CLK_clk_out")
  {
    // generate the default clock
    CLK.initialize(false);
    SC_THREAD(gen_clock);

    // generate the default reset
    RST_N.initialize(true);
    SC_THREAD(gen_reset);

    // generate the "a" port clock
    CLK_clk_a.initialize(false);
    SC_THREAD(gen_clock_a);

    // generate the "a" port reset
    RST_N_rstn_a.initialize(true);
    SC_THREAD(gen_reset_a);

    // generate the "b" port clock
    CLK_clk_b.initialize(false);
    SC_THREAD(gen_clock_b);

    // generate the "b" port reset
    RST_N_rstn_b.initialize(true);
    SC_THREAD(gen_reset_b);

    // generate the output clock
    CLK_clk_out.initialize(false);
    SC_THREAD(gen_clock_out);
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

  void gen_clock_a()
  {
    wait(1,SC_NS);
    CLK_clk_a.write(true);
    wait(6,SC_NS);
    while (true)
    {
      CLK_clk_a.write(false);
      wait(7,SC_NS);
      CLK_clk_a.write(true);
      wait(7,SC_NS);
    }
  }

  void gen_reset_a()
  {
    RST_N_rstn_a.write(false);
    wait(2,SC_NS);
    RST_N_rstn_a.write(true);
  }

  void gen_clock_b()
  {
    wait(1,SC_NS);
    CLK_clk_b.write(true);
    wait(3,SC_NS);
    while (true)
    {
      CLK_clk_b.write(false);
      wait(4,SC_NS);
      CLK_clk_b.write(true);
      wait(4,SC_NS);
    }
  }

  void gen_reset_b()
  {
    RST_N_rstn_b.write(false);
    wait(2,SC_NS);
    RST_N_rstn_b.write(true);
  }

  void gen_clock_out()
  {
    wait(1,SC_NS);
    CLK_clk_out.write(true);
    wait(5,SC_NS);
    while (true)
    {
      CLK_clk_out.write(false);
      wait(5,SC_NS);
      CLK_clk_out.write(true);
      wait(6,SC_NS);
    }
  }
};

// This is the main testbench module
SC_MODULE(mkTb)
{
 public:
  // clock and reset input ports
  sc_in<bool> CLK;
  sc_in<bool> RST_N;
  sc_in<bool> CLK_clk_a;
  sc_in<bool> RST_N_rstn_a;
  sc_in<bool> CLK_clk_b;
  sc_in<bool> RST_N_rstn_b;
  sc_in<bool> CLK_clk_out;

  // deq method ports
  sc_in<bool>  RDY_deq;
  sc_out<bool> EN_deq;

  // first method ports
  sc_in<bool>       RDY_first;
  sc_in<sc_bv<32> > first;

  // enq_a method ports
  sc_in<bool>        RDY_enq_a;
  sc_out<bool>       EN_enq_a;
  sc_out<sc_bv<32> > enq_a_x;

  // enq_b method ports
  sc_in<bool>        RDY_enq_b;
  sc_out<bool>       EN_enq_b;
  sc_out<sc_bv<32> > enq_b_x;

  // flip method ports
  sc_in<bool>  RDY_flip;
  sc_out<bool> EN_flip;

  // constructor
  SC_CTOR(mkTb)
    : CLK("CLK"), RST_N("RST_N")
    , CLK_clk_a("clk_a"), RST_N_rstn_a("rstn_a")
    , CLK_clk_b("clk_b"), RST_N_rstn_b("rstn_b")
    , CLK_clk_out("clk_out")
    , RDY_deq("RDY_deq"), EN_deq("EN_deq")
    , RDY_first("RDY_first"), first("first")
    , RDY_enq_a("RDY_enq_a"), EN_enq_a("EN_enq_a"), enq_a_x("enq_a_x")
    , RDY_enq_b("RDY_enq_b"), EN_enq_b("EN_enq_b"), enq_b_x("enq_b_x")
    , RDY_flip("RDY_flip"), EN_flip("EN_flip")
  {
    SC_THREAD(drive_port_a);   // uses dynamic sensitivity
    SC_THREAD(drive_port_b);   // uses dynamic sensitivity
    SC_THREAD(drive_flip);     // uses dynamic sensitivity
    SC_THREAD(check_out_port); // uses dynamic sensitivity
  }

 private:

  void drive_port_a()
  {
    // wait to come out of reset
    if (RST_N_rstn_a == 0) wait(RST_N_rstn_a.posedge_event());

    // Loop generating test stimulus
    for (unsigned int count = 0; count < 100; ++count)
    {
      // call the do_enq helper routine that twiddles the signals
      do_enq(&CLK_clk_a, &RDY_enq_a, &EN_enq_a, &enq_a_x, count | 0xa0000000);
      printf("%llu: put: %x on port A\n",
             sc_time_stamp().value(), count | 0xa0000000);
    }

    // Test done, we can exit
    sc_stop();
  }

  void drive_port_b()
  {
    // wait to come out of reset
    if (RST_N_rstn_b == 0) wait(RST_N_rstn_b.posedge_event());

    // Loop generating test stimulus
    for (unsigned int count = 0; count < 100; ++count)
    {
      // call the do_enq helper routine that twiddles the signals
      do_enq(&CLK_clk_b, &RDY_enq_b, &EN_enq_b, &enq_b_x, count | 0xb0000000);
      printf("%llu: put: %x on port B\n",
             sc_time_stamp().value(), count | 0xb0000000);
    }

    // Test done, we can exit
    sc_stop();
  }

  void drive_flip()
  {
    // wait to come out of reset
    if (RST_N == 0) wait(RST_N.posedge_event());

    // Loop generating test stimulus
    unsigned int x = 0;
    bool en_flip;
    while (true)
    {
      // assume that flip is always ready
      en_flip = (x % 10 == 3) || (x % 7 == 2);
      ++x;
      EN_flip.write(en_flip);
      wait(CLK.posedge_event());
      if (en_flip)
        printf("%llu: flipped\n", sc_time_stamp().value());
    }
  }

  void check_out_port()
  {
    while (true)
    {
      while (!RDY_first || !RDY_deq)
        wait(RDY_first.posedge_event() | RDY_deq.posedge_event());
      EN_deq.write(true);
      wait(CLK_clk_out.posedge_event());
      EN_deq.write(false);
      unsigned int x = first.read().to_uint();
      printf("%llu: got: %x\n", sc_time_stamp().value(), x);
      wait(SC_ZERO_TIME);
    }
  }

  void do_enq(sc_in<bool>* clk, sc_in<bool>* rdy,
              sc_out<bool>* en, sc_out<sc_bv<32> >* input,
	      unsigned int val)
  {
    // wait for the enq method to become ready
    if (!rdy->read()) wait(rdy->posedge_event());

    // trigger the enq method
    en->write(true);
    input->write(val);

    // return EN to false after the clock edge
    wait(clk->posedge_event());
    en->write(false);
    wait(SC_ZERO_TIME);
  }
};


int sc_main(int argc, char* argv[])
{
  // Make the clock and reset generator
  mkMain top("top");

  // Make the testbench
  mkTb tb("tb");

  // Make the DUT
  mkMCD mcd("mcd");

  // connect the clocks and resets to the testbench and DUT
  sc_signal<bool> clk;
  sc_signal<bool> rstn;
  top.CLK.bind(clk);
  top.RST_N.bind(rstn);
  tb.CLK.bind(clk);
  tb.RST_N.bind(rstn);
  mcd.CLK.bind(clk);
  mcd.RST_N.bind(rstn);

  sc_signal<bool> clk_a;
  sc_signal<bool> rstn_a;
  top.CLK_clk_a.bind(clk_a);
  top.RST_N_rstn_a.bind(rstn_a);
  tb.CLK_clk_a.bind(clk_a);
  tb.RST_N_rstn_a.bind(rstn_a);
  mcd.CLK_clk_a.bind(clk_a);
  mcd.RST_N_rstn_a.bind(rstn_a);

  sc_signal<bool> clk_b;
  sc_signal<bool> rstn_b;
  top.CLK_clk_b.bind(clk_b);
  top.RST_N_rstn_b.bind(rstn_b);
  tb.CLK_clk_b.bind(clk_b);
  tb.RST_N_rstn_b.bind(rstn_b);
  mcd.CLK_clk_b.bind(clk_b);
  mcd.RST_N_rstn_b.bind(rstn_b);

  sc_signal<bool> clk_out;
  top.CLK_clk_out.bind(clk_out);
  tb.CLK_clk_out.bind(clk_out);
  mcd.CLK_clk_out.bind(clk_out);

  // connect the ports for the enq_a method
  sc_signal<bool>       RDY_enq_a;
  sc_signal<bool>       EN_enq_a;
  sc_signal<sc_bv<32> > enq_a_x;
  mcd.RDY_enq_a.bind(RDY_enq_a);
  tb.RDY_enq_a.bind(RDY_enq_a);
  mcd.EN_enq_a.bind(EN_enq_a);
  tb.EN_enq_a.bind(EN_enq_a);
  mcd.enq_a_x.bind(enq_a_x);
  tb.enq_a_x.bind(enq_a_x);

  // connect the ports for the enq_b method
  sc_signal<bool>       RDY_enq_b;
  sc_signal<bool>       EN_enq_b;
  sc_signal<sc_bv<32> > enq_b_x;
  mcd.RDY_enq_b.bind(RDY_enq_b);
  tb.RDY_enq_b.bind(RDY_enq_b);
  mcd.EN_enq_b.bind(EN_enq_b);
  tb.EN_enq_b.bind(EN_enq_b);
  mcd.enq_b_x.bind(enq_b_x);
  tb.enq_b_x.bind(enq_b_x);

  // connect the ports for the deq method
  sc_signal<bool>       RDY_deq;
  sc_signal<bool>       EN_deq;
  mcd.RDY_deq.bind(RDY_deq);
  tb.RDY_deq.bind(RDY_deq);
  mcd.EN_deq.bind(EN_deq);
  tb.EN_deq.bind(EN_deq);

  // connect the ports for the first method
  sc_signal<bool>       RDY_first;
  sc_signal<sc_bv<32> > first;
  mcd.RDY_first.bind(RDY_first);
  tb.RDY_first.bind(RDY_first);
  mcd.first.bind(first);
  tb.first.bind(first);

  // connect the ports for the flip method
  sc_signal<bool>       RDY_flip;
  sc_signal<bool >      EN_flip;
  mcd.RDY_flip.bind(RDY_flip);
  tb.RDY_flip.bind(RDY_flip);
  mcd.EN_flip.bind(EN_flip);
  tb.EN_flip.bind(EN_flip);

/*
  // setup tracing
  sc_trace_file* tf = sc_create_vcd_trace_file("trace");

  TRACE(clk);
  TRACE(rstn);
  TRACE(clk_a);
  TRACE(rstn_a);
  TRACE(clk_b);
  TRACE(rstn_b);
  TRACE(clk_out);

  TRACE(RDY_flip);
  TRACE(EN_flip);

  TRACE(RDY_first);
  TRACE(first);

  TRACE(RDY_deq);
  TRACE(EN_deq);

  TRACE(RDY_enq_a);
  TRACE(EN_enq_a);
  TRACE(enq_a_x);

  TRACE(RDY_enq_b);
  TRACE(EN_enq_b);
  TRACE(enq_b_x);

  bk_enable_VCD_dumping();
*/

  // kick off simulation
  sc_start();

/*
  // shutdown tracing
  sc_close_vcd_trace_file(tf);
  bk_disable_VCD_dumping();
*/

  return 0;
}
