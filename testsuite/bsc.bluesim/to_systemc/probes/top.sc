
#include <systemc.h>

#include "mkDut_systemc.h"
#include "bluesim_probes.h"

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

SC_MODULE(mkTb)
{
  // clock input port
  sc_in<bool> CLK;

  // constructor
  SC_HAS_PROCESS(mkTb);
  mkTb(sc_module_name instname, mkDut* dut)
    : sc_module(instname), CLK("CLK"), dut_ptr(dut), count(0),
      probe_idx(NULL), probe_fifo(NULL), probe_rf(NULL)
  {
    SC_THREAD(show_probes);
  }

  virtual void start_of_simulation()
  {
    // get probe addresses
    probe_idx  = &(dut_ptr->_model_inst->INST_idx.getProbe());
    probe_fifo = &(dut_ptr->_model_inst->INST_fifo.getProbe());
    probe_rf   = &(dut_ptr->_model_inst->INST_rf.getProbe());

    // configure the register file contents using the probe_rf
    probe_rf->write( 0,  2);
    probe_rf->write( 1,  3);
    probe_rf->write( 2,  5);
    probe_rf->write( 3,  7);
    probe_rf->write( 4, 11);
    probe_rf->write( 5, 13);
    probe_rf->write( 6, 17);
    probe_rf->write( 7, 19);
    probe_rf->write( 8, 23);
    probe_rf->write( 9, 29);
    probe_rf->write(10, 31);
    probe_rf->write(11, 37);
    probe_rf->write(12, 41);
    probe_rf->write(13, 43);
    probe_rf->write(14, 47);
    probe_rf->write(15, 53);
  }

  void show_probes()
  {
    while (count < 100)
    {
      wait(CLK->negedge_event());
      ++count;
      std::cout << "idx = " << ((int) probe_idx->read()) << std::endl;
      if (!probe_fifo->is_valid_address(probe_fifo->low_address()))
      {
        std::cout << "FIFO is empty." << std::endl;
      }
      else
      {
        std::cout << "FIFO contains:" << std::endl;
        for (unsigned int n = probe_fifo->low_address();
	     n <= probe_fifo->high_address();
             ++n)
        {
	  std::cout << "  " << n << ": " << probe_fifo->read(n) << std::endl;
        }
      }
    }
    sc_stop();
  }

  private:
    unsigned int count;
    mkDut* dut_ptr;
    BluespecProbe<unsigned char>* probe_idx;
    BluespecProbe<unsigned int>* probe_fifo;
    BluespecProbe<unsigned int, unsigned char>* probe_rf;
};

int sc_main(int argc, char* argv[])
{
  // Make the clock and reset generator
  mkMain top("top");

  // Make the DUT
  mkDut dut("dut");

  // Make the testbench
  mkTb tb("tb", &dut);

  // connect the clock and reset to the testbench and DUT
  sc_signal<bool> clk;
  sc_signal<bool> rstn;
  top.CLK.bind(clk);
  top.RST_N.bind(rstn);
  tb.CLK.bind(clk);
  dut.CLK.bind(clk);
  dut.RST_N.bind(rstn);

  sc_start();

  return 0;
}
