#include <iostream>

#include <systemc.h>

#include "TbGetPut.sch"

void mkTbGetPut::RL_send_input()
{	
  std::cout << "sending: " << count << std::endl;
  ++count;
  count_sig = count;
}

void mkTbGetPut::RL_get_output()
{
  sc_uint<8> x = dut_out_get->read();
  std::cout << "received: " << x.to_uint() << std::endl;
}

void mkTbGetPut::RL_done()
{
  sc_stop();
}

void mkTbGetPut::posedge_clk()
{
  if (in_reset)
  {
    count = 0;
    count_sig = count;
  }
  else
  {
    if ((count > 100) && (dut_RDY_out_get->read() == 0)) RL_done();
    if (dut_RDY_out_get->read() != 0) RL_get_output();
    if ((count <= 100) && (dut_RDY_in_put->read() != 0)) RL_send_input();
  }

  dut_in_put->write(count);
}

void mkTbGetPut::combinational_paths()
{
  dut_EN_in_put->write((count <= 100) && dut_RDY_in_put->read());
}

void mkTbGetPut::handle_reset()
{
  in_reset = !RST_N;
}
