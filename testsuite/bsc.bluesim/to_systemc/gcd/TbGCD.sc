#include <iostream>

#include <systemc.h>

#include "TbGCD.sch"

void mkTbGCD::RL_send_input()
{
  std::cout << "computing gcd(" << count1 << "," << count2 << ")" << std::endl;
  count1 += 3;
  count2 += 2;
}

void mkTbGCD::RL_get_result()
{
  tbresult = gcd_result->read();
  std::cout << "result = " << gcd_result->read().to_uint() << std::endl;
}

void mkTbGCD::RL_done()
{
  sc_stop();
}

void mkTbGCD::posedge_clk()
{
  if (in_reset)
  {
    count1 = 3;
    count2 = 7;
    tbresult = 0;
  }
  else
  {
    if (count2 > 100) RL_done();
    if (gcd_RDY_result->read() != 0) RL_get_result();
    if (gcd_RDY_start->read() != 0) RL_send_input();
  }

  // update combinational outputs
  gcd_start_num1->write(count1);
  gcd_start_num2->write(count2);
}

void mkTbGCD::combinational_paths()
{
  gcd_EN_start->write(gcd_RDY_start->read());
}

void mkTbGCD::handle_reset()
{
  in_reset = !RST_N;
}
