//Write address is incremented by 2 on every write cycle and 
//data input is incremented by 1 on every write cycle
//Read is Validated by fail signal for test to pass

import Design::*;
import Clocks::*;

module mkTestbench_same_with_phase_diff(Empty);
   Clock           clk_wr();
   mkAbsoluteClock t_clk_wr(15, 17, clk_wr);

   Clock           clk_rd();
   mkAbsoluteClock t_clk_rd(2, 19, clk_rd);

   Reset              rst_wr();
   mkInitialReset#(2) t_rst_wr(rst_wr, clocked_by clk_wr);

   Reset              rst_rd();
   mkInitialReset#(2) t_rst_rd(rst_rd, clocked_by clk_rd);

   Design_IFC                dut();
   mkDesign#(clk_wr, rst_wr) t_dut(dut, clocked_by clk_rd, reset_by rst_rd);

   Reg#(Bit#(16))   wadd_cnt();
   mkReg#(0)        t_wadd_cnt(wadd_cnt, clocked_by clk_wr, reset_by rst_wr);

   Reg#(Bit#(8))    data();
   mkReg#(0)        t_data(data, clocked_by clk_wr, reset_by rst_wr);

   Reg#(Bit#(16))   radd_cnt();
   mkReg#(0)        t_radd_cnt(radd_cnt, clocked_by clk_rd, reset_by rst_rd);

   SyncBitIfc#(Bit#(1))     sync();
   mkSyncBit      t_sync(clk_wr, rst_wr, clk_rd, sync);

   rule write(wadd_cnt < 20);
	wadd_cnt <= wadd_cnt + 2;
	data <= data + 1;
	dut.write(wadd_cnt, data);
	$display($time, "\tWrite data %d at location %d", data, wadd_cnt + 2);
	if (wadd_cnt == 18)
	   sync.send(1'b1);
   endrule

   Reg#(Bit#(8))    check_data();
   mkReg#(0)        t_check_data(check_data, clocked_by clk_rd, reset_by rst_rd);

   Reg#(Bit#(1))    fail();
   mkReg#(0)        t_fail(fail, clocked_by clk_rd, reset_by rst_rd);

   rule read(sync.read == 1);
	radd_cnt <= radd_cnt + 2;
	if (radd_cnt > 0)
	begin
	  check_data <= check_data + 1;
	  $display($time, "\tData at location %d = %d", dut.dout, radd_cnt);
	end
	if (dut.dout != check_data)
	  fail <= 1;
	dut.read(radd_cnt);
	if (radd_cnt == 20)
	begin
	  if (fail == 1)
	    $display("\tSimulation Fails");
	  else
	    $display("\tSimulation Passes");
	  $finish(0);
	end
   endrule
endmodule
