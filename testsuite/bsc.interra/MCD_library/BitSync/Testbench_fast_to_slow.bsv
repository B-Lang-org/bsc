//Data change waits until the select Bit is visible in the slow domain.


import Design::*;
import Clocks::*;

module mkTestbench_fast_to_slow(Empty);
   Clock           clk_slow();
   mkAbsoluteClock t_clk_slow(7, 67, clk_slow);

   Clock           clk_fast();
   mkAbsoluteClock t_clk_fast(2, 17, clk_fast);

   Reset              rst_slow();
   mkInitialReset#(2) t_rst_slow(rst_slow, clocked_by clk_slow);

   Reset              rst_fast();
   mkInitialReset#(2) t_rst_fast(rst_fast, clocked_by clk_fast);

   Design_IFC                    dut();
   mkDesign#(clk_fast, rst_fast) t_dut(dut, clocked_by clk_slow, reset_by rst_slow);

   Reg#(Bit#(16))    in_data_n();
   mkReg#(0)         t_in_data_n(in_data_n, clocked_by clk_slow, reset_by rst_slow);

   Reg#(Bit#(1))    sel_n();
   mkReg#(0)        t_sel_n(sel_n, clocked_by clk_fast, reset_by rst_fast);

   Reg#(Bit#(1))    bit_sel();
   mkReg#(0)        t_bit_sel(bit_sel, clocked_by clk_slow, reset_by rst_slow);

   Reg#(Bool)     start_sig <- mkReg(True, clocked_by clk_slow, reset_by rst_slow);

   rule slow_domain(start_sig == True);
	if (bit_sel == 0)
	begin
	  bit_sel <= 1;
	  in_data_n[7:0] <= in_data_n[7:0] + 1;
	end
	else begin
	  in_data_n[15:8] <= in_data_n[15:8] + 1;
	  bit_sel <= 0;
	end
	dut.inp_clk1(in_data_n);
	$display ($time, "\tOut Data =%h", dut.out_data);
   endrule

   rule fast_domain;
	sel_n <= ~sel_n;
	dut.inp_clk2(sel_n);
   endrule

   rule fin(dut.out_data == 78);
	$finish(2'b00);
   endrule
endmodule
