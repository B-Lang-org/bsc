//Data change waits until the select Bit is visible in the data domain.


import Design::*;
import Clocks::*;

module mkTestbench_same_with_phase_diff(Empty);
   Clock           clk_2();
   mkAbsoluteClock t_clk_2(7, 19, clk_2);

   Clock           clk_1();
   mkAbsoluteClock t_clk_1(2, 17, clk_1);

   Reset              rst_2();
   mkInitialReset#(2) t_rst_2(rst_2, clocked_by clk_2);

   Reset              rst_1();
   mkInitialReset#(2) t_rst_1(rst_1, clocked_by clk_1);

   Design_IFC                    dut();
   mkDesign#(clk_1, rst_1) t_dut(dut, clocked_by clk_2, reset_by rst_2);

   Reg#(Bit#(16))    in_data_n();
   mkReg#(0)         t_in_data_n(in_data_n, clocked_by clk_2, reset_by rst_2);

   Reg#(Bit#(1))    sel_n();
   mkReg#(0)        t_sel_n(sel_n, clocked_by clk_1, reset_by rst_1);

   Reg#(Bit#(1))    bit_sel();
   mkReg#(0)        t_bit_sel(bit_sel, clocked_by clk_2, reset_by rst_2);

   Reg#(Bool)     start_sig <- mkReg(True, clocked_by clk_2, reset_by rst_2);

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
	$display ($time,"\tOut Data =%h", dut.out_data);
   endrule

   rule fast_domain;
	sel_n <= ~sel_n;
	dut.inp_clk2(sel_n);
   endrule

   rule fin(dut.out_data == 78);
	$finish(2'b00);
   endrule
endmodule
