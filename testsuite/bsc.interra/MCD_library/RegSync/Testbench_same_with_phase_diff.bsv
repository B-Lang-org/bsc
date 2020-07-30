
import Design::*;
import Clocks::*;

module mkTestbench_same_with_phase_diff(Empty);
   Clock           clk_1();
   mkAbsoluteClock t_clk_1(7, 19, clk_1);

   Clock           clk_2();
   mkAbsoluteClock t_clk_2(2, 17, clk_2);

   Reset              rst_2();
   mkInitialReset#(2) t_rst_2(rst_2, clocked_by clk_2);

   Reset              rst_1();
   mkInitialReset#(2) t_rst_1(rst_1, clocked_by clk_1);

   Design_IFC                    dut();
   mkDesign#(clk_2, rst_2) t_dut(dut, clocked_by clk_1, reset_by rst_1);

   Reg#(Bit#(12))   in_cnt();
   mkReg#(0)        t_in_cnt(in_cnt, clocked_by clk_1, reset_by rst_1);

   rule inp;
	in_cnt <= {in_cnt[11:6] + 2, in_cnt[5:0] + 1};
	dut.start(in_cnt[5:0], in_cnt[11:6]);
   endrule

   Reg#(Bit#(7))    out_reg();
   mkReg#(0)        t_out_reg(out_reg, clocked_by clk_2, reset_by rst_2);

   rule check;
	out_reg <= dut.out_data;
	if (out_reg != dut.out_data)
	  $display ($time, "\tOut Data =%d", dut.out_data);
   endrule

   rule finish_rl(dut.out_data == 93);
	$finish(2'b00);
   endrule
endmodule
