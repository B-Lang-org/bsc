
import SyncRegToSlow::*;
import Clocks::*;

module mkTestbench_fast_to_slow(Empty);
   Clock           clk_fast();
   mkAbsoluteClock t_clk_fast(7, 67, clk_fast);

   Reset              rst_fast();
   mkInitialReset#(10) t_rst_fast(rst_fast, clocked_by clk_fast);

   ClockDividerIfc    div();
   mkClockDivider#(4) t_div(div, clocked_by clk_fast, reset_by rst_fast);

   Reset              rst_slow();
   mkInitialReset#(2) t_rst_slow(rst_slow, clocked_by div.slowClock);

   SyncRegSlow_IFC            dut();
   mkSyncRegSlow#(clk_fast)   t_dut(dut, clocked_by div.slowClock, reset_by rst_slow);

   Reg#(Bit#(12))   in_cnt();
   mkReg#(0)        t_in_cnt(in_cnt, clocked_by clk_fast, reset_by rst_fast);

   rule inp;
	in_cnt <= {in_cnt[11:6] + 2, in_cnt[5:0] + 1};
	dut.start(in_cnt[5:0], in_cnt[11:6]);
   endrule

   Reg#(Bit#(7))    out_reg();
   mkReg#(0)        t_out_reg(out_reg, clocked_by dut.clk_slow, reset_by dut.rst_slow);

   function ActionValue#(Bit#(64)) adjusted_time(Bit#(64) lag);
   actionvalue
     let t <- $time;
     if (genVerilog)
       return (t + lag);
     else
       return t;
   endactionvalue
   endfunction

   rule check;
	out_reg <= dut.out_data;
	if (out_reg != dut.out_data)
	  $display (adjusted_time(134), "\tOut Data =%d", dut.out_data);
   endrule

   rule finish_rl(dut.out_data == 93);
	$finish(2'b00);
   endrule
endmodule
