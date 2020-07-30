
import Design::*;
import Clocks::*;

module mkTestbench_fast_to_slow(Empty);
   Clock clk_slow <- mkAbsoluteClock(7, 67);
   Reset rst_slow <- mkInitialReset(2, clocked_by clk_slow);

   Clock clk_fast <- mkAbsoluteClock(2, 17);
   Reset rst_fast <- mkInitialReset(2, clocked_by clk_fast);

   Design_IFC dut <- mkDesign(clk_fast, rst_fast,
                              clocked_by clk_slow, reset_by rst_slow);

   Reg#(UInt#(16)) ticks <- mkReg(0);
   Reg#(UInt#(16)) syncSent <- mkSyncReg(0, clk_fast, rst_fast, clk_slow);

   // executes in current clock
   rule cycle_count;
       ticks <= ticks + 1;
   endrule

   // executes in current clock
   rule abort (ticks > 1000);
     $display("Test was aborted at %t", $time);
     $finish(0);
   endrule

   // executes in source clock (clk_fast)
   rule stop_sending (dut.sent > 15);
     dut.stop();
   endrule

   // executes in source clock (clk_fast)
   rule monitor_sent;
     syncSent <= dut.sent;
   endrule

   // executes in destination clock (clk_slow)
   rule done (dut.recvd > 15 && dut.recvd == syncSent);
     $display("Test completed normally at %t", $time);
     $finish(0);
   endrule

endmodule
