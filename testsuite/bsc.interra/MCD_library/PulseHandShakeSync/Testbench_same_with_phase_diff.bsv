import Design::*;
import Clocks::*;

module mkTestbench_same_with_phase_diff(Empty);
   // Destination clock
   Clock clk_1 <- mkAbsoluteClock(7, 19);
   Reset rst_1 <- mkInitialReset(2, clocked_by clk_1);

   // Source clock
   Clock clk_2 <- mkAbsoluteClock(2, 17);
   Reset rst_2 <- mkInitialReset(2, clocked_by clk_2);

   Design_IFC dut <- mkDesign(clk_2, rst_2,
                              clocked_by clk_1, reset_by rst_1);

   Reg#(UInt#(16)) ticks <- mkReg(0);
   Reg#(UInt#(16)) syncSent <- mkSyncReg(0, clk_2, rst_2, clk_1);

   // executes in current clock
   rule cycle_count;
       ticks <= ticks + 1;
   endrule

   // executes in current clock
   rule abort (ticks > 1000);
     $display("Test was aborted at %t", $time);
     $finish(0);
   endrule

   // executes in source clock (clk_2)
   rule stop_sending (dut.sent > 15);
     dut.stop();
   endrule

   // executes in source clock (clk_2)
   rule monitor_sent;
     syncSent <= dut.sent;
   endrule

   // executes in destination clock (clk_1)
   rule done (dut.recvd > 15 && dut.recvd == syncSent);
     $display("Test completed normally at %t", $time);
     $finish(0);
   endrule

endmodule
