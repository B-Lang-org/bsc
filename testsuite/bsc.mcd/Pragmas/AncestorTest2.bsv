import Clocks::*;

(* synthesize *)
module sysAncestorTest2();
   
   GatedClockIfc gc1 <- mkGatedClockFromCC(True);
   Clock clk1 = gc1.new_clk;
   
   GatedClockIfc gc2 <- mkGatedClockFromCC(True);
   Clock clk2 = gc2.new_clk;
   
   // this should trigger an error
   Empty sub <- mkSub(clk1, clocked_by clk2);
   
endmodule

(* synthesize *)
(* gate_all_clocks *)
(* clock_ancestors = "default_clock AOF clk_in" *)
module mkSub(Clock clk_in, Empty ifc);
   
   Reg#(UInt#(8)) count1 <- mkReg(0);
   Reg#(UInt#(8)) count2 <- mkReg(0, clocked_by clk_in);
   
   rule r1;
      count1 <= count1 + 1;
      $display("default_clock");
   endrule
   
   rule r2;
      count2 <= count2 + 1;
      $display("clk_in");
   endrule
   
endmodule: mkSub
