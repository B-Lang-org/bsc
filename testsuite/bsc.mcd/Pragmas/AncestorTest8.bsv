import Clocks::*;

(* synthesize *)
module sysAncestorTest8();
   
   Clock clk <- exposeCurrentClock();
   
   // this is OK
   Empty sub <- mkSub(clk);   
   
endmodule

(* synthesize *)
(* gate_input_clocks = "clk_in" *)
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
