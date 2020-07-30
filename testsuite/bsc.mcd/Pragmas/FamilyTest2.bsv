import Clocks::*;

(* synthesize *)
module sysFamilyTest2();
   
   Clock clk <- exposeCurrentClock();
   
   GatedClockIfc gc <- mkGatedClockFromCC(True);
   Clock clk2 = gc.new_clk;
   
   Empty mid <- mkMid(clk, clocked_by clk2);
   
endmodule

(* synthesize *)
(* gate_input_clocks = "default_clock" *)
(* clock_family = "default_clock, xclk" *)
module mkMid(Clock xclk, Empty ifc);
   
   GatedClockIfc gc <- mkGatedClockFromCC(True);
   Clock clk2 = gc.new_clk;
   
   // this is OK
   Empty sub <- mkSub(clk2, clocked_by xclk);   
   
endmodule

(* synthesize *)
(* gate_input_clocks = "clk_in" *)
(* clock_family = "default_clock, clk_in" *)
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
