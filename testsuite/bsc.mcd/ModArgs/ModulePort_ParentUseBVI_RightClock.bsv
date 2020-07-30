import Clocks::*;

(* synthesize *)
module sysModulePort_ParentUseBVI_RightClock ();

   Clock clk2 <- mkAbsoluteClock(7,15);
   
   Reg#(Bit#(32)) x <- mkRegU(clocked_by clk2);

   Empty i <- mkSub (x, clk2);
endmodule

import "BVI"
module mkSub #(Bit#(32) x)
              (Clock c2, Empty i);
   input_clock clk2() = c2;
   port X clocked_by(clk2) = x;
endmodule

