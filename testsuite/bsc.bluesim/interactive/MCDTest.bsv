import Clocks::*;

(* synthesize *)
module mkMCDTest();

   Clock clk2 <- mkAbsoluteClock(2, 7);
   Reset rst2 <- mkInitialReset(2, clocked_by clk2);

   // in default clock domain
   Reg#(Bool)     flip <- mkReg(False);

   // in clk2 domain
   Reg#(UInt#(8)) count <- mkReg(0, clocked_by clk2, reset_by rst2);

   rule flip_default_clock;
     flip <= !flip;
   endrule

   rule incr_clk2;
     count <= count + 1;
   endrule

   rule stop_clk2 (count > 20);
     $finish(0);
   endrule

endmodule
