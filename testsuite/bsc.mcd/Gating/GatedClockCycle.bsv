import Clocks::*;

// Clock period
Integer p1 = 10;

// the initial value of the register will be AA
Bit#(8) init_val = 8'hAA;

(* synthesize *)
module sysGatedClockCycle ();
   GatedClockIfc g <- mkGatedClockFromCC(False);
   Clock clk2 = g.new_clk;

   Reg#(Bool) rg1 <- mkRegU (clocked_by clk2);
   Reg#(Bit#(8)) rg2 <- mkRegU;

   rule r1;
      rg1 <= !rg1;
      g.setGateCond(rg1);
      $display("rg1", rg1);
   endrule
   
   rule r2;
      rg2 <= rg2 + 1;
      $display("rg2 = ", rg2);
   endrule

   rule stop (rg2 > (init_val + 17));
      $finish(0);
   endrule

endmodule

