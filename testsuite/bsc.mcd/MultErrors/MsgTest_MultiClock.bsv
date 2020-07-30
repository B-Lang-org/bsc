import Clocks::*;

interface Ifc;
   interface Clock clk4;
endinterface

(* synthesize *)
module sysMsgTest_MultiClock (Clock clk2, Ifc ifc);

   Clock clk3 <- mkAbsoluteClock(15, 20);

   Reg#(Bool) rg1 <- mkRegU();
   Reg#(Bool) rg2 <- mkRegU(clocked_by clk2);
   Reg#(Bool) rg3 <- mkRegU(clocked_by clk3);

   rule r;
     rg1 <= !rg1;
     rg2 <= !rg2;
     rg3 <= !rg3;
   endrule

   interface clk4 = clk3;

endmodule

