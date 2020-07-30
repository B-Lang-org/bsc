import Clocks::*;

interface Ifc;
   interface Clock clk4;
endinterface

(* synthesize *)
module sysMsgTest_ClockOfMultiClock (Clock clk2, Ifc ifc);

   Clock clk1 <- exposeCurrentClock;

   Clock clk3 <- mkAbsoluteClock(15, 20);

   Reg#(Bool) rg1 <- mkRegU();
   Reg#(Bool) rg2 <- mkRegU(clocked_by clk2);
   Reg#(Bool) rg3 <- mkRegU(clocked_by clk3);

   let e = action
             rg1 <= !rg1;
             rg2 <= !rg2;
             rg3 <= !rg3;
           endaction;

   if (clockOf(e) == clk1)
     messageM("True");
   else
     messageM("False");

   interface clk4 = clk3;

endmodule

