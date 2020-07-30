import Clocks::*;

interface Ifc;
   interface Reset rst4;
endinterface

(* synthesize *)
module sysMsgTest_MultiReset (Reset rst2, Ifc ifc);

   Clock clk <- exposeCurrentClock;

   Reset rst1 <- exposeCurrentReset;

   MakeResetIfc mr <- mkReset(2,True,clk);
   Reset rst3 = mr.new_rst;

   Reg#(Bool) rg1 <- mkReg(True);
   Reg#(Bool) rg2 <- mkReg(True, reset_by rst2);
   Reg#(Bool) rg3 <- mkReg(True, reset_by rst3);

   let e = action
             rg1 <= !rg1;
             rg2 <= !rg2;
             rg3 <= !rg3;
           endaction;

   if (resetOf(e) == rst1)
     messageM("True");
   else
     messageM("False");

   interface rst4 = rst3;

endmodule

