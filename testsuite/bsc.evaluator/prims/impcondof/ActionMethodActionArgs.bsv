import FIFO::*;

(* synthesize *)
module sysActionMethodActionArgs();

   FIFO#(Bool) f1 <- mkFIFO;
   FIFO#(Bool) f2 <- mkFIFO;

   Reg#(Bool) rg1 <- mkRegU;
   Reg#(Bool) rg2 <- mkRegU;

   Action a =
      action
         rg1 <= f1.first;
         rg2 <= f2.first;
      endaction;

   rule r;
      $display("cond = %d", impCondOf(a));
   endrule

endmodule
