import FIFO::*;

(* synthesize *)
module sysActionForeignTaskArgs();

   FIFO#(Bool) f1 <- mkFIFO;
   FIFO#(Bool) f2 <- mkFIFO;

   Action a =
      action
         $display("f1 = %d", f1.first);
         $display("f2 = %d", f2.first);
      endaction;

   rule r;
      $display("cond = %d", impCondOf(a));
   endrule

endmodule
