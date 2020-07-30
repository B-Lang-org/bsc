import FIFO::*;

import "BDPI" function Bool myfunc (Bool v);

(* synthesize *)
module sysActionForeignFuncArgs();

   FIFO#(Bool) f1 <- mkFIFO;
   FIFO#(Bool) f2 <- mkFIFO;

   Action a =
      action
         $display("f1 = %d", myfunc(f1.first));
         $display("f2 = %d", myfunc(f2.first));
      endaction;

   rule r;
      $display("cond = %d", impCondOf(a));
   endrule

endmodule
