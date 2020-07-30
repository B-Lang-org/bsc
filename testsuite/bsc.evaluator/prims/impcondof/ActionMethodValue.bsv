import FIFO::*;

(* synthesize *)
module sysActionMethodValue();

   FIFO#(Bool) f1 <- mkFIFO;
   FIFO#(Bool) f2 <- mkFIFO;

   Action a =
      action
         let b1 = f1.first;
         let b2 = f2.first;
	 $display(b1, b2);
      endaction;

   rule r;
      $display("cond = %d", impCondOf(a));
   endrule

endmodule
