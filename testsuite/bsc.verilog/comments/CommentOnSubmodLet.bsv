import FIFO::*;

(* synthesize *)
module mkCommentOnSubmodLet();

   Bool v = True;
   
   (* doc = "This is a FIFO" *)
   let f1();
   mkFIFO the_f1(f1);

   (* doc = "This is a FIFO too" *)
   let f2 <- mkFIFO;

   rule set_types;
      f1.enq(v);
      f2.enq(v);
   endrule

endmodule

