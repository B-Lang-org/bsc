import FIFO::*;

(* synthesize *)
module mkCommentOnSubmodShorthandSeparate();

   FIFO#(Bool) f1;

   (* doc = "This is a FIFO" *)
   f1 <- mkFIFO;

endmodule

