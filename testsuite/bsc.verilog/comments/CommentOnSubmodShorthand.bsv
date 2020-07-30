import FIFO::*;

(* synthesize *)
module mkCommentOnSubmodShorthand();

   (* doc = "This is also a FIFO" *)
   FIFO#(Bool) f2 <- mkFIFO;

endmodule

