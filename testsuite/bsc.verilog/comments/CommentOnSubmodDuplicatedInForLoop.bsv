import FIFO::*;

(* synthesize *)
module mkCommentOnSubmodDuplicatedInForLoop();

   for (Integer i=0; i<4; i=i+1)
      (* doc = "This is also a FIFO" *)
      FIFO#(Bool) f <- mkFIFO;

endmodule
