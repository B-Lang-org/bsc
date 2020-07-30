import FIFO::*;

(* synthesize *)
module sysDuplicateCommentOnSubmod();

   // test that duplicate strings are not removed
   (* doc = "This appears twice" *)
   (* doc = "This is unique" *)
   (* doc = "This appears twice" *)
   (* doc = "This is also unique" *)
   FIFO#(Bool) f1 <- mkFIFO;

endmodule

