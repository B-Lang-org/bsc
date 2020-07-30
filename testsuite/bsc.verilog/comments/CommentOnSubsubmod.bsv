import FIFO::*;

(* synthesize *)
module mkCommentOnSubsubmod();
   FIFO#(Bool) s();
   mkSub the_s(s);
endmodule

module mkSub (FIFO#(Bool));
   (* doc = "This is a FIFO" *)
   FIFO#(Bool) f1();
   mkFIFO the_f1(f1);
   return f1;
endmodule

