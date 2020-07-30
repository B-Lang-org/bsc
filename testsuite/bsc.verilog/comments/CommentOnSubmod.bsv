import FIFO::*;

(* synthesize *)
module mkCommentOnSubmod();

   // tests also: \n in string, multiple doc in same list, multiple lists
   (* doc = "This is a FIFO", doc = "Foo\nBar" *)
   (* doc = "Baz" *)
   FIFO#(Bool) f1();
   mkFIFO the_f1(f1);

endmodule

