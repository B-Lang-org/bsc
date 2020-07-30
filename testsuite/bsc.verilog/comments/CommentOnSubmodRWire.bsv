(* synthesize *)
module mkCommentOnSubmodRWire();

   (* doc = "This is an rwire" *)
   RWire#(Bool) rw();
   mkRWire the_rw(rw);

endmodule

