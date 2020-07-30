
(* synthesize *)
module mkCommentOnSubmodReg();

   (* doc = "This is a register" *)
   Reg#(Bool) r();
   mkRegU the_r(r);

endmodule

