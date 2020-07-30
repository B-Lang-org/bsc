(* synthesize *)
module mkCommentOnSubmodMultiBind();
   (* doc = "This is a register" *)
   Reg#(Bool) r1 <- mkRegU, r2 <- mkRegU;
endmodule

