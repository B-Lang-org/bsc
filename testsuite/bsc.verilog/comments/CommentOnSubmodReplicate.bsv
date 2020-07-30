import Vector::*;

(* synthesize *)
module mkCommentOnSubmodReplicate();

   (* doc = "This is a register" *)
   Vector#(4, Reg#(Bit#(4))) repReg <- replicateM(mkReg(0));

endmodule

