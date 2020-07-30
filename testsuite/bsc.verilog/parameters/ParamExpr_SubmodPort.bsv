(* synthesize *)
module mkParamExpr_SubmodPort ();
   Reg#(Bool) s <- mkRegU;
   Reg#(Bool) r <- mkReg(s);
endmodule

