(* synthesize *)
module mkParamExpr_Port#(Bool foo) ();
   Reg#(Bool) r <- mkReg(foo);
endmodule

