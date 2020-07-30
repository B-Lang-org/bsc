
(* synthesize *)
module sysArrayDecl_Bind_ExtraVar_ArrayType ();

  Array#(Reg#(Bool)) rgA <- mkCReg(3, True), rgB <- mkCReg(2, False);

endmodule
