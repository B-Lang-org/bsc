
(* synthesize *)
module sysArrayDecl_Bind_ExtraVar_WrongSize ();

  Reg#(Bool) rgA[3] <- mkCReg(3, True), rgB[3] <- mkCReg(2, False);

endmodule
