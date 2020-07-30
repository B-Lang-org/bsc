
(* synthesize *)
module sysArrayDecl_Bind_ExtraVar ();

  Reg#(Bool) rgA[3] <- mkCReg(3, True), rgB[2] <- mkCReg(2, False);

endmodule
