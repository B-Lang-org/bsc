
(* synthesize *)
module sysArrayDecl_Bind_WrongSize ();

  Reg#(Bool) rg[3] <- mkCReg(4, True);

endmodule
