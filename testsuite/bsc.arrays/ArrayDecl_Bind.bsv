
(* synthesize *)
module sysArrayDecl_Bind ();

  Reg#(Bool) rg[3] <- mkCReg(3, True);

endmodule
