
(* synthesize *)
module sysArrayDecl_Expr_WrongSize ();

  Bool arr0[4] = {True, False, True, False};
  // wrong size
  Bool arr[3] = arr0;
  
  Reg#(Bool) r0 <- mkReg(arr[0]);
  Reg#(Bool) r1 <- mkReg(arr[1]);
  Reg#(Bool) r2 <- mkReg(arr[2]);

endmodule
