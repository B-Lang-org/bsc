
(* synthesize *)
module sysMultiArrayDecl_Expr_WrongSubSize ();

  Bool tmp[4] = {False, True, False, True};
  Bool arr0[3][4] = {tmp, tmp, tmp};

  Bool arr[3][3] = arr0;

  Reg#(Bool) r0 <- mkReg(arr[0][0]);
  Reg#(Bool) r1 <- mkReg(arr[1][1]);
  Reg#(Bool) r2 <- mkReg(arr[2][2]);

endmodule
