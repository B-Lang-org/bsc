
(* synthesize *)
module sysMultiArrayDecl_Expr_WrongSubSize ();

  Bool tmp[3] = {False, True, False};
  Bool arr0[4][3] = {tmp, tmp, tmp, tmp};

  Bool arr[3][3] = arr0;

  Reg#(Bool) r0 <- mkReg(arr[0][0]);
  Reg#(Bool) r1 <- mkReg(arr[1][1]);
  Reg#(Bool) r2 <- mkReg(arr[2][2]);

endmodule
