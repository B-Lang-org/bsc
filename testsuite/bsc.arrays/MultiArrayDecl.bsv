
(* synthesize *)
module sysMultiArrayDecl ();

  Bool tmp[3] = {False, True, False};

  Bool arr[3][3] = {{False, False, True}, tmp, {True, False, False}};
  
  Reg#(Bool) r0 <- mkReg(arr[0][0]);
  Reg#(Bool) r1 <- mkReg(arr[1][1]);
  Reg#(Bool) r2 <- mkReg(arr[2][2]);

endmodule
