
(* synthesize *)
module sysArrayDecl_WrongSize ();

  Bool arr[3] = {True, False, True, False};
  
  Reg#(Bool) r0 <- mkReg(arr[0]);
  Reg#(Bool) r1 <- mkReg(arr[1]);
  Reg#(Bool) r2 <- mkReg(arr[2]);

endmodule
