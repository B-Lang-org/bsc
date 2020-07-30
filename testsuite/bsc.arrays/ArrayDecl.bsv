
(* synthesize *)
module sysArrayDecl ();

  Bool arr[3] = {True, False, True};
  
  Reg#(Bool) r0 <- mkReg(arr[0]);
  Reg#(Bool) r1 <- mkReg(arr[1]);
  Reg#(Bool) r2 <- mkReg(arr[2]);

endmodule
