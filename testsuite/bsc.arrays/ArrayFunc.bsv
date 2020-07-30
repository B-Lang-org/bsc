
(* synthesize *)
module sysArrayFuncDecl ();

  function Bool[] testFunc(Bool x[]);
    
    return x;
  
  endfunction

  Bool tmp[3] = {False, True, False};

  let tmp2 = testFunc(tmp);

  Reg#(Bool) r0 <- mkReg(tmp[0]);
  Reg#(Bool) r1 <- mkReg(tmp2[1]);
  Reg#(Bool) r2 <- mkReg(tmp[2]);

endmodule
