// Test for a bug when evaluating SLE and SLT on static 0-width values

(* synthesize *)
module sysSignedCompare_Int0 ();
  Int#(0) x = 0;
  Int#(0) y = 0;

  Bool resSLT = x < y;
  Reg#(Bool) rgSLT <- mkReg(resSLT);

  Bool resSLE = x <= y;
  Reg#(Bool) rgSLE <- mkReg(resSLE);

  Bool resSGT = x > y;
  Reg#(Bool) rgSGT <- mkReg(resSGT);

  Bool resSGE = x >= y;
  Reg#(Bool) rgSGE <- mkReg(resSGE);
endmodule
