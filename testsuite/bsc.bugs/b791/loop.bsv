import Vector::*;

`define N 10

(* synthesize *)
module loop();
  Vector#(`N, Reg#(int)) regs;
  Integer i;
  for (i=0; i < `N; i = i + 1) regs[i] <- mkReg(0);
  rule them_all;
  endrule
endmodule: loop
