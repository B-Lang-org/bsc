import Clocks::*;

interface ResetOut;
   interface Reset rst;
endinterface

(* synthesize *)
module sysEResetMux3(Reset r1, Reset r2, ResetOut ifc);
  Reg#(Bool) b <- mkReg(False);

  interface rst = b ? r1 : r2;
endmodule

