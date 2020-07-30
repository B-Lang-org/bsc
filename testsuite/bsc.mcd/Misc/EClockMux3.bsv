import Clocks::*;

interface ClockOut;
   interface Clock clk;
endinterface

(* synthesize *)
module sysEClockMux3(Clock c1, Clock c2, ClockOut ifc);
  Reg#(Bool) b <- mkReg(False);

  interface clk = b ? c1 : c2;
endmodule

