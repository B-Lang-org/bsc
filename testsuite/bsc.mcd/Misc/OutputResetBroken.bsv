import Clocks::*;

interface OutputResetBroken;
   interface Reset r;
endinterface 

(* synthesize *)
module sysOutputResetBroken(Clock c1, Clock c2, OutputResetBroken ifc);
  
  SelectClkIfc s <- mkClockSelect(2, c1, c2);

  method r = s.reset_out;

endmodule
