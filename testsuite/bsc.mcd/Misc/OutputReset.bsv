import Clocks::*;

interface OutputReset;
   interface Clock c;
   interface Reset r;
endinterface 

(* synthesize *)
module sysOutputReset(Clock c1, Clock c2, OutputReset ifc);
  
  SelectClkIfc s <- mkClockSelect(2, c1, c2);

  method c = s.clock_out;
  method r = s.reset_out;

endmodule
