import Clocks::*;

interface OutputReset2;
   interface Clock c;
   interface Reset r;
   method Bit#(32) test();
endinterface 

(* synthesize *)
module sysOutputReset2(Clock c1, Clock c2, OutputReset2 ifc);
 
  SelectClkIfc s <- mkClockSelect(2, c1, c2);

  Reg#(Bit#(32)) data();
  mkReg#(0) i_data(data, clocked_by(s.clock_out), reset_by(s.reset_out));

  method c = s.clock_out;
  method r = s.reset_out;
  method test = data;
  
endmodule
