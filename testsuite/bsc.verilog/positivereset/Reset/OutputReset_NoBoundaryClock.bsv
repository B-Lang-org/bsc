import Clocks :: *;

interface Ifc;
   interface Reset rst_out;
endinterface

(* synthesize *)
module sysOutputReset_NoBoundaryClock (Ifc);
   // make a new clock, which is not exported
   Clock c2 <- mkAbsoluteClock (17, 42);

   // make a reset sync'd to this clock
   MakeResetIfc i <- mkReset(2,True,c2);

   // export only the reset
   interface rst_out = i.new_rst;
   
endmodule
