interface Ifc;
   interface Clock clk1;
   interface Clock clk2;
   interface Reset rst;
endinterface

import "BVI"
module mkBVI(Ifc);
   default_clock no_clock;
   default_reset no_reset;

   output_clock clk1 (CLK1);
   output_clock clk2 (CLK2);

   output_reset rst(RSTN) clocked_by(clk1);
endmodule

(* synthesize *)
module sysCheckResetClockFail1 ();
   Ifc i <- mkBVI;

   Reg#(Bool) r1 <- mkReg(True, clocked_by i.clk1, reset_by i.rst);
   // not in the same family, so should be an error
   Reg#(Bool) r2 <- mkReg(True, clocked_by i.clk2, reset_by i.rst);

endmodule
