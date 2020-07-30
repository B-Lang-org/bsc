
// Test that using mkConnection on two BVI ifc Inouts on different clocks
// triggers an error

import Connectable::*;

(*synthesize*)
module sysCheckClocks_ConnectBVIIfcToBVIIfc_DiffClock (Clock c2, Empty e);
   Ifc i1 <- mkInout;
   Ifc i2 <- mkInout(clocked_by c2);

   mkConnection(i1.io, i2.io);
endmodule

interface Ifc;
   interface Inout#(Bool) io;
endinterface

import "BVI" Source =
module mkInout(Ifc);
   default_clock clk();
   default_reset no_reset;
   ifc_inout io(X1);
endmodule

