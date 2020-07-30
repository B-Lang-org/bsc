
// Test that the BVI ifc Inout and the BVI modarg Inout get assigned
// different clocks and that the instantiation of the second one fails

(*synthesize*)
module sysCheckClocks_BVIIfcToBVIArg_DiffClock (Clock c2, Empty e);
   Ifc i1 <- mkSource;
   Empty i2 <- mkSink(i1.io, clocked_by c2);
endmodule

interface Ifc;
   interface Inout#(Bool) io;
endinterface

import "BVI" Source =
module mkSource(Ifc);
   default_clock clk();
   default_reset no_reset;
   ifc_inout io(X1);
endmodule

import "BVI" Sink =
module mkSink#(Inout#(Bool) io)(Empty);
   default_clock clk();
   default_reset no_reset;
   inout X2 = io;
endmodule
