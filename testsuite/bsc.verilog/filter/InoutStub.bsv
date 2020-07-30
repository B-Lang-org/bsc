// Some inout stubs to test Verilog generation

interface InoutSrcStub;
   method Inout#(Int#(5)) foo;
endinterface

import "BVI" InoutStubSrc1 =
module mkInoutStubSrc1(InoutSrcStub);
   ifc_inout foo(FOO);
   default_clock clk();
   default_reset rst();
endmodule

import "BVI" InoutStubSrc2 =
module mkInoutStubSrc2(InoutSrcStub);
   ifc_inout foo(BAR);
   default_clock clk();
   default_reset rst();
endmodule

import "BVI" InoutArgStub =
module mkInoutArgStub#(Inout#(Int#(5)) bar)();
   inout ARG = bar;
   default_clock clk();
   default_reset rst();
endmodule
