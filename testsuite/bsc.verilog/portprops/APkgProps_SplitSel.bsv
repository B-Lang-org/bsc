// Test the APackage-based VIOProps deduction (getIOPropsA) for the
// selected result ports of a split method (ATupleSel around the call):
// each element of the child's split-output method is wired to its own
// parent output, and each takes the child's declared property for THAT
// port (ATupleSel indices are 1-based):
//  - outx is the registered element (port 1), so it is "reg"
//  - outy is the constant element (port 2), so it is "const"
// A regression test against selecting the wrong port's properties.

import SplitPorts::*;

typedef struct { Bit#(8) x; Bit#(8) y; } FooSS deriving (Bits);

interface APkgProps_SplitSel_Sub;
   method ShallowSplit#(FooSS) get();
endinterface

(* synthesize *)
module mkAPkgProps_SplitSel_Sub (APkgProps_SplitSel_Sub);
   Reg#(Bit#(8)) r <- mkRegU;
   method get = ShallowSplit(FooSS { x: r, y: 8'hAB });
endmodule

interface APkgProps_SplitSel;
   method Bit#(8) outx();
   method Bit#(8) outy();
endinterface

(* synthesize *)
module sysAPkgProps_SplitSel (APkgProps_SplitSel);
   APkgProps_SplitSel_Sub s <- mkAPkgProps_SplitSel_Sub;
   method outx = unShallowSplit(s.get).x;
   method outy = unShallowSplit(s.get).y;
endmodule
