// An argument inout fed through to an interface inout, across a
// module boundary: the leaf's argument pin is live (one net at two
// pins; this line is the regression guard), and the parent -- whose
// interface inout is fed from the leaf's interface inout rather than
// directly from an argument -- reports all of its pins live too.

interface HierIfc;
  interface Inout#(Bit#(32)) io_ifc;
endinterface

(*synthesize*)
module sysArgToIfcLeaf #(Inout#(Bit#(32)) io_arg) (HierIfc);
  interface io_ifc = io_arg;
endmodule

(*synthesize*)
module sysInoutProps_ArgToIfcHier #(Inout#(Bit#(32)) io_arg) (HierIfc);
  HierIfc leaf <- sysArgToIfcLeaf(io_arg);
  interface io_ifc = leaf.io_ifc;
endmodule
