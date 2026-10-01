// An argument inout exposed at an inout inside a subinterface: the
// interface-inout definition is found through the hierarchical
// interface, and the argument pin is live.

interface Inner;
  interface Inout#(Bit#(32)) io_ifc;
endinterface

interface SubIfc;
  interface Inner inner;
endinterface

(*synthesize*)
module sysInoutProps_ArgToSubIfc #(Inout#(Bit#(32)) io_arg) (SubIfc);
  interface Inner inner;
    interface io_ifc = io_arg;
  endinterface
endmodule
