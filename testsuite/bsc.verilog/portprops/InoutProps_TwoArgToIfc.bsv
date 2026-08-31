// Two independent argument inouts, each fed through to its own
// interface inout: each argument pin is live via its own
// interface-inout definition (exercises multiple io_ds entries).

interface TwoIfc;
  interface Inout#(Bit#(8))  io_a;
  interface Inout#(Bit#(16)) io_b;
endinterface

(*synthesize*)
module sysInoutProps_TwoArgToIfc #(Inout#(Bit#(8))  arg_a,
                                   Inout#(Bit#(16)) arg_b) (TwoIfc);
  interface io_a = arg_a;
  interface io_b = arg_b;
endmodule
