
interface Ifc;
  interface Inout#(Bit#(32)) io_ifc;
endinterface

(*synthesize*)
module sysInoutProps_ArgToIfc #(Inout#(Bit#(32)) io_arg) (Ifc);
  interface io_ifc = io_arg;
endmodule

