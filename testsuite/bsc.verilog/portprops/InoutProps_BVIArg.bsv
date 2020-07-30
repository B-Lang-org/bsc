
import "BVI" 
module mkInoutProps_BVIArg_Sub #(Inout#(Bit#(32)) io_arg) ();
    inout IO = io_arg;
endmodule

(*synthesize*)
module sysInoutProps_BVIArg #(Inout#(Bit#(32)) io_arg) ();
  let s <- mkInoutProps_BVIArg_Sub(io_arg);
endmodule

