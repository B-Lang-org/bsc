
interface Ifc;
  interface Inout#(Bit#(32)) io_ifc;
endinterface

import "BVI" 
module mkInoutProps_UnusedArgBVI_Sub #(Inout#(Bit#(32)) io_arg) (Ifc);
    inout IO_ARG = io_arg;
    ifc_inout io_ifc(IO_IFC);
    path (IO_ARG, IO_IFC);
endmodule

(*synthesize*)
module sysInoutProps_UnusedArgBVI #(Inout#(Bit#(32)) io_arg) ();
   let m <- mkInoutProps_UnusedArgBVI_Sub(io_arg);
endmodule

