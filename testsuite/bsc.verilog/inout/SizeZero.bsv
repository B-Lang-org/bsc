
// Test that we generate Verilog for Inout of size zero
// (and don't create a port for it)

interface Ifc#(numeric type n);
   interface Inout#(Bit#(n)) io_out;
endinterface

(*synthesize*)
module sysSizeZero #(Inout#(Bit#(0)) io_in) (Ifc#(0));
    interface io_out = io_in;
endmodule


