interface Ifc;
   interface Inout#(Bool) io;
endinterface

(* synthesize *)
module mkModparamInout #(parameter int io) (Inout#(Bool) ii, Ifc i);
   interface io = ii;
endmodule

