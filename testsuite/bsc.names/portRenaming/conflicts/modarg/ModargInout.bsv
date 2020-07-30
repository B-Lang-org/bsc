interface Ifc;
   interface Inout#(Bool) io;
endinterface

(* synthesize *)
module mkModargInout (Inout#(Bool) ii, int io, Ifc i);
   interface io = ii;
endmodule

