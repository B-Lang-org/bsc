interface Ifc;
   interface Inout#(Bool) io;
endinterface

(* synthesize *)
module mkModargInoutRename ( (* port="io" *)Inout#(Bool) ii, Ifc i);
   interface io = ii;
endmodule

