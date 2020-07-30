interface Ifc;
   (* prefix="t" *)
   interface SubIfc s;
endinterface

interface SubIfc;
   interface Inout#(Bool) io;
endinterface

(* synthesize *)
module mkModargInoutPrefix (Inout#(Bool) ii, int t_io, Ifc i);
   interface SubIfc s;
     interface io = ii;
   endinterface
endmodule

