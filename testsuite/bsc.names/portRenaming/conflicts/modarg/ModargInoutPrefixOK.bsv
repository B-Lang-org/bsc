interface Ifc;
   (* prefix="t" *)
   interface SubIfc s;
endinterface

interface SubIfc;
   interface Inout#(Bool) io;
endinterface

(* synthesize *)
module mkModargInoutPrefixOK (Inout#(Bool) ii, int s_io, Ifc i);
   interface SubIfc s;
     interface io = ii;
   endinterface
endmodule

