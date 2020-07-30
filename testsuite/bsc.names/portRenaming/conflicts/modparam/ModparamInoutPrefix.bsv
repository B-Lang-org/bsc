interface Ifc;
   (* prefix="t" *)
   interface SubIfc s;
endinterface

interface SubIfc;
   interface Inout#(Bool) io;
endinterface

(* synthesize *)
module mkModparamInoutPrefix
          #(parameter int t_io)
          (Inout#(Bool) ii, Ifc i);
   interface SubIfc s;
     interface io = ii;
   endinterface
endmodule

