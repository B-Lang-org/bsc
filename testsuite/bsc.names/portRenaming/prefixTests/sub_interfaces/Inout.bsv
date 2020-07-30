interface Ifc;
 (* prefix = "p1" *)
 interface SubIfc s;
endinterface

interface SubIfc;
 (* prefix = "p2" *)
 interface Inout#(Bool) io;
endinterface

(* synthesize *)
module mkInout #(Inout#(Bool) ii) (Ifc);
    interface SubIfc s;
      interface io = ii;
    endinterface
endmodule
