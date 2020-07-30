interface Ifc;
 (* prefix = "p1" *)
 interface SubIfc s;
endinterface

interface SubIfc;
 (* prefix = "p2" *)
 interface Reset r;
endinterface

(* synthesize *)
module mkReset (Ifc);
    Reset rst <- exposeCurrentReset;
    interface SubIfc s;
      interface r = rst;
    endinterface
endmodule
