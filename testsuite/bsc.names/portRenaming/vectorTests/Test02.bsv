import Vector::*;

interface IFC0;
   method Action test(Bit#(32) a, Bit#(32) b);
endinterface

interface IFC1;
   interface Vector#(4, Vector#(5, IFC0)) ifcs;
endinterface

(* synthesize *)
module mkTest02(IFC1);
   interface ifcs = ?;
endmodule
