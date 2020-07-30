import Vector::*;

interface IFC0;
   method Action test(Bit#(32) a, Bit#(32) b);
endinterface

interface IFC1;
   interface Vector#(5, IFC0) ifcs;
endinterface

(* synthesize *)
module mkTest01(IFC1);
   interface ifcs = ?;
endmodule
