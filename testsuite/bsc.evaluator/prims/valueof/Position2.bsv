
typedef Bit#(8) T;

interface Ifc#(type t);
endinterface

(* synthesize *)
module mkTest();
   Ifc#(Bit#(8)) m <- mkSub;
endmodule

module mkSub(Ifc#(t))
 provisos (Bits#(t,st));
   Reg#(Bit#(3)) rg <- mkReg(fromInteger(valueOf(st)));
endmodule
