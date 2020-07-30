
import Position3Sub::*;

typedef Bit#(8) T;

(* synthesize *)
module mkTest();
   Ifc#(Bit#(8), Bit#(3)) m <- mkSub;
endmodule

