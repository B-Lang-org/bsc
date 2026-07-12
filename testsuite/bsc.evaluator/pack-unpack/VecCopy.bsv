package VecCopy;

// Cancellation at scale, in BSV syntax: a vector of registers of a
// custom struct type, copied elementwise.  All eight pack(unpack(Q))
// round trips cancel: no ENTERED-* lines, and every dst element's D_IN
// is a wire from the corresponding src register.
import Vector::*;

typedef struct { Bit#(16) v; } T2;

instance Bits#(T2, 16);
   function Bit#(16) pack(T2 x) = primSeq(message("ENTERED-PACK", 0), x.v);
   function T2 unpack(Bit#(16) b) = primSeq(message("ENTERED-UNPACK", 0), T2 { v: b });
endinstance

(* synthesize *)
module mkVecCopy();
   Vector#(8, Reg#(T2)) src <- replicateM(mkRegU);
   Vector#(8, Reg#(T2)) dst <- replicateM(mkRegU);
   rule copy;
      for (Integer i = 0; i < 8; i = i + 1)
         dst[i] <= src[i];
   endrule
endmodule

endpackage
