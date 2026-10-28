package Gigo;

// The documented semantics change of coercion cancellation: bits
// arriving from outside are no longer laundered through a
// decode/re-encode round trip.  unpack of an input port re-packed to an
// output port is a wire, even for a type whose encoding has unused
// values (the union below has a 2-bit tag with only 3 used tags, and
// don't-care payload bits in some arms).
typedef union tagged {
   void Nothing2;
   Bit#(8) Small;
   Bit#(13) Big;
} U deriving (Bits);

interface GigoIfc;
   (* always_ready *)
   method Bit#(15) out((* port="inp" *) Bit#(15) inp);
endinterface

(* synthesize *)
module mkGigo(GigoIfc);
   method Bit#(15) out(Bit#(15) inp);
      U u = unpack(inp);
      return pack(u);
   endmethod
endmodule

endpackage
