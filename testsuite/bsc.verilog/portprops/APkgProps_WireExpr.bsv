// Test that the analysis propagates actual expressions through wires
// (not just properties and constants), so reductions which only
// become applicable after wire inlining are still seen:
//  - "taut" is guarded by (b || nb.wget) where nb carries !b through
//    a wire from an always-firing rule: the tautology is recognized
//    through the wire, so RDY_taut is "const"
//  - "same" reads a wire set to the same expression (register r) by
//    two different rules: the setters share one mux arm, the wire is
//    an alias of r, and the validity is the OR of complementary
//    WILL_FIREs -- so "same" is "reg" and RDY_same is "const"

interface APkgProps_WireExpr;
   method Bit#(8) same();
   method Bool taut();
endinterface

(* synthesize *)
module sysAPkgProps_WireExpr (APkgProps_WireExpr);
   Reg#(Bool) b <- mkRegU;
   Reg#(Bit#(8)) r <- mkRegU;
   Reg#(Bool) s <- mkRegU;
   RWire#(Bool) nb <- mkRWire;
   RWire#(Bit#(8)) w <- mkRWire;

   rule feed;
      nb.wset(!b);
   endrule

   rule pathA (b);
      w.wset(r);
   endrule

   rule pathB (!b);
      w.wset(r);
   endrule

   method Bit#(8) same() if (w.wget matches tagged Valid .*);
      return validValue(w.wget);
   endmethod

   method Bool taut() if (b || fromMaybe(False, nb.wget));
      return s;
   endmethod
endmodule
