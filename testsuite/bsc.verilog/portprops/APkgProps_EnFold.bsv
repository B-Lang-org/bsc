// Test the folding of the references AState creates for callers'
// WILL_FIREs (the enable of a port, and the selectors of its
// argument muxes):
//  - in mkEnFoldShared, the rule and the method perform the same
//    action, so they share the single write arm of register rg, and
//    the port's enable is WILL_FIRE_r || WILL_FIRE_m; the rule is
//    blocked exactly when the method fires (they conflict and the
//    method is more urgent), so the OR is a tautology and EN_m
//    drives nothing -- "unused"
//  - in mkEnFoldLast, two (exclusive) methods set the wire with
//    different data, making a two-arm data mux; the mux's default is
//    a don't-care, so the last arm needs no selector, and the wire's
//    validity is discarded (validValue) -- EN_set2 is "unused",
//    while EN_set1 (the surviving selector) is used

interface OneAct;
   method Action m();
endinterface

(* synthesize *)
module mkEnFoldShared (OneAct);
   Reg#(Bool) rg <- mkReg(False);
   Action act = action
                   rg <= !rg;
                endaction;

   rule r;
      act;
   endrule

   method Action m();
      act;
   endmethod
endmodule

interface TwoSet;
   method Action set1(Bit#(8) a);
   method Action set2(Bit#(8) a);
   method Bit#(8) get();
endinterface

(* synthesize *)
module mkEnFoldLast (TwoSet);
   RWire#(Bit#(8)) w <- mkRWire;

   method Action set1(a);
      w.wset(a);
   endmethod

   method Action set2(a);
      w.wset(a + 1);
   endmethod

   method Bit#(8) get() if (validValue(w.wget) >= 4);
      return validValue(w.wget);
   endmethod
endmodule
