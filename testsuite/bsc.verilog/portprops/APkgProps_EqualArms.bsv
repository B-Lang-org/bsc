// Test a method argument that the two deductions disagree about, in
// the direction where getIOProps concludes more than getIOPropsA.
//
// Two callers reach the submodule's put method: the rule passes
// `validValue(w.wget)` and the method passes `x`, and the wire is set
// from `x` in that same method, so after inlining both arms carry the
// same signal.  The netlist optimization merges the equal arms into a
// direct connection to the submodule's register input, so getIOProps
// reports put2_x "reg".  getIOPropsA models the argument mux from the
// schedule's port allocation and classifies both call sites as
// surviving mux inputs, so it concludes nothing.
//
// (Contrast with APkgProps_Arb, where the arbitration is decided
// outright, and APkgProps_Mux, where the arms genuinely differ.)

interface EqualArmsSink;
   method Action put(Bit#(8) v);
endinterface

(* synthesize *)
module mkEqualArmsSink (EqualArmsSink);
   Reg#(Bit#(8)) r <- mkReg(0);
   method Action put(Bit#(8) v);
      r <= v;
   endmethod
endmodule

interface APkgProps_EqualArms;
   method Action put2(Bit#(8) x);
endinterface

(* synthesize *)
module sysAPkgProps_EqualArms (APkgProps_EqualArms);
   EqualArmsSink sub <- mkEqualArmsSink;
   RWire#(Bit#(8)) w <- mkRWire;

   rule rb (w.wget matches tagged Valid .*);
      sub.put(validValue(w.wget));
   endrule

   method Action put2(Bit#(8) x);
      w.wset(x);
      sub.put(x);
   endmethod
endmodule
