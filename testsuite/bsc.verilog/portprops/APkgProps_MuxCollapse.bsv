// Test a selector input that the two deductions disagree about, in
// the direction where getIOProps concludes more than getIOPropsA.
//
// Both arms of the mux carry the same value: the wire is set from the
// register unconditionally, so `validValue(w.wget)` and `r` are the
// same signal after inlining.  The netlist optimization collapses the
// mux to a direct assignment, leaving the selector driving nothing, so
// getIOProps reports pick_c "unused".  getIOPropsA classifies a
// selector as an opaque use and concludes nothing about it, because
// its agreement rule applies to the value it deduces for an output,
// not backwards to the inputs of a mux it has decided survives.
//
// (Contrast with APkgProps_Mux, where the two setters genuinely
// differ and both analyses agree that nothing flows through.)

interface APkgProps_MuxCollapse;
   method Bit#(8) pick(Bool c);
endinterface

(* synthesize *)
module sysAPkgProps_MuxCollapse (APkgProps_MuxCollapse);
   Reg#(Bit#(8)) r <- mkReg(0);
   RWire#(Bit#(8)) w <- mkRWire;

   rule fill;
      w.wset(r);
   endrule

   method Bit#(8) pick(Bool c) = c ? r : validValue(w.wget);
endmodule
