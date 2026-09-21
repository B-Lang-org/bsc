// Regression test for SMT disjointness conversion of method results that
// are split tuples (one Verilog output port per tuple element).
//
// In AExpr2Yices/AExpr2STP, an `ATupleSel` of an `AMethCall`/`AMethValue`
// must map the (1-based) tuple element index to the corresponding output
// port via `getMethodOutputPorts ... `genericIndex` (selIdx - 1)`.  An
// earlier version omitted the `- 1`, which selected the wrong port and ran
// off the end of the port list (`genericIndex: index too large`) for the
// last element.  This test forces both the value-method and the
// ActionValue-method arm through the SMT solver under both -sat backends.

interface ValSub;
   method Tuple2#(Bool, Bool) get(Bit#(8) x);
endinterface

(* synthesize *)
module mkValSub(ValSub);
   method Tuple2#(Bool, Bool) get(Bit#(8) x);
      return tuple2(x == 0, x == 1);
   endmethod
endmodule

interface AVSub;
   method ActionValue#(Tuple2#(Bool, Bool)) get();
endinterface

(* synthesize *)
module mkAVSub(AVSub);
   Reg#(Bit#(8)) r <- mkReg(0);
   method ActionValue#(Tuple2#(Bool, Bool)) get();
      r <= r + 1;
      return tuple2(r == 0, r == 1);
   endmethod
endmodule

(* synthesize *)
module sysSplitTupleMethodTest();
   ValSub vs <- mkValSub;
   AVSub  avs <- mkAVSub;
   Reg#(Bit#(8))   x  <- mkReg(0);
   Reg#(UInt#(12)) uc <- mkReg(0);
   Reg#(UInt#(12)) ud <- mkReg(0);

   // Value method: both tuple elements (output ports 1 and 2 of vs.get)
   // appear in provably-disjoint rule guards, so the SMT solver must prove
   // aa and ab are mutually exclusive (both write uc).
   Tuple2#(Bool, Bool) p = vs.get(x);
   Bool c1 = tpl_1(p);
   Bool c2 = tpl_2(p);

   rule aa (c1 && !c2);
      uc <= uc + 1;
   endrule
   rule ab (!c1 && c2);
      uc <= uc + 2;
   endrule

   // ActionValue method: both tuple elements (output ports 1 and 2 of
   // avs.get) guard writes to a shared register, so the SMT solver must
   // prove the two conditional updates are mutually exclusive.
   rule cc;
      match {.d1, .d2} <- avs.get();
      if (d1 && !d2) ud <= ud + 1;
      if (!d1 && d2) ud <= ud + 2;
   endrule
endmodule
