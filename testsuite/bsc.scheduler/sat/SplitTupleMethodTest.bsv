// Regression test for SMT disjointness conversion of method results that
// are split tuples (one Verilog output port per tuple element).
//
// In AExpr2Yices/AExpr2STP, an `ATupleSel` of an `AMethCall`/`AMethValue`
// must map the (1-based) tuple element index to the corresponding output
// port via `getMethodOutputPortAt`, which does
// `getMethodOutputPorts ... `genericIndex` (selIdx - 1)`.  An earlier
// version omitted the `- 1`, which selected the wrong port and ran off the
// end of the port list (`genericIndex: index too large`) for the last
// element.  This test forces both the value-method and the
// ActionValue-method arm through the SMT solver under both -sat backends.
//
// On this branch tuples do not split into per-element ports by default, so
// the method results are wrapped in ShallowSplit to give each tuple element
// its own output port (get_fst / get_snd).

import SplitPorts::*;

function Tuple2#(Bool, Bool) unwrap(ShallowSplit#(Tuple2#(Bool, Bool)) s);
   case (s) matches
      tagged ShallowSplit .p : return p;
   endcase
endfunction

interface ValSub;
   method ShallowSplit#(Tuple2#(Bool, Bool)) get(Bit#(8) x);
endinterface

(* synthesize *)
module mkValSub(ValSub);
   method ShallowSplit#(Tuple2#(Bool, Bool)) get(Bit#(8) x);
      return ShallowSplit(tuple2(x == 0, x == 1));
   endmethod
endmodule

interface AVSub;
   method ActionValue#(ShallowSplit#(Tuple2#(Bool, Bool))) get();
endinterface

(* synthesize *)
module mkAVSub(AVSub);
   Reg#(Bit#(8)) r <- mkReg(0);
   method ActionValue#(ShallowSplit#(Tuple2#(Bool, Bool))) get();
      r <= r + 1;
      return ShallowSplit(tuple2(r == 0, r == 1));
   endmethod
endmodule

(* synthesize *)
module sysSplitTupleMethodTest();
   ValSub vs <- mkValSub;
   AVSub  avs <- mkAVSub;
   Reg#(Bit#(8))   x  <- mkReg(0);
   Reg#(UInt#(12)) uc <- mkReg(0);
   Reg#(UInt#(12)) ud <- mkReg(0);

   // Value method: both tuple elements (output ports get_fst and get_snd of
   // vs.get) appear in provably-disjoint rule guards, so the SMT solver must
   // prove aa and ab are mutually exclusive (both write uc).
   Tuple2#(Bool, Bool) p = unwrap(vs.get(x));
   Bool c1 = tpl_1(p);
   Bool c2 = tpl_2(p);

   rule aa (c1 && !c2);
      uc <= uc + 1;
   endrule
   rule ab (!c1 && c2);
      uc <= uc + 2;
   endrule

   // ActionValue method: both tuple elements (output ports get_fst and
   // get_snd of avs.get) guard writes to a shared register, so the SMT solver
   // must prove the two conditional updates are mutually exclusive.
   rule cc;
      let s <- avs.get();
      match {.d1, .d2} = unwrap(s);
      if (d1 && !d2) ud <= ud + 1;
      if (!d1 && d2) ud <= ud + 2;
   endrule
endmodule
