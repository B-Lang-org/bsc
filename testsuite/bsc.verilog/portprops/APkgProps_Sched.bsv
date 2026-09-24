// Test that the APackage-based VIOProps deduction (getIOPropsA)
// realizes the consequences of the schedule, which AAddScheduleDefs
// records in the CAN_FIRE/WILL_FIRE definitions:
//  - the rule "put" conflicts with the (more urgent) value method
//    "get", so it can never fire (its WILL_FIRE is the constant 0):
//    the bypass wire inside the BypassReg is never valid and "get"
//    reduces to the register output, "reg"
//  - the rule "fill" always fires (its WILL_FIRE is the constant 1),
//    so the wire behind "look" is always valid and RDY_look is "const"

interface BypassReg#(type tp);
   method Action _write(tp v);
   method tp _read();
endinterface

module mkBypassReg (BypassReg#(typ)) provisos (Bits#(typ,szN));
   Reg#(typ)   rg <- mkRegU;
   RWire#(typ) wr <- mkRWire;

   method Action _write(typ v);
      wr.wset(v);
      rg <= v;
   endmethod

   method typ _read();
      if (wr.wget matches tagged Valid .v)
         return v;
      else
         return rg;
   endmethod
endmodule

interface APkgProps_Sched;
   method Bool get();
   method Bit#(8) look();
endinterface

(* synthesize *)
module sysAPkgProps_Sched (APkgProps_Sched);
   BypassReg#(Bool) r <- mkBypassReg();
   Reg#(Bit#(8)) cnt <- mkRegU;
   RWire#(Bit#(8)) w <- mkRWire;

   // this rule should cause a warning that it will never fire
   // (it conflicts with the more urgent method "get")
   rule put;
      r <= True;
   endrule

   rule fill;
      w.wset(cnt);
   endrule

   method Bool get() = r;

   method Bit#(8) look() if (w.wget matches tagged Valid .*);
      return validValue(w.wget);
   endmethod
endmodule
