// Test the APackage-based VIOProps deduction (getIOPropsA) through
// inlined wire instances (RWire), compared with the ASPackage-based
// deduction (getIOProps):
//  - setV_v passes through rw1 (single setter) into a register's D_IN,
//    so it is "reg"
//  - deadSet_v sets rw2, whose value is never read, so it is "unused"
//  - neverGet reads rw3, which is never set, so it is "const"
//  - hasDead is the validity of rw3, also "const"
// The APackage-based dump additionally labels the unused RST_N with
// its structural "reset" property.

interface APkgProps_Wires;
   method Action setV(Bit#(8) v);
   method Action deadSet(Bit#(8) v);
   method Bit#(8) neverGet();
   method Bool hasDead();
endinterface

(* synthesize *)
module sysAPkgProps_Wires (APkgProps_Wires);
   Reg#(Bit#(8)) r <- mkRegU;
   RWire#(Bit#(8)) rw1 <- mkRWire;
   RWire#(Bit#(8)) rw2 <- mkRWire;
   RWire#(Bit#(8)) rw3 <- mkRWire;

   rule move (rw1.wget matches tagged Valid .x);
      r <= x;
   endrule

   method Action setV(Bit#(8) v);
      rw1.wset(v);
   endmethod

   method Action deadSet(Bit#(8) v);
      rw2.wset(v);
   endmethod

   method neverGet = fromMaybe(0, rw3.wget);

   method hasDead = isValid(rw3.wget);
endmodule
