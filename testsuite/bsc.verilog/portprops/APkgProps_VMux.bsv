// Test the arbitration modeling of the argument muxes of VALUE
// methods (AState's "expr blobs"): unique calls to a value method of
// a state instance which share a port are muxed, selecting on the
// callers' control signals (the WILL_FIRE of a rule, the RDY of an
// interface value method):
//  - in mkVMuxWired, the single call of sub.get (used by the value
//    method "data_out") is a direct connection, so no selector
//    references anything; the wire's validity is discarded
//    (validValue) and its single setter makes the data an alias of
//    the argument -- so EN_data_in drives no hardware and is
//    "unused" (and data_in_x flows directly to the lookup)
//  - in sysAPkgProps_VMux, rules pA and pB are exclusive and share
//    subP.get's one port; pB conflicts with the more urgent value
//    method "peek" and can never fire, so its arm is dropped, the
//    surviving arm is a direct connection, and "ib" (feeding only
//    the dropped arm) is "unused"
//  - rules exA and exB share subX.get's port and both can fire:
//    the parallel mux survives, and both "ic" and "id" are used

interface Lookup;
   method Bit#(8) get(Bit#(3) i);
endinterface

(* synthesize *)
module mkVMuxLookup(Lookup);
   Reg#(Bit#(64)) tab <- mkRegU;
   method Bit#(8) get(Bit#(3) i);
      return truncate(tab >> {i, 3'b000});
   endmethod
endmodule

interface Wired;
   (* always_ready *)
   method Action data_in(Bit#(3) x);
   (* always_ready *)
   method Bit#(8) data_out();
endinterface

(* synthesize *)
module mkVMuxWired(Wired);
   RWire#(Bit#(3)) w <- mkRWire;
   Lookup sub <- mkVMuxLookup;
   method Action data_in(Bit#(3) x);
      w.wset(x);
   endmethod
   method Bit#(8) data_out();
      return sub.get(validValue(w.wget));
   endmethod
endmodule

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

interface APkgProps_VMux;
   method Bit#(8) o1();
   method Bit#(8) o3();
   method Bool peek();
endinterface

(* synthesize *)
module sysAPkgProps_VMux (Bit#(3) ia, Bit#(3) ib, Bit#(3) ic, Bit#(3) id,
                          APkgProps_VMux ifc);
   Lookup subP <- mkVMuxLookup;
   Lookup subX <- mkVMuxLookup;
   Reg#(Bit#(8)) r1 <- mkRegU;
   Reg#(Bit#(8)) r3 <- mkRegU;
   Reg#(Bool) b <- mkRegU;
   BypassReg#(Bool) k <- mkBypassReg();

   rule pA (b);
      r1 <= subP.get(ia);
   endrule

   // this rule should cause a warning that it will never fire
   // (it conflicts with the more urgent method "peek")
   rule pB (!b);
      r1 <= subP.get(ib);
      k <= True;
   endrule

   rule exA (b);
      r3 <= subX.get(ic);
   endrule

   rule exB (!b);
      r3 <= subX.get(id);
   endrule

   method o1 = r1;
   method o3 = r3;
   method peek = k;
endmodule
