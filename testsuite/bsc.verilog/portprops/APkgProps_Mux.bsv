// Test that properties do NOT flow through surviving muxes: both
// setters are live (their WILL_FIREs are not constant), so the
// register's D_IN and the wire's data come from muxes, and the
// method arguments are used but carry no "reg" property -- in both
// analyses.  (Contrast with APkgProps_Arb, where the arbitration is
// decided outright and the winner's argument is a direct
// connection.)

interface APkgProps_Mux;
   method Action setA(Bit#(8) v);
   method Action setB(Bit#(8) v);
   method Bit#(8) get();
endinterface

(* synthesize *)
module sysAPkgProps_Mux (APkgProps_Mux);
   Reg#(Bit#(8)) r <- mkRegU;
   RWire#(Bit#(8)) w <- mkRWire;

   method Action setA(Bit#(8) v);
      r <= v;
      w.wset(v);
   endmethod

   method Action setB(Bit#(8) v);
      r <= v + 1;
      w.wset(v + 1);
   endmethod

   method get = fromMaybe(r, w.wget);
endmodule
