
typedef Bit#(4) Idx;

interface Ifc;
   method ActionValue#(Bool) m(Idx i);
endinterface

(* synthesize *)
module sysMethodEnableToArgMux (Ifc);
   LookupIfc rf <- mkMethodEnableToArgMux_Sub;
   Reg#(Idx) ptr <- mkRegU;

   rule r;
      ptr <= ptr + 1;
      $display(rf.lookup(ptr));
   endrule

   method ActionValue#(Bool) m(Idx i);
      ptr <= ptr + i; // this makes the rule conflict with the method
      return rf.lookup(i);
   endmethod

endmodule    

interface LookupIfc;
   method Bool lookup(Idx i);
endinterface

// make RegFile-like module but with only one port
(* synthesize *)
module mkMethodEnableToArgMux_Sub(LookupIfc);
   Reg#(Bool) rs[32];
   for (Integer i=0; i<32; i=i+1)
      rs[i] <- mkRegU;

   method lookup(i) = rs[i];
endmodule

