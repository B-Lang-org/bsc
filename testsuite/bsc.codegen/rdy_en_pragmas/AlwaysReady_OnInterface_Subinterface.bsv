
interface Ifc;
   interface SubIfc v;
endinterface

(* always_ready *)
interface SubIfc;
   method Action _write(Bool x);
   method Bool _read();
endinterface

(* synthesize *)
module sysAlwaysReady_OnInterface_Subinterface (Ifc);
   SubIfc dummy =
      interface SubIfc;
         method _read = False;
         method _write(x) = noAction;
      endinterface;
   interface v = dummy;
endmodule

