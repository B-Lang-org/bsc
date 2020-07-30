
interface Ifc;
   interface Reg#(Bool) v;
endinterface

(* synthesize *)
(* always_ready *)
module sysAlwaysReady_OnModule_FullInterface (Ifc);
   Reg#(Bool) dummy =
      interface Reg;
         method _read = False;
         method _write(x) = noAction;
      endinterface;
   interface v = dummy;
endmodule

