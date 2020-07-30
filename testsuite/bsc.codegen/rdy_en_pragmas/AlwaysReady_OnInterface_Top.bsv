
(* always_ready *)
interface Ifc;
   interface Reg#(Bool) v;
endinterface

(* synthesize *)
module sysAlwaysReady_OnInterface_Top (Ifc);
   Reg#(Bool) dummy =
      interface Reg;
         method _read = False;
         method _write(x) = noAction;
      endinterface;
   interface v = dummy;
endmodule

