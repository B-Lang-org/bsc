
interface Ifc;
   (* always_ready *)
   interface Reg#(Bool) v;
endinterface

(* synthesize *)
module sysAlwaysReady_OnSubinterface (Ifc);
   Reg#(Bool) dummy =
      interface Reg;
         method _read = False;
         method _write(x) = noAction;
      endinterface;
   interface v = dummy;
endmodule

