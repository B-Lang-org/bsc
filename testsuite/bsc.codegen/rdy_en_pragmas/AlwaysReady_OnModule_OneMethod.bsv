
interface Ifc;
   interface Reg#(Bool) v;
endinterface

(* synthesize *)
(* always_ready="v._write" *)
module sysAlwaysReady_OnModule_OneMethod (Ifc);
   Reg#(Bool) rg <- mkRegU;
   Reg#(Bool) dummy =
      interface Reg;
         method _read if (rg) = False;
         method _write(x) = noAction;
      endinterface;
   interface v = dummy;
endmodule

