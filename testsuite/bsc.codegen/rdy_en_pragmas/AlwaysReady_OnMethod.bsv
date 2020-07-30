
interface Ifc;
   method Action _write(Bool x);
   (* always_ready *)
   method Bool _read();
endinterface

(* synthesize *)
module sysAlwaysReady_OnMethod (Ifc);
   method _read = False;
   method _write(x) = noAction;
endmodule

