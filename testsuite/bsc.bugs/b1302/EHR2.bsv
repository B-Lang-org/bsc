import EHR_new::*;

interface EHR2#(type t);
   interface Reg#(t) r1;
   interface Reg#(t) r2;
endinterface

(* synthesize *)
module mkEHR2 (EHR2#(Bit#(32)));
   EHR#(2,Bit#(32)) ehr <- mkEHR(0+5);
   interface r1 = ehr[0];
   interface r2 = ehr[1];
endmodule

