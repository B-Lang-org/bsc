interface Ifc;
   interface Clock c;
endinterface

(* synthesize *)
module mkModparamGate #((*parameter="CLK_GATE_c"*)parameter int c) (Ifc);
   method c = noClock;
endmodule

