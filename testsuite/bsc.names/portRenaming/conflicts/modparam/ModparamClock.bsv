interface Ifc;
   interface Clock c;
endinterface

(* synthesize *)
module mkModparamClock #((*parameter="CLK_c"*)parameter int c) (Ifc);
endmodule

