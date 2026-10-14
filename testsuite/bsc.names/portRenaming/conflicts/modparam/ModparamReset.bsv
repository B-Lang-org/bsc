interface Ifc;
   interface Reset r;
endinterface

(* synthesize *)
module mkModparamReset #((*parameter="RST_N_r"*)parameter int r) (Ifc);
   method r = noReset;
endmodule

