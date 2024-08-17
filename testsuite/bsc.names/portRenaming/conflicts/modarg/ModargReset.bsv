interface Ifc;
   interface Reset r;
endinterface

(* synthesize *)
module mkModargReset ((*port="RST_N_r"*)int r, Ifc i);
   method r = noReset;
endmodule

