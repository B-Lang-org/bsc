interface Ifc;
   method Bool r;
endinterface

(* synthesize *)
module mkModparamResult #(parameter int r) (Ifc);
endmodule

