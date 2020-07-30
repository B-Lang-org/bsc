interface Ifc;
   method Bool r;
endinterface

(* synthesize *)
module mkModargResult #(int r) (Ifc);
endmodule

