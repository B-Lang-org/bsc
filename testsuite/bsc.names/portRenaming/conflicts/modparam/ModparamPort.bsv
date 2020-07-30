interface Ifc;
   method Bool m(Bool r);
endinterface

(* synthesize *)
module mkModparamPort #(parameter int m_r) (Ifc);
    return ?;
endmodule

