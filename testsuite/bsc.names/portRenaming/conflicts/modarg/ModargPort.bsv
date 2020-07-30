interface Ifc;
   method Bool m(Bool r);
endinterface

(* synthesize *)
module mkModargPort #(int m_r) (Ifc);
    return ?;
endmodule

