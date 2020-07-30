interface Ifc;
   method Bool m(Bool r);
endinterface

(* synthesize *)
module mkModparamPortRename #((* parameter="m_r" *)parameter int n) (Ifc);
    return ?;
endmodule

