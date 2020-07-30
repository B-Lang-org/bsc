interface Ifc;
   method Bool m(Bool r);
endinterface

(* synthesize *)
module mkModargPortRename ( (* port="m_r" *)int n, Ifc i);
    return ?;
endmodule

