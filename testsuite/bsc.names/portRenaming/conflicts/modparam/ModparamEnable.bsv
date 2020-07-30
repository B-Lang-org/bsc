interface Ifc;
   (* enable="e" *)
   method Action m;
endinterface

(* synthesize *)
module mkModparamEnable #(parameter int e) (Ifc);
    return ?;
endmodule

