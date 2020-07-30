interface Ifc;
   (* enable="e" *)
   method Action m;
endinterface

(* synthesize *)
module mkModargEnable #(int e) (Ifc);
    return ?;
endmodule

