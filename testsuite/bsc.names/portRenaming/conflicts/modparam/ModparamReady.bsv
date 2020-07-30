// also, test that the renaming of the modparam is taken into account

interface Ifc;
   (* ready="R" *)
   method Bool m;
endinterface

(* synthesize *)
module mkModparamReady #((* parameter="R" *)parameter int r) (Ifc);
    return ?;
endmodule

