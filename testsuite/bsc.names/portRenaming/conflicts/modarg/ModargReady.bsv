// also, test that the renaming of the modarg is taken into account

interface Ifc;
   (* ready="R" *)
   method Bool m;
endinterface

(* synthesize *)
module mkModargReady ((* port="R" *)int r, Ifc i);
    return ?;
endmodule

