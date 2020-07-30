interface Ifc;
    (* enable="CLK_c" *)
    method Action m;
    interface Clock c;
endinterface

(* synthesize *)
module mkClockEnable(Ifc);
endmodule
