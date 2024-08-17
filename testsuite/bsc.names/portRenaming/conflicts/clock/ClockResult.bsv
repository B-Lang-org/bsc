interface Ifc;
    (* result="CLK_c" *)
    method Bool m;
    interface Clock c;
endinterface

(* synthesize *)
module mkClockResult(Ifc);
    method m = False;
    method c = noClock;
endmodule
