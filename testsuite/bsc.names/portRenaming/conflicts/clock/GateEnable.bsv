interface Ifc;
    (* enable="CLK_GATE_c" *)
    method Action m;
    interface Clock c;
endinterface

(* synthesize *)
module mkGateEnable(Ifc);
    method m = noAction;
    method c = noClock;
endmodule
