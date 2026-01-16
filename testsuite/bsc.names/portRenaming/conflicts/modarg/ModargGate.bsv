interface Ifc;
   interface Clock c;
endinterface

(* synthesize *)
module mkModargGate ((*port="CLK_GATE_c"*)int c, Ifc i);
   method c = noClock;
endmodule

