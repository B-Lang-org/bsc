interface Ifc;
   interface Clock c;
endinterface

(* synthesize *)
module mkModargClock ((*port="CLK_c"*)int c, Ifc i);
   method c = noClock;
endmodule

