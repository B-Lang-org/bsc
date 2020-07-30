interface Ifc;
   (* prefix="t" *)
   interface SubIfc s;
endinterface

interface SubIfc;
   interface Clock c;
endinterface

(* synthesize *)
module mkModargClockPrefix ((*port="CLK_t_c"*)int c, Ifc i);
   interface SubIfc s;
      interface c = noClock;
   endinterface
endmodule

