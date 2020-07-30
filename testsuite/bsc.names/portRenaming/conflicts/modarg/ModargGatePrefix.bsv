interface Ifc;
   (* prefix="t" *)
   interface SubIfc s;
endinterface

interface SubIfc;
   interface Clock c;
endinterface

(* synthesize *)
module mkModargGatePrefix ((*port="CLK_GATE_t_c"*)int c, Ifc i);
   interface SubIfc s;
      interface c = noClock;
   endinterface
endmodule

