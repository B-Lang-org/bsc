interface Ifc;
   (* prefix="t" *)
   interface SubIfc s;
endinterface

interface SubIfc;
   interface Clock c;
endinterface

(* synthesize *)
module mkModargClockPrefixOK ((*port="CLK_s_c"*)int c, Ifc i);
   interface SubIfc s;
      interface c = noClock;
   endinterface
endmodule

