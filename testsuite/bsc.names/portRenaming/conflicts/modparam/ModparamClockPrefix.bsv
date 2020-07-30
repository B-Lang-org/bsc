interface Ifc;
   (* prefix="t" *)
   interface SubIfc s;
endinterface

interface SubIfc;
   interface Clock c;
endinterface

(* synthesize *)
module mkModparamClockPrefix
          #((*parameter="CLK_t_c"*)parameter int c)
          (Ifc);
   interface SubIfc s;
      interface c = noClock;
   endinterface
endmodule

