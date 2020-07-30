interface Ifc;
   (* prefix="t" *)
   interface SubIfc s;
endinterface

interface SubIfc;
   interface Clock c;
endinterface

(* synthesize *)
module mkModparamClockPrefixOK
          #((*parameter="CLK_s_c"*)parameter int c)
          (Ifc);
   interface SubIfc s;
      interface c = noClock;
   endinterface
endmodule

