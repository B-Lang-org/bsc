interface Ifc;
   (* prefix="t" *)
   interface SubIfc s;
endinterface

interface SubIfc;
   interface Reset r;
endinterface

(* synthesize *)
module mkModparamResetPrefix
          #((*parameter="RST_N_t_r"*)parameter int r)
          (Ifc);
   interface SubIfc s;
      interface r = noReset;
   endinterface
endmodule

