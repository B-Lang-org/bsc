interface Ifc;
   (* prefix="t" *)
   interface SubIfc s;
endinterface

interface SubIfc;
   interface Reset r;
endinterface

(* synthesize *)
module mkModparamResetPrefixOK
          #((*parameter="RST_N_s_r"*)parameter int r)
          (Ifc);
   interface SubIfc s;
      interface r = noReset;
   endinterface
endmodule

