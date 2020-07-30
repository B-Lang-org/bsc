interface Ifc;
   (* prefix="t" *)
   interface SubIfc s;
endinterface

interface SubIfc;
   interface Reset r;
endinterface

(* synthesize *)
module mkModargResetPrefix ((*port="RST_N_t_r"*)int r, Ifc i);
   interface SubIfc s;
      interface r = noReset;
   endinterface
endmodule

