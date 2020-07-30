(* synthesize *)
module mkModArg_Inout_ClockMismatch_NoClock ();
  Ifc m <- makeInout(clocked_by noClock);
  useInout(m.i);
endmodule

interface Ifc;
  interface Inout#(Bool) i;
endinterface

import "BVI"
module makeInout (Ifc);
  ifc_inout i(I1);
endmodule

import "BVI"
module useInout #(Inout#(Bool) i) ();
  inout I2 = i;
endmodule

