(* synthesize *)
module mkModArg_Port_ClockMismatch_NoClock ();
  Ifc m <- makePort;
  usePort(m.p);
endmodule

interface Ifc;
  method Bool p;
endinterface

import "BVI"
module makePort (Ifc);
  method P p();
endmodule

import "BVI"
module usePort #(Bool p) ();
  port P clocked_by (no_clock) = p;
endmodule

