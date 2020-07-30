// Very simple multiple-errors testcase

import Vector::*;

interface Test;
  method Bool test;
endinterface

// array out-of-bounds
(* synthesize *)
module mkErrorOne(Test);
  Vector#(5, Bool) v = replicate(True);

  method test = v[5];
endmodule

interface ClockIfc;
  interface Clock clk_out;
endinterface

// won't compile because of undetermined Clock
(* synthesize *)
module mkErrorTwo(ClockIfc);
  interface clk_out = ?;
endmodule

// uses mkErrorOne
(* synthesize *) 
module mkErrorTop();

  Test t <- mkErrorOne;

  rule go;
    $display(t.test);
    $finish(0);
  endrule

endmodule
