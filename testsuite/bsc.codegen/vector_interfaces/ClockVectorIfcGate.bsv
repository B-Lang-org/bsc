import Vector::*;

interface ClockVector#(numeric type n);
   interface Vector#(n, Clock) clocks;
endinterface

(* gate_all_clocks *)
(* synthesize *)
module mkClockVectorPassThrough#(Vector#(3, Clock) in_clocks)(ClockVector#(3));
   interface clocks = in_clocks;
endmodule
