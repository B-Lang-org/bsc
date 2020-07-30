import Vector::*;

typedef 0 N;

interface Ifc#(numeric type n);
   interface Vector#(n, Clock) clocks;
   interface Vector#(n, Reset) resets;
endinterface

(* synthesize *)
(* gate_all_clocks *)
module sysSizeZero (Ifc#(N));
   Clock clk <- exposeCurrentClock;
   Reset rst <- exposeCurrentReset;

   interface clocks = replicate(clk);
   interface resets = replicate(rst);
endmodule

