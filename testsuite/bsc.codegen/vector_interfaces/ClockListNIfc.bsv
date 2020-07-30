import ListN::*;

interface ClockListN#(numeric type n);
   interface ListN#(n, Clock) clocks;
endinterface


(* synthesize *)
module mkClockListNPassThrough#(ListN#(3, Clock) in_clocks)(ClockListN#(3));
   interface clocks = in_clocks;
endmodule
