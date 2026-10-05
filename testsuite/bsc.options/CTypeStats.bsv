// Exercises enough of the type machinery that the CType interning
// counters are non-zero, for the -trace-ctype-stats tests below.
(* synthesize *)
module mkCTypeStats(Empty);
   Reg#(Bit#(8)) count <- mkReg(0);
   rule step;
      count <= count + 1;
   endrule
endmodule
