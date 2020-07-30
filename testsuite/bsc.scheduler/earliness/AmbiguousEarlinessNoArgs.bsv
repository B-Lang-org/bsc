import FIFO::*;

(* synthesize *)
module mkAmbiguousEarlinessNoArgs ();
   FIFO#(Bool) fifo <- mkFIFO;

   rule rl_A;
      fifo.clear();
   endrule

   rule rl_B;
      fifo.clear();
   endrule
endmodule

