import FIFO :: *;

typedef Tuple2#(Bit#(m),Bit#(n)) SXpair#(type m, type n);

function SXpair#(m,n) step (SXpair#(m,n) sx, Nat j);
   match {.s, .x} = sx;
   Bit#(n) new_x;
   if (s[j] == 0)
      new_x = x;
   else
      new_x = x << (1 << j);  // x << exp(2,j)
   return tuple2(s,new_x);
endfunction

module mkLsStep#(FIFO#(SXpair#(m,n)) fIn, Integer j) (FIFO#(SXpair#(m,n)));

   FIFO#(SXpair#(m,n)) fOut();
   mkFIFO the_fOut(fOut);

   rule shift;

      // TASK: Write the shift action.
      //       You can test your code by running the testbench on mkLs3
      // ...
      fOut.enq(step(fIn.first(), fromInteger(j)));
      fIn.deq();
   endrule

   return (fOut);
endmodule

module mkLs (FIFO#(SXpair#(m,n)));
   Integer max = valueOf(m);

   FIFO#(SXpair#(m,n)) fifos[max+1];

   FIFO#(SXpair#(m,n)) fifo0();
   mkFIFO the_fifo0(fifo0);
   fifos[0] = fifo0;

   for (Integer k = 1; k <= max; k = k + 1) begin
      FIFO#(SXpair#(m,n)) fifol();
      mkLsStep#(fifos[k-1], k) stage(fifol);
      fifos[k] = fifol;
   end

   method enq = ?;
   method deq = ?;
   method first = ?;
   method clear = ?;

endmodule

(* synthesize *)
module mkTest (Empty);

   FIFO#(SXpair#(4,16)) ls();
   mkLs the_ls(ls);

endmodule
