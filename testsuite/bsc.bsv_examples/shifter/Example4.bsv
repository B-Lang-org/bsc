/*----------------------------------------------------------------------------

Example4

The combinational shifter from Example3 can be pipelined by adding
buffers between the series of shifts.  The exercises below implement
a pipelined shifter with FIFOs as buffers.

-----------------------------------------------------------------------------*/

// The pipeline buffers are FIFOs in this example
import FIFO::*;

// Define an alias for the pair of a shift amount and in input vector,
// since we will use this repeatedly.
typedef Tuple2#(Bit#(m),Bit#(n)) SXpair#(type m, type n);

// The step function from Example3 rewritten to take and return a pair
function SXpair#(m,n) step (SXpair#(m,n) sx, Nat j);

   // Give the names "s" and "x" to the parts of the input
   match {.s, .x} = sx;

   // Compute the shifted output
   Bit#(n) new_x;
   if (s[j] == 0)
      new_x = x;
   else
      new_x = x << (1 << j);  // x << exp(2,j)

   // Return the shift amount with the shifted vector
   return tuple2(s,new_x);
endfunction


// Given the buffer from the previous stage, instantiate a buffer
// for the next stage and the logic between the two.  The logic is
// parameterized by which stage this is (the parameter j).

module mkLsStep#(FIFO#(SXpair#(m,n)) fIn, Integer j) (FIFO#(SXpair#(m,n)));

   // Output buffer
   FIFO#(SXpair#(m,n)) fOut();
   mkFIFO the_fOut(fOut);

   // The logic
   rule shift;
      let sx = fIn.first();
      fIn.deq();
      fOut.enq(step(sx, fromInteger(j)));
   endrule

   // Export the interface to the instantiated FIFO
   return (fOut);

endmodule


// A shifter module which is hardcoded for a 3-bit shift amount.
module mkLs3 (FIFO#(SXpair#(m,n)));

   // Input FIFO
   FIFO#(SXpair#(m,n)) fifo0();   
   mkFIFO the_fifo0(fifo0);
   
   // Stage 1
   FIFO#(SXpair#(m,n)) fifo1();
   mkLsStep#(fifo0, 0) stage1(fifo1);

   // Stage 2
   FIFO#(SXpair#(m,n)) fifo2();
   mkLsStep#(fifo1, 1) stage2(fifo2);

   // Stage 3 (and output FIFO)
   FIFO#(SXpair#(m,n)) fifo3();
   mkLsStep#(fifo2, 2) stage3(fifo3);

   // Interface (enq into input, deq from output)
   method enq = fifo0.enq;
   method deq = fifo3.deq;
   method first = fifo3.first;

   method clear();
      action
	 fifo0.clear; fifo1.clear; fifo2.clear; fifo3.clear;
      endaction
   endmethod

endmodule


// The generalized pipeline for shifting an n-bit vector by an m-bit
// shift amount.  The pipeline implements the shifting in "m" stages.

module mkLs (FIFO#(SXpair#(m,n)));
   Integer max = valueOf(m);

   // RegFile of FIFO interfaces
   FIFO#(SXpair#(m,n)) fifos[max+1];

   // The input FIFO
   // mkFIFO the_fifo0(fifos[0]);
   FIFO#(SXpair#(m,n)) fifo0();
   mkFIFO the_fifo0(fifo0);
   fifos[0] = fifo0;

   // The stages
   for (Integer j = 0; j < max; j = j+1) begin
      // mkLsStep#(fifos[j], j) tmp(fifos[j+1]);
      FIFO#(SXpair#(m,n)) tmp();
      mkLsStep#(fifos[j], j) the_tmp(tmp);
      fifos[j+1] = tmp;
   end

   // Interface (enq into input, deq from output)
   method enq = (fifos[0]).enq;
   method deq = (fifos[max]).deq;
   method first = (fifos[max]).first;

   method clear();
      action
	 for (Integer j = 0; j <= max; j = j+1)
	    (fifos[j]).clear;
      endaction
   endmethod

endmodule


// Inlined version of the generalized shifter
module mkLsV2 (FIFO#(SXpair#(m,n)));
   Integer max = valueOf(m);

   // RegFile of FIFO interfaces
   FIFO#(SXpair#(m,n)) fifos[max+1];

   // The buffers
   for (Integer j = 0; j <= max; j = j+1) begin
      // mkFIFO tmp(fifos[j]);
      FIFO#(SXpair#(m,n)) tmp();
      mkFIFO the_tmp(tmp);
      fifos[j] = tmp;
   end
      
   // The stages
   for (Integer j = 0; j < max; j = j+1)
      rule shift;
	 let fIn = fifos[j];
	 let fOut = fifos[j+1];
	 let sx = fIn.first();
	 fIn.deq();
	 fOut.enq(step(sx, fromInteger(j)));
      endrule

   // Interface (enq into input, deq from output)
   method enq = (fifos[0]).enq;
   method deq = (fifos[max]).deq;
   method first = (fifos[max]).first;

   method clear();
      action
	 for (Integer j = 0; j <= max; j = j+1)
	    (fifos[j]).clear;
      endaction
   endmethod

endmodule

