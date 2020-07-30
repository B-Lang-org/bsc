/*----------------------------------------------------------------------------

Example7 Questions
 
The functions in this file are list-based versions of those in Example4
(replacing for-loops with list functions).

-----------------------------------------------------------------------------*/

// Need to import the List package to use the List functions
import List::*;

// The pipeline buffers are FIFOs in this example
import FIFO::*;


// For reference, this is how the foldlM function is defined in the
// library:

function Module#(ta) my_foldlM (function Module#(ta) f (ta a, tb b),
				Module#(ta) zmod, List#(tb) list);
   if (isNull(list))
      return (zmod);
   else
      begin
         module [Module] m(ta);
	    tb        fst  = head(list);
	    List#(tb) rest = tail(list);

	    // instantiate the submodule
	    ta zres();
	    zmod the_zmod(zres);

	    // instantiate next part
	    ta res();
	    my_foldlM#(f, f(zres, fst), rest) the_res(res);

	    return (res);
	 endmodule

	 return (m);
      end
endfunction


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


// A list implementation of mkLsStep and mkLs from Example4:

module mkLsStep#(FIFO#(SXpair#(m,n)) fIn, Integer j) (FIFO#(SXpair#(m,n)));

   // TASK: Copy module mkLsStep exactly from Example4 and place it here
   // The List version of mkLs will use this module unchanged.

   return (?);

endmodule


// The generalized pipeline for shifting an n-bit vector by an m-bit
// shift amount.  The pipeline implements the shifting in "m" stages.

module mkLs (FIFO#(SXpair#(m,n)));
   Integer max = valueOf(m);

   // Instantiate the input FIFO
   FIFO#(SXpair#(m,n)) fifo0();
   mkFIFO the_fifo0(fifo0);

   // TASK: Instantiate the pipeline stages.
   // HINT: Use foldlM to return an interface of type FIFO#(SXpair#(m,n))
   // ...

   // TASK: Implement the interface.
   //       "enq" into the input FIFO, "deq" from the output FIFO
   
   method enq = ?;
   method deq = ?;
   method first = ?;

   // To implement clear, we would need to change mkLsStep to pass the
   // clear signal from the output to the input.  See below.
   method clear = noAction;

endmodule


// Version of mkLsStep which propagates the "clear" signal

module mkLsStepV2#(FIFO#(SXpair#(m,n)) fIn, Integer j) (FIFO#(SXpair#(m,n)));

   // TASK: Define this module in preparation for mkLsV2.
   //
   // Module mkLs only has access to the very last interface resulting
   // from the call to foldlM.  If we use mkLsStep unchanged from
   // Example4, then the clear signal does not clear all the FIFOs.
   //
   // Define this module so that "clear" is properly handled.
   //
   // HINT: Since mkLs only has access to the last FIFO interface,
   //       the call to the "clear" method of that final interface
   //       must pass the signal back to all the previous FIFOs.

   // Interface (enq unused, only deq used)
   method enq = ?;
   method deq = ?;
   method first = ?;
   method clear();
      action
	 // ...
      endaction
   endmethod

endmodule


// Generalized pipeline with the "clear" method implemented

module mkLsV2 (FIFO#(SXpair#(m,n)));
   Integer max = valueOf(m);

   // TASK: Rewrite mkLs to properly implement the "clear" method
   //       using mkLsV2.
   // ...
   
   method enq = ?;
   method deq = ?;
   method first = ?;
   method clear = ?;

endmodule
