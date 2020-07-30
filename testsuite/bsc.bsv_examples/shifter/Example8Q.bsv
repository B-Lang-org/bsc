/*----------------------------------------------------------------------------

Example8 Questions

The functions in this file are list-based versions of those in Example5
(replacing for-loops with list functions).

-----------------------------------------------------------------------------*/

// Need to import the List package to use the List functions
import List::*;


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


// Synchronous shifter interface
interface SShifter#(type m, type n);
   method ActionValue#(Bit#(n)) push(SXpair#(m,n) sx);
endinterface


// Generalized shifter
module mkLs (SShifter#(m,n));
   Integer max = valueOf(m);

   // TASK: Copy the array of pipeline registers from Example5 and
   //       reuse it here.


   // TASK: Define the synchronous shift action using list functions.
   //       You will need to define a helper function which is map'd
   //       or fold'd over a list.
   // HINT: You may want to use functions such as "map" and "upto",
   //       or "foldr" or "foldl".  You may need to use the function
   //       "joinActions" to join a list of actions into one parallel
   //       action.

   Action shift = ?;


   // Interface
   method push(sx);
      actionvalue

	 // TASK: Copy the interface definition from Example5 and reuse
	 //       it here.

	 return (?);
      endactionvalue
   endmethod

endmodule
