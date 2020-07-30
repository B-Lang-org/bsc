/*----------------------------------------------------------------------------

Example6 Questions
 
The functions in this file are list-based versions of those in Example3
(replacing for-loops with list functions).

-----------------------------------------------------------------------------*/

// Need to import the List package to use the List functions
import List::*;


// For reference, this is how the foldl function is defined in the
// List library:

function ta my_foldl (function ta f (ta a, tb b), ta z, List#(tb) list);
   if (isNull(list))
      return (z);
   else
      begin
	 tb        fst  = head(list);
	 List#(tb) rest = tail(list);
	 return (my_foldl(f, f(z, fst), rest));
      end
endfunction


// Define an alias for the pair of a shift amount and in input vector,
// since we will use this repeatedly.
typedef Tuple2#(Bit#(m),Bit#(n)) SXpair#(type m, type n);


// The step function from Example3 rewritten to take and return a pair
function SXpair#(m,n) step2 (SXpair#(m,n) sx, Nat j);

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


// A list implementation of function "f" from Example3:

function Bit#(n) f2 (Bit#(m) s, Bit#(n) x);
   Integer max = valueOf(m);

   // TASK: Write the body of the function.
   // HINT: Start with the initial s/x pair and 
   //       use the "foldl" function to cascade the series of shifts
   //       to produce the final output.

   return (?);  // return (x << s)
endfunction

