/*----------------------------------------------------------------------------

Example3 Questions

In the presentation slides and in the files Example1.bsv and
Example2.bsv, we saw that shifting by an m-bit vector can be
decomposed into a series of m shifts based on the separates bits of
the shifting amount.  Each shifts by 2^j or not, based on the j-th
digit of the shifting amount.  Example2 implemented this for a fixed
3-bit shifting amount.  The exercises below describe a function which
generalizes to any m-bit shift amount.

-----------------------------------------------------------------------------*/

// "step" is a function which takes the shifting amount "s", a value to
// be shifted "x", and a number "j" indicating which stage of shifting
// this is.  If the "j"-th bit of "s" is 1, then shift by 2 to the power
// of "j".

function Bit#(n) step (Bit#(m) s, Bit#(n) x, Nat j);
   if (s[j] == 0)
      return x;
   else
      return (x << (1 << j));  // x << exp(2,j)
endfunction


// The generalized function for shifting an n-bit vector by an m-bit
// shift amount.  The function implements combinational logic for the
// series of "m" shifts.

function Bit#(n) f (Bit#(m) s, Bit#(n) x);
   Integer max = valueOf(m);
   Bit#(n) xA [max+1];  // array of intermediate results

   // The input to the computation
   xA[0] = x;

   for (Integer j = 0; j < max; j = j + 1)

      // TASK: Fill in the blank (using the function "step")
      xA[j+1] = ?;

   // The output of the computation
   return xA[max];
endfunction

