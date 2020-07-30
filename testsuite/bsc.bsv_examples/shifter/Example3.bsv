/*----------------------------------------------------------------------------

Example3

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

// The 3-bit version from Example2:
function Bit#(n) f_3bit (Bit#(3) s, Bit#(n) x);
   Bit#(n) x0 = step(s, x,  0);
   Bit#(n) x1 = step(s, x0, 1);
   Bit#(n) x2 = step(s, x1, 2);
   return (x2);
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
      xA[j+1] = step (s, xA[j], fromInteger(j));

   // The output of the computation
   return xA[max];
endfunction


/*----------------------------------------------------------------------------

Version 2: Takes a pair, returns a pair

Below is another version of the above examples.  This version uses a
step function which takes a pair as input and returns a pair as
output.  This version is more easily developed into a pipelined
shifter in Example4.  The step function defined on pairs is also
needed for the List versions, developed in Example6.

-----------------------------------------------------------------------------*/

typedef Tuple2#(Bit#(m),Bit#(n)) SXpair#(type m, type n);

function SXpair#(m,n) step2 (SXpair#(m,n) sx, Nat j);
   match {.s, .x} = sx;

   Bit#(n) new_x;
   if (s[j] == 0)
      new_x = x;
   else
      new_x = x << (1 << j);  // x << exp(2,j)

   return tuple2(s,new_x);
endfunction

// The 3-bit version from Example2:
function Bit#(n) f2_3bit (Bit#(3) s, Bit#(n) x);
   SXpair#(3,n) sx  = tuple2(s,x);
   SXpair#(3,n) sx0 = step2(sx,  0);
   SXpair#(3,n) sx1 = step2(sx0, 1);
   SXpair#(3,n) sx2 = step2(sx1, 2);
   return (tpl_2(sx2));  // == x2
endfunction

// A generalized version:
function Bit#(n) f2 (Bit#(m) s, Bit#(n) x);
   Integer max = valueOf(m);
   SXpair#(m,n) sxA [max+1];  // array of intermediate results
   sxA[0] = tuple2(s,x);
   for (Integer j = 0; j < max; j = j + 1)
      sxA[j+1] = step2 (sxA[j], fromInteger(j));
   return tpl_2(sxA[max]);
endfunction

