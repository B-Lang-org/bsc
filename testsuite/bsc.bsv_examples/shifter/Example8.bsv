/*----------------------------------------------------------------------------

Example8
 
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

   // RegFile of pipeline registers
   List#(Reg#(SXpair#(m,n))) regs <- mapM(constFn(mkRegU), upto(0, max));

   // The synchronized pipeline shift
   function Action mkShift(Integer j);
      action
	 regs[j+1] <= step(regs[j], fromInteger(j));
      endaction
   endfunction

   Action shift = joinActions(map(mkShift, upto(0, max-1)));
   
   // Interface
   method push(sx);
      actionvalue
	 (regs[0]) <= sx;  // push the new value
	 shift;            // shift the other registers
	 // return the x of the last register
	 let last_sx = regs[max];
	 Bit#(n) last_x = tpl_2(last_sx);
	 return(last_x);
      endactionvalue
   endmethod

endmodule


/*----------------------------------------------------------------------------

The module defined above does not include a mechanism for knowing which
data are bogus (corresponding to cycles when the client didn't provide
any input).  The module below implements the same shifter as above
except that the registers between the stages include a presence bit
which indicates whether the data is valid.  A new interface SMShifter
is defined to allow the client to push a Maybe value -- Invalid when
not inserting new data, and Valid when sending a request.  The output,
then, is also a Maybe indicating when valid data is present.

-----------------------------------------------------------------------------*/


// Shifter with valid bit, to identify idle cycles
interface SMShifter#(type m, type n);
   method ActionValue#(Maybe#(Bit#(n))) push(Maybe#(SXpair#(m,n)) msx);
endinterface


// Generalized shifter
module mkLsV3 (SMShifter#(m,n));
   Integer max = valueOf(m);

   // RegFile of pipeline registers
   List#(Reg#(Maybe#(SXpair#(m,n)))) regs;
   regs <- mapM(constFn(mkReg(Invalid)), upto(0, max));

   // The synchronized pipeline shift
   function Action mkShift(Integer j);
      action
	 let in_r = regs[j];
	 let res = step(validValue(in_r), fromInteger(j));
	 regs[j+1] <= isValid(in_r) ? Valid(res) : Invalid;
      endaction
   endfunction

   Action shift = joinActions(map(mkShift, upto(0, max-1)));
   
   // Interface
   method push(sx);
      actionvalue
	 (regs[0]) <= sx;  // push the new value
	 shift;            // shift the other registers
	 // return the x of the last register
	 let last_sx = regs[max];
	 let ret_val = isValid(last_sx) ?
	               Valid (tpl_2(validValue(last_sx))) : // Valid x
	               Invalid ;
	 return(ret_val);
      endactionvalue
   endmethod

endmodule
