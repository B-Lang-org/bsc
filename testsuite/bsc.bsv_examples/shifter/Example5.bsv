/*----------------------------------------------------------------------------

Example5

The shifters which were implemented as flexible pipelines in Example4
are implemented here as rigid pipelines.  The buffers between
the stages are registers, and all stages shift at once.  There is no
back-pressure; unlike the FIFO pipelines in Example4 which have an
asynchronous handshake for receiving the result of shifting, the result
in the rigid pipeline must be accepted m+1 cycles later or it is lost.

The function step is used unchanged from the previous examples.  An
interface SShifter is defined for the synchronous push and pull of data.

-----------------------------------------------------------------------------*/


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


// Fixed size shifter:
module mkLs3 (SShifter#(m,n));

   // Input Reg
   Reg#(SXpair#(m,n)) reg0();
   mkRegU the_reg0(reg0);

   Reg#(SXpair#(m,n)) reg1();
   mkRegU the_reg1(reg1);

   Reg#(SXpair#(m,n)) reg2();
   mkRegU the_reg2(reg2);

   Reg#(SXpair#(m,n)) reg3();
   mkRegU the_reg3(reg3);

   // The synchronized pipeline shift
   Action shift = action
		     reg1 <= step(reg0, 0);
		     reg2 <= step(reg1, 1);
		     reg3 <= step(reg2, 2);
		  endaction;

   // Interface
   method push(sx);
      actionvalue
	 reg0 <= sx;  // push the new value
	 shift;       // shift the other registers
	 return(tpl_2(reg3)); // return the x of the last register
      endactionvalue
   endmethod

endmodule


// Generalized shifter
module mkLs (SShifter#(m,n));
   Integer max = valueOf(m);

   // RegFile of pipeline registers
   Reg#(SXpair#(m,n)) regs[max+1];

   // Register-instantiating loop
   for (Integer j = 0; j <= max; j = j+1) begin
      // mkReg tmp(regs[j]);
      Reg#(SXpair#(m,n)) tmp();
      mkRegU the_tmp(tmp);
      regs[j] = tmp;
   end

   // The synchronized pipeline shift
   Action shift =
      action
	 for (Integer j = 0; j < max; j = j+1) begin
	    regs[j+1] <= step(regs[j], fromInteger(j));
	 end
      endaction;

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


// Inlined version of the generalized shifter
// Generalized shifter
module mkLsV2 (SShifter#(m,n));
   Integer max = valueOf(m);

   // RegFile of pipeline registers
   Reg#(SXpair#(m,n)) regs[max+1];

   // Register-instantiating loop
   for (Integer j = 0; j <= max; j = j+1) begin
      // mkReg tmp(regs[j]);
      Reg#(SXpair#(m,n)) tmp();
      mkRegU the_tmp(tmp);
      regs[j] = tmp;
   end

   method push(sx);
      actionvalue
	 (regs[0]) <= sx;  // push the new value
	 for (Integer j = 0; j < max; j = j+1) begin // shift other registers
	    regs[j+1] <= step(regs[j], fromInteger(j));
	 end
	 // return the x of the last register
	 let last_sx = regs[max];
	 Bit#(n) last_x = tpl_2(last_sx);
	 return(last_x);
      endactionvalue
   endmethod

endmodule

/*----------------------------------------------------------------------------

The modules defined above do not include a mechanism for knowing which
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

module mkLsV3 (SMShifter#(m,n));
   Integer max = valueOf(m);

   // RegFile of pipeline registers
   Reg#(Maybe#(SXpair#(m,n))) regs[max+1];

   // Register-instantiating loop
   for (Integer j = 0; j <= max; j = j+1) begin
      // mkReg tmp(regs[j]);
      Reg#(Maybe#(SXpair#(m,n))) tmp();
      mkReg#(Invalid) the_tmp(tmp);
      regs[j] = tmp;
   end

   method push(msx);
      actionvalue
	 (regs[0]) <= msx;  // push the new value
	 for (Integer j = 0; j < max; j = j+1)  // shift the other registers
	    begin
	       let m = regs[j];  // the incoming maybe value
	       // the result if the incoming value is present
	       let res = step(validValue(m), fromInteger(j));
	       // write the result, carrying the valid bit
	       (regs[j+1]) <= isValid(m) ? Valid(res) : Invalid ;
	    end
	 // return the x of the last register
	 let last_sx = regs[max];
	 let ret_val = (isValid(last_sx)) ?
	               Valid (tpl_2(validValue(last_sx))) :  // Valid x
	               Invalid ;
	 return (ret_val);
      endactionvalue
   endmethod

endmodule
