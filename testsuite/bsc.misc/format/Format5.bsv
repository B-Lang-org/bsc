package Format5;

import FShow::*;
import Vector::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

typedef struct {Vector#(n, Bool) data;
               } Foo#(numeric type n) deriving (Eq, Bits, Bounded);


(* synthesize *)
module sysFormat5 (Empty);
   
   Reg#(Bit#(6)) count <- mkReg(0);
   Reg#(Foo#(6)) foo   <- mkReg(?);
   Reg#(Foo#(6)) foo2   <- mkReg(?);
   
   rule do_display;
      $display("(%0d) foo is:", $time, fshow(foo), fshow(foo2));
      Bit#(640) h <- $swriteAV("(%0d) foo is:", $time, fshow(foo), fshow(foo2));
      $display("%s", h);
   endrule
   
   rule every;
      count <= count + 1;
      foo   <= unpack(count + 1);
      foo2  <= unpack(count + 3);
      if (count == 10) $finish;
   endrule
   
endmodule

////////////////////////////////////////////////////////////////////////////////
/// Slow version of FShow instance
////////////////////////////////////////////////////////////////////////////////

instance FShow#(Foo#(n));
   function Fmt fshow (Foo#(n) obj);
      Fmt retval = fshow("(");

      for(Integer i=0; i<valueOf(n); i=i+1) 
	 if(obj.data[i]) 
	    retval = retval + $format("%0b", obj.data[i]);
	 else 
	    retval = retval + $format("??");

      return retval + fshow(")");

   endfunction
endinstance

////////////////////////////////////////////////////////////////////////////////
/// Fast version of FShow instance
////////////////////////////////////////////////////////////////////////////////
/* -----\/----- EXCLUDED -----\/-----

instance FShow#(Foo#(n));
   function Fmt fshow (Foo#(n) obj);
      Fmt retval = fshow("(");

      for(Integer i=0; i<valueOf(n); i=i+1) 
	 retval = retval + ((obj.data[i]) ? $format("%0b", obj.data[i]) : $format("??"));

      return retval + fshow(")");

   endfunction
endinstance
 -----/\----- EXCLUDED -----/\----- */

endpackage