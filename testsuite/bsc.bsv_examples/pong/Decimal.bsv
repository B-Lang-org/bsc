import Vector::*;
import SVA::*;
import AssertionWires::*;

function Bool goodValue(Vector#(n, DecDigit) ds);
   return ((ds[0]& 3) != 3);
endfunction
	      
typedef  Bit#(4) DecDigit;
			  
interface DecCounter#(type n);
    method Action inc;
    method Vector#(n, DecDigit) getDigits;
endinterface: DecCounter
			
module [AssertModule] mkDecCounter#(Integer i) (DecCounter#(n));
   Reg#(Vector#(n, DecDigit)) digits();
   mkReg#(unpack(0)) the_digits(digits);

   sequence notunsafe;
     goodValue(digits);
   endsequence

   property safe;
     notunsafe  ;// |=> notunsafe;
   endproperty

   AssertionReg a();
   mkAssertionReg#(i) the_a(a);

   always assert property(safe) else a.set;

   method getDigits(); 
      return (digits);
   endmethod: getDigits
   
   method Action inc(); 
                 digits <= incr(digits);
   endmethod: inc
endmodule

function Vector#(n, DecDigit) incr (Vector#(n, DecDigit) xs);
  function addC (ci, x);
    return ((x + ci == 10) ? tuple2(1 , 0) : tuple2(0 , (x + ci)));
  endfunction
  let co_xsnew =  mapAccumL(addC, 1, xs);
  return tpl_2(co_xsnew);
endfunction: incr
