package Sub ;

export ArithIO(..);
		   
export msub;
export Sub_t;
	     
import UInt::*;
	     
typedef  UInt#(32) Sub_t;

// Interface for general arith operation
interface ArithIO#(parameter type a_t);
    method Action start(a_t xxxx1, a_t yyyy2);
    method a_t subout;
endinterface: ArithIO

(* synthesize *)
module msub( ArithIO#(Sub_t)) ;
        Reg #(Sub_t) result() ;
        mkRegU i1( result );

       method start( xxxx1, yyyy2) ;
          action
                result <= xxxx1 - yyyy2 ;
          endaction 
      endmethod: start 

      method subout () ;
        subout =  result ;
      endmethod: subout

endmodule: msub 

// method is xxxx1 - yyyy2

endpackage
