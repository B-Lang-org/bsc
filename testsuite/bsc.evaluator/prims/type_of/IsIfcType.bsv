import FIFO::*;

function Action testType(Type t);
   action 
      $display(printType(t), ": %0b", isInterfaceType(t));
   endaction
endfunction

(* synthesize *)
module sysIsIfcType();
   
   Integer i = ?;
   Reg#(Bit#(32)) r = ?;
   FIFO#(Bit#(32)) f = ?;
   Maybe#(Reg#(Bit#(32))) mr = ?;
   	  
   rule test;
      testType(typeOf(i));
      testType(typeOf(r));
      testType(typeOf(asIfc(r)));
      testType(typeOf(f));
      testType(typeOf(mr));
      $finish(0);	  
   endrule
	
endmodule
	  
	  
	  
      
