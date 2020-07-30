package Example1;

import FIFOF::*;

//(* always_ready *)
interface Ifc;
   method ActionValue#(Bool) produce;
   method ActionValue#(Maybe#(int)) consume;
endinterface

(* synthesize *)
(* options="-aggressive-conditions" *)
module mkAOptTwoMethodsUsingSamePort(Ifc);
   Reg#(int) value <- mkReg(0);
   FIFOF#(int) queue <- mkSizedFIFOF(23);
   
   method ActionValue#(Bool) produce;
      if (queue.notFull)
	 begin
	    queue.enq(value);
	    value <= value + 1;
	    return True;
	 end
      else return False;
   endmethod
   
   method ActionValue#(Maybe#(int)) consume;
      if (queue.notEmpty)
	 begin
	    let x = queue.first;
	    queue.deq;
	    return tagged Valid x;
	 end
      else return tagged Invalid;
   endmethod
   
endmodule

endpackage

