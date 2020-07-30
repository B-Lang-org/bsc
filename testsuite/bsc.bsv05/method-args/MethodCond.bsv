import FIFO::*;

interface Test#(type a);
   method ActionValue#(a) push(Bool queue, a val);
endinterface

(* synthesize *)
module mkTest(Test#(Bit#(32)));
   FIFO#(Bit#(32)) f0 <- mkFIFO;
   FIFO#(Bit#(32)) f1 <- mkFIFO;
   
   Reg#(Bool) ready <- mkReg(True);
   
   method ActionValue#(Bit#(32)) push(b, v) if(ready);
      if (b) 
	 f0.enq(v);
      else
	 f1.enq(v);      
      return(v);
   endmethod
endmodule

	 
