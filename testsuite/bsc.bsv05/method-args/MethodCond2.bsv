import FIFO::*;

interface Test#(type a);
   method ActionValue#(a) push(Bool queue, a val);
endinterface

module mkTest(Test#(a)) provisos(Bits#(a, sa));
   FIFO#(a) f0 <- mkFIFO;
   FIFO#(a) f1 <- mkFIFO;
   
   Reg#(Bool) ready <- mkReg(True);
   
   method ActionValue#(a) push(b, v) if(ready);
      if (b) 
	 f0.enq(v);
      else
	 f1.enq(v);      
      return(v);
   endmethod
endmodule

	 
