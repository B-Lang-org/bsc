import FIFO :: *;
(* always_ready *)
interface IFC#(type mType);
 method Action start(mType a, mType b);
 method mType result(mType c);
 method ActionValue#(mType) check(mType d);
endinterface


typedef Bit#(5) Type;

(* synthesize *)
module mkDesign_08 (IFC#(Type));

  FIFO#(Type) fifo1 <- mkFIFO;
  FIFO#(Type) fifo2 <- mkFIFO;


  method Action start(a,b);
    fifo1.enq(a);
    fifo2.enq(b);
  endmethod	

  method Type result(c);
    return fifo1.first+c;
  endmethod	
  	 
  method ActionValue#(Type) check(d);
    fifo1.enq(fifo1.first + 1);
    fifo2.enq(fifo2.first + 2);
    return fifo2.first+d;
  endmethod	
endmodule
