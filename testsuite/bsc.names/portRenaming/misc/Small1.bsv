import FIFOF :: * ;

//(* always_ready *)
interface Fifo_ifc#(type any_t);
   (* always_ready, result="HEADelement" *)
   method  any_t               first_element() ;

   (* prefix = "PrefixName", enable="EN1",  always_ready *)    
   method  Action              enqueue( any_t data_in ) ;

   (* prefix = "", enable="ENQsafeToEnqueueOn2" *)
      (* ready = "enq2RDYfoo" *)      //   (* always_ready *)
   method  Action              enqueue2( (* port="Data" *) any_t _ ) ;

      (* always_ready, result="DEQRES" *)
   method  ActionValue#(any_t) dequeue() ;
endinterface 



(* synthesize  *)
module mkSmallTest1 ( Fifo_ifc#(Bit#(3))) ;
   FIFOF#(Bit#(3)) tfifo <- mkUGFIFOF ;

   method first_element ;
      return tfifo.first ;
   endmethod

   method Action enqueue ( data_in ) ;
      tfifo.enq( data_in ) ;
   endmethod

   method  Action enqueue2( data ) if (tfifo.notFull) ;
      tfifo.enq( data ) ;
   endmethod

   method  ActionValue#(Bit#(3)) dequeue() ;
      tfifo.deq;
      return tfifo.first ;
   endmethod
   

endmodule

