import FIFOF :: * ;


interface Fifo_ifc#(type any_t);
   method  any_t               first_element() ;
   method  Action              enqueue( any_t data_in ) ;
   method  Action              enqueue2( any_t x ) ;
   method  ActionValue#(any_t) dequeue() ;
endinterface 

(* always_enabled *)    
interface Combined#(type a) ;

   (* prefix= "fifoifcae" *)
   (* always_ready = 0 *)
   interface Fifo_ifc#(int) fifoifcAE ;
      
 endinterface

      
(*  synthesize  *)
module mkSmallTest4 ( Combined#(int) ) ;

   FIFOF#(int) tfifo <- mkUGFIFOF ;

   interface Fifo_ifc fifoifcAE ;
      method first_element ;
         return tfifo.first ;
      endmethod
      
      method Action enqueue ( data_in ) ;
         tfifo.enq( data_in ) ;
      endmethod
      
      method  Action enqueue2( data )  if (tfifo.notFull) ;
         tfifo.enq( data ) ;
      endmethod
      
      method  ActionValue#(int) dequeue() ;
         tfifo.deq;
         return tfifo.first ;
      endmethod
   endinterface


   

endmodule

