import FIFOF :: * ;

interface XX ;

   (* prefix = "" *)
   method int foo( int xxx, int yyy ) ;

endinterface


//(* always_ready *)
interface Fifo_ifc#(type any_t);
   (* always_ready, prefix="first", result="HEADelement" *)
   method  any_t               first_element() ;
   (* prefix = "PrefixName_", always_ready *)    
   method  Action              enqueue( any_t data_in ) ;

   (* prefix = "", enable="ENQsafeToEnqueueOn2" *)
      (* ready = "RDYenq2" *)         
   method  Action              enqueue2( (* port="Data" *) any_t _ ) ;

      (* always_ready, result="DEQRES" *)
   method  ActionValue#(any_t) dequeue() ;
endinterface 


interface Combined#(type a) ;
   (* prefix = "TOPENQUEUE" *)    
   method  Action              topcenqueue( int data ) ;

   (* prefix = "XX" *)    
   interface XX _xxifc ;

   (* prefix = "YY" *)    
   interface Fifo_ifc#(a) fifoifc ;

   (* prefix = "AR", always_ready *)    
   interface Fifo_ifc#(int) fifoifcAR ;

   (* prefix = "AE", always_enabled *)    
   interface Fifo_ifc#(int) fifoifcAE ;
      
 endinterface

      
(* synthesize  *)
module mkSmallTest2 ( Combined#(int) ) ;

   FIFOF#(int) tfifo <- mkUGFIFOF ;

   method Action topcenqueue( int d) ;
      tfifo.clear ;
   endmethod

   interface XX _xxifc ;
      method foo (int xxx, int yyy );
         return xxx + yyy;
      endmethod
   endinterface

   interface Fifo_ifc fifoifcAR ;
      method first_element ;
         return tfifo.first ;
      endmethod
      
      method Action enqueue ( data_in ) ;
         tfifo.enq( data_in ) ;
      endmethod
      
      method  Action enqueue2( data ) ; // if (tfifo.notFull) ;
         tfifo.enq( data ) ;
      endmethod
      
      method  ActionValue#(int) dequeue() ;
         tfifo.deq;
         return tfifo.first ;
      endmethod
   endinterface

   interface Fifo_ifc fifoifcAE ;
      method first_element ;
         return tfifo.first ;
      endmethod
      
      method Action enqueue ( data_in ) ;
         tfifo.enq( data_in ) ;
      endmethod
      
      method  Action enqueue2( data ) ; // if (tfifo.notFull) ;
         tfifo.enq( data ) ;
      endmethod
      
      method  ActionValue#(int) dequeue() ;
         tfifo.deq;
         return tfifo.first ;
      endmethod
   endinterface


   

endmodule

