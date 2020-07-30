import FIFOF :: * ;
import Ifc3 :: * ;

      
(* synthesize  *)
module mkSmallTest3 ( Combined#(int) ) ;

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

   interface Fifo_ifc fifoifc ;
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

