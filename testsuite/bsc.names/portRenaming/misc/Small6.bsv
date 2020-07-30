import FIFOF :: * ;
import Small6Ifc :: * ;

(* synthesize  *)
module mkSmallTest6 ( Fifo_ifc#(Bit#(3))) ;
   FIFOF#(Bit#(3)) tfifo <- mkUGFIFOF ;

   method first_element ;
      return tfifo.first ;
   endmethod

   method Action enqueue ( data_in ) ;
      tfifo.enq( data_in ) ;
   endmethod

   method  Action enqueue2( data ) ; // if (tfifo.notFull) ;
      tfifo.enq( data ) ;
   endmethod

   method  ActionValue#(Bit#(3)) dequeue() ;
      tfifo.deq;
      return tfifo.first ;
   endmethod
   

endmodule

(* synthesize *)
module sysSmall6 () ;


   Fifo_ifc#(Bit#(3)) dut <- mkSmallTest6 ;

   
endmodule
