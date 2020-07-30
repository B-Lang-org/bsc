(* always_ready *)
interface XX ;

   (* prefix = "" *)
   method int foo( int xxx, int yyy ) ;

endinterface



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
      
 endinterface

