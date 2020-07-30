package Small6Ifc ;

(* always_enabled *)
interface Fifo_ifc#(type any_t);
   (* result="HEADelement" *)
   method  any_t               first_element() ;

   (* prefix = "PrefixName", enable="ENenque1"  *)    
   method  Action              enqueue( any_t data_in ) ;

   (* prefix = "", enable="ENQOn2" *)
   (* ready = "BAD_rdy_enq2" *) 
   method  Action              enqueue2( (* port="Data" *) any_t _ ) ;

   (* result="DEQRES" *)
   method  ActionValue#(any_t) dequeue() ;
endinterface 

endpackage 
