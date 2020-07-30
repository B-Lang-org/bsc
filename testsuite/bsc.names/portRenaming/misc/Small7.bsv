import FIFOF :: * ;


(* always_ready, always_enabled *)
interface XX ;

   (* prefix = "" *)
   method ActionValue#(int) foo( int xxx, int yyy ) ;

endinterface


interface Combined#(type a) ;

   interface XX x1 ;
   interface XX x2 ;

endinterface

      
(* synthesize  *)
module mkSmallTest7 ( Combined#(int) ) ;

   

endmodule

