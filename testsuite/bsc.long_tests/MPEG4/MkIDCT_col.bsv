//////////////1 D Column IDCT////////////////////////////////////////

package MkIDCT_col;

import MkIDCT_1D :: *;
import TBuffer :: *;

(* always_ready,
  always_enabled,
  synthesize *)
module mkIDCT_col (IDCT_1D_IFC#(16,9));
    
   IDCT_1D_IFC#(16, 9) wrap();
   mkIDCT_1D the_wrap(wrap);

   RWire#(DataStrobe#(16)) dataStrobe() ;
   mkRWire i_dataStrobe(dataStrobe) ;

   rule always_fire (True);
      if ( dataStrobe.wget matches tagged Just {.x, .y} )
           wrap.start (x, y);
    endrule
    
    method Action start (a, b);
        dataStrobe.wset ( tuple2(a,b) ) ;
    endmethod : start
    
    method result ();
        return (wrap.result); 
    endmethod : result

endmodule : mkIDCT_col


endpackage : MkIDCT_col
