/////////////1D Row IDCT ////////////////////////////////////////////


package MkIDCT_row;

import MkIDCT_1D :: *;
import TBuffer :: *;


(* always_ready,
  always_enabled,
  synthesize *)
module mkIDCT_row (IDCT_1D_IFC#(12,16));
    
   IDCT_1D_IFC#(12,16) wrap();
   mkIDCT_1D the_wrap(wrap);

   RWire#(DataStrobe#(12)) dataStrobe();
   mkRWire i_dataStrobe(dataStrobe) ;

   rule always_fire (True);
      if (dataStrobe.wget matches tagged Just {.x, .y} )
           wrap.start (x, y);
    endrule
    
    method Action start (a, b);
        dataStrobe.wset( tuple2(a,b) );
    endmethod : start
    
    method result ();
        return (wrap.result); 
    endmethod : result

endmodule : mkIDCT_row

endpackage : MkIDCT_row
