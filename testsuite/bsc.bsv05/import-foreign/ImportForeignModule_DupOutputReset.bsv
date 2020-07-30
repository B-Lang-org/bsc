// Test that duplicate output reset declarations are not permitted

interface OutRst;
   interface Reset out_reset;
endinterface

import "BVI" MOD =
module mkMyReg ( OutRst ) ;

   default_clock no_clock ;
   no_reset ;
   
   output_reset out_reset (RSTN_OUT1) ;
   output_reset out_reset (RSTN_OUT2) ;
endmodule

