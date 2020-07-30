// Test that clashing input and output reset declarations are not permitted

interface OutRst;
   interface Reset out_reset;
endinterface

import "BVI" MOD =
module mkMyReg ( Reset aRst, OutRst ifcout ) ;

   default_clock no_clock ;
   no_reset ;

   input_reset out_reset (RSTN_IN) = aRst ;
   
   output_reset out_reset (RSTN_OUT) ;
endmodule

