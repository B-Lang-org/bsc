// Test that clashing input and output clock declarations are not permitted

interface OutClk;
   interface Clock out_clock;
endinterface

import "BVI" MOD =
module mkMyReg ( Clock aClk, OutClk ifcout ) ;

   default_clock no_clock ;
   no_reset ;

   input_clock out_clock (CLK_IN) = aClk;

   output_clock out_clock (CLK_OUT) ;
endmodule

