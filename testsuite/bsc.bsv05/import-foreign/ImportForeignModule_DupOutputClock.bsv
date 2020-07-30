// Test that duplicate output clock declarations are not permitted

interface OutClk;
   interface Clock out_clock;
endinterface

import "BVI" MOD =
module mkMyReg ( OutClk ) ;

   default_clock no_clock ;
   no_reset ;
   
   output_clock out_clock (CLK_OUT1) ;
   output_clock out_clock (CLK_OUT2) ;
endmodule

