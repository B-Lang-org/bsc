// Test that the user cannot declare an output clock named "no_clock"

interface OutClk;
   interface Clock no_clock;
endinterface

import "BVI" MOD =
module mkMyReg ( OutClk ) ;

   default_clock clk (CLK, (*unused*)CLK_GATE) ;
   no_reset ;
   
   output_clock no_clock (CLK_OUT) ;
endmodule

