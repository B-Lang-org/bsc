// Test that the user cannot declare an output reset named "no_reset"

interface OutRst;
   interface Reset no_reset;
endinterface

import "BVI" MOD =
module mkMyReg ( OutRst ) ;

   default_clock no_clock ;
   default_reset rst <- exposeCurrentReset ;
   
   output_reset no_reset (RSTN_OUT);

endmodule

