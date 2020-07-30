// Test that an input clock cannot omit both the name and the ports

import "BVI" MOD =
module mkMyReg ( Empty ifcout ) ;

   default_clock no_clock ;
   no_reset ;

   input_clock () <- exposeCurrentClock ;

endmodule

