// Test that ports can have port properties

import "BVI" MOD =
module mkMod ( Clock aClk,
	       Empty ifcout ) ;

   default_clock no_clock ;
   no_reset ;

   input_clock aClk(A_CLK, A_CLKGATE) = aClk ;
   
   port (* reg *) D_IN = 1;

endmodule

