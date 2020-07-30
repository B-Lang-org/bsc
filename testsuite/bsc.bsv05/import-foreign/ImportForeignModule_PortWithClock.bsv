// Test that ports can have an associated clock

import "BVI" MOD =
module mkMod ( Clock aClk,
	       Empty ifcout ) ;

   default_clock no_clock ;
   no_reset ;

   input_clock aClk(A_CLK, A_CLKGATE) = aClk ;
   
   port D_IN clocked_by (aClk) = 1;

endmodule

