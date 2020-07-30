// Test that ports can have an associated reset

import "BVI" MOD =
module mkMod ( Clock aClk, Reset aRst,
	       Empty ifcout ) ;

   default_clock no_clock ;
   no_reset ;

   input_clock aClk(A_CLK, A_CLKGATE) = aClk ;
   input_reset aRst(A_RSTN) clocked_by (aClk) = aRst ;
   
   port D_IN clocked_by (aClk) reset_by (aRst) = 1;

endmodule

