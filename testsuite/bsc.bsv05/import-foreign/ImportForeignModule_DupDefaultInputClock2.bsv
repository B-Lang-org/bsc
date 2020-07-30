// Test that the user can't use "default_clock" with input clock details
// for a name already declared as an input clock

// This version tests for just the port provided.

import "BVI" MOD =
module mkMod ( Clock aClk, 
	       Empty ifcout ) ;

   input_clock clk (CLK) = aClk ;
   default_clock clk (CLK2) ;

   no_reset ;
endmodule

