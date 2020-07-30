// Test that the user can't use "default_clock" with input clock details
// for a name already declared as an input clock

import "BVI" MOD =
module mkMod ( Clock aClk, 
	       Clock bClk, 
	       Empty ifcout ) ;

   input_clock clk (CLK) = aClk ;
   default_clock clk (CLK2) = bClk ;

   no_reset ;
endmodule

