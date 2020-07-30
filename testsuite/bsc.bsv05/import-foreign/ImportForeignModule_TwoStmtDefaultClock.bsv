// Test that the user can declare an input clock as the default clock

import "BVI" MOD =
module mkMod ( Clock aClk, 
	       Empty ifcout ) ;

   input_clock clk (CLK) = aClk ;
   default_clock clk ;

   no_reset ;
endmodule

