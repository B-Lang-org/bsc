// Test that the user can't use "default_reset" with input reset details
// for a name already declared as an input reset

// This version tests for just the port provided.

import "BVI" MOD =
module mkMod ( Reset aRst, 
	       Empty ifcout ) ;

   default_clock no_clock ;

   input_reset rst (RSTN) = aRst ;
   default_reset rst (RSTN2) ;
endmodule

