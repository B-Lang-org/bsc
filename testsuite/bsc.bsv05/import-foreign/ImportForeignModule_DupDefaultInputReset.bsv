// Test that the user can't use "default_reset" with input reset details
// for a name already declared as an input reset

import "BVI" MOD =
module mkMod ( Reset aRst, 
	       Reset bRst, 
	       Empty ifcout ) ;

   default_clock no_clock ;

   input_reset rst (RSTN) = aRst ;
   default_reset rst (RSTN2) = bRst ;
endmodule

