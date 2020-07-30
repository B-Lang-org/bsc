// Test that the user can declare an input reset as the default reset

import "BVI" MOD =
module mkMod ( Reset aRst, 
	       Empty ifcout ) ;

   default_clock no_clock ;

   input_reset rst (RSTN) = aRst ;
   default_reset rst ;
endmodule

