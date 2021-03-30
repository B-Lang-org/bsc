// Test that an undeclared reset is detected in port statements

import "BVI" MOD =
module mkMod ( Empty ifcout ) ;

   port D_IN reset_by (c) = 1;

endmodule

