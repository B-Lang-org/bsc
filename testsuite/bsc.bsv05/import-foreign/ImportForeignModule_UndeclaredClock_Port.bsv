// Test that an undeclared clock is detected in port statements

import "BVI" MOD =
module mkMod ( Empty ifcout ) ;

   port D_IN clocked_by (c) = 1;

endmodule

