// Test that the user cannot declare default reset multiple times

import "BVI" MOD =
module mkMyReg ( Reset aRst,
		 Reset aRst,
		 Empty ifcout ) ;

   no_clok ;
   default_reset aRst1 (RSTN1) = aRst ;
   default_reset aRst2 (RSTN2) = aRst ;

endmodule

