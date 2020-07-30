// Test that duplicate input reset declarations are not permitted

import "BVI" MOD =
module mkMyReg ( Reset aRst, 
		 Reset bRst, 
		 Empty ifcout ) ;

   default_clock no_clock ;
   no_reset ;

   input_reset aRst (A_RSTN) = aRst ;
   // accidentally declare with same name
   input_reset aRst (B_RSTN) = bRst ;

endmodule

