// Test that the user cannot declare an input reset named "no_reset"

import "BVI" MOD =
module mkMyReg ( Reset aRst, 
		 Reg#(Bool) ifcout ) ;

   default_clock no_clock ;
   default_reset rst (RSTN) <- exposeCurrentReset ;
   
   input_reset no_reset (RSTN2) = aRst ;

   method       _write(D_IN) enable(EN) ;
   method Q_OUT _read ;

endmodule

