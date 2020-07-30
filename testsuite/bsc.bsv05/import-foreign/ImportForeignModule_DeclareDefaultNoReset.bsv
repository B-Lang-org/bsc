// Test that the user cannot provide ports/expr for default reset "no_reset";

import "BVI" MOD =
module mkMyReg ( Clock aClk, 
		 Reg#(Bool) ifcout ) ;

   default_clock no_clock ;
   default_reset no_reset (RSTN) ;
   
   method       _write(D_IN) enable(EN) ;
   method Q_OUT _read ;

endmodule

