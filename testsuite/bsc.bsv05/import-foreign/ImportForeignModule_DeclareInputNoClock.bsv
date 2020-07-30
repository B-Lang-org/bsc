// Test that the user cannot declare an input clock named "no_clock"

import "BVI" MOD =
module mkMyReg ( Clock aClk, 
		 Reg#(Bool) ifcout ) ;

   default_clock clk (CLK, (*unused*)CLK_GATE) ;
   no_reset ;
   
   input_clock no_clock (A_CLK, A_CLKGATE) = aClk ;

   method       _write(D_IN) enable(EN) ;
   method Q_OUT _read ;

endmodule

