// Test that duplicate input clock declarations are not permitted

import "BVI" MOD =
module mkMyReg ( Clock aClk, 
		 Clock bClk, 
		 Reg#(Bool) ifcout ) ;

   default_clock no_clock ;
   no_reset ;

   input_clock  aClk(A_CLK, A_CLKGATE) = aClk ;
   // accidentally declare with same name
   input_clock  aClk(B_CLK, B_CLKGATE) = bClk ;

   method _write(D_IN) enable(EN) clocked_by(aClk) reset_by(no_reset);
   method Q_OUT _read clocked_by(aClk) reset_by(no_reset);

   schedule _read  CF  _read  ;
   schedule _read  SB  _write ;
   schedule _write SBR _write ;
endmodule

