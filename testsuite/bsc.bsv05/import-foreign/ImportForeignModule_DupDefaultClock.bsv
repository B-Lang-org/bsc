// Test that the user cannot declare default clock multiple times

import "BVI" MOD =
module mkMyReg ( Clock aClk, 
		 Clock bClk,
		 Reg#(Bool) ifcout ) ;

   default_clock aClk1 (CLK1, (*unused*)CLK_GATE1) = aClk ;
   default_clock aClk2 (CLK2, (*unused*)CLK_GATE2) = bClk ;
   no_reset;

   method       _write(D_IN) enable(EN) clocked_by(aClk1);
   method Q_OUT _read                   clocked_by(aClk1);

   //schedule _read  CF  _read  ;
   //schedule _read  SB  _write ;
   //schedule _write SBR _write ;
endmodule

