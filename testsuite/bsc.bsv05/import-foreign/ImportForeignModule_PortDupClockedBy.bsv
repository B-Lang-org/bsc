// Test that the user cannot declare a port clocked_by multiple times

import "BVI" MOD =
module mkMyReg ( Clock aClk, 
		 Clock bClk,
		 Bool b,
		 Reg#(Bool) ifcout ) ;

   default_clock no_clock;
   no_reset;

   input_clock aClk1 (CLK1, (*unused*)CLK_GATE1) = aClk ;
   input_clock aClk2 (CLK2, (*unused*)CLK_GATE2) = bClk ;

   port B clocked_by(aClk1) clocked_by(aClk2) = b;

   method       _write(D_IN) enable(EN) clocked_by(aClk1);
   method Q_OUT _read                   clocked_by(aClk1);

   //schedule _read  CF  _read  ;
   //schedule _read  SB  _write ;
   //schedule _write SBR _write ;
endmodule

