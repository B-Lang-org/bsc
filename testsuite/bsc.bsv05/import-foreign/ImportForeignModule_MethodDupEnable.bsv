// Test that the user cannot declare an enable multiple times

import "BVI" MOD =
module mkMyReg ( Reg#(Bool) ifcout ) ;

   default_clock clk (CLK);
   no_reset;

   method       _write(D_IN) enable(EN) ready(RDY_W) enable(EN2);
   method Q_OUT _read;

   //schedule _read  CF  _read  ;
   //schedule _read  SB  _write ;
   //schedule _write SBR _write ;
endmodule

