// Test that the user cannot declare a ready multiple times

import "BVI" MOD =
module mkMyReg ( Reg#(Bool) ifcout ) ;

   default_clock clk (CLK);
   no_reset;

   method       _write(D_IN) ready(RDY_W) enable(EN) ready(RDY);
   method Q_OUT _read;

   //schedule _read  CF  _read  ;
   //schedule _read  SB  _write ;
   //schedule _write SBR _write ;
endmodule

