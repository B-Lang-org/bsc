// test that "default_reset no_reset" is acceptable

import "BVI" MOD =
module mkMyReg ( Reg#(Bool) ) ;

   default_clock clk(CLK) ;
   default_reset no_reset ;

   method       _write(D_IN) enable(EN) ;
   method Q_OUT _read ;

endmodule
