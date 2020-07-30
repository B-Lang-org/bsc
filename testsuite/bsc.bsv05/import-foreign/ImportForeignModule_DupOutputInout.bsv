// Test that the user cannot declare the same ifc Inout multiple times

interface Ifc;
  interface Inout#(Bool) io;
endinterface

import "BVI" MOD =
module mkMyReg ( Ifc ) ;

   default_clock clk (CLK);
   no_reset;

   ifc_inout io(IO1);
   ifc_inout io(IO2);
endmodule

