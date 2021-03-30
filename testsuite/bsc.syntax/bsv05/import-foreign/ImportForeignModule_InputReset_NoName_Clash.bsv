// Test that input_reset and output_reset names are considered
// when generating implicit names (and that clashes are avoided)

// The names 1, 5, 7 will be chosen for the unnamed resets

interface Ifc;
  interface Reset _rst__4;
  interface Reset _rst__6;
endinterface

import "BVI" MOD =
module mkMod (Ifc) ;

   default_clock no_clock ;
   no_reset ;

   input_reset _rst__2 (RSTA) <- exposeCurrentReset ;

   input_reset (RST1) <- exposeCurrentReset ;

   input_reset _rst__3 (RSTB) <- exposeCurrentReset ;

   input_reset (RST5) <- exposeCurrentReset ;

   output_reset _rst__4 (RSTC) ;

   input_reset (RST7) <- exposeCurrentReset ;

   output_reset _rst__6 (RSTD) ;

endmodule

