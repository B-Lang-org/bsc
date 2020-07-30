// Test that input_clock and output_clock names are considered
// when generating implicit names (and that clashes are avoided)

// The names 1, 5, 7 will be chosen for the unnamed clocks

interface Ifc;
  interface Clock _clk__4;
  interface Clock _clk__6;
endinterface

import "BVI" MOD =
module mkMod (Ifc) ;

   default_clock no_clock ;
   no_reset ;

   input_clock _clk__2 (CLKA) <- exposeCurrentClock ;

   input_clock (CLK1) <- exposeCurrentClock ;

   input_clock _clk__3 (CLKB) <- exposeCurrentClock ;

   input_clock (CLK5) <- exposeCurrentClock ;

   output_clock _clk__4 (CLKC) ;

   input_clock (CLK7) <- exposeCurrentClock ;

   output_clock _clk__6 (CLKD) ;

endmodule

