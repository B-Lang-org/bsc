module launderClock(Clock i, Clock o);
  return i;
endmodule

import "BVI" MOD =
module mkMod (Empty ifc) ;

   default_clock no_clock ;
   no_reset ;

   input_clock (CLK1) <- launderClock(noClock) ;

   input_clock (CLK2) <- launderClock(noClock) ;

endmodule

