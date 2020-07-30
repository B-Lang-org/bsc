module launderReset(Reset i, Reset o);
  return i;
endmodule

import "BVI" MOD =
module mkMod (Empty ifc) ;

   default_clock no_clock ;
   no_reset ;

   input_reset (RST1) <- launderReset(noReset) ;

   input_reset (RST2) <- launderReset(noReset) ;

endmodule

