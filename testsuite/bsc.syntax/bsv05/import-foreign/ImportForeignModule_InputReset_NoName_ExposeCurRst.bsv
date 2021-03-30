
import "BVI" MOD =
module mkMod (Empty ifc) ;

   default_clock no_clock ;
   no_reset ;

   input_reset (RST1) <- exposeCurrentReset ;

   input_reset (RST2) <- exposeCurrentReset ;

endmodule

