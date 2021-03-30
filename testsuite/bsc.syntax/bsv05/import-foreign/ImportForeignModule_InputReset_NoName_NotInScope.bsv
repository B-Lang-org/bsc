
import "BVI" MOD =
module mkMod (Empty ifc) ;

   default_clock no_clock ;
   no_reset ;

   input_reset (RST1) <- exposeCurrentReset ;

   input_reset (RST2) <- exposeCurrentReset ;

   // this name should not be in scope
   port P reset_by (_rst__1) = True ;
endmodule

