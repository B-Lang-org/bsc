
import "BVI" MOD =
module mkMod (Empty ifc) ;

   default_clock no_clock ;
   no_reset ;

   input_clock (CLK1) <- exposeCurrentClock ;

   input_clock (CLK2) <- exposeCurrentClock ;

endmodule

