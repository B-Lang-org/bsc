
import "BVI" MOD =
module mkMod (Empty ifc) ;

   let default_clock = noClock;

   default_clock no_clock ;
   no_reset ;

   // What happens when we implicitly call it "default_clock"?!
   input_clock (CLK) = default_clock ;

endmodule

