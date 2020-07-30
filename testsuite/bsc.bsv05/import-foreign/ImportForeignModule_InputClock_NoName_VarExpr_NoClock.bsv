
import "BVI" MOD =
module mkMod (Empty ifc) ;

   let no_clock = noClock;

   // What happens when we implicitly call it "no_clock"?!
   input_clock (CLK2) = no_clock ;

endmodule

