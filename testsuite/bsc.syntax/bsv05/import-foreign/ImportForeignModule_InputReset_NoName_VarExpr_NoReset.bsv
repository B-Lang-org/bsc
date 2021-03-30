
import "BVI" MOD =
module mkMod (Empty ifc) ;

   let no_reset = noReset;

   // What happens when we implicitly call it "no_reset"?!
   input_reset (RST2) = no_reset ;

endmodule

