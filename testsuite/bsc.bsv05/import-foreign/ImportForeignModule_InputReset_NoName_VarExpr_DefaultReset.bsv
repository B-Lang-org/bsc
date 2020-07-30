
import "BVI" MOD =
module mkMod (Empty ifc) ;

   let default_reset = noReset ;

   default_clock no_clock ;
   no_reset ;

   // What happens when we implicitly call it "default_reset"?!
   input_reset (RSTN) = default_reset ;

endmodule

