
import "BVI" MOD =
module mkMod () ;

   default_reset _ (RST1) <- exposeCurrentReset ;

   port P reset_by (_) = True ;

endmodule

