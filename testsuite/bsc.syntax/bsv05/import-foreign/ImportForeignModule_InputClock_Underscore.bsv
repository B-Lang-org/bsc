
import "BVI" MOD =
module mkMod () ;

   default_clock no_clock ;
   no_reset ;

   input_clock _ (CLK1) <- exposeCurrentClock ;

   input_reset rst (RSTN) clocked_by (_) = noReset;

endmodule

