
import "BVI" MOD =
module mkMod () ;

   no_reset ;

   default_clock _ (CLK1) <- exposeCurrentClock ;

   input_reset rst (RSTN) clocked_by (_) = noReset ;

endmodule

