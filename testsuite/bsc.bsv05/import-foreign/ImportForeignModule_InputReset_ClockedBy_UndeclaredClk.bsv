
import "BVI" MOD =
module mkMod () ;

   default_clock no_clock ;
   no_reset ;

   input_clock clk (CLK) <- exposeCurrentClock ;

   // use the wrong name here
   input_reset rst (RSTN) clocked_by (foo) = noReset;

endmodule

