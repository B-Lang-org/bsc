import Clocks::*;
import AlwaysWrite::*;

(* synthesize *)
module mkDefaultValue1();

   WriteOnly#(UInt#(7)) d1 <- mkAlwaysWrite(clocked_by primMakeDisabledClock);

   rule handle_d1;
       d1 <= 5;
   endrule

endmodule

