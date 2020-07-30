import Clocks::*;
import AlwaysWrite::*;

// should fail with a clock-crossing error because of different disabled clocks
(* synthesize *)
module mkDefaultValue2Broken();

   WriteOnly#(UInt#(66)) d1 <- mkAlwaysWrite(clocked_by primMakeDisabledClock);
   WriteOnly#(UInt#(99)) d2 <- mkAlwaysWrite(clocked_by primMakeDisabledClock);

   rule handle_defaults;
       d1 <= 17;
       d2 <= 23;
   endrule

endmodule

