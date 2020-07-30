import Clocks::*;
import AlwaysWrite::*;

(* synthesize *)
module mkDefaultValue2OK1();

   WriteOnly#(UInt#(92)) d1 <- mkAlwaysWrite(clocked_by primMakeDisabledClock);
   WriteOnly#(UInt#(17)) d2 <- mkAlwaysWrite(clocked_by primMakeDisabledClock);

   rule handle_d1;
       d1 <= 99;
   endrule
   
   rule handle_d2;
       d2 <= 73;
   endrule

endmodule

