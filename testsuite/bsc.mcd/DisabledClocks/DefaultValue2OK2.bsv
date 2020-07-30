import Clocks::*;
import AlwaysWrite::*;

(* synthesize *)
module mkDefaultValue2OK2();

   module mkSharedClock(Clock);
      return(primMakeDisabledClock);
   endmodule

   let sharedClock <- mkSharedClock;

   WriteOnly#(UInt#(12)) d1 <- mkAlwaysWrite(clocked_by sharedClock);
   WriteOnly#(UInt#(12)) d2 <- mkAlwaysWrite(clocked_by sharedClock);

   rule handle_defaults;
       d1 <= 97;
       d2 <= 29;
   endrule

endmodule

