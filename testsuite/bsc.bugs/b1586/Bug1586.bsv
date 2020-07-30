import Clocks::*;

module mkResetCombined();
   Clock c <- exposeCurrentClock;
   Reset r <- exposeCurrentReset;
   ReadOnly#(Bool) sInReset_val = isResetAsserted(clocked_by c, reset_by r);
endmodule

