import Clocks::*;

(* synthesize *)
module sysEUndetReset2(Empty);

  Clock c <- exposeCurrentClock;

  Reset r <- mkSyncReset(1, ?, c);

  Reg#(Bool) s();
  mkReg#(False) the_s(s, reset_by r);
 
endmodule


