// R1 trigger: multiple reset domains -> per-reset always-block groups
import Clocks::*;

(* synthesize *)
module sysStableMultiReset();
   Clock clk <- exposeCurrentClock;
   Reset rst <- exposeCurrentReset;
   Reset r1 <- mkSyncReset(2, rst, clk);
   Reset r2 <- mkAsyncReset(2, rst, clk);
   Reg#(UInt#(8)) a <- mkReg(0);
   Reg#(UInt#(8)) b <- mkReg(1, reset_by r1);
   Reg#(UInt#(8)) c <- mkReg(2, reset_by r2);
   rule ra; a <= a + 1; endrule
   rule rb; b <= b + a; endrule
   rule rc; c <= c + b; endrule
endmodule
