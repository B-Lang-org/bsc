import Clocks::*;

(* synthesize *)
module sysNullCrossingReg();
   Clock c2 <- mkAbsoluteClock(35, 7);
   Reset r2 <- mkInitialReset(1, clocked_by c2);

   Clock c3 <- mkAbsoluteClock(45, 8);
   Reset r3 <- mkInitialReset(1, clocked_by c3);

   Reg#(Bool) start <- mkReg(True);
   Reg#(Bool) done1 <- mkReg(False, clocked_by c2, reset_by r2);
   Reg#(Bool) done2 <- mkReg(False, clocked_by c3, reset_by r3);

   CrossingReg#(int) r <- mkNullCrossingReg(noClock, 0);

   rule do_start (start);
      start <= False;
      r <= 17;
   endrule

   rule do_sync1 (!done1);
      $display("r = %d", r.crossed);
      done1 <= True;
   endrule

   rule do_sync2 (!done2);
      $display("r = %d", r.crossed);
      done2 <= True;
   endrule

   rule do_done2 (done2);
      $finish(0);
   endrule

endmodule

