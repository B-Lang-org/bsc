import RandTop3A::*;
import Clocks::*;

(* synthesize *)
module mkTop(Empty);
   Reg#(Nat) ctr <- mkReg(0);

   Clock defclock <- exposeCurrentClock;
   MakeResetIfc rifc0 <- mkReset(2, True, defclock);
   Reset r0 = rifc0.new_rst;

   Reg#(Bool) greg0 <- mkReg(True);
   Reg#(Bool) greg1 <- mkReg(True);
   Reg#(Bool) greg2 <- mkReg(True);
   Reg#(UInt#(4)) fr1 <- mkReg(3);

   rule steer;
      if (ctr<20) rifc0.assertReset;
      if (ctr==50) greg1 <= False;
      if (ctr==100) greg1 <= True;
      if (ctr==150) greg2 <= False;
      if (ctr==200) greg2 <= True;
      if (ctr==250) greg0 <= False;
      if (ctr==300) greg0 <= True;
      if (ctr==320) fr1 <= 7;
      if (ctr==400) $finish(0);
      
      ctr <= ctr+1;
   endrule

   ExtIfc randifc();
   mkRandTop dut(fr1, greg0, greg1, greg2, randifc, reset_by r0);
endmodule

