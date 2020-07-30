import RandTop5::*;
import Clocks::*;

interface Bool2ResetIfc;
   method Reset r();
endinterface

(* synthesize *)
module mkTop(Empty);
   Reg#(Nat) ctr <- mkReg(0);

   Clock uc0 <- mkAbsoluteClock(10,17);
   Clock uc1 <- mkAbsoluteClock(10,29);
   Clock uc2 <- mkAbsoluteClock(10,37);

   GatedClockIfc g0 <- mkGatedClock (True, uc0);
   GatedClockIfc g1 <- mkGatedClock (True, uc1);
   GatedClockIfc g2 <- mkGatedClock (True, uc2);
   Clock c0 = g0.new_clk;
   Clock c1 = g1.new_clk;
   Clock c2 = g2.new_clk;

   MakeResetIfc rifc0 <- mkReset(1, True, c0);
   MakeResetIfc rifc1 <- mkReset(1, True, c1);
   MakeResetIfc rifc2 <- mkReset(1, True, c2);
   Reset r0 = rifc0.new_rst;
   Reset r1 = rifc1.new_rst;
   Reset r2 = rifc2.new_rst;
   
   rule steer;
      if (ctr<10)
	 begin
	    rifc0.assertReset;
	    rifc1.assertReset;
	    rifc2.assertReset;
	 end
      if (ctr==50) g1.setGateCond(False);
      if (ctr==100) g1.setGateCond(True);
      if (ctr==150) g2.setGateCond(False);
      if (ctr==200) g2.setGateCond(True);
      if (ctr==250) g0.setGateCond(False);
      if (ctr==300) g0.setGateCond(True);
//      if (ctr==350) g1.setGateCond(False);
      if ((ctr>=360) && (ctr<380)) rifc1.assertReset;
//      if (ctr==370) g1.setGateCond(True);
      if (ctr==400) $finish(0);
      
      ctr <= ctr+1;
   endrule

   ExtIfc randifc();
   mkRandTop dut(c1, r1, c2, r2, randifc, clocked_by c0, reset_by r0);
endmodule

